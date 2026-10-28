(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.H Require GcFlushU15.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.grayquant_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)



(* [comment removed for export] *)
Definition W_16a44 : bv 32 := 0xff010113.
Lemma F_16a44 : fetch_word Ubsan.M.loaded_segments (0x16b48 : word) = Some W_16a44.
Proof. vm_refl. Qed.
Lemma D_16a44 : decode_any W_16a44 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16a48 : bv 32 := 0x00113423.
Lemma F_16a48 : fetch_word Ubsan.M.loaded_segments (0x16b4c : word) = Some W_16a48.
Proof. vm_refl. Qed.
Lemma D_16a48 : decode_any W_16a48 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16a4c : bv 32 := 0x00813023.
Lemma F_16a4c : fetch_word Ubsan.M.loaded_segments (0x16b50 : word) = Some W_16a4c.
Proof. vm_refl. Qed.
Lemma D_16a4c : decode_any W_16a4c = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16a50 : bv 32 := 0x098000ef.
Lemma F_16a50 : fetch_word Ubsan.M.loaded_segments (0x16b54 : word) = Some W_16a50.
Proof. vm_refl. Qed.
Lemma D_16a50 : decode_any W_16a50 = Some (Jal 1 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16a54 : bv 32 := 0x04050263.
Lemma F_16a54 : fetch_word Ubsan.M.loaded_segments (0x16b58 : word) = Some W_16a54.
Proof. vm_refl. Qed.
Lemma D_16a54 : decode_any W_16a54 = Some (Branch BC_EQ 10 0 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16a58 : bv 32 := 0x00757593.
Lemma F_16a58 : fetch_word Ubsan.M.loaded_segments (0x16b5c : word) = Some W_16a58.
Proof. vm_refl. Qed.
Lemma D_16a58 : decode_any W_16a58 = Some (OpImm ALU_AND 11 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16a5c : bv 32 := 0x08059463.
Lemma F_16a5c : fetch_word Ubsan.M.loaded_segments (0x16b60 : word) = Some W_16a5c.
Proof. vm_refl. Qed.
Lemma D_16a5c : decode_any W_16a5c = Some (Branch BC_NE 11 0 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16a60 : bv 32 := 0x01056583.
Lemma F_16a60 : fetch_word Ubsan.M.loaded_segments (0x16b64 : word) = Some W_16a60.
Proof. vm_refl. Qed.
Lemma D_16a60 : decode_any W_16a60 = Some (Load SZ4 false 11 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16a64 : bv 32 := 0x00456603.
Lemma F_16a64 : fetch_word Ubsan.M.loaded_segments (0x16b68 : word) = Some W_16a64.
Proof. vm_refl. Qed.
Lemma D_16a64 : decode_any W_16a64 = Some (Load SZ4 false 12 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16a68 : bv 32 := 0x00259593.
Lemma F_16a68 : fetch_word Ubsan.M.loaded_segments (0x16b6c : word) = Some W_16a68.
Proof. vm_refl. Qed.
Lemma D_16a68 : decode_any W_16a68 = Some (ShiftImm ALU_SLL 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16a6c : bv 32 := 0x02c596b3.
Lemma F_16a6c : fetch_word Ubsan.M.loaded_segments (0x16b70 : word) = Some W_16a6c.
Proof. vm_refl. Qed.
Lemma D_16a6c : decode_any W_16a6c = Some (Mul M_MULH 13 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16a70 : bv 32 := 0x02c58633.
Lemma F_16a70 : fetch_word Ubsan.M.loaded_segments (0x16b74 : word) = Some W_16a70.
Proof. vm_refl. Qed.
Lemma D_16a70 : decode_any W_16a70 = Some (Mul M_MUL 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16a74 : bv 32 := 0x43f65593.
Lemma F_16a74 : fetch_word Ubsan.M.loaded_segments (0x16b78 : word) = Some W_16a74.
Proof. vm_refl. Qed.
Lemma D_16a74 : decode_any W_16a74 = Some (ShiftImm ALU_SRA 11 12 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16a78 : bv 32 := 0x06b69663.
Lemma F_16a78 : fetch_word Ubsan.M.loaded_segments (0x16b7c : word) = Some W_16a78.
Proof. vm_refl. Qed.
Lemma D_16a78 : decode_any W_16a78 = Some (Branch BC_NE 13 11 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16a7c : bv 32 := 0x03853583.
Lemma F_16a7c : fetch_word Ubsan.M.loaded_segments (0x16b80 : word) = Some W_16a7c.
Proof. vm_refl. Qed.
Lemma D_16a7c : decode_any W_16a7c = Some (Load SZ8 true 11 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16a80 : bv 32 := 0x00050413.
Lemma F_16a80 : fetch_word Ubsan.M.loaded_segments (0x16b84 : word) = Some W_16a80.
Proof. vm_refl. Qed.
Lemma D_16a80 : decode_any W_16a80 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16a84 : bv 32 := 0x00058513.
Lemma F_16a84 : fetch_word Ubsan.M.loaded_segments (0x16b88 : word) = Some W_16a84.
Proof. vm_refl. Qed.
Lemma D_16a84 : decode_any W_16a84 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16a88 : bv 32 := 0x00000593.
Lemma F_16a88 : fetch_word Ubsan.M.loaded_segments (0x16b8c : word) = Some W_16a88.
Proof. vm_refl. Qed.
Lemma D_16a88 : decode_any W_16a88 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16a8c : bv 32 := 0x7391b0ef.
Lemma F_16a8c : fetch_word Ubsan.M.loaded_segments (0x16b90 : word) = Some W_16a8c.
Proof. vm_refl. Qed.
Lemma D_16a8c : decode_any W_16a8c = Some (Jal 1 114488, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16a90 : bv 32 := 0x00040513.
Lemma F_16a90 : fetch_word Ubsan.M.loaded_segments (0x16b94 : word) = Some W_16a90.
Proof. vm_refl. Qed.
Lemma D_16a90 : decode_any W_16a90 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16a94 : bv 32 := 0x0400006f.
Lemma F_16a94 : fetch_word Ubsan.M.loaded_segments (0x16b98 : word) = Some W_16a94.
Proof. vm_refl. Qed.
Lemma D_16a94 : decode_any W_16a94 = Some (Jal 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16a98 : bv 32 := 0x0001d517.
Lemma F_16a98 : fetch_word Ubsan.M.loaded_segments (0x16b9c : word) = Some W_16a98.
Proof. vm_refl. Qed.
Lemma D_16a98 : decode_any W_16a98 = Some (Auipc 10 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16a9c : bv 32 := 0x65c53503.
Lemma F_16a9c : fetch_word Ubsan.M.loaded_segments (0x16ba0 : word) = Some W_16a9c.
Proof. vm_refl. Qed.
Lemma D_16a9c : decode_any W_16a9c = Some (Load SZ8 true 10 10 1628, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16aa0 : bv 32 := 0x00052503.
Lemma F_16aa0 : fetch_word Ubsan.M.loaded_segments (0x16ba4 : word) = Some W_16aa0.
Proof. vm_refl. Qed.
Lemma D_16aa0 : decode_any W_16aa0 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16aa4 : bv 32 := 0x00500593.
Lemma F_16aa4 : fetch_word Ubsan.M.loaded_segments (0x16ba8 : word) = Some W_16aa4.
Proof. vm_refl. Qed.
Lemma D_16aa4 : decode_any W_16aa4 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16aa8 : bv 32 := 0x02a5c463.
Lemma F_16aa8 : fetch_word Ubsan.M.loaded_segments (0x16bac : word) = Some W_16aa8.
Proof. vm_refl. Qed.
Lemma D_16aa8 : decode_any W_16aa8 = Some (Branch BC_LT 11 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16aac : bv 32 := 0xffffa517.
Lemma F_16aac : fetch_word Ubsan.M.loaded_segments (0x16bb0 : word) = Some W_16aac.
Proof. vm_refl. Qed.
Lemma D_16aac : decode_any W_16aac = Some (Auipc 10 1048570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16ab0 : bv 32 := 0xffffa597.
Lemma F_16ab0 : fetch_word Ubsan.M.loaded_segments (0x16bb4 : word) = Some W_16ab0.
Proof. vm_refl. Qed.
Lemma D_16ab0 : decode_any W_16ab0 = Some (Auipc 11 1048570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16ab4 : bv 32 := 0x96f50513.
Lemma F_16ab4 : fetch_word Ubsan.M.loaded_segments (0x16bb8 : word) = Some W_16ab4.
Proof. vm_refl. Qed.
Lemma D_16ab4 : decode_any W_16ab4 = Some (OpImm ALU_ADD 10 10 2415, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16ab8 : bv 32 := 0xc9858593.
Lemma F_16ab8 : fetch_word Ubsan.M.loaded_segments (0x16bbc : word) = Some W_16ab8.
Proof. vm_refl. Qed.
Lemma D_16ab8 : decode_any W_16ab8 = Some (OpImm ALU_ADD 11 11 3224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16abc : bv 32 := 0x00000613.
Lemma F_16abc : fetch_word Ubsan.M.loaded_segments (0x16bc0 : word) = Some W_16abc.
Proof. vm_refl. Qed.
Lemma D_16abc : decode_any W_16abc = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16ac0 : bv 32 := 0x00813083.
Lemma F_16ac0 : fetch_word Ubsan.M.loaded_segments (0x16bc4 : word) = Some W_16ac0.
Proof. vm_refl. Qed.
Lemma D_16ac0 : decode_any W_16ac0 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16ac4 : bv 32 := 0x00013403.
Lemma F_16ac4 : fetch_word Ubsan.M.loaded_segments (0x16bc8 : word) = Some W_16ac4.
Proof. vm_refl. Qed.
Lemma D_16ac4 : decode_any W_16ac4 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16ac8 : bv 32 := 0x01010113.
Lemma F_16ac8 : fetch_word Ubsan.M.loaded_segments (0x16bcc : word) = Some W_16ac8.
Proof. vm_refl. Qed.
Lemma D_16ac8 : decode_any W_16ac8 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16acc : bv 32 := 0x9edfe06f.
Lemma F_16acc : fetch_word Ubsan.M.loaded_segments (0x16bd0 : word) = Some W_16acc.
Proof. vm_refl. Qed.
Lemma D_16acc : decode_any W_16acc = Some (Jal 0 2091500, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16ad4 : bv 32 := 0x00813083.
Lemma F_16ad4 : fetch_word Ubsan.M.loaded_segments (0x16bd8 : word) = Some W_16ad4.
Proof. vm_refl. Qed.
Lemma D_16ad4 : decode_any W_16ad4 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16ad8 : bv 32 := 0x00013403.
Lemma F_16ad8 : fetch_word Ubsan.M.loaded_segments (0x16bdc : word) = Some W_16ad8.
Proof. vm_refl. Qed.
Lemma D_16ad8 : decode_any W_16ad8 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16adc : bv 32 := 0x01010113.
Lemma F_16adc : fetch_word Ubsan.M.loaded_segments (0x16be0 : word) = Some W_16adc.
Proof. vm_refl. Qed.
Lemma D_16adc : decode_any W_16adc = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16ae0 : bv 32 := 0x00008067.
Lemma F_16ae0 : fetch_word Ubsan.M.loaded_segments (0x16be4 : word) = Some W_16ae0.
Proof. vm_refl. Qed.
Lemma D_16ae0 : decode_any W_16ae0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16ae8 : bv 32 := 0xfe010113.
Lemma F_16ae8 : fetch_word Ubsan.M.loaded_segments (0x16bec : word) = Some W_16ae8.
Proof. vm_refl. Qed.
Lemma D_16ae8 : decode_any W_16ae8 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16aec : bv 32 := 0x00113c23.
Lemma F_16aec : fetch_word Ubsan.M.loaded_segments (0x16bf0 : word) = Some W_16aec.
Proof. vm_refl. Qed.
Lemma D_16aec : decode_any W_16aec = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16af0 : bv 32 := 0x00813823.
Lemma F_16af0 : fetch_word Ubsan.M.loaded_segments (0x16bf4 : word) = Some W_16af0.
Proof. vm_refl. Qed.
Lemma D_16af0 : decode_any W_16af0 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16af4 : bv 32 := 0x00913423.
Lemma F_16af4 : fetch_word Ubsan.M.loaded_segments (0x16bf8 : word) = Some W_16af4.
Proof. vm_refl. Qed.
Lemma D_16af4 : decode_any W_16af4 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16af8 : bv 32 := 0x00058493.
Lemma F_16af8 : fetch_word Ubsan.M.loaded_segments (0x16bfc : word) = Some W_16af8.
Proof. vm_refl. Qed.
Lemma D_16af8 : decode_any W_16af8 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16afc : bv 32 := 0x134000ef.
Lemma F_16afc : fetch_word Ubsan.M.loaded_segments (0x16c00 : word) = Some W_16afc.
Proof. vm_refl. Qed.
Lemma D_16afc : decode_any W_16afc = Some (Jal 1 308, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16b00 : bv 32 := 0x04050863.
Lemma F_16b00 : fetch_word Ubsan.M.loaded_segments (0x16c04 : word) = Some W_16b00.
Proof. vm_refl. Qed.
Lemma D_16b00 : decode_any W_16b00 = Some (Branch BC_EQ 10 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16b04 : bv 32 := 0x00050413.
Lemma F_16b04 : fetch_word Ubsan.M.loaded_segments (0x16c08 : word) = Some W_16b04.
Proof. vm_refl. Qed.
Lemma D_16b04 : decode_any W_16b04 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16b08 : bv 32 := 0x00757513.
Lemma F_16b08 : fetch_word Ubsan.M.loaded_segments (0x16c0c : word) = Some W_16b08.
Proof. vm_refl. Qed.
Lemma D_16b08 : decode_any W_16b08 = Some (OpImm ALU_AND 10 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16b0c : bv 32 := 0x12051063.
Lemma F_16b0c : fetch_word Ubsan.M.loaded_segments (0x16c10 : word) = Some W_16b0c.
Proof. vm_refl. Qed.
Lemma D_16b0c : decode_any W_16b0c = Some (Branch BC_NE 10 0 288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16b10 : bv 32 := 0x01042503.
Lemma F_16b10 : fetch_word Ubsan.M.loaded_segments (0x16c14 : word) = Some W_16b10.
Proof. vm_refl. Qed.
Lemma D_16b10 : decode_any W_16b10 = Some (Load SZ4 true 10 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16b14 : bv 32 := 0x00251513.
Lemma F_16b14 : fetch_word Ubsan.M.loaded_segments (0x16c18 : word) = Some W_16b14.
Proof. vm_refl. Qed.
Lemma D_16b14 : decode_any W_16b14 = Some (ShiftImm ALU_SLL 10 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16b18 : bv 32 := 0x029515b3.
Lemma F_16b18 : fetch_word Ubsan.M.loaded_segments (0x16c1c : word) = Some W_16b18.
Proof. vm_refl. Qed.
Lemma D_16b18 : decode_any W_16b18 = Some (Mul M_MULH 11 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16b1c : bv 32 := 0x02950533.
Lemma F_16b1c : fetch_word Ubsan.M.loaded_segments (0x16c20 : word) = Some W_16b1c.
Proof. vm_refl. Qed.
Lemma D_16b1c : decode_any W_16b1c = Some (Mul M_MUL 10 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16b20 : bv 32 := 0x43f55613.
Lemma F_16b20 : fetch_word Ubsan.M.loaded_segments (0x16c24 : word) = Some W_16b20.
Proof. vm_refl. Qed.
Lemma D_16b20 : decode_any W_16b20 = Some (ShiftImm ALU_SRA 12 10 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16b24 : bv 32 := 0x10c59463.
Lemma F_16b24 : fetch_word Ubsan.M.loaded_segments (0x16c28 : word) = Some W_16b24.
Proof. vm_refl. Qed.
Lemma D_16b24 : decode_any W_16b24 = Some (Branch BC_NE 11 12 264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16b28 : bv 32 := 0x0001e597.
Lemma F_16b28 : fetch_word Ubsan.M.loaded_segments (0x16c2c : word) = Some W_16b28.
Proof. vm_refl. Qed.
Lemma D_16b28 : decode_any W_16b28 = Some (Auipc 11 30, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16b2c : bv 32 := 0x64c58493.
Lemma F_16b2c : fetch_word Ubsan.M.loaded_segments (0x16c30 : word) = Some W_16b2c.
Proof. vm_refl. Qed.
Lemma D_16b2c : decode_any W_16b2c = Some (OpImm ALU_ADD 9 11 1612, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16b30 : bv 32 := 0x0004b583.
Lemma F_16b30 : fetch_word Ubsan.M.loaded_segments (0x16c34 : word) = Some W_16b30.
Proof. vm_refl. Qed.
Lemma D_16b30 : decode_any W_16b30 = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16b34 : bv 32 := 0x000580e7.
Lemma F_16b34 : fetch_word Ubsan.M.loaded_segments (0x16c38 : word) = Some W_16b34.
Proof. vm_refl. Qed.
Lemma D_16b34 : decode_any W_16b34 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16b38 : bv 32 := 0x04050a63.
Lemma F_16b38 : fetch_word Ubsan.M.loaded_segments (0x16c3c : word) = Some W_16b38.
Proof. vm_refl. Qed.
Lemma D_16b38 : decode_any W_16b38 = Some (Branch BC_EQ 10 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16b3c : bv 32 := 0x02a43c23.
Lemma F_16b3c : fetch_word Ubsan.M.loaded_segments (0x16c40 : word) = Some W_16b3c.
Proof. vm_refl. Qed.
Lemma D_16b3c : decode_any W_16b3c = Some (Store SZ8 8 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16b40 : bv 32 := 0x00040513.
Lemma F_16b40 : fetch_word Ubsan.M.loaded_segments (0x16c44 : word) = Some W_16b40.
Proof. vm_refl. Qed.
Lemma D_16b40 : decode_any W_16b40 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16b44 : bv 32 := 0x00000593.
Lemma F_16b44 : fetch_word Ubsan.M.loaded_segments (0x16c48 : word) = Some W_16b44.
Proof. vm_refl. Qed.
Lemma D_16b44 : decode_any W_16b44 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16b48 : bv 32 := 0x560010ef.
Lemma F_16b48 : fetch_word Ubsan.M.loaded_segments (0x16c4c : word) = Some W_16b48.
Proof. vm_refl. Qed.
Lemma D_16b48 : decode_any W_16b48 = Some (Jal 1 5472, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16b4c : bv 32 := 0x0c80006f.
Lemma F_16b4c : fetch_word Ubsan.M.loaded_segments (0x16c50 : word) = Some W_16b4c.
Proof. vm_refl. Qed.
Lemma D_16b4c : decode_any W_16b4c = Some (Jal 0 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16b50 : bv 32 := 0x0001d517.
Lemma F_16b50 : fetch_word Ubsan.M.loaded_segments (0x16c54 : word) = Some W_16b50.
Proof. vm_refl. Qed.
Lemma D_16b50 : decode_any W_16b50 = Some (Auipc 10 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16b54 : bv 32 := 0x5a453503.
Lemma F_16b54 : fetch_word Ubsan.M.loaded_segments (0x16c58 : word) = Some W_16b54.
Proof. vm_refl. Qed.
Lemma D_16b54 : decode_any W_16b54 = Some (Load SZ8 true 10 10 1444, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16b58 : bv 32 := 0x00052503.
Lemma F_16b58 : fetch_word Ubsan.M.loaded_segments (0x16c5c : word) = Some W_16b58.
Proof. vm_refl. Qed.
Lemma D_16b58 : decode_any W_16b58 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16b5c : bv 32 := 0x00500593.
Lemma F_16b5c : fetch_word Ubsan.M.loaded_segments (0x16c60 : word) = Some W_16b5c.
Proof. vm_refl. Qed.
Lemma D_16b5c : decode_any W_16b5c = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16b60 : bv 32 := 0x0aa5c863.
Lemma F_16b60 : fetch_word Ubsan.M.loaded_segments (0x16c64 : word) = Some W_16b60.
Proof. vm_refl. Qed.
Lemma D_16b60 : decode_any W_16b60 = Some (Branch BC_LT 11 10 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16b64 : bv 32 := 0xffffa517.
Lemma F_16b64 : fetch_word Ubsan.M.loaded_segments (0x16c68 : word) = Some W_16b64.
Proof. vm_refl. Qed.
Lemma D_16b64 : decode_any W_16b64 = Some (Auipc 10 1048570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16b68 : bv 32 := 0xffffa597.
Lemma F_16b68 : fetch_word Ubsan.M.loaded_segments (0x16c6c : word) = Some W_16b68.
Proof. vm_refl. Qed.
Lemma D_16b68 : decode_any W_16b68 = Some (Auipc 11 1048570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16b6c : bv 32 := 0x8b750513.
Lemma F_16b6c : fetch_word Ubsan.M.loaded_segments (0x16c70 : word) = Some W_16b6c.
Proof. vm_refl. Qed.
Lemma D_16b6c : decode_any W_16b6c = Some (OpImm ALU_ADD 10 10 2231, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16b70 : bv 32 := 0xa6258593.
Lemma F_16b70 : fetch_word Ubsan.M.loaded_segments (0x16c74 : word) = Some W_16b70.
Proof. vm_refl. Qed.
Lemma D_16b70 : decode_any W_16b70 = Some (OpImm ALU_ADD 11 11 2658, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16b74 : bv 32 := 0x00000613.
Lemma F_16b74 : fetch_word Ubsan.M.loaded_segments (0x16c78 : word) = Some W_16b74.
Proof. vm_refl. Qed.
Lemma D_16b74 : decode_any W_16b74 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16b78 : bv 32 := 0x01813083.
Lemma F_16b78 : fetch_word Ubsan.M.loaded_segments (0x16c7c : word) = Some W_16b78.
Proof. vm_refl. Qed.
Lemma D_16b78 : decode_any W_16b78 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16b7c : bv 32 := 0x01013403.
Lemma F_16b7c : fetch_word Ubsan.M.loaded_segments (0x16c80 : word) = Some W_16b7c.
Proof. vm_refl. Qed.
Lemma D_16b7c : decode_any W_16b7c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16b80 : bv 32 := 0x00813483.
Lemma F_16b80 : fetch_word Ubsan.M.loaded_segments (0x16c84 : word) = Some W_16b80.
Proof. vm_refl. Qed.
Lemma D_16b80 : decode_any W_16b80 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16b84 : bv 32 := 0x02010113.
Lemma F_16b84 : fetch_word Ubsan.M.loaded_segments (0x16c88 : word) = Some W_16b84.
Proof. vm_refl. Qed.
Lemma D_16b84 : decode_any W_16b84 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16b88 : bv 32 := 0x931fe06f.
Lemma F_16b88 : fetch_word Ubsan.M.loaded_segments (0x16c8c : word) = Some W_16b88.
Proof. vm_refl. Qed.
Lemma D_16b88 : decode_any W_16b88 = Some (Jal 0 2091312, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16b8c : bv 32 := 0x01440513.
Lemma F_16b8c : fetch_word Ubsan.M.loaded_segments (0x16c90 : word) = Some W_16b8c.
Proof. vm_refl. Qed.
Lemma D_16b8c : decode_any W_16b8c = Some (OpImm ALU_ADD 10 8 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16b90 : bv 32 := 0xfff00593.
Lemma F_16b90 : fetch_word Ubsan.M.loaded_segments (0x16c94 : word) = Some W_16b90.
Proof. vm_refl. Qed.
Lemma D_16b90 : decode_any W_16b90 = Some (OpImm ALU_ADD 11 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16b94 : bv 32 := 0x06b5252f.
Lemma F_16b94 : fetch_word Ubsan.M.loaded_segments (0x16c98 : word) = Some W_16b94.
Proof. vm_refl. Qed.
Lemma D_16b94 : decode_any W_16b94 = Some (Amo AMO_ADD AW true true 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16b98 : bv 32 := 0x00100593.
Lemma F_16b98 : fetch_word Ubsan.M.loaded_segments (0x16c9c : word) = Some W_16b98.
Proof. vm_refl. Qed.
Lemma D_16b98 : decode_any W_16b98 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16b9c : bv 32 := 0x04b51063.
Lemma F_16b9c : fetch_word Ubsan.M.loaded_segments (0x16ca0 : word) = Some W_16b9c.
Proof. vm_refl. Qed.
Lemma D_16b9c : decode_any W_16b9c = Some (Branch BC_NE 10 11 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16ba0 : bv 32 := 0x03843503.
Lemma F_16ba0 : fetch_word Ubsan.M.loaded_segments (0x16ca4 : word) = Some W_16ba0.
Proof. vm_refl. Qed.
Lemma D_16ba0 : decode_any W_16ba0 = Some (Load SZ8 true 10 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16ba4 : bv 32 := 0x00050663.
Lemma F_16ba4 : fetch_word Ubsan.M.loaded_segments (0x16ca8 : word) = Some W_16ba4.
Proof. vm_refl. Qed.
Lemma D_16ba4 : decode_any W_16ba4 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16bb0 : bv 32 := 0x02843503.
Lemma F_16bb0 : fetch_word Ubsan.M.loaded_segments (0x16cb4 : word) = Some W_16bb0.
Proof. vm_refl. Qed.
Lemma D_16bb0 : decode_any W_16bb0 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16bb4 : bv 32 := 0x00050463.
Lemma F_16bb4 : fetch_word Ubsan.M.loaded_segments (0x16cb8 : word) = Some W_16bb4.
Proof. vm_refl. Qed.
Lemma D_16bb4 : decode_any W_16bb4 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16bbc : bv 32 := 0x03043503.
Lemma F_16bbc : fetch_word Ubsan.M.loaded_segments (0x16cc0 : word) = Some W_16bbc.
Proof. vm_refl. Qed.
Lemma D_16bbc : decode_any W_16bbc = Some (Load SZ8 true 10 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16bc0 : bv 32 := 0x00a13023.
Lemma F_16bc0 : fetch_word Ubsan.M.loaded_segments (0x16cc4 : word) = Some W_16bc0.
Proof. vm_refl. Qed.
Lemma D_16bc0 : decode_any W_16bc0 = Some (Store SZ8 2 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16bc4 : bv 32 := 0x00050863.
Lemma F_16bc4 : fetch_word Ubsan.M.loaded_segments (0x16cc8 : word) = Some W_16bc4.
Proof. vm_refl. Qed.
Lemma D_16bc4 : decode_any W_16bc4 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16bd4 : bv 32 := 0x00040513.
Lemma F_16bd4 : fetch_word Ubsan.M.loaded_segments (0x16cd8 : word) = Some W_16bd4.
Proof. vm_refl. Qed.
Lemma D_16bd4 : decode_any W_16bd4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16bd8 : bv 32 := 0x579110ef.
Lemma F_16bd8 : fetch_word Ubsan.M.loaded_segments (0x16cdc : word) = Some W_16bd8.
Proof. vm_refl. Qed.
Lemma D_16bd8 : decode_any W_16bd8 = Some (Jal 1 73080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16bdc : bv 32 := 0x0001d517.
Lemma F_16bdc : fetch_word Ubsan.M.loaded_segments (0x16ce0 : word) = Some W_16bdc.
Proof. vm_refl. Qed.
Lemma D_16bdc : decode_any W_16bdc = Some (Auipc 10 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16be0 : bv 32 := 0x51853503.
Lemma F_16be0 : fetch_word Ubsan.M.loaded_segments (0x16ce4 : word) = Some W_16be0.
Proof. vm_refl. Qed.
Lemma D_16be0 : decode_any W_16be0 = Some (Load SZ8 true 10 10 1304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16be4 : bv 32 := 0x00052503.
Lemma F_16be4 : fetch_word Ubsan.M.loaded_segments (0x16ce8 : word) = Some W_16be4.
Proof. vm_refl. Qed.
Lemma D_16be4 : decode_any W_16be4 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16be8 : bv 32 := 0x00500593.
Lemma F_16be8 : fetch_word Ubsan.M.loaded_segments (0x16cec : word) = Some W_16be8.
Proof. vm_refl. Qed.
Lemma D_16be8 : decode_any W_16be8 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16bec : bv 32 := 0x02a5c263.
Lemma F_16bec : fetch_word Ubsan.M.loaded_segments (0x16cf0 : word) = Some W_16bec.
Proof. vm_refl. Qed.
Lemma D_16bec : decode_any W_16bec = Some (Branch BC_LT 11 10 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16bf0 : bv 32 := 0xffffa517.
Lemma F_16bf0 : fetch_word Ubsan.M.loaded_segments (0x16cf4 : word) = Some W_16bf0.
Proof. vm_refl. Qed.
Lemma D_16bf0 : decode_any W_16bf0 = Some (Auipc 10 1048570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16bf4 : bv 32 := 0xffffa597.
Lemma F_16bf4 : fetch_word Ubsan.M.loaded_segments (0x16cf8 : word) = Some W_16bf4.
Proof. vm_refl. Qed.
Lemma D_16bf4 : decode_any W_16bf4 = Some (Auipc 11 1048570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16bf8 : bv 32 := 0x3f350513.
Lemma F_16bf8 : fetch_word Ubsan.M.loaded_segments (0x16cfc : word) = Some W_16bf8.
Proof. vm_refl. Qed.
Lemma D_16bf8 : decode_any W_16bf8 = Some (OpImm ALU_ADD 10 10 1011, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16bfc : bv 32 := 0x9d658593.
Lemma F_16bfc : fetch_word Ubsan.M.loaded_segments (0x16d00 : word) = Some W_16bfc.
Proof. vm_refl. Qed.
Lemma D_16bfc : decode_any W_16bfc = Some (OpImm ALU_ADD 11 11 2518, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16c00 : bv 32 := 0x00000613.
Lemma F_16c00 : fetch_word Ubsan.M.loaded_segments (0x16d04 : word) = Some W_16c00.
Proof. vm_refl. Qed.
Lemma D_16c00 : decode_any W_16c00 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16c04 : bv 32 := 0x8b5fe0ef.
Lemma F_16c04 : fetch_word Ubsan.M.loaded_segments (0x16d08 : word) = Some W_16c04.
Proof. vm_refl. Qed.
Lemma D_16c04 : decode_any W_16c04 = Some (Jal 1 2091188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16c08 : bv 32 := 0x00050413.
Lemma F_16c08 : fetch_word Ubsan.M.loaded_segments (0x16d0c : word) = Some W_16c08.
Proof. vm_refl. Qed.
Lemma D_16c08 : decode_any W_16c08 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16c0c : bv 32 := 0x0080006f.
Lemma F_16c0c : fetch_word Ubsan.M.loaded_segments (0x16d10 : word) = Some W_16c0c.
Proof. vm_refl. Qed.
Lemma D_16c0c : decode_any W_16c0c = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16c14 : bv 32 := 0x00040513.
Lemma F_16c14 : fetch_word Ubsan.M.loaded_segments (0x16d18 : word) = Some W_16c14.
Proof. vm_refl. Qed.
Lemma D_16c14 : decode_any W_16c14 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16c18 : bv 32 := 0x01813083.
Lemma F_16c18 : fetch_word Ubsan.M.loaded_segments (0x16d1c : word) = Some W_16c18.
Proof. vm_refl. Qed.
Lemma D_16c18 : decode_any W_16c18 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16c1c : bv 32 := 0x01013403.
Lemma F_16c1c : fetch_word Ubsan.M.loaded_segments (0x16d20 : word) = Some W_16c1c.
Proof. vm_refl. Qed.
Lemma D_16c1c : decode_any W_16c1c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16c20 : bv 32 := 0x00813483.
Lemma F_16c20 : fetch_word Ubsan.M.loaded_segments (0x16d24 : word) = Some W_16c20.
Proof. vm_refl. Qed.
Lemma D_16c20 : decode_any W_16c20 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16c24 : bv 32 := 0x02010113.
Lemma F_16c24 : fetch_word Ubsan.M.loaded_segments (0x16d28 : word) = Some W_16c24.
Proof. vm_refl. Qed.
Lemma D_16c24 : decode_any W_16c24 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16c28 : bv 32 := 0x00008067.
Lemma F_16c28 : fetch_word Ubsan.M.loaded_segments (0x16d2c : word) = Some W_16c28.
Proof. vm_refl. Qed.
Lemma D_16c28 : decode_any W_16c28 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
