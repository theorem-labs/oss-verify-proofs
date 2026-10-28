(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.H Require GcFlushS2.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_19c84 : bv 32 := 0xfd010113.
Lemma F_19c84 : fetch_word Ubsan.M.loaded_segments (0x19c84 : word) = Some W_19c84.
Proof. vm_refl. Qed.
Lemma D_19c84 : decode_any W_19c84 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c88 : bv 32 := 0x02113423.
Lemma F_19c88 : fetch_word Ubsan.M.loaded_segments (0x19c88 : word) = Some W_19c88.
Proof. vm_refl. Qed.
Lemma D_19c88 : decode_any W_19c88 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c8c : bv 32 := 0x02813023.
Lemma F_19c8c : fetch_word Ubsan.M.loaded_segments (0x19c8c : word) = Some W_19c8c.
Proof. vm_refl. Qed.
Lemma D_19c8c : decode_any W_19c8c = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c90 : bv 32 := 0x00913c23.
Lemma F_19c90 : fetch_word Ubsan.M.loaded_segments (0x19c90 : word) = Some W_19c90.
Proof. vm_refl. Qed.
Lemma D_19c90 : decode_any W_19c90 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c94 : bv 32 := 0x0e058863.
Lemma F_19c94 : fetch_word Ubsan.M.loaded_segments (0x19c94 : word) = Some W_19c94.
Proof. vm_refl. Qed.
Lemma D_19c94 : decode_any W_19c94 = Some (Branch BC_EQ 11 0 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c98 : bv 32 := 0x10050a63.
Lemma F_19c98 : fetch_word Ubsan.M.loaded_segments (0x19c98 : word) = Some W_19c98.
Proof. vm_refl. Qed.
Lemma D_19c98 : decode_any W_19c98 = Some (Branch BC_EQ 10 0 276, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c9c : bv 32 := 0x0ea58063.
Lemma F_19c9c : fetch_word Ubsan.M.loaded_segments (0x19c9c : word) = Some W_19c9c.
Proof. vm_refl. Qed.
Lemma D_19c9c : decode_any W_19c9c = Some (Branch BC_EQ 11 10 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_19ca0 : bv 32 := 0x0075f613.
Lemma F_19ca0 : fetch_word Ubsan.M.loaded_segments (0x19ca0 : word) = Some W_19ca0.
Proof. vm_refl. Qed.
Lemma D_19ca0 : decode_any W_19ca0 = Some (OpImm ALU_AND 12 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_19ca4 : bv 32 := 0x1c061e63.
Lemma F_19ca4 : fetch_word Ubsan.M.loaded_segments (0x19ca4 : word) = Some W_19ca4.
Proof. vm_refl. Qed.
Lemma D_19ca4 : decode_any W_19ca4 = Some (Branch BC_NE 12 0 476, 4%Z).
Proof. vm_refl. Qed.

Definition W_19ca8 : bv 32 := 0x00757613.
Lemma F_19ca8 : fetch_word Ubsan.M.loaded_segments (0x19ca8 : word) = Some W_19ca8.
Proof. vm_refl. Qed.
Lemma D_19ca8 : decode_any W_19ca8 = Some (OpImm ALU_AND 12 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_19cac : bv 32 := 0x1c061a63.
Lemma F_19cac : fetch_word Ubsan.M.loaded_segments (0x19cac : word) = Some W_19cac.
Proof. vm_refl. Qed.
Lemma D_19cac : decode_any W_19cac = Some (Branch BC_NE 12 0 468, 4%Z).
Proof. vm_refl. Qed.

Definition W_19cb0 : bv 32 := 0x0085a603.
Lemma F_19cb0 : fetch_word Ubsan.M.loaded_segments (0x19cb0 : word) = Some W_19cb0.
Proof. vm_refl. Qed.
Lemma D_19cb0 : decode_any W_19cb0 = Some (Load SZ4 true 12 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_19cb4 : bv 32 := 0x00852683.
Lemma F_19cb4 : fetch_word Ubsan.M.loaded_segments (0x19cb4 : word) = Some W_19cb4.
Proof. vm_refl. Qed.
Lemma D_19cb4 : decode_any W_19cb4 = Some (Load SZ4 true 13 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_19cb8 : bv 32 := 0x10d61e63.
Lemma F_19cb8 : fetch_word Ubsan.M.loaded_segments (0x19cb8 : word) = Some W_19cb8.
Proof. vm_refl. Qed.
Lemma D_19cb8 : decode_any W_19cb8 = Some (Branch BC_NE 12 13 284, 4%Z).
Proof. vm_refl. Qed.

Definition W_19cbc : bv 32 := 0x03053603.
Lemma F_19cbc : fetch_word Ubsan.M.loaded_segments (0x19cbc : word) = Some W_19cbc.
Proof. vm_refl. Qed.
Lemma D_19cbc : decode_any W_19cbc = Some (Load SZ8 true 12 10 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_19cc0 : bv 32 := 0x00c13823.
Lemma F_19cc0 : fetch_word Ubsan.M.loaded_segments (0x19cc0 : word) = Some W_19cc0.
Proof. vm_refl. Qed.
Lemma D_19cc0 : decode_any W_19cc0 = Some (Store SZ8 2 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_19cc4 : bv 32 := 0x02060063.
Lemma F_19cc4 : fetch_word Ubsan.M.loaded_segments (0x19cc4 : word) = Some W_19cc4.
Proof. vm_refl. Qed.
Lemma D_19cc4 : decode_any W_19cc4 = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_19cc8 : bv 32 := 0x00050413.
Lemma F_19cc8 : fetch_word Ubsan.M.loaded_segments (0x19cc8 : word) = Some W_19cc8.
Proof. vm_refl. Qed.
Lemma D_19cc8 : decode_any W_19cc8 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19ccc : bv 32 := 0x01010513.
Lemma F_19ccc : fetch_word Ubsan.M.loaded_segments (0x19ccc : word) = Some W_19ccc.
Proof. vm_refl. Qed.
Lemma D_19ccc : decode_any W_19ccc = Some (OpImm ALU_ADD 10 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_19cd0 : bv 32 := 0x00058493.
Lemma F_19cd0 : fetch_word Ubsan.M.loaded_segments (0x19cd0 : word) = Some W_19cd0.
Proof. vm_refl. Qed.
Lemma D_19cd0 : decode_any W_19cd0 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19cd4 : bv 32 := 0x579030ef.
Lemma F_19cd4 : fetch_word Ubsan.M.loaded_segments (0x19cd4 : word) = Some W_19cd4.
Proof. vm_refl. Qed.
Lemma D_19cd4 : decode_any W_19cd4 = Some (Jal 1 15736, 4%Z).
Proof. vm_refl. Qed.

Definition W_19cd8 : bv 32 := 0x00048593.
Lemma F_19cd8 : fetch_word Ubsan.M.loaded_segments (0x19cd8 : word) = Some W_19cd8.
Proof. vm_refl. Qed.
Lemma D_19cd8 : decode_any W_19cd8 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19cdc : bv 32 := 0x00040513.
Lemma F_19cdc : fetch_word Ubsan.M.loaded_segments (0x19cdc : word) = Some W_19cdc.
Proof. vm_refl. Qed.
Lemma D_19cdc : decode_any W_19cdc = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19ce0 : bv 32 := 0x02043823.
Lemma F_19ce0 : fetch_word Ubsan.M.loaded_segments (0x19ce0 : word) = Some W_19ce0.
Proof. vm_refl. Qed.
Lemma D_19ce0 : decode_any W_19ce0 = Some (Store SZ8 8 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_19ce4 : bv 32 := 0x0305b403.
Lemma F_19ce4 : fetch_word Ubsan.M.loaded_segments (0x19ce4 : word) = Some W_19ce4.
Proof. vm_refl. Qed.
Lemma D_19ce4 : decode_any W_19ce4 = Some (Load SZ8 true 8 11 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_19ce8 : bv 32 := 0x08040a63.
Lemma F_19ce8 : fetch_word Ubsan.M.loaded_segments (0x19ce8 : word) = Some W_19ce8.
Proof. vm_refl. Qed.
Lemma D_19ce8 : decode_any W_19ce8 = Some (Branch BC_EQ 8 0 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_19cec : bv 32 := 0x00050493.
Lemma F_19cec : fetch_word Ubsan.M.loaded_segments (0x19cec : word) = Some W_19cec.
Proof. vm_refl. Qed.
Lemma D_19cec : decode_any W_19cec = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19cf0 : bv 32 := 0x00c10613.
Lemma F_19cf0 : fetch_word Ubsan.M.loaded_segments (0x19cf0 : word) = Some W_19cf0.
Proof. vm_refl. Qed.
Lemma D_19cf0 : decode_any W_19cf0 = Some (OpImm ALU_ADD 12 2 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_19cf4 : bv 32 := 0x00040513.
Lemma F_19cf4 : fetch_word Ubsan.M.loaded_segments (0x19cf4 : word) = Some W_19cf4.
Proof. vm_refl. Qed.
Lemma D_19cf4 : decode_any W_19cf4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19cf8 : bv 32 := 0x00000593.
Lemma F_19cf8 : fetch_word Ubsan.M.loaded_segments (0x19cf8 : word) = Some W_19cf8.
Proof. vm_refl. Qed.
Lemma D_19cf8 : decode_any W_19cf8 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19cfc : bv 32 := 0x239030ef.
Lemma F_19cfc : fetch_word Ubsan.M.loaded_segments (0x19cfc : word) = Some W_19cfc.
Proof. vm_refl. Qed.
Lemma D_19cfc : decode_any W_19cfc = Some (Jal 1 14904, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d00 : bv 32 := 0x00c12503.
Lemma F_19d00 : fetch_word Ubsan.M.loaded_segments (0x19d00 : word) = Some W_19d00.
Proof. vm_refl. Qed.
Lemma D_19d00 : decode_any W_19d00 = Some (Load SZ4 true 10 2 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d04 : bv 32 := 0x10050663.
Lemma F_19d04 : fetch_word Ubsan.M.loaded_segments (0x19d04 : word) = Some W_19d04.
Proof. vm_refl. Qed.
Lemma D_19d04 : decode_any W_19d04 = Some (Branch BC_EQ 10 0 268, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d08 : bv 32 := 0x00040513.
Lemma F_19d08 : fetch_word Ubsan.M.loaded_segments (0x19d08 : word) = Some W_19d08.
Proof. vm_refl. Qed.
Lemma D_19d08 : decode_any W_19d08 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d0c : bv 32 := 0x111030ef.
Lemma F_19d0c : fetch_word Ubsan.M.loaded_segments (0x19d0c : word) = Some W_19d0c.
Proof. vm_refl. Qed.
Lemma D_19d0c : decode_any W_19d0c = Some (Jal 1 14608, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d10 : bv 32 := 0x12050463.
Lemma F_19d10 : fetch_word Ubsan.M.loaded_segments (0x19d10 : word) = Some W_19d10.
Proof. vm_refl. Qed.
Lemma D_19d10 : decode_any W_19d10 = Some (Branch BC_EQ 10 0 296, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d14 : bv 32 := 0x00048593.
Lemma F_19d14 : fetch_word Ubsan.M.loaded_segments (0x19d14 : word) = Some W_19d14.
Proof. vm_refl. Qed.
Lemma D_19d14 : decode_any W_19d14 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d18 : bv 32 := 0x0304b603.
Lemma F_19d18 : fetch_word Ubsan.M.loaded_segments (0x19d18 : word) = Some W_19d18.
Proof. vm_refl. Qed.
Lemma D_19d18 : decode_any W_19d18 = Some (Load SZ8 true 12 9 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d1c : bv 32 := 0x00c13823.
Lemma F_19d1c : fetch_word Ubsan.M.loaded_segments (0x19d1c : word) = Some W_19d1c.
Proof. vm_refl. Qed.
Lemma D_19d1c : decode_any W_19d1c = Some (Store SZ8 2 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d20 : bv 32 := 0x00060c63.
Lemma F_19d20 : fetch_word Ubsan.M.loaded_segments (0x19d20 : word) = Some W_19d20.
Proof. vm_refl. Qed.
Lemma D_19d20 : decode_any W_19d20 = Some (Branch BC_EQ 12 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d24 : bv 32 := 0x00050413.
Lemma F_19d24 : fetch_word Ubsan.M.loaded_segments (0x19d24 : word) = Some W_19d24.
Proof. vm_refl. Qed.
Lemma D_19d24 : decode_any W_19d24 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d28 : bv 32 := 0x01010513.
Lemma F_19d28 : fetch_word Ubsan.M.loaded_segments (0x19d28 : word) = Some W_19d28.
Proof. vm_refl. Qed.
Lemma D_19d28 : decode_any W_19d28 = Some (OpImm ALU_ADD 10 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d2c : bv 32 := 0x521030ef.
Lemma F_19d2c : fetch_word Ubsan.M.loaded_segments (0x19d2c : word) = Some W_19d2c.
Proof. vm_refl. Qed.
Lemma D_19d2c : decode_any W_19d2c = Some (Jal 1 15648, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d30 : bv 32 := 0x00040513.
Lemma F_19d30 : fetch_word Ubsan.M.loaded_segments (0x19d30 : word) = Some W_19d30.
Proof. vm_refl. Qed.
Lemma D_19d30 : decode_any W_19d30 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d34 : bv 32 := 0x00048593.
Lemma F_19d34 : fetch_word Ubsan.M.loaded_segments (0x19d34 : word) = Some W_19d34.
Proof. vm_refl. Qed.
Lemma D_19d34 : decode_any W_19d34 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d38 : bv 32 := 0x02a5b823.
Lemma F_19d38 : fetch_word Ubsan.M.loaded_segments (0x19d38 : word) = Some W_19d38.
Proof. vm_refl. Qed.
Lemma D_19d38 : decode_any W_19d38 = Some (Store SZ8 11 10 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d3c : bv 32 := 0x01010613.
Lemma F_19d3c : fetch_word Ubsan.M.loaded_segments (0x19d3c : word) = Some W_19d3c.
Proof. vm_refl. Qed.
Lemma D_19d3c : decode_any W_19d3c = Some (OpImm ALU_ADD 12 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d40 : bv 32 := 0x00000593.
Lemma F_19d40 : fetch_word Ubsan.M.loaded_segments (0x19d40 : word) = Some W_19d40.
Proof. vm_refl. Qed.
Lemma D_19d40 : decode_any W_19d40 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d44 : bv 32 := 0x1f1030ef.
Lemma F_19d44 : fetch_word Ubsan.M.loaded_segments (0x19d44 : word) = Some W_19d44.
Proof. vm_refl. Qed.
Lemma D_19d44 : decode_any W_19d44 = Some (Jal 1 14832, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d48 : bv 32 := 0x01012503.
Lemma F_19d48 : fetch_word Ubsan.M.loaded_segments (0x19d48 : word) = Some W_19d48.
Proof. vm_refl. Qed.
Lemma D_19d48 : decode_any W_19d48 = Some (Load SZ4 true 10 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d4c : bv 32 := 0x02051863.
Lemma F_19d4c : fetch_word Ubsan.M.loaded_segments (0x19d4c : word) = Some W_19d4c.
Proof. vm_refl. Qed.
Lemma D_19d4c : decode_any W_19d4c = Some (Branch BC_NE 10 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d50 : bv 32 := 0x0002b517.
Lemma F_19d50 : fetch_word Ubsan.M.loaded_segments (0x19d50 : word) = Some W_19d50.
Proof. vm_refl. Qed.
Lemma D_19d50 : decode_any W_19d50 = Some (Auipc 10 43, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d54 : bv 32 := 0x14853503.
Lemma F_19d54 : fetch_word Ubsan.M.loaded_segments (0x19d54 : word) = Some W_19d54.
Proof. vm_refl. Qed.
Lemma D_19d54 : decode_any W_19d54 = Some (Load SZ8 true 10 10 328, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d58 : bv 32 := 0x00052503.
Lemma F_19d58 : fetch_word Ubsan.M.loaded_segments (0x19d58 : word) = Some W_19d58.
Proof. vm_refl. Qed.
Lemma D_19d58 : decode_any W_19d58 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d5c : bv 32 := 0x00500593.
Lemma F_19d5c : fetch_word Ubsan.M.loaded_segments (0x19d5c : word) = Some W_19d5c.
Proof. vm_refl. Qed.
Lemma D_19d5c : decode_any W_19d5c = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d60 : bv 32 := 0x00a5ce63.
Lemma F_19d60 : fetch_word Ubsan.M.loaded_segments (0x19d60 : word) = Some W_19d60.
Proof. vm_refl. Qed.
Lemma D_19d60 : decode_any W_19d60 = Some (Branch BC_LT 11 10 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d64 : bv 32 := 0xffff8517.
Lemma F_19d64 : fetch_word Ubsan.M.loaded_segments (0x19d64 : word) = Some W_19d64.
Proof. vm_refl. Qed.
Lemma D_19d64 : decode_any W_19d64 = Some (Auipc 10 1048568, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d68 : bv 32 := 0xffff7597.
Lemma F_19d68 : fetch_word Ubsan.M.loaded_segments (0x19d68 : word) = Some W_19d68.
Proof. vm_refl. Qed.
Lemma D_19d68 : decode_any W_19d68 = Some (Auipc 11 1048567, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d6c : bv 32 := 0xd9450513.
Lemma F_19d6c : fetch_word Ubsan.M.loaded_segments (0x19d6c : word) = Some W_19d6c.
Proof. vm_refl. Qed.
Lemma D_19d6c : decode_any W_19d6c = Some (OpImm ALU_ADD 10 10 3476, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d70 : bv 32 := 0x60158593.
Lemma F_19d70 : fetch_word Ubsan.M.loaded_segments (0x19d70 : word) = Some W_19d70.
Proof. vm_refl. Qed.
Lemma D_19d70 : decode_any W_19d70 = Some (OpImm ALU_ADD 11 11 1537, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d74 : bv 32 := 0x00100613.
Lemma F_19d74 : fetch_word Ubsan.M.loaded_segments (0x19d74 : word) = Some W_19d74.
Proof. vm_refl. Qed.
Lemma D_19d74 : decode_any W_19d74 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d78 : bv 32 := 0x87cfe0ef.
Lemma F_19d78 : fetch_word Ubsan.M.loaded_segments (0x19d78 : word) = Some W_19d78.
Proof. vm_refl. Qed.
Lemma D_19d78 : decode_any W_19d78 = Some (Jal 1 2089084, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d7c : bv 32 := 0x00000513.
Lemma F_19d7c : fetch_word Ubsan.M.loaded_segments (0x19d7c : word) = Some W_19d7c.
Proof. vm_refl. Qed.
Lemma D_19d7c : decode_any W_19d7c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d80 : bv 32 := 0x0ec0006f.
Lemma F_19d80 : fetch_word Ubsan.M.loaded_segments (0x19d80 : word) = Some W_19d80.
Proof. vm_refl. Qed.
Lemma D_19d80 : decode_any W_19d80 = Some (Jal 0 236, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d84 : bv 32 := 0x0002b517.
Lemma F_19d84 : fetch_word Ubsan.M.loaded_segments (0x19d84 : word) = Some W_19d84.
Proof. vm_refl. Qed.
Lemma D_19d84 : decode_any W_19d84 = Some (Auipc 10 43, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d88 : bv 32 := 0x11453503.
Lemma F_19d88 : fetch_word Ubsan.M.loaded_segments (0x19d88 : word) = Some W_19d88.
Proof. vm_refl. Qed.
Lemma D_19d88 : decode_any W_19d88 = Some (Load SZ8 true 10 10 276, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d8c : bv 32 := 0x00052503.
Lemma F_19d8c : fetch_word Ubsan.M.loaded_segments (0x19d8c : word) = Some W_19d8c.
Proof. vm_refl. Qed.
Lemma D_19d8c : decode_any W_19d8c = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d90 : bv 32 := 0x00500593.
Lemma F_19d90 : fetch_word Ubsan.M.loaded_segments (0x19d90 : word) = Some W_19d90.
Proof. vm_refl. Qed.
Lemma D_19d90 : decode_any W_19d90 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d94 : bv 32 := 0x0ca5ca63.
Lemma F_19d94 : fetch_word Ubsan.M.loaded_segments (0x19d94 : word) = Some W_19d94.
Proof. vm_refl. Qed.
Lemma D_19d94 : decode_any W_19d94 = Some (Branch BC_LT 11 10 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d98 : bv 32 := 0xffff6517.
Lemma F_19d98 : fetch_word Ubsan.M.loaded_segments (0x19d98 : word) = Some W_19d98.
Proof. vm_refl. Qed.
Lemma D_19d98 : decode_any W_19d98 = Some (Auipc 10 1048566, 4%Z).
Proof. vm_refl. Qed.

Definition W_19d9c : bv 32 := 0xffff7597.
Lemma F_19d9c : fetch_word Ubsan.M.loaded_segments (0x19d9c : word) = Some W_19d9c.
Proof. vm_refl. Qed.
Lemma D_19d9c : decode_any W_19d9c = Some (Auipc 11 1048567, 4%Z).
Proof. vm_refl. Qed.

Definition W_19da0 : bv 32 := 0x51c50513.
Lemma F_19da0 : fetch_word Ubsan.M.loaded_segments (0x19da0 : word) = Some W_19da0.
Proof. vm_refl. Qed.
Lemma D_19da0 : decode_any W_19da0 = Some (OpImm ALU_ADD 10 10 1308, 4%Z).
Proof. vm_refl. Qed.

Definition W_19da4 : bv 32 := 0xb4458593.
Lemma F_19da4 : fetch_word Ubsan.M.loaded_segments (0x19da4 : word) = Some W_19da4.
Proof. vm_refl. Qed.
Lemma D_19da4 : decode_any W_19da4 = Some (OpImm ALU_ADD 11 11 2884, 4%Z).
Proof. vm_refl. Qed.

Definition W_19da8 : bv 32 := 0x0500006f.
Lemma F_19da8 : fetch_word Ubsan.M.loaded_segments (0x19da8 : word) = Some W_19da8.
Proof. vm_refl. Qed.
Lemma D_19da8 : decode_any W_19da8 = Some (Jal 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_19dac : bv 32 := 0x0002b517.
Lemma F_19dac : fetch_word Ubsan.M.loaded_segments (0x19dac : word) = Some W_19dac.
Proof. vm_refl. Qed.
Lemma D_19dac : decode_any W_19dac = Some (Auipc 10 43, 4%Z).
Proof. vm_refl. Qed.

Definition W_19db0 : bv 32 := 0x0ec53503.
Lemma F_19db0 : fetch_word Ubsan.M.loaded_segments (0x19db0 : word) = Some W_19db0.
Proof. vm_refl. Qed.
Lemma D_19db0 : decode_any W_19db0 = Some (Load SZ8 true 10 10 236, 4%Z).
Proof. vm_refl. Qed.

Definition W_19db4 : bv 32 := 0x00052503.
Lemma F_19db4 : fetch_word Ubsan.M.loaded_segments (0x19db4 : word) = Some W_19db4.
Proof. vm_refl. Qed.
Lemma D_19db4 : decode_any W_19db4 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19db8 : bv 32 := 0x00500593.
Lemma F_19db8 : fetch_word Ubsan.M.loaded_segments (0x19db8 : word) = Some W_19db8.
Proof. vm_refl. Qed.
Lemma D_19db8 : decode_any W_19db8 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_19dbc : bv 32 := 0x0aa5c663.
Lemma F_19dbc : fetch_word Ubsan.M.loaded_segments (0x19dbc : word) = Some W_19dbc.
Proof. vm_refl. Qed.
Lemma D_19dbc : decode_any W_19dbc = Some (Branch BC_LT 11 10 172, 4%Z).
Proof. vm_refl. Qed.

Definition W_19dc0 : bv 32 := 0xffff8517.
Lemma F_19dc0 : fetch_word Ubsan.M.loaded_segments (0x19dc0 : word) = Some W_19dc0.
Proof. vm_refl. Qed.
Lemma D_19dc0 : decode_any W_19dc0 = Some (Auipc 10 1048568, 4%Z).
Proof. vm_refl. Qed.

Definition W_19dc4 : bv 32 := 0xffff7597.
Lemma F_19dc4 : fetch_word Ubsan.M.loaded_segments (0x19dc4 : word) = Some W_19dc4.
Proof. vm_refl. Qed.
Lemma D_19dc4 : decode_any W_19dc4 = Some (Auipc 11 1048567, 4%Z).
Proof. vm_refl. Qed.

Definition W_19dc8 : bv 32 := 0xb7050513.
Lemma F_19dc8 : fetch_word Ubsan.M.loaded_segments (0x19dc8 : word) = Some W_19dc8.
Proof. vm_refl. Qed.
Lemma D_19dc8 : decode_any W_19dc8 = Some (OpImm ALU_ADD 10 10 2928, 4%Z).
Proof. vm_refl. Qed.

Definition W_19dcc : bv 32 := 0xb1c58593.
Lemma F_19dcc : fetch_word Ubsan.M.loaded_segments (0x19dcc : word) = Some W_19dcc.
Proof. vm_refl. Qed.
Lemma D_19dcc : decode_any W_19dcc = Some (OpImm ALU_ADD 11 11 2844, 4%Z).
Proof. vm_refl. Qed.

Definition W_19dd0 : bv 32 := 0x0280006f.
Lemma F_19dd0 : fetch_word Ubsan.M.loaded_segments (0x19dd0 : word) = Some W_19dd0.
Proof. vm_refl. Qed.
Lemma D_19dd0 : decode_any W_19dd0 = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_19dd4 : bv 32 := 0x0002b517.
Lemma F_19dd4 : fetch_word Ubsan.M.loaded_segments (0x19dd4 : word) = Some W_19dd4.
Proof. vm_refl. Qed.
Lemma D_19dd4 : decode_any W_19dd4 = Some (Auipc 10 43, 4%Z).
Proof. vm_refl. Qed.

Definition W_19dd8 : bv 32 := 0x0c453503.
Lemma F_19dd8 : fetch_word Ubsan.M.loaded_segments (0x19dd8 : word) = Some W_19dd8.
Proof. vm_refl. Qed.
Lemma D_19dd8 : decode_any W_19dd8 = Some (Load SZ8 true 10 10 196, 4%Z).
Proof. vm_refl. Qed.

Definition W_19ddc : bv 32 := 0x00052503.
Lemma F_19ddc : fetch_word Ubsan.M.loaded_segments (0x19ddc : word) = Some W_19ddc.
Proof. vm_refl. Qed.
Lemma D_19ddc : decode_any W_19ddc = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19de0 : bv 32 := 0x00500593.
Lemma F_19de0 : fetch_word Ubsan.M.loaded_segments (0x19de0 : word) = Some W_19de0.
Proof. vm_refl. Qed.
Lemma D_19de0 : decode_any W_19de0 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_19de4 : bv 32 := 0x08a5c263.
Lemma F_19de4 : fetch_word Ubsan.M.loaded_segments (0x19de4 : word) = Some W_19de4.
Proof. vm_refl. Qed.
Lemma D_19de4 : decode_any W_19de4 = Some (Branch BC_LT 11 10 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_19de8 : bv 32 := 0xffff8517.
Lemma F_19de8 : fetch_word Ubsan.M.loaded_segments (0x19de8 : word) = Some W_19de8.
Proof. vm_refl. Qed.
Lemma D_19de8 : decode_any W_19de8 = Some (Auipc 10 1048568, 4%Z).
Proof. vm_refl. Qed.

Definition W_19dec : bv 32 := 0xffff7597.
Lemma F_19dec : fetch_word Ubsan.M.loaded_segments (0x19dec : word) = Some W_19dec.
Proof. vm_refl. Qed.
Lemma D_19dec : decode_any W_19dec = Some (Auipc 11 1048567, 4%Z).
Proof. vm_refl. Qed.

Definition W_19df0 : bv 32 := 0xf8d50513.
Lemma F_19df0 : fetch_word Ubsan.M.loaded_segments (0x19df0 : word) = Some W_19df0.
Proof. vm_refl. Qed.
Lemma D_19df0 : decode_any W_19df0 = Some (OpImm ALU_ADD 10 10 3981, 4%Z).
Proof. vm_refl. Qed.

Definition W_19df4 : bv 32 := 0xaf458593.
Lemma F_19df4 : fetch_word Ubsan.M.loaded_segments (0x19df4 : word) = Some W_19df4.
Proof. vm_refl. Qed.
Lemma D_19df4 : decode_any W_19df4 = Some (OpImm ALU_ADD 11 11 2804, 4%Z).
Proof. vm_refl. Qed.

Definition W_19df8 : bv 32 := 0x00100613.
Lemma F_19df8 : fetch_word Ubsan.M.loaded_segments (0x19df8 : word) = Some W_19df8.
Proof. vm_refl. Qed.
Lemma D_19df8 : decode_any W_19df8 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_19dfc : bv 32 := 0x02813083.
Lemma F_19dfc : fetch_word Ubsan.M.loaded_segments (0x19dfc : word) = Some W_19dfc.
Proof. vm_refl. Qed.
Lemma D_19dfc : decode_any W_19dfc = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_19e00 : bv 32 := 0x02013403.
Lemma F_19e00 : fetch_word Ubsan.M.loaded_segments (0x19e00 : word) = Some W_19e00.
Proof. vm_refl. Qed.
Lemma D_19e00 : decode_any W_19e00 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_19e04 : bv 32 := 0x01813483.
Lemma F_19e04 : fetch_word Ubsan.M.loaded_segments (0x19e04 : word) = Some W_19e04.
Proof. vm_refl. Qed.
Lemma D_19e04 : decode_any W_19e04 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_19e08 : bv 32 := 0x03010113.
Lemma F_19e08 : fetch_word Ubsan.M.loaded_segments (0x19e08 : word) = Some W_19e08.
Proof. vm_refl. Qed.
Lemma D_19e08 : decode_any W_19e08 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_19e0c : bv 32 := 0xfe9fd06f.
Lemma F_19e0c : fetch_word Ubsan.M.loaded_segments (0x19e0c : word) = Some W_19e0c.
Proof. vm_refl. Qed.
Lemma D_19e0c : decode_any W_19e0c = Some (Jal 0 2088936, 4%Z).
Proof. vm_refl. Qed.

Definition W_19e10 : bv 32 := 0x0002b517.
Lemma F_19e10 : fetch_word Ubsan.M.loaded_segments (0x19e10 : word) = Some W_19e10.
Proof. vm_refl. Qed.
Lemma D_19e10 : decode_any W_19e10 = Some (Auipc 10 43, 4%Z).
Proof. vm_refl. Qed.

Definition W_19e14 : bv 32 := 0x08853503.
Lemma F_19e14 : fetch_word Ubsan.M.loaded_segments (0x19e14 : word) = Some W_19e14.
Proof. vm_refl. Qed.
Lemma D_19e14 : decode_any W_19e14 = Some (Load SZ8 true 10 10 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_19e18 : bv 32 := 0x00052503.
Lemma F_19e18 : fetch_word Ubsan.M.loaded_segments (0x19e18 : word) = Some W_19e18.
Proof. vm_refl. Qed.
Lemma D_19e18 : decode_any W_19e18 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19e1c : bv 32 := 0x00500593.
Lemma F_19e1c : fetch_word Ubsan.M.loaded_segments (0x19e1c : word) = Some W_19e1c.
Proof. vm_refl. Qed.
Lemma D_19e1c : decode_any W_19e1c = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_19e20 : bv 32 := 0x04a5c463.
Lemma F_19e20 : fetch_word Ubsan.M.loaded_segments (0x19e20 : word) = Some W_19e20.
Proof. vm_refl. Qed.
Lemma D_19e20 : decode_any W_19e20 = Some (Branch BC_LT 11 10 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_19e24 : bv 32 := 0xffff8517.
Lemma F_19e24 : fetch_word Ubsan.M.loaded_segments (0x19e24 : word) = Some W_19e24.
Proof. vm_refl. Qed.
Lemma D_19e24 : decode_any W_19e24 = Some (Auipc 10 1048568, 4%Z).
Proof. vm_refl. Qed.

Definition W_19e28 : bv 32 := 0xffff7597.
Lemma F_19e28 : fetch_word Ubsan.M.loaded_segments (0x19e28 : word) = Some W_19e28.
Proof. vm_refl. Qed.
Lemma D_19e28 : decode_any W_19e28 = Some (Auipc 11 1048567, 4%Z).
Proof. vm_refl. Qed.

Definition W_19e2c : bv 32 := 0x9d650513.
Lemma F_19e2c : fetch_word Ubsan.M.loaded_segments (0x19e2c : word) = Some W_19e2c.
Proof. vm_refl. Qed.
Lemma D_19e2c : decode_any W_19e2c = Some (OpImm ALU_ADD 10 10 2518, 4%Z).
Proof. vm_refl. Qed.

Definition W_19e30 : bv 32 := 0xab858593.
Lemma F_19e30 : fetch_word Ubsan.M.loaded_segments (0x19e30 : word) = Some W_19e30.
Proof. vm_refl. Qed.
Lemma D_19e30 : decode_any W_19e30 = Some (OpImm ALU_ADD 11 11 2744, 4%Z).
Proof. vm_refl. Qed.

Definition W_19e34 : bv 32 := 0x0280006f.
Lemma F_19e34 : fetch_word Ubsan.M.loaded_segments (0x19e34 : word) = Some W_19e34.
Proof. vm_refl. Qed.
Lemma D_19e34 : decode_any W_19e34 = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_19e38 : bv 32 := 0x0002b517.
Lemma F_19e38 : fetch_word Ubsan.M.loaded_segments (0x19e38 : word) = Some W_19e38.
Proof. vm_refl. Qed.
Lemma D_19e38 : decode_any W_19e38 = Some (Auipc 10 43, 4%Z).
Proof. vm_refl. Qed.

Definition W_19e3c : bv 32 := 0x06053503.
Lemma F_19e3c : fetch_word Ubsan.M.loaded_segments (0x19e3c : word) = Some W_19e3c.
Proof. vm_refl. Qed.
Lemma D_19e3c : decode_any W_19e3c = Some (Load SZ8 true 10 10 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_19e40 : bv 32 := 0x00052503.
Lemma F_19e40 : fetch_word Ubsan.M.loaded_segments (0x19e40 : word) = Some W_19e40.
Proof. vm_refl. Qed.
Lemma D_19e40 : decode_any W_19e40 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19e44 : bv 32 := 0x00500593.
Lemma F_19e44 : fetch_word Ubsan.M.loaded_segments (0x19e44 : word) = Some W_19e44.
Proof. vm_refl. Qed.
Lemma D_19e44 : decode_any W_19e44 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_19e48 : bv 32 := 0x02a5c063.
Lemma F_19e48 : fetch_word Ubsan.M.loaded_segments (0x19e48 : word) = Some W_19e48.
Proof. vm_refl. Qed.
Lemma D_19e48 : decode_any W_19e48 = Some (Branch BC_LT 11 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_19e4c : bv 32 := 0xffff7517.
Lemma F_19e4c : fetch_word Ubsan.M.loaded_segments (0x19e4c : word) = Some W_19e4c.
Proof. vm_refl. Qed.
Lemma D_19e4c : decode_any W_19e4c = Some (Auipc 10 1048567, 4%Z).
Proof. vm_refl. Qed.

Definition W_19e50 : bv 32 := 0xffff7597.
Lemma F_19e50 : fetch_word Ubsan.M.loaded_segments (0x19e50 : word) = Some W_19e50.
Proof. vm_refl. Qed.
Lemma D_19e50 : decode_any W_19e50 = Some (Auipc 11 1048567, 4%Z).
Proof. vm_refl. Qed.

Definition W_19e54 : bv 32 := 0x92750513.
Lemma F_19e54 : fetch_word Ubsan.M.loaded_segments (0x19e54 : word) = Some W_19e54.
Proof. vm_refl. Qed.
Lemma D_19e54 : decode_any W_19e54 = Some (OpImm ALU_ADD 10 10 2343, 4%Z).
Proof. vm_refl. Qed.

Definition W_19e58 : bv 32 := 0xa9058593.
Lemma F_19e58 : fetch_word Ubsan.M.loaded_segments (0x19e58 : word) = Some W_19e58.
Proof. vm_refl. Qed.
Lemma D_19e58 : decode_any W_19e58 = Some (OpImm ALU_ADD 11 11 2704, 4%Z).
Proof. vm_refl. Qed.

Definition W_19e5c : bv 32 := 0x00100613.
Lemma F_19e5c : fetch_word Ubsan.M.loaded_segments (0x19e5c : word) = Some W_19e5c.
Proof. vm_refl. Qed.
Lemma D_19e5c : decode_any W_19e5c = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_19e60 : bv 32 := 0xf95fd0ef.
Lemma F_19e60 : fetch_word Ubsan.M.loaded_segments (0x19e60 : word) = Some W_19e60.
Proof. vm_refl. Qed.
Lemma D_19e60 : decode_any W_19e60 = Some (Jal 1 2088852, 4%Z).
Proof. vm_refl. Qed.

Definition W_19e64 : bv 32 := 0x0080006f.
Lemma F_19e64 : fetch_word Ubsan.M.loaded_segments (0x19e64 : word) = Some W_19e64.
Proof. vm_refl. Qed.
Lemma D_19e64 : decode_any W_19e64 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_19e68 : bv 32 := 0x00100513.
Lemma F_19e68 : fetch_word Ubsan.M.loaded_segments (0x19e68 : word) = Some W_19e68.
Proof. vm_refl. Qed.
Lemma D_19e68 : decode_any W_19e68 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_19e6c : bv 32 := 0x02813083.
Lemma F_19e6c : fetch_word Ubsan.M.loaded_segments (0x19e6c : word) = Some W_19e6c.
Proof. vm_refl. Qed.
Lemma D_19e6c : decode_any W_19e6c = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_19e70 : bv 32 := 0x02013403.
Lemma F_19e70 : fetch_word Ubsan.M.loaded_segments (0x19e70 : word) = Some W_19e70.
Proof. vm_refl. Qed.
Lemma D_19e70 : decode_any W_19e70 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_19e74 : bv 32 := 0x01813483.
Lemma F_19e74 : fetch_word Ubsan.M.loaded_segments (0x19e74 : word) = Some W_19e74.
Proof. vm_refl. Qed.
Lemma D_19e74 : decode_any W_19e74 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_19e78 : bv 32 := 0x03010113.
Lemma F_19e78 : fetch_word Ubsan.M.loaded_segments (0x19e78 : word) = Some W_19e78.
Proof. vm_refl. Qed.
Lemma D_19e78 : decode_any W_19e78 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_19e7c : bv 32 := 0x00008067.
Lemma F_19e7c : fetch_word Ubsan.M.loaded_segments (0x19e7c : word) = Some W_19e7c.
Proof. vm_refl. Qed.
Lemma D_19e7c : decode_any W_19e7c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19e80 : bv 32 := 0xc0001073.
Lemma F_19e80 : fetch_word Ubsan.M.loaded_segments (0x19e80 : word) = Some W_19e80.
Proof. vm_refl. Qed.
Lemma D_19e80 : decode_any W_19e80 = Some (Csr CSR_RW 0 0 3072, 4%Z).
Proof. vm_refl. Qed.
