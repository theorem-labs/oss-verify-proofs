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

Definition W_199dc : bv 32 := 0xfe010113.
Lemma F_199dc : fetch_word Ubsan.M.loaded_segments (0x199dc : word) = Some W_199dc.
Proof. vm_refl. Qed.
Lemma D_199dc : decode_any W_199dc = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_199e0 : bv 32 := 0x00113c23.
Lemma F_199e0 : fetch_word Ubsan.M.loaded_segments (0x199e0 : word) = Some W_199e0.
Proof. vm_refl. Qed.
Lemma D_199e0 : decode_any W_199e0 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_199e4 : bv 32 := 0x00813823.
Lemma F_199e4 : fetch_word Ubsan.M.loaded_segments (0x199e4 : word) = Some W_199e4.
Proof. vm_refl. Qed.
Lemma D_199e4 : decode_any W_199e4 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_199e8 : bv 32 := 0x00913423.
Lemma F_199e8 : fetch_word Ubsan.M.loaded_segments (0x199e8 : word) = Some W_199e8.
Proof. vm_refl. Qed.
Lemma D_199e8 : decode_any W_199e8 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_199ec : bv 32 := 0x01213023.
Lemma F_199ec : fetch_word Ubsan.M.loaded_segments (0x199ec : word) = Some W_199ec.
Proof. vm_refl. Qed.
Lemma D_199ec : decode_any W_199ec = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_199f0 : bv 32 := 0x04050263.
Lemma F_199f0 : fetch_word Ubsan.M.loaded_segments (0x199f0 : word) = Some W_199f0.
Proof. vm_refl. Qed.
Lemma D_199f0 : decode_any W_199f0 = Some (Branch BC_EQ 10 0 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_199f4 : bv 32 := 0x00050493.
Lemma F_199f4 : fetch_word Ubsan.M.loaded_segments (0x199f4 : word) = Some W_199f4.
Proof. vm_refl. Qed.
Lemma D_199f4 : decode_any W_199f4 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_199f8 : bv 32 := 0x00757513.
Lemma F_199f8 : fetch_word Ubsan.M.loaded_segments (0x199f8 : word) = Some W_199f8.
Proof. vm_refl. Qed.
Lemma D_199f8 : decode_any W_199f8 = Some (OpImm ALU_AND 10 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_199fc : bv 32 := 0x12051c63.
Lemma F_199fc : fetch_word Ubsan.M.loaded_segments (0x199fc : word) = Some W_199fc.
Proof. vm_refl. Qed.
Lemma D_199fc : decode_any W_199fc = Some (Branch BC_NE 10 0 312, 4%Z).
Proof. vm_refl. Qed.

Definition W_19a00 : bv 32 := 0x0004a503.
Lemma F_19a00 : fetch_word Ubsan.M.loaded_segments (0x19a00 : word) = Some W_19a00.
Proof. vm_refl. Qed.
Lemma D_19a00 : decode_any W_19a00 = Some (Load SZ4 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19a04 : bv 32 := 0x0044a583.
Lemma F_19a04 : fetch_word Ubsan.M.loaded_segments (0x19a04 : word) = Some W_19a04.
Proof. vm_refl. Qed.
Lemma D_19a04 : decode_any W_19a04 = Some (Load SZ4 true 11 9 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_19a08 : bv 32 := 0x0084a603.
Lemma F_19a08 : fetch_word Ubsan.M.loaded_segments (0x19a08 : word) = Some W_19a08.
Proof. vm_refl. Qed.
Lemma D_19a08 : decode_any W_19a08 = Some (Load SZ4 true 12 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_19a0c : bv 32 := 0x969ff0ef.
Lemma F_19a0c : fetch_word Ubsan.M.loaded_segments (0x19a0c : word) = Some W_19a0c.
Proof. vm_refl. Qed.
Lemma D_19a0c : decode_any W_19a0c = Some (Jal 1 2095464, 4%Z).
Proof. vm_refl. Qed.

Definition W_19a10 : bv 32 := 0x04050663.
Lemma F_19a10 : fetch_word Ubsan.M.loaded_segments (0x19a10 : word) = Some W_19a10.
Proof. vm_refl. Qed.
Lemma D_19a10 : decode_any W_19a10 = Some (Branch BC_EQ 10 0 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_19a14 : bv 32 := 0x00050413.
Lemma F_19a14 : fetch_word Ubsan.M.loaded_segments (0x19a14 : word) = Some W_19a14.
Proof. vm_refl. Qed.
Lemma D_19a14 : decode_any W_19a14 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19a18 : bv 32 := 0x08a48663.
Lemma F_19a18 : fetch_word Ubsan.M.loaded_segments (0x19a18 : word) = Some W_19a18.
Proof. vm_refl. Qed.
Lemma D_19a18 : decode_any W_19a18 = Some (Branch BC_EQ 9 10 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_19a1c : bv 32 := 0x00c4a503.
Lemma F_19a1c : fetch_word Ubsan.M.loaded_segments (0x19a1c : word) = Some W_19a1c.
Proof. vm_refl. Qed.
Lemma D_19a1c : decode_any W_19a1c = Some (Load SZ4 true 10 9 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_19a20 : bv 32 := 0x00747913.
Lemma F_19a20 : fetch_word Ubsan.M.loaded_segments (0x19a20 : word) = Some W_19a20.
Proof. vm_refl. Qed.
Lemma D_19a20 : decode_any W_19a20 = Some (OpImm ALU_AND 18 8 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_19a24 : bv 32 := 0x08a05863.
Lemma F_19a24 : fetch_word Ubsan.M.loaded_segments (0x19a24 : word) = Some W_19a24.
Proof. vm_refl. Qed.
Lemma D_19a24 : decode_any W_19a24 = Some (Branch BC_GE 0 10 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_19a28 : bv 32 := 0x10091663.
Lemma F_19a28 : fetch_word Ubsan.M.loaded_segments (0x19a28 : word) = Some W_19a28.
Proof. vm_refl. Qed.
Lemma D_19a28 : decode_any W_19a28 = Some (Branch BC_NE 18 0 268, 4%Z).
Proof. vm_refl. Qed.

Definition W_19a2c : bv 32 := 0x00a42623.
Lemma F_19a2c : fetch_word Ubsan.M.loaded_segments (0x19a2c : word) = Some W_19a2c.
Proof. vm_refl. Qed.
Lemma D_19a2c : decode_any W_19a2c = Some (Store SZ4 8 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_19a30 : bv 32 := 0x0b00006f.
Lemma F_19a30 : fetch_word Ubsan.M.loaded_segments (0x19a30 : word) = Some W_19a30.
Proof. vm_refl. Qed.
Lemma D_19a30 : decode_any W_19a30 = Some (Jal 0 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_19a34 : bv 32 := 0x0002b517.
Lemma F_19a34 : fetch_word Ubsan.M.loaded_segments (0x19a34 : word) = Some W_19a34.
Proof. vm_refl. Qed.
Lemma D_19a34 : decode_any W_19a34 = Some (Auipc 10 43, 4%Z).
Proof. vm_refl. Qed.

Definition W_19a38 : bv 32 := 0x46453503.
Lemma F_19a38 : fetch_word Ubsan.M.loaded_segments (0x19a38 : word) = Some W_19a38.
Proof. vm_refl. Qed.
Lemma D_19a38 : decode_any W_19a38 = Some (Load SZ8 true 10 10 1124, 4%Z).
Proof. vm_refl. Qed.

Definition W_19a3c : bv 32 := 0x00052503.
Lemma F_19a3c : fetch_word Ubsan.M.loaded_segments (0x19a3c : word) = Some W_19a3c.
Proof. vm_refl. Qed.
Lemma D_19a3c : decode_any W_19a3c = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19a40 : bv 32 := 0x00500593.
Lemma F_19a40 : fetch_word Ubsan.M.loaded_segments (0x19a40 : word) = Some W_19a40.
Proof. vm_refl. Qed.
Lemma D_19a40 : decode_any W_19a40 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_19a44 : bv 32 := 0x04a5cc63.
Lemma F_19a44 : fetch_word Ubsan.M.loaded_segments (0x19a44 : word) = Some W_19a44.
Proof. vm_refl. Qed.
Lemma D_19a44 : decode_any W_19a44 = Some (Branch BC_LT 11 10 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_19a48 : bv 32 := 0xffff7517.
Lemma F_19a48 : fetch_word Ubsan.M.loaded_segments (0x19a48 : word) = Some W_19a48.
Proof. vm_refl. Qed.
Lemma D_19a48 : decode_any W_19a48 = Some (Auipc 10 1048567, 4%Z).
Proof. vm_refl. Qed.

Definition W_19a4c : bv 32 := 0xffff8597.
Lemma F_19a4c : fetch_word Ubsan.M.loaded_segments (0x19a4c : word) = Some W_19a4c.
Proof. vm_refl. Qed.
Lemma D_19a4c : decode_any W_19a4c = Some (Auipc 11 1048568, 4%Z).
Proof. vm_refl. Qed.

Definition W_19a50 : bv 32 := 0x86c50513.
Lemma F_19a50 : fetch_word Ubsan.M.loaded_segments (0x19a50 : word) = Some W_19a50.
Proof. vm_refl. Qed.
Lemma D_19a50 : decode_any W_19a50 = Some (OpImm ALU_ADD 10 10 2156, 4%Z).
Proof. vm_refl. Qed.

Definition W_19a54 : bv 32 := 0x31158593.
Lemma F_19a54 : fetch_word Ubsan.M.loaded_segments (0x19a54 : word) = Some W_19a54.
Proof. vm_refl. Qed.
Lemma D_19a54 : decode_any W_19a54 = Some (OpImm ALU_ADD 11 11 785, 4%Z).
Proof. vm_refl. Qed.

Definition W_19a58 : bv 32 := 0x0280006f.
Lemma F_19a58 : fetch_word Ubsan.M.loaded_segments (0x19a58 : word) = Some W_19a58.
Proof. vm_refl. Qed.
Lemma D_19a58 : decode_any W_19a58 = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_19a5c : bv 32 := 0x0002b517.
Lemma F_19a5c : fetch_word Ubsan.M.loaded_segments (0x19a5c : word) = Some W_19a5c.
Proof. vm_refl. Qed.
Lemma D_19a5c : decode_any W_19a5c = Some (Auipc 10 43, 4%Z).
Proof. vm_refl. Qed.

Definition W_19a60 : bv 32 := 0x43c53503.
Lemma F_19a60 : fetch_word Ubsan.M.loaded_segments (0x19a60 : word) = Some W_19a60.
Proof. vm_refl. Qed.
Lemma D_19a60 : decode_any W_19a60 = Some (Load SZ8 true 10 10 1084, 4%Z).
Proof. vm_refl. Qed.

Definition W_19a64 : bv 32 := 0x00052503.
Lemma F_19a64 : fetch_word Ubsan.M.loaded_segments (0x19a64 : word) = Some W_19a64.
Proof. vm_refl. Qed.
Lemma D_19a64 : decode_any W_19a64 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19a68 : bv 32 := 0x00500593.
Lemma F_19a68 : fetch_word Ubsan.M.loaded_segments (0x19a68 : word) = Some W_19a68.
Proof. vm_refl. Qed.
Lemma D_19a68 : decode_any W_19a68 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_19a6c : bv 32 := 0x02a5c863.
Lemma F_19a6c : fetch_word Ubsan.M.loaded_segments (0x19a6c : word) = Some W_19a6c.
Proof. vm_refl. Qed.
Lemma D_19a6c : decode_any W_19a6c = Some (Branch BC_LT 11 10 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_19a70 : bv 32 := 0xffff7517.
Lemma F_19a70 : fetch_word Ubsan.M.loaded_segments (0x19a70 : word) = Some W_19a70.
Proof. vm_refl. Qed.
Lemma D_19a70 : decode_any W_19a70 = Some (Auipc 10 1048567, 4%Z).
Proof. vm_refl. Qed.

Definition W_19a74 : bv 32 := 0xffff8597.
Lemma F_19a74 : fetch_word Ubsan.M.loaded_segments (0x19a74 : word) = Some W_19a74.
Proof. vm_refl. Qed.
Lemma D_19a74 : decode_any W_19a74 = Some (Auipc 11 1048568, 4%Z).
Proof. vm_refl. Qed.

Definition W_19a78 : bv 32 := 0xcf550513.
Lemma F_19a78 : fetch_word Ubsan.M.loaded_segments (0x19a78 : word) = Some W_19a78.
Proof. vm_refl. Qed.
Lemma D_19a78 : decode_any W_19a78 = Some (OpImm ALU_ADD 10 10 3317, 4%Z).
Proof. vm_refl. Qed.

Definition W_19a7c : bv 32 := 0x2e958593.
Lemma F_19a7c : fetch_word Ubsan.M.loaded_segments (0x19a7c : word) = Some W_19a7c.
Proof. vm_refl. Qed.
Lemma D_19a7c : decode_any W_19a7c = Some (OpImm ALU_ADD 11 11 745, 4%Z).
Proof. vm_refl. Qed.

Definition W_19a80 : bv 32 := 0x00000613.
Lemma F_19a80 : fetch_word Ubsan.M.loaded_segments (0x19a80 : word) = Some W_19a80.
Proof. vm_refl. Qed.
Lemma D_19a80 : decode_any W_19a80 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19a84 : bv 32 := 0x01813083.
Lemma F_19a84 : fetch_word Ubsan.M.loaded_segments (0x19a84 : word) = Some W_19a84.
Proof. vm_refl. Qed.
Lemma D_19a84 : decode_any W_19a84 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_19a88 : bv 32 := 0x01013403.
Lemma F_19a88 : fetch_word Ubsan.M.loaded_segments (0x19a88 : word) = Some W_19a88.
Proof. vm_refl. Qed.
Lemma D_19a88 : decode_any W_19a88 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_19a8c : bv 32 := 0x00813483.
Lemma F_19a8c : fetch_word Ubsan.M.loaded_segments (0x19a8c : word) = Some W_19a8c.
Proof. vm_refl. Qed.
Lemma D_19a8c : decode_any W_19a8c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_19a90 : bv 32 := 0x00013903.
Lemma F_19a90 : fetch_word Ubsan.M.loaded_segments (0x19a90 : word) = Some W_19a90.
Proof. vm_refl. Qed.
Lemma D_19a90 : decode_any W_19a90 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19a94 : bv 32 := 0x02010113.
Lemma F_19a94 : fetch_word Ubsan.M.loaded_segments (0x19a94 : word) = Some W_19a94.
Proof. vm_refl. Qed.
Lemma D_19a94 : decode_any W_19a94 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_19a98 : bv 32 := 0xc2cfe06f.
Lemma F_19a98 : fetch_word Ubsan.M.loaded_segments (0x19a98 : word) = Some W_19a98.
Proof. vm_refl. Qed.
Lemma D_19a98 : decode_any W_19a98 = Some (Jal 0 2090028, 4%Z).
Proof. vm_refl. Qed.

Definition W_19a9c : bv 32 := 0x00000413.
Lemma F_19a9c : fetch_word Ubsan.M.loaded_segments (0x19a9c : word) = Some W_19a9c.
Proof. vm_refl. Qed.
Lemma D_19a9c : decode_any W_19a9c = Some (OpImm ALU_ADD 8 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19aa0 : bv 32 := 0x0780006f.
Lemma F_19aa0 : fetch_word Ubsan.M.loaded_segments (0x19aa0 : word) = Some W_19aa0.
Proof. vm_refl. Qed.
Lemma D_19aa0 : decode_any W_19aa0 = Some (Jal 0 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_19aa4 : bv 32 := 0x00040513.
Lemma F_19aa4 : fetch_word Ubsan.M.loaded_segments (0x19aa4 : word) = Some W_19aa4.
Proof. vm_refl. Qed.
Lemma D_19aa4 : decode_any W_19aa4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19aa8 : bv 32 := 0x00048593.
Lemma F_19aa8 : fetch_word Ubsan.M.loaded_segments (0x19aa8 : word) = Some W_19aa8.
Proof. vm_refl. Qed.
Lemma D_19aa8 : decode_any W_19aa8 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19aac : bv 32 := 0x1d8000ef.
Lemma F_19aac : fetch_word Ubsan.M.loaded_segments (0x19aac : word) = Some W_19aac.
Proof. vm_refl. Qed.
Lemma D_19aac : decode_any W_19aac = Some (Jal 1 472, 4%Z).
Proof. vm_refl. Qed.

Definition W_19ab0 : bv 32 := 0x05c0006f.
Lemma F_19ab0 : fetch_word Ubsan.M.loaded_segments (0x19ab0 : word) = Some W_19ab0.
Proof. vm_refl. Qed.
Lemma D_19ab0 : decode_any W_19ab0 = Some (Jal 0 92, 4%Z).
Proof. vm_refl. Qed.

Definition W_19ab4 : bv 32 := 0x0002b517.
Lemma F_19ab4 : fetch_word Ubsan.M.loaded_segments (0x19ab4 : word) = Some W_19ab4.
Proof. vm_refl. Qed.
Lemma D_19ab4 : decode_any W_19ab4 = Some (Auipc 10 43, 4%Z).
Proof. vm_refl. Qed.

Definition W_19ab8 : bv 32 := 0x3e453503.
Lemma F_19ab8 : fetch_word Ubsan.M.loaded_segments (0x19ab8 : word) = Some W_19ab8.
Proof. vm_refl. Qed.
Lemma D_19ab8 : decode_any W_19ab8 = Some (Load SZ8 true 10 10 996, 4%Z).
Proof. vm_refl. Qed.

Definition W_19abc : bv 32 := 0x00052503.
Lemma F_19abc : fetch_word Ubsan.M.loaded_segments (0x19abc : word) = Some W_19abc.
Proof. vm_refl. Qed.
Lemma D_19abc : decode_any W_19abc = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19ac0 : bv 32 := 0x00500593.
Lemma F_19ac0 : fetch_word Ubsan.M.loaded_segments (0x19ac0 : word) = Some W_19ac0.
Proof. vm_refl. Qed.
Lemma D_19ac0 : decode_any W_19ac0 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_19ac4 : bv 32 := 0x00a5ce63.
Lemma F_19ac4 : fetch_word Ubsan.M.loaded_segments (0x19ac4 : word) = Some W_19ac4.
Proof. vm_refl. Qed.
Lemma D_19ac4 : decode_any W_19ac4 = Some (Branch BC_LT 11 10 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_19ac8 : bv 32 := 0xffff7517.
Lemma F_19ac8 : fetch_word Ubsan.M.loaded_segments (0x19ac8 : word) = Some W_19ac8.
Proof. vm_refl. Qed.
Lemma D_19ac8 : decode_any W_19ac8 = Some (Auipc 10 1048567, 4%Z).
Proof. vm_refl. Qed.

Definition W_19acc : bv 32 := 0xffff9597.
Lemma F_19acc : fetch_word Ubsan.M.loaded_segments (0x19acc : word) = Some W_19acc.
Proof. vm_refl. Qed.
Lemma D_19acc : decode_any W_19acc = Some (Auipc 11 1048569, 4%Z).
Proof. vm_refl. Qed.

Definition W_19ad0 : bv 32 := 0xf9d50513.
Lemma F_19ad0 : fetch_word Ubsan.M.loaded_segments (0x19ad0 : word) = Some W_19ad0.
Proof. vm_refl. Qed.
Lemma D_19ad0 : decode_any W_19ad0 = Some (OpImm ALU_ADD 10 10 3997, 4%Z).
Proof. vm_refl. Qed.

Definition W_19ad4 : bv 32 := 0x85b58593.
Lemma F_19ad4 : fetch_word Ubsan.M.loaded_segments (0x19ad4 : word) = Some W_19ad4.
Proof. vm_refl. Qed.
Lemma D_19ad4 : decode_any W_19ad4 = Some (OpImm ALU_ADD 11 11 2139, 4%Z).
Proof. vm_refl. Qed.

Definition W_19ad8 : bv 32 := 0x00100613.
Lemma F_19ad8 : fetch_word Ubsan.M.loaded_segments (0x19ad8 : word) = Some W_19ad8.
Proof. vm_refl. Qed.
Lemma D_19ad8 : decode_any W_19ad8 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_19adc : bv 32 := 0xb18fe0ef.
Lemma F_19adc : fetch_word Ubsan.M.loaded_segments (0x19adc : word) = Some W_19adc.
Proof. vm_refl. Qed.
Lemma D_19adc : decode_any W_19adc = Some (Jal 1 2089752, 4%Z).
Proof. vm_refl. Qed.

Definition W_19ae0 : bv 32 := 0x04091a63.
Lemma F_19ae0 : fetch_word Ubsan.M.loaded_segments (0x19ae0 : word) = Some W_19ae0.
Proof. vm_refl. Qed.
Lemma D_19ae0 : decode_any W_19ae0 = Some (Branch BC_NE 18 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_19ae4 : bv 32 := 0x0184b503.
Lemma F_19ae4 : fetch_word Ubsan.M.loaded_segments (0x19ae4 : word) = Some W_19ae4.
Proof. vm_refl. Qed.
Lemma D_19ae4 : decode_any W_19ae4 = Some (Load SZ8 true 10 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_19ae8 : bv 32 := 0x00a43c23.
Lemma F_19ae8 : fetch_word Ubsan.M.loaded_segments (0x19ae8 : word) = Some W_19ae8.
Proof. vm_refl. Qed.
Lemma D_19ae8 : decode_any W_19ae8 = Some (Store SZ8 8 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_19aec : bv 32 := 0x00040513.
Lemma F_19aec : fetch_word Ubsan.M.loaded_segments (0x19aec : word) = Some W_19aec.
Proof. vm_refl. Qed.
Lemma D_19aec : decode_any W_19aec = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19af0 : bv 32 := 0x00048593.
Lemma F_19af0 : fetch_word Ubsan.M.loaded_segments (0x19af0 : word) = Some W_19af0.
Proof. vm_refl. Qed.
Lemma D_19af0 : decode_any W_19af0 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19af4 : bv 32 := 0x190000ef.
Lemma F_19af4 : fetch_word Ubsan.M.loaded_segments (0x19af4 : word) = Some W_19af4.
Proof. vm_refl. Qed.
Lemma D_19af4 : decode_any W_19af4 = Some (Jal 1 400, 4%Z).
Proof. vm_refl. Qed.

Definition W_19af8 : bv 32 := 0x0284b583.
Lemma F_19af8 : fetch_word Ubsan.M.loaded_segments (0x19af8 : word) = Some W_19af8.
Proof. vm_refl. Qed.
Lemma D_19af8 : decode_any W_19af8 = Some (Load SZ8 true 11 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_19afc : bv 32 := 0x02840513.
Lemma F_19afc : fetch_word Ubsan.M.loaded_segments (0x19afc : word) = Some W_19afc.
Proof. vm_refl. Qed.
Lemma D_19afc : decode_any W_19afc = Some (OpImm ALU_ADD 10 8 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b00 : bv 32 := 0xd64fe0ef.
Lemma F_19b00 : fetch_word Ubsan.M.loaded_segments (0x19b00 : word) = Some W_19b00.
Proof. vm_refl. Qed.
Lemma D_19b00 : decode_any W_19b00 = Some (Jal 1 2090340, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b04 : bv 32 := 0x0204a503.
Lemma F_19b04 : fetch_word Ubsan.M.loaded_segments (0x19b04 : word) = Some W_19b04.
Proof. vm_refl. Qed.
Lemma D_19b04 : decode_any W_19b04 = Some (Load SZ4 true 10 9 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b08 : bv 32 := 0x02a42023.
Lemma F_19b08 : fetch_word Ubsan.M.loaded_segments (0x19b08 : word) = Some W_19b08.
Proof. vm_refl. Qed.
Lemma D_19b08 : decode_any W_19b08 = Some (Store SZ4 8 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b0c : bv 32 := 0x00040513.
Lemma F_19b0c : fetch_word Ubsan.M.loaded_segments (0x19b0c : word) = Some W_19b0c.
Proof. vm_refl. Qed.
Lemma D_19b0c : decode_any W_19b0c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b10 : bv 32 := 0x00000593.
Lemma F_19b10 : fetch_word Ubsan.M.loaded_segments (0x19b10 : word) = Some W_19b10.
Proof. vm_refl. Qed.
Lemma D_19b10 : decode_any W_19b10 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b14 : bv 32 := 0x200020ef.
Lemma F_19b14 : fetch_word Ubsan.M.loaded_segments (0x19b14 : word) = Some W_19b14.
Proof. vm_refl. Qed.
Lemma D_19b14 : decode_any W_19b14 = Some (Jal 1 8704, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b18 : bv 32 := 0x00040513.
Lemma F_19b18 : fetch_word Ubsan.M.loaded_segments (0x19b18 : word) = Some W_19b18.
Proof. vm_refl. Qed.
Lemma D_19b18 : decode_any W_19b18 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b1c : bv 32 := 0x01813083.
Lemma F_19b1c : fetch_word Ubsan.M.loaded_segments (0x19b1c : word) = Some W_19b1c.
Proof. vm_refl. Qed.
Lemma D_19b1c : decode_any W_19b1c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b20 : bv 32 := 0x01013403.
Lemma F_19b20 : fetch_word Ubsan.M.loaded_segments (0x19b20 : word) = Some W_19b20.
Proof. vm_refl. Qed.
Lemma D_19b20 : decode_any W_19b20 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b24 : bv 32 := 0x00813483.
Lemma F_19b24 : fetch_word Ubsan.M.loaded_segments (0x19b24 : word) = Some W_19b24.
Proof. vm_refl. Qed.
Lemma D_19b24 : decode_any W_19b24 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b28 : bv 32 := 0x00013903.
Lemma F_19b28 : fetch_word Ubsan.M.loaded_segments (0x19b28 : word) = Some W_19b28.
Proof. vm_refl. Qed.
Lemma D_19b28 : decode_any W_19b28 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b2c : bv 32 := 0x02010113.
Lemma F_19b2c : fetch_word Ubsan.M.loaded_segments (0x19b2c : word) = Some W_19b2c.
Proof. vm_refl. Qed.
Lemma D_19b2c : decode_any W_19b2c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b30 : bv 32 := 0x00008067.
Lemma F_19b30 : fetch_word Ubsan.M.loaded_segments (0x19b30 : word) = Some W_19b30.
Proof. vm_refl. Qed.
Lemma D_19b30 : decode_any W_19b30 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b34 : bv 32 := 0xc0001073.
Lemma F_19b34 : fetch_word Ubsan.M.loaded_segments (0x19b34 : word) = Some W_19b34.
Proof. vm_refl. Qed.
Lemma D_19b34 : decode_any W_19b34 = Some (Csr CSR_RW 0 0 3072, 4%Z).
Proof. vm_refl. Qed.
