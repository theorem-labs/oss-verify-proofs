(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Ubsan.
Open Scope bv_scope.

#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_221b0 : bv 32 := 0x00d4f863.
Lemma F_221b0 : fetch_word Ubsan.M.loaded_segments (0x221b0 : word) = Some W_221b0.
Proof. vm_refl. Qed.
Lemma D_221b0 : decode_any W_221b0 = Some (Branch BC_GEU 9 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_221c0 : bv 32 := 0x0096f863.
Lemma F_221c0 : fetch_word Ubsan.M.loaded_segments (0x221c0 : word) = Some W_221c0.
Proof. vm_refl. Qed.
Lemma D_221c0 : decode_any W_221c0 = Some (Branch BC_GEU 13 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_221fc : bv 32 := 0x03356e63.
Lemma F_221fc : fetch_word Ubsan.M.loaded_segments (0x221fc : word) = Some W_221fc.
Proof. vm_refl. Qed.
Lemma D_221fc : decode_any W_221fc = Some (Branch BC_LTU 10 19 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_22224 : bv 32 := 0xfaa9fae3.
Lemma F_22224 : fetch_word Ubsan.M.loaded_segments (0x22224 : word) = Some W_22224.
Proof. vm_refl. Qed.
Lemma D_22224 : decode_any W_22224 = Some (Branch BC_GEU 19 10 8116, 4%Z).
Proof. vm_refl. Qed.

Definition W_22264 : bv 32 := 0x00008067.
Lemma F_22264 : fetch_word Ubsan.M.loaded_segments (0x22264 : word) = Some W_22264.
Proof. vm_refl. Qed.
Lemma D_22264 : decode_any W_22264 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_222c0 : bv 32 := 0x00008067.
Lemma F_222c0 : fetch_word Ubsan.M.loaded_segments (0x222c0 : word) = Some W_222c0.
Proof. vm_refl. Qed.
Lemma D_222c0 : decode_any W_222c0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_224c4 : bv 32 := 0x00008067.
Lemma F_224c4 : fetch_word Ubsan.M.loaded_segments (0x224c4 : word) = Some W_224c4.
Proof. vm_refl. Qed.
Lemma D_224c4 : decode_any W_224c4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_22bf8 : bv 32 := 0x00008067.
Lemma F_22bf8 : fetch_word Ubsan.M.loaded_segments (0x22bf8 : word) = Some W_22bf8.
Proof. vm_refl. Qed.
Lemma D_22bf8 : decode_any W_22bf8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_22d90 : bv 32 := 0x02054063.
Lemma F_22d90 : fetch_word Ubsan.M.loaded_segments (0x22d90 : word) = Some W_22d90.
Proof. vm_refl. Qed.
Lemma D_22d90 : decode_any W_22d90 = Some (Branch BC_LT 10 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_22d94 : bv 32 := 0x00000593.
Lemma F_22d94 : fetch_word Ubsan.M.loaded_segments (0x22d94 : word) = Some W_22d94.
Proof. vm_refl. Qed.
Lemma D_22d94 : decode_any W_22d94 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_22d98 : bv 32 := 0x00058613.
Lemma F_22d98 : fetch_word Ubsan.M.loaded_segments (0x22d98 : word) = Some W_22d98.
Proof. vm_refl. Qed.
Lemma D_22d98 : decode_any W_22d98 = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_22d9c : bv 32 := 0x0015859b.
Lemma F_22d9c : fetch_word Ubsan.M.loaded_segments (0x22d9c : word) = Some W_22d9c.
Proof. vm_refl. Qed.
Lemma D_22d9c : decode_any W_22d9c = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_22da0 : bv 32 := 0x0ac5ce63.
Lemma F_22da0 : fetch_word Ubsan.M.loaded_segments (0x22da0 : word) = Some W_22da0.
Proof. vm_refl. Qed.
Lemma D_22da0 : decode_any W_22da0 = Some (Branch BC_LT 11 12 188, 4%Z).
Proof. vm_refl. Qed.

Definition W_22da4 : bv 32 := 0x00151513.
Lemma F_22da4 : fetch_word Ubsan.M.loaded_segments (0x22da4 : word) = Some W_22da4.
Proof. vm_refl. Qed.
Lemma D_22da4 : decode_any W_22da4 = Some (ShiftImm ALU_SLL 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_22da8 : bv 32 := 0xfe0558e3.
Lemma F_22da8 : fetch_word Ubsan.M.loaded_segments (0x22da8 : word) = Some W_22da8.
Proof. vm_refl. Qed.
Lemma D_22da8 : decode_any W_22da8 = Some (Branch BC_GE 10 0 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_22df0 : bv 32 := 0x04090463.
Lemma F_22df0 : fetch_word Ubsan.M.loaded_segments (0x22df0 : word) = Some W_22df0.
Proof. vm_refl. Qed.
Lemma D_22df0 : decode_any W_22df0 = Some (Branch BC_EQ 18 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_22e14 : bv 32 := 0x02a97263.
Lemma F_22e14 : fetch_word Ubsan.M.loaded_segments (0x22e14 : word) = Some W_22e14.
Proof. vm_refl. Qed.
Lemma D_22e14 : decode_any W_22e14 = Some (Branch BC_GEU 18 10 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_22e58 : bv 32 := 0x00008067.
Lemma F_22e58 : fetch_word Ubsan.M.loaded_segments (0x22e58 : word) = Some W_22e58.
Proof. vm_refl. Qed.
Lemma D_22e58 : decode_any W_22e58 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_22eb0 : bv 32 := 0x01176663.
Lemma F_22eb0 : fetch_word Ubsan.M.loaded_segments (0x22eb0 : word) = Some W_22eb0.
Proof. vm_refl. Qed.
Lemma D_22eb0 : decode_any W_22eb0 = Some (Branch BC_LTU 14 17 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_22eb4 : bv 32 := 0x02e89463.
Lemma F_22eb4 : fetch_word Ubsan.M.loaded_segments (0x22eb4 : word) = Some W_22eb4.
Proof. vm_refl. Qed.
Lemma D_22eb4 : decode_any W_22eb4 = Some (Branch BC_NE 17 14 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_22eb8 : bv 32 := 0x0255e263.
Lemma F_22eb8 : fetch_word Ubsan.M.loaded_segments (0x22eb8 : word) = Some W_22eb8.
Proof. vm_refl. Qed.
Lemma D_22eb8 : decode_any W_22eb8 = Some (Branch BC_LTU 11 5 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_22ed4 : bv 32 := 0xff1764e3.
Lemma F_22ed4 : fetch_word Ubsan.M.loaded_segments (0x22ed4 : word) = Some W_22ed4.
Proof. vm_refl. Qed.
Lemma D_22ed4 : decode_any W_22ed4 = Some (Branch BC_LTU 14 17 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_22ed8 : bv 32 := 0xfddff06f.
Lemma F_22ed8 : fetch_word Ubsan.M.loaded_segments (0x22ed8 : word) = Some W_22ed8.
Proof. vm_refl. Qed.
Lemma D_22ed8 : decode_any W_22ed8 = Some (Jal 0 2097116, 4%Z).
Proof. vm_refl. Qed.

Definition W_22f28 : bv 32 := 0x00071463.
Lemma F_22f28 : fetch_word Ubsan.M.loaded_segments (0x22f28 : word) = Some W_22f28.
Proof. vm_refl. Qed.
Lemma D_22f28 : decode_any W_22f28 = Some (Branch BC_NE 14 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_22f2c : bv 32 := 0x02d7ea63.
Lemma F_22f2c : fetch_word Ubsan.M.loaded_segments (0x22f2c : word) = Some W_22f2c.
Proof. vm_refl. Qed.
Lemma D_22f2c : decode_any W_22f2c = Some (Branch BC_LTU 15 13 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_22f58 : bv 32 := 0xfe0714e3.
Lemma F_22f58 : fetch_word Ubsan.M.loaded_segments (0x22f58 : word) = Some W_22f58.
Proof. vm_refl. Qed.
Lemma D_22f58 : decode_any W_22f58 = Some (Branch BC_NE 14 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_22f5c : bv 32 := 0xfed872e3.
Lemma F_22f5c : fetch_word Ubsan.M.loaded_segments (0x22f5c : word) = Some W_22f5c.
Proof. vm_refl. Qed.
Lemma D_22f5c : decode_any W_22f5c = Some (Branch BC_GEU 16 13 8164, 4%Z).
Proof. vm_refl. Qed.

Definition W_22f64 : bv 32 := 0x00008067.
Lemma F_22f64 : fetch_word Ubsan.M.loaded_segments (0x22f64 : word) = Some W_22f64.
Proof. vm_refl. Qed.
Lemma D_22f64 : decode_any W_22f64 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_23094 : bv 32 := 0x08897063.
Lemma F_23094 : fetch_word Ubsan.M.loaded_segments (0x23094 : word) = Some W_23094.
Proof. vm_refl. Qed.
Lemma D_23094 : decode_any W_23094 = Some (Branch BC_GEU 18 8 128, 4%Z).
Proof. vm_refl. Qed.
