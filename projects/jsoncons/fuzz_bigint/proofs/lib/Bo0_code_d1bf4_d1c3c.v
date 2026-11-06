(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_d1bf4 : bv 32 := 0xff010113.
Lemma F_d1bf4 : fetch_word AsanUbsan.M.loaded_segments (0xd1bf4 : word) = Some W_d1bf4.
Proof. vm_refl. Qed.
Lemma D_d1bf4 : decode_any W_d1bf4 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1bf8 : bv 32 := 0x00113423.
Lemma F_d1bf8 : fetch_word AsanUbsan.M.loaded_segments (0xd1bf8 : word) = Some W_d1bf8.
Proof. vm_refl. Qed.
Lemma D_d1bf8 : decode_any W_d1bf8 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1bfc : bv 32 := 0x00813023.
Lemma F_d1bfc : fetch_word AsanUbsan.M.loaded_segments (0xd1bfc : word) = Some W_d1bfc.
Proof. vm_refl. Qed.
Lemma D_d1bfc : decode_any W_d1bfc = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1c00 : bv 32 := 0x00153413.
Lemma F_d1c00 : fetch_word AsanUbsan.M.loaded_segments (0xd1c00 : word) = Some W_d1c00.
Proof. vm_refl. Qed.
Lemma D_d1c00 : decode_any W_d1c00 = Some (OpImm ALU_SLTU 8 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1c04 : bv 32 := 0x00850433.
Lemma F_d1c04 : fetch_word AsanUbsan.M.loaded_segments (0xd1c04 : word) = Some W_d1c04.
Proof. vm_refl. Qed.
Lemma D_d1c04 : decode_any W_d1c04 = Some (Op ALU_ADD 8 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1c08 : bv 32 := 0x00040513.
Lemma F_d1c08 : fetch_word AsanUbsan.M.loaded_segments (0xd1c08 : word) = Some W_d1c08.
Proof. vm_refl. Qed.
Lemma D_d1c08 : decode_any W_d1c08 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1c0c : bv 32 := 0xacc8e0ef.
Lemma F_d1c0c : fetch_word AsanUbsan.M.loaded_segments (0xd1c0c : word) = Some W_d1c0c.
Proof. vm_refl. Qed.
Lemma D_d1c0c : decode_any W_d1c0c = Some (Jal 1 1630924, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1c10 : bv 32 := 0x00051e63.
Lemma F_d1c10 : fetch_word AsanUbsan.M.loaded_segments (0xd1c10 : word) = Some W_d1c10.
Proof. vm_refl. Qed.
Lemma D_d1c10 : decode_any W_d1c10 = Some (Branch BC_NE 10 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1c14 : bv 32 := 0xd64c30ef.
Lemma F_d1c14 : fetch_word AsanUbsan.M.loaded_segments (0xd1c14 : word) = Some W_d1c14.
Proof. vm_refl. Qed.
Lemma D_d1c14 : decode_any W_d1c14 = Some (Jal 1 1848676, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1c18 : bv 32 := 0x02050263.
Lemma F_d1c18 : fetch_word AsanUbsan.M.loaded_segments (0xd1c18 : word) = Some W_d1c18.
Proof. vm_refl. Qed.
Lemma D_d1c18 : decode_any W_d1c18 = Some (Branch BC_EQ 10 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1c1c : bv 32 := 0x000500e7.
Lemma F_d1c1c : fetch_word AsanUbsan.M.loaded_segments (0xd1c1c : word) = Some W_d1c1c.
Proof. vm_refl. Qed.
Lemma D_d1c1c : decode_any W_d1c1c = Some (Jalr 1 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1c20 : bv 32 := 0x00040513.
Lemma F_d1c20 : fetch_word AsanUbsan.M.loaded_segments (0xd1c20 : word) = Some W_d1c20.
Proof. vm_refl. Qed.
Lemma D_d1c20 : decode_any W_d1c20 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1c24 : bv 32 := 0xab48e0ef.
Lemma F_d1c24 : fetch_word AsanUbsan.M.loaded_segments (0xd1c24 : word) = Some W_d1c24.
Proof. vm_refl. Qed.
Lemma D_d1c24 : decode_any W_d1c24 = Some (Jal 1 1630900, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1c28 : bv 32 := 0xfe0506e3.
Lemma F_d1c28 : fetch_word AsanUbsan.M.loaded_segments (0xd1c28 : word) = Some W_d1c28.
Proof. vm_refl. Qed.
Lemma D_d1c28 : decode_any W_d1c28 = Some (Branch BC_EQ 10 0 8172, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1c2c : bv 32 := 0x00813083.
Lemma F_d1c2c : fetch_word AsanUbsan.M.loaded_segments (0xd1c2c : word) = Some W_d1c2c.
Proof. vm_refl. Qed.
Lemma D_d1c2c : decode_any W_d1c2c = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1c30 : bv 32 := 0x00013403.
Lemma F_d1c30 : fetch_word AsanUbsan.M.loaded_segments (0xd1c30 : word) = Some W_d1c30.
Proof. vm_refl. Qed.
Lemma D_d1c30 : decode_any W_d1c30 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1c34 : bv 32 := 0x01010113.
Lemma F_d1c34 : fetch_word AsanUbsan.M.loaded_segments (0xd1c34 : word) = Some W_d1c34.
Proof. vm_refl. Qed.
Lemma D_d1c34 : decode_any W_d1c34 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1c38 : bv 32 := 0x00008067.
Lemma F_d1c38 : fetch_word AsanUbsan.M.loaded_segments (0xd1c38 : word) = Some W_d1c38.
Proof. vm_refl. Qed.
Lemma D_d1c38 : decode_any W_d1c38 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
