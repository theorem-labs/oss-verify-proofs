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

Definition W_71dc0 : bv 32 := 0xfffff637.
Lemma F_71dc0 : fetch_word AsanUbsan.M.loaded_segments (0x71dc0 : word) = Some W_71dc0.
Proof. vm_refl. Qed.
Lemma D_71dc0 : decode_any W_71dc0 = Some (Lui 12 1048575, 4%Z).
Proof. vm_refl. Qed.

Definition W_71dc4 : bv 32 := 0x0016069b.
Lemma F_71dc4 : fetch_word AsanUbsan.M.loaded_segments (0x71dc4 : word) = Some W_71dc4.
Proof. vm_refl. Qed.
Lemma D_71dc4 : decode_any W_71dc4 = Some (OpImm32 13 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_71dc8 : bv 32 := 0x00d56863.
Lemma F_71dc8 : fetch_word AsanUbsan.M.loaded_segments (0x71dc8 : word) = Some W_71dc8.
Proof. vm_refl. Qed.
Lemma D_71dc8 : decode_any W_71dc8 = Some (Branch BC_LTU 10 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_71dcc : bv 32 := 0x00058663.
Lemma F_71dcc : fetch_word AsanUbsan.M.loaded_segments (0x71dcc : word) = Some W_71dcc.
Proof. vm_refl. Qed.
Lemma D_71dcc : decode_any W_71dcc = Some (Branch BC_EQ 11 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_71dd0 : bv 32 := 0x40a006bb.
Lemma F_71dd0 : fetch_word AsanUbsan.M.loaded_segments (0x71dd0 : word) = Some W_71dd0.
Proof. vm_refl. Qed.
Lemma D_71dd0 : decode_any W_71dd0 = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_71dd4 : bv 32 := 0x00d5a023.
Lemma F_71dd4 : fetch_word AsanUbsan.M.loaded_segments (0x71dd4 : word) = Some W_71dd4.
Proof. vm_refl. Qed.
Lemma D_71dd4 : decode_any W_71dd4 = Some (Store SZ4 11 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71dd8 : bv 32 := 0x00a63533.
Lemma F_71dd8 : fetch_word AsanUbsan.M.loaded_segments (0x71dd8 : word) = Some W_71dd8.
Proof. vm_refl. Qed.
Lemma D_71dd8 : decode_any W_71dd8 = Some (Op ALU_SLTU 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_71ddc : bv 32 := 0x00008067.
Lemma F_71ddc : fetch_word AsanUbsan.M.loaded_segments (0x71ddc : word) = Some W_71ddc.
Proof. vm_refl. Qed.
Lemma D_71ddc : decode_any W_71ddc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71de0 : bv 32 := 0x0de00893.
Lemma F_71de0 : fetch_word AsanUbsan.M.loaded_segments (0x71de0 : word) = Some W_71de0.
Proof. vm_refl. Qed.
Lemma D_71de0 : decode_any W_71de0 = Some (OpImm ALU_ADD 17 0 222, 4%Z).
Proof. vm_refl. Qed.

Definition W_71de4 : bv 32 := 0x00000073.
Lemma F_71de4 : fetch_word AsanUbsan.M.loaded_segments (0x71de4 : word) = Some W_71de4.
Proof. vm_refl. Qed.
Lemma D_71de4 : decode_any W_71de4 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_71de4 : is_ecall W_71de4 = true.
Proof. reflexivity. Qed.

Definition W_71de8 : bv 32 := 0x00008067.
Lemma F_71de8 : fetch_word AsanUbsan.M.loaded_segments (0x71de8 : word) = Some W_71de8.
Proof. vm_refl. Qed.
Lemma D_71de8 : decode_any W_71de8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71dec : bv 32 := 0x0d700893.
Lemma F_71dec : fetch_word AsanUbsan.M.loaded_segments (0x71dec : word) = Some W_71dec.
Proof. vm_refl. Qed.
Lemma D_71dec : decode_any W_71dec = Some (OpImm ALU_ADD 17 0 215, 4%Z).
Proof. vm_refl. Qed.

Definition W_71df0 : bv 32 := 0x00000073.
Lemma F_71df0 : fetch_word AsanUbsan.M.loaded_segments (0x71df0 : word) = Some W_71df0.
Proof. vm_refl. Qed.
Lemma D_71df0 : decode_any W_71df0 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_71df0 : is_ecall W_71df0 = true.
Proof. reflexivity. Qed.

Definition W_71df4 : bv 32 := 0x00008067.
Lemma F_71df4 : fetch_word AsanUbsan.M.loaded_segments (0x71df4 : word) = Some W_71df4.
Proof. vm_refl. Qed.
Lemma D_71df4 : decode_any W_71df4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
