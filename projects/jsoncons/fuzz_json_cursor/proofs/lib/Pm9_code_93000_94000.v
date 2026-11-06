(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_931b4 : bv 32 := 0xfffff637.
Lemma F_931b4 : fetch_word AsanUbsan.M.loaded_segments (0x931fc : word) = Some W_931b4.
Proof. vm_refl. Qed.
Lemma D_931b4 : decode_any W_931b4 = Some (Lui 12 1048575, 4%Z).
Proof. vm_refl. Qed.

Definition W_931b8 : bv 32 := 0x0016069b.
Lemma F_931b8 : fetch_word AsanUbsan.M.loaded_segments (0x93200 : word) = Some W_931b8.
Proof. vm_refl. Qed.
Lemma D_931b8 : decode_any W_931b8 = Some (OpImm32 13 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_931bc : bv 32 := 0x00d56863.
Lemma F_931bc : fetch_word AsanUbsan.M.loaded_segments (0x93204 : word) = Some W_931bc.
Proof. vm_refl. Qed.
Lemma D_931bc : decode_any W_931bc = Some (Branch BC_LTU 10 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_931cc : bv 32 := 0x00a63533.
Lemma F_931cc : fetch_word AsanUbsan.M.loaded_segments (0x93214 : word) = Some W_931cc.
Proof. vm_refl. Qed.
Lemma D_931cc : decode_any W_931cc = Some (Op ALU_SLTU 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_931d0 : bv 32 := 0x00008067.
Lemma F_931d0 : fetch_word AsanUbsan.M.loaded_segments (0x93218 : word) = Some W_931d0.
Proof. vm_refl. Qed.
Lemma D_931d0 : decode_any W_931d0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_931d4 : bv 32 := 0x0de00893.
Lemma F_931d4 : fetch_word AsanUbsan.M.loaded_segments (0x9321c : word) = Some W_931d4.
Proof. vm_refl. Qed.
Lemma D_931d4 : decode_any W_931d4 = Some (OpImm ALU_ADD 17 0 222, 4%Z).
Proof. vm_refl. Qed.

Definition W_931d8 : bv 32 := 0x00000073.
Lemma F_931d8 : fetch_word AsanUbsan.M.loaded_segments (0x93220 : word) = Some W_931d8.
Proof. vm_refl. Qed.
Lemma D_931d8 : decode_any W_931d8 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_931d8 : is_ecall W_931d8 = true.
Proof. reflexivity. Qed.

Definition W_931dc : bv 32 := 0x00008067.
Lemma F_931dc : fetch_word AsanUbsan.M.loaded_segments (0x93224 : word) = Some W_931dc.
Proof. vm_refl. Qed.
Lemma D_931dc : decode_any W_931dc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_931e0 : bv 32 := 0x0d700893.
Lemma F_931e0 : fetch_word AsanUbsan.M.loaded_segments (0x93228 : word) = Some W_931e0.
Proof. vm_refl. Qed.
Lemma D_931e0 : decode_any W_931e0 = Some (OpImm ALU_ADD 17 0 215, 4%Z).
Proof. vm_refl. Qed.

Definition W_931e4 : bv 32 := 0x00000073.
Lemma F_931e4 : fetch_word AsanUbsan.M.loaded_segments (0x9322c : word) = Some W_931e4.
Proof. vm_refl. Qed.
Lemma D_931e4 : decode_any W_931e4 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_931e4 : is_ecall W_931e4 = true.
Proof. reflexivity. Qed.

Definition W_931e8 : bv 32 := 0x00008067.
Lemma F_931e8 : fetch_word AsanUbsan.M.loaded_segments (0x93230 : word) = Some W_931e8.
Proof. vm_refl. Qed.
Lemma D_931e8 : decode_any W_931e8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_931fc : bv 32 := 0x000c1697.
Lemma F_931fc : fetch_word AsanUbsan.M.loaded_segments (0x93244 : word) = Some W_931fc.
Proof. vm_refl. Qed.
Lemma D_931fc : decode_any W_931fc = Some (Auipc 13 193, 4%Z).
Proof. vm_refl. Qed.

Definition W_93200 : bv 32 := 0x2fc6b683.
Lemma F_93200 : fetch_word AsanUbsan.M.loaded_segments (0x93248 : word) = Some W_93200.
Proof. vm_refl. Qed.
Lemma D_93200 : decode_any W_93200 = Some (Load SZ8 true 13 13 764, 4%Z).
Proof. vm_refl. Qed.

Definition W_93204 : bv 32 := 0x00068a63.
Lemma F_93204 : fetch_word AsanUbsan.M.loaded_segments (0x9324c : word) = Some W_93204.
Proof. vm_refl. Qed.
Lemma D_93204 : decode_any W_93204 = Some (Branch BC_EQ 13 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_93208 : bv 32 := 0x00400693.
Lemma F_93208 : fetch_word AsanUbsan.M.loaded_segments (0x93250 : word) = Some W_93208.
Proof. vm_refl. Qed.
Lemma D_93208 : decode_any W_93208 = Some (OpImm ALU_ADD 13 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_9320c : bv 32 := 0x00d60663.
Lemma F_9320c : fetch_word AsanUbsan.M.loaded_segments (0x93254 : word) = Some W_9320c.
Proof. vm_refl. Qed.
Lemma D_9320c : decode_any W_9320c = Some (Branch BC_EQ 12 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_93218 : bv 32 := 0x0e900893.
Lemma F_93218 : fetch_word AsanUbsan.M.loaded_segments (0x93260 : word) = Some W_93218.
Proof. vm_refl. Qed.
Lemma D_93218 : decode_any W_93218 = Some (OpImm ALU_ADD 17 0 233, 4%Z).
Proof. vm_refl. Qed.

Definition W_9321c : bv 32 := 0x00000073.
Lemma F_9321c : fetch_word AsanUbsan.M.loaded_segments (0x93264 : word) = Some W_9321c.
Proof. vm_refl. Qed.
Lemma D_9321c : decode_any W_9321c = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_9321c : is_ecall W_9321c = true.
Proof. reflexivity. Qed.

Definition W_93220 : bv 32 := 0x0005051b.
Lemma F_93220 : fetch_word AsanUbsan.M.loaded_segments (0x93268 : word) = Some W_93220.
Proof. vm_refl. Qed.
Lemma D_93220 : decode_any W_93220 = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_93224 : bv 32 := 0x00008067.
Lemma F_93224 : fetch_word AsanUbsan.M.loaded_segments (0x9326c : word) = Some W_93224.
Proof. vm_refl. Qed.
Lemma D_93224 : decode_any W_93224 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

