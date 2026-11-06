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

Definition W_9d124 : bv 32 := 0xfe010113.
Lemma F_9d124 : fetch_word AsanUbsan.M.loaded_segments (0x9d16c : word) = Some W_9d124.
Proof. vm_refl. Qed.
Lemma D_9d124 : decode_any W_9d124 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d128 : bv 32 := 0x00113c23.
Lemma F_9d128 : fetch_word AsanUbsan.M.loaded_segments (0x9d170 : word) = Some W_9d128.
Proof. vm_refl. Qed.
Lemma D_9d128 : decode_any W_9d128 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d12c : bv 32 := 0x00813823.
Lemma F_9d12c : fetch_word AsanUbsan.M.loaded_segments (0x9d174 : word) = Some W_9d12c.
Proof. vm_refl. Qed.
Lemma D_9d12c : decode_any W_9d12c = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d130 : bv 32 := 0x00913423.
Lemma F_9d130 : fetch_word AsanUbsan.M.loaded_segments (0x9d178 : word) = Some W_9d130.
Proof. vm_refl. Qed.
Lemma D_9d130 : decode_any W_9d130 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d134 : bv 32 := 0x01213023.
Lemma F_9d134 : fetch_word AsanUbsan.M.loaded_segments (0x9d17c : word) = Some W_9d134.
Proof. vm_refl. Qed.
Lemma D_9d134 : decode_any W_9d134 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d138 : bv 32 := 0x00060413.
Lemma F_9d138 : fetch_word AsanUbsan.M.loaded_segments (0x9d180 : word) = Some W_9d138.
Proof. vm_refl. Qed.
Lemma D_9d138 : decode_any W_9d138 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d13c : bv 32 := 0x00058493.
Lemma F_9d13c : fetch_word AsanUbsan.M.loaded_segments (0x9d184 : word) = Some W_9d13c.
Proof. vm_refl. Qed.
Lemma D_9d13c : decode_any W_9d13c = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d140 : bv 32 := 0x00058513.
Lemma F_9d140 : fetch_word AsanUbsan.M.loaded_segments (0x9d188 : word) = Some W_9d140.
Proof. vm_refl. Qed.
Lemma D_9d140 : decode_any W_9d140 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d144 : bv 32 := 0x00060593.
Lemma F_9d144 : fetch_word AsanUbsan.M.loaded_segments (0x9d18c : word) = Some W_9d144.
Proof. vm_refl. Qed.
Lemma D_9d144 : decode_any W_9d144 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d148 : bv 32 := 0x00068613.
Lemma F_9d148 : fetch_word AsanUbsan.M.loaded_segments (0x9d190 : word) = Some W_9d148.
Proof. vm_refl. Qed.
Lemma D_9d148 : decode_any W_9d148 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d14c : bv 32 := 0xf19f70ef.
Lemma F_9d14c : fetch_word AsanUbsan.M.loaded_segments (0x9d194 : word) = Some W_9d14c.
Proof. vm_refl. Qed.
Lemma D_9d14c : decode_any W_9d14c = Some (Jal 1 2064152, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d150 : bv 32 := 0x00050e63.
Lemma F_9d150 : fetch_word AsanUbsan.M.loaded_segments (0x9d198 : word) = Some W_9d150.
Proof. vm_refl. Qed.
Lemma D_9d150 : decode_any W_9d150 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d154 : bv 32 := 0x01813083.
Lemma F_9d154 : fetch_word AsanUbsan.M.loaded_segments (0x9d19c : word) = Some W_9d154.
Proof. vm_refl. Qed.
Lemma D_9d154 : decode_any W_9d154 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d158 : bv 32 := 0x01013403.
Lemma F_9d158 : fetch_word AsanUbsan.M.loaded_segments (0x9d1a0 : word) = Some W_9d158.
Proof. vm_refl. Qed.
Lemma D_9d158 : decode_any W_9d158 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d15c : bv 32 := 0x00813483.
Lemma F_9d15c : fetch_word AsanUbsan.M.loaded_segments (0x9d1a4 : word) = Some W_9d15c.
Proof. vm_refl. Qed.
Lemma D_9d15c : decode_any W_9d15c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d160 : bv 32 := 0x00013903.
Lemma F_9d160 : fetch_word AsanUbsan.M.loaded_segments (0x9d1a8 : word) = Some W_9d160.
Proof. vm_refl. Qed.
Lemma D_9d160 : decode_any W_9d160 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d164 : bv 32 := 0x02010113.
Lemma F_9d164 : fetch_word AsanUbsan.M.loaded_segments (0x9d1ac : word) = Some W_9d164.
Proof. vm_refl. Qed.
Lemma D_9d164 : decode_any W_9d164 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d168 : bv 32 := 0x00008067.
Lemma F_9d168 : fetch_word AsanUbsan.M.loaded_segments (0x9d1b0 : word) = Some W_9d168.
Proof. vm_refl. Qed.
Lemma D_9d168 : decode_any W_9d168 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d270 : bv 32 := 0x00058513.
Lemma F_9d270 : fetch_word AsanUbsan.M.loaded_segments (0x9d2b8 : word) = Some W_9d270.
Proof. vm_refl. Qed.
Lemma D_9d270 : decode_any W_9d270 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d274 : bv 32 := 0x00060593.
Lemma F_9d274 : fetch_word AsanUbsan.M.loaded_segments (0x9d2bc : word) = Some W_9d274.
Proof. vm_refl. Qed.
Lemma D_9d274 : decode_any W_9d274 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d278 : bv 32 := 0x00068613.
Lemma F_9d278 : fetch_word AsanUbsan.M.loaded_segments (0x9d2c0 : word) = Some W_9d278.
Proof. vm_refl. Qed.
Lemma D_9d278 : decode_any W_9d278 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d27c : bv 32 := 0xc65f706f.
Lemma F_9d27c : fetch_word AsanUbsan.M.loaded_segments (0x9d2c4 : word) = Some W_9d27c.
Proof. vm_refl. Qed.
Lemma D_9d27c : decode_any W_9d27c = Some (Jal 0 2063460, 4%Z).
Proof. vm_refl. Qed.

