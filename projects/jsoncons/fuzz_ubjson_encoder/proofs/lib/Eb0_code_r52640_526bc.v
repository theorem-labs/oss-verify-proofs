(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_6c1f0 : bv 32 := 0xfe010113.
Lemma F_6c1f0 : fetch_word AsanUbsan.M.loaded_segments (0x6c240 : word) = Some W_6c1f0.
Proof. vm_refl. Qed.
Lemma D_6c1f0 : decode_any W_6c1f0 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c1f4 : bv 32 := 0x00113c23.
Lemma F_6c1f4 : fetch_word AsanUbsan.M.loaded_segments (0x6c244 : word) = Some W_6c1f4.
Proof. vm_refl. Qed.
Lemma D_6c1f4 : decode_any W_6c1f4 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c1f8 : bv 32 := 0x00813823.
Lemma F_6c1f8 : fetch_word AsanUbsan.M.loaded_segments (0x6c248 : word) = Some W_6c1f8.
Proof. vm_refl. Qed.
Lemma D_6c1f8 : decode_any W_6c1f8 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c1fc : bv 32 := 0x00913423.
Lemma F_6c1fc : fetch_word AsanUbsan.M.loaded_segments (0x6c24c : word) = Some W_6c1fc.
Proof. vm_refl. Qed.
Lemma D_6c1fc : decode_any W_6c1fc = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c200 : bv 32 := 0x01213023.
Lemma F_6c200 : fetch_word AsanUbsan.M.loaded_segments (0x6c250 : word) = Some W_6c200.
Proof. vm_refl. Qed.
Lemma D_6c200 : decode_any W_6c200 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c204 : bv 32 := 0x00050413.
Lemma F_6c204 : fetch_word AsanUbsan.M.loaded_segments (0x6c254 : word) = Some W_6c204.
Proof. vm_refl. Qed.
Lemma D_6c204 : decode_any W_6c204 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c208 : bv 32 := 0x038160ef.
Lemma F_6c208 : fetch_word AsanUbsan.M.loaded_segments (0x6c258 : word) = Some W_6c208.
Proof. vm_refl. Qed.
Lemma D_6c208 : decode_any W_6c208 = Some (Jal 1 90168, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c20c : bv 32 := 0x000d3597.
Lemma F_6c20c : fetch_word AsanUbsan.M.loaded_segments (0x6c25c : word) = Some W_6c20c.
Proof. vm_refl. Qed.
Lemma D_6c20c : decode_any W_6c20c = Some (Auipc 11 211, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c210 : bv 32 := 0x56c5b583.
Lemma F_6c210 : fetch_word AsanUbsan.M.loaded_segments (0x6c260 : word) = Some W_6c210.
Proof. vm_refl. Qed.
Lemma D_6c210 : decode_any W_6c210 = Some (Load SZ8 true 11 11 1388, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c214 : bv 32 := 0x00050913.
Lemma F_6c214 : fetch_word AsanUbsan.M.loaded_segments (0x6c264 : word) = Some W_6c214.
Proof. vm_refl. Qed.
Lemma D_6c214 : decode_any W_6c214 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c218 : bv 32 := 0x00040513.
Lemma F_6c218 : fetch_word AsanUbsan.M.loaded_segments (0x6c268 : word) = Some W_6c218.
Proof. vm_refl. Qed.
Lemma D_6c218 : decode_any W_6c218 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c21c : bv 32 := 0x000580e7.
Lemma F_6c21c : fetch_word AsanUbsan.M.loaded_segments (0x6c26c : word) = Some W_6c21c.
Proof. vm_refl. Qed.
Lemma D_6c21c : decode_any W_6c21c = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c220 : bv 32 := 0x00050493.
Lemma F_6c220 : fetch_word AsanUbsan.M.loaded_segments (0x6c270 : word) = Some W_6c220.
Proof. vm_refl. Qed.
Lemma D_6c220 : decode_any W_6c220 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c224 : bv 32 := 0x02090663.
Lemma F_6c224 : fetch_word AsanUbsan.M.loaded_segments (0x6c274 : word) = Some W_6c224.
Proof. vm_refl. Qed.
Lemma D_6c224 : decode_any W_6c224 = Some (Branch BC_EQ 18 0 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c228 : bv 32 := 0x019180ef.
Lemma F_6c228 : fetch_word AsanUbsan.M.loaded_segments (0x6c278 : word) = Some W_6c228.
Proof. vm_refl. Qed.
Lemma D_6c228 : decode_any W_6c228 = Some (Jal 1 100376, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c22c : bv 32 := 0x00050863.
Lemma F_6c22c : fetch_word AsanUbsan.M.loaded_segments (0x6c27c : word) = Some W_6c22c.
Proof. vm_refl. Qed.
Lemma D_6c22c : decode_any W_6c22c = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c230 : bv 32 := 0x03053603.
Lemma F_6c230 : fetch_word AsanUbsan.M.loaded_segments (0x6c280 : word) = Some W_6c230.
Proof. vm_refl. Qed.
Lemma D_6c230 : decode_any W_6c230 = Some (Load SZ8 true 12 10 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c234 : bv 32 := 0x03853683.
Lemma F_6c234 : fetch_word AsanUbsan.M.loaded_segments (0x6c284 : word) = Some W_6c234.
Proof. vm_refl. Qed.
Lemma D_6c234 : decode_any W_6c234 = Some (Load SZ8 true 13 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c238 : bv 32 := 0x00c0006f.
Lemma F_6c238 : fetch_word AsanUbsan.M.loaded_segments (0x6c288 : word) = Some W_6c238.
Proof. vm_refl. Qed.
Lemma D_6c238 : decode_any W_6c238 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c244 : bv 32 := 0x00040513.
Lemma F_6c244 : fetch_word AsanUbsan.M.loaded_segments (0x6c294 : word) = Some W_6c244.
Proof. vm_refl. Qed.
Lemma D_6c244 : decode_any W_6c244 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c248 : bv 32 := 0x00048593.
Lemma F_6c248 : fetch_word AsanUbsan.M.loaded_segments (0x6c298 : word) = Some W_6c248.
Proof. vm_refl. Qed.
Lemma D_6c248 : decode_any W_6c248 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c24c : bv 32 := 0x725250ef.
Lemma F_6c24c : fetch_word AsanUbsan.M.loaded_segments (0x6c29c : word) = Some W_6c24c.
Proof. vm_refl. Qed.
Lemma D_6c24c : decode_any W_6c24c = Some (Jal 1 155428, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c250 : bv 32 := 0x00048513.
Lemma F_6c250 : fetch_word AsanUbsan.M.loaded_segments (0x6c2a0 : word) = Some W_6c250.
Proof. vm_refl. Qed.
Lemma D_6c250 : decode_any W_6c250 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c254 : bv 32 := 0x01813083.
Lemma F_6c254 : fetch_word AsanUbsan.M.loaded_segments (0x6c2a4 : word) = Some W_6c254.
Proof. vm_refl. Qed.
Lemma D_6c254 : decode_any W_6c254 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c258 : bv 32 := 0x01013403.
Lemma F_6c258 : fetch_word AsanUbsan.M.loaded_segments (0x6c2a8 : word) = Some W_6c258.
Proof. vm_refl. Qed.
Lemma D_6c258 : decode_any W_6c258 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c25c : bv 32 := 0x00813483.
Lemma F_6c25c : fetch_word AsanUbsan.M.loaded_segments (0x6c2ac : word) = Some W_6c25c.
Proof. vm_refl. Qed.
Lemma D_6c25c : decode_any W_6c25c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c260 : bv 32 := 0x00013903.
Lemma F_6c260 : fetch_word AsanUbsan.M.loaded_segments (0x6c2b0 : word) = Some W_6c260.
Proof. vm_refl. Qed.
Lemma D_6c260 : decode_any W_6c260 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c264 : bv 32 := 0x02010113.
Lemma F_6c264 : fetch_word AsanUbsan.M.loaded_segments (0x6c2b4 : word) = Some W_6c264.
Proof. vm_refl. Qed.
Lemma D_6c264 : decode_any W_6c264 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c268 : bv 32 := 0x00008067.
Lemma F_6c268 : fetch_word AsanUbsan.M.loaded_segments (0x6c2b8 : word) = Some W_6c268.
Proof. vm_refl. Qed.
Lemma D_6c268 : decode_any W_6c268 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
