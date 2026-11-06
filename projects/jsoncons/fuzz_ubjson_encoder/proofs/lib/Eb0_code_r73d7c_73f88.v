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

Definition W_8f184 : bv 32 := 0xef010113.
Lemma F_8f184 : fetch_word AsanUbsan.M.loaded_segments (0x8f1d4 : word) = Some W_8f184.
Proof. vm_refl. Qed.
Lemma D_8f184 : decode_any W_8f184 = Some (OpImm ALU_ADD 2 2 3824, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f188 : bv 32 := 0x10113423.
Lemma F_8f188 : fetch_word AsanUbsan.M.loaded_segments (0x8f1d8 : word) = Some W_8f188.
Proof. vm_refl. Qed.
Lemma D_8f188 : decode_any W_8f188 = Some (Store SZ8 2 1 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f18c : bv 32 := 0x10813023.
Lemma F_8f18c : fetch_word AsanUbsan.M.loaded_segments (0x8f1dc : word) = Some W_8f18c.
Proof. vm_refl. Qed.
Lemma D_8f18c : decode_any W_8f18c = Some (Store SZ8 2 8 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f190 : bv 32 := 0x0e913c23.
Lemma F_8f190 : fetch_word AsanUbsan.M.loaded_segments (0x8f1e0 : word) = Some W_8f190.
Proof. vm_refl. Qed.
Lemma D_8f190 : decode_any W_8f190 = Some (Store SZ8 2 9 248, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f194 : bv 32 := 0x0f213823.
Lemma F_8f194 : fetch_word AsanUbsan.M.loaded_segments (0x8f1e4 : word) = Some W_8f194.
Proof. vm_refl. Qed.
Lemma D_8f194 : decode_any W_8f194 = Some (Store SZ8 2 18 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f198 : bv 32 := 0x0f313423.
Lemma F_8f198 : fetch_word AsanUbsan.M.loaded_segments (0x8f1e8 : word) = Some W_8f198.
Proof. vm_refl. Qed.
Lemma D_8f198 : decode_any W_8f198 = Some (Store SZ8 2 19 232, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f19c : bv 32 := 0x0f413023.
Lemma F_8f19c : fetch_word AsanUbsan.M.loaded_segments (0x8f1ec : word) = Some W_8f19c.
Proof. vm_refl. Qed.
Lemma D_8f19c : decode_any W_8f19c = Some (Store SZ8 2 20 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f1a0 : bv 32 := 0x0d513c23.
Lemma F_8f1a0 : fetch_word AsanUbsan.M.loaded_segments (0x8f1f0 : word) = Some W_8f1a0.
Proof. vm_refl. Qed.
Lemma D_8f1a0 : decode_any W_8f1a0 = Some (Store SZ8 2 21 216, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f1a4 : bv 32 := 0x00050913.
Lemma F_8f1a4 : fetch_word AsanUbsan.M.loaded_segments (0x8f1f4 : word) = Some W_8f1a4.
Proof. vm_refl. Qed.
Lemma D_8f1a4 : decode_any W_8f1a4 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f1a8 : bv 32 := 0xfff00513.
Lemma F_8f1a8 : fetch_word AsanUbsan.M.loaded_segments (0x8f1f8 : word) = Some W_8f1a8.
Proof. vm_refl. Qed.
Lemma D_8f1a8 : decode_any W_8f1a8 = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f1ac : bv 32 := 0x12090463.
Lemma F_8f1ac : fetch_word AsanUbsan.M.loaded_segments (0x8f1fc : word) = Some W_8f1ac.
Proof. vm_refl. Qed.
Lemma D_8f1ac : decode_any W_8f1ac = Some (Branch BC_EQ 18 0 296, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f1b0 : bv 32 := 0x00060413.
Lemma F_8f1b0 : fetch_word AsanUbsan.M.loaded_segments (0x8f200 : word) = Some W_8f1b0.
Proof. vm_refl. Qed.
Lemma D_8f1b0 : decode_any W_8f1b0 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f1b4 : bv 32 := 0x000ae617.
Lemma F_8f1b4 : fetch_word AsanUbsan.M.loaded_segments (0x8f204 : word) = Some W_8f1b4.
Proof. vm_refl. Qed.
Lemma D_8f1b4 : decode_any W_8f1b4 = Some (Auipc 12 174, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f1b8 : bv 32 := 0x6b463603.
Lemma F_8f1b8 : fetch_word AsanUbsan.M.loaded_segments (0x8f208 : word) = Some W_8f1b8.
Proof. vm_refl. Qed.
Lemma D_8f1b8 : decode_any W_8f1b8 = Some (Load SZ8 true 12 12 1716, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f1bc : bv 32 := 0x10464603.
Lemma F_8f1bc : fetch_word AsanUbsan.M.loaded_segments (0x8f20c : word) = Some W_8f1bc.
Proof. vm_refl. Qed.
Lemma D_8f1bc : decode_any W_8f1bc = Some (Load SZ1 false 12 12 260, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f1c0 : bv 32 := 0x00167613.
Lemma F_8f1c0 : fetch_word AsanUbsan.M.loaded_segments (0x8f210 : word) = Some W_8f1c0.
Proof. vm_refl. Qed.
Lemma D_8f1c0 : decode_any W_8f1c0 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f1c4 : bv 32 := 0x10060863.
Lemma F_8f1c4 : fetch_word AsanUbsan.M.loaded_segments (0x8f214 : word) = Some W_8f1c4.
Proof. vm_refl. Qed.
Lemma D_8f1c4 : decode_any W_8f1c4 = Some (Branch BC_EQ 12 0 272, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f2d4 : bv 32 := 0x0005051b.
Lemma F_8f2d4 : fetch_word AsanUbsan.M.loaded_segments (0x8f324 : word) = Some W_8f2d4.
Proof. vm_refl. Qed.
Lemma D_8f2d4 : decode_any W_8f2d4 = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f2d8 : bv 32 := 0x10813083.
Lemma F_8f2d8 : fetch_word AsanUbsan.M.loaded_segments (0x8f328 : word) = Some W_8f2d8.
Proof. vm_refl. Qed.
Lemma D_8f2d8 : decode_any W_8f2d8 = Some (Load SZ8 true 1 2 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f2dc : bv 32 := 0x10013403.
Lemma F_8f2dc : fetch_word AsanUbsan.M.loaded_segments (0x8f32c : word) = Some W_8f2dc.
Proof. vm_refl. Qed.
Lemma D_8f2dc : decode_any W_8f2dc = Some (Load SZ8 true 8 2 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f2e0 : bv 32 := 0x0f813483.
Lemma F_8f2e0 : fetch_word AsanUbsan.M.loaded_segments (0x8f330 : word) = Some W_8f2e0.
Proof. vm_refl. Qed.
Lemma D_8f2e0 : decode_any W_8f2e0 = Some (Load SZ8 true 9 2 248, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f2e4 : bv 32 := 0x0f013903.
Lemma F_8f2e4 : fetch_word AsanUbsan.M.loaded_segments (0x8f334 : word) = Some W_8f2e4.
Proof. vm_refl. Qed.
Lemma D_8f2e4 : decode_any W_8f2e4 = Some (Load SZ8 true 18 2 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f2e8 : bv 32 := 0x0e813983.
Lemma F_8f2e8 : fetch_word AsanUbsan.M.loaded_segments (0x8f338 : word) = Some W_8f2e8.
Proof. vm_refl. Qed.
Lemma D_8f2e8 : decode_any W_8f2e8 = Some (Load SZ8 true 19 2 232, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f2ec : bv 32 := 0x0e013a03.
Lemma F_8f2ec : fetch_word AsanUbsan.M.loaded_segments (0x8f33c : word) = Some W_8f2ec.
Proof. vm_refl. Qed.
Lemma D_8f2ec : decode_any W_8f2ec = Some (Load SZ8 true 20 2 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f2f0 : bv 32 := 0x0d813a83.
Lemma F_8f2f0 : fetch_word AsanUbsan.M.loaded_segments (0x8f340 : word) = Some W_8f2f0.
Proof. vm_refl. Qed.
Lemma D_8f2f0 : decode_any W_8f2f0 = Some (Load SZ8 true 21 2 216, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f2f4 : bv 32 := 0x11010113.
Lemma F_8f2f4 : fetch_word AsanUbsan.M.loaded_segments (0x8f344 : word) = Some W_8f2f4.
Proof. vm_refl. Qed.
Lemma D_8f2f4 : decode_any W_8f2f4 = Some (OpImm ALU_ADD 2 2 272, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f2f8 : bv 32 := 0x00008067.
Lemma F_8f2f8 : fetch_word AsanUbsan.M.loaded_segments (0x8f348 : word) = Some W_8f2f8.
Proof. vm_refl. Qed.
Lemma D_8f2f8 : decode_any W_8f2f8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
