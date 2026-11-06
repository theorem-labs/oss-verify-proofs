(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_7a148 : bv 32 := 0x0100006f.
Lemma F_7a148 : fetch_word Asan.M.loaded_segments (0x7a198 : word) = Some W_7a148.
Proof. vm_refl. Qed.
Lemma D_7a148 : decode_any W_7a148 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a14c : bv 32 := 0x1dc0006f.
Lemma F_7a14c : fetch_word Asan.M.loaded_segments (0x7a19c : word) = Some W_7a14c.
Proof. vm_refl. Qed.
Lemma D_7a14c : decode_any W_7a14c = Some (Jal 0 476, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a154 : bv 32 := 0x7400006f.
Lemma F_7a154 : fetch_word Asan.M.loaded_segments (0x7a1a4 : word) = Some W_7a154.
Proof. vm_refl. Qed.
Lemma D_7a154 : decode_any W_7a154 = Some (Jal 0 1856, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a158 : bv 32 := 0x81010113.
Lemma F_7a158 : fetch_word Asan.M.loaded_segments (0x7a1a8 : word) = Some W_7a158.
Proof. vm_refl. Qed.
Lemma D_7a158 : decode_any W_7a158 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a15c : bv 32 := 0x7e113423.
Lemma F_7a15c : fetch_word Asan.M.loaded_segments (0x7a1ac : word) = Some W_7a15c.
Proof. vm_refl. Qed.
Lemma D_7a15c : decode_any W_7a15c = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a160 : bv 32 := 0x7e813023.
Lemma F_7a160 : fetch_word Asan.M.loaded_segments (0x7a1b0 : word) = Some W_7a160.
Proof. vm_refl. Qed.
Lemma D_7a160 : decode_any W_7a160 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a164 : bv 32 := 0x7c913c23.
Lemma F_7a164 : fetch_word Asan.M.loaded_segments (0x7a1b4 : word) = Some W_7a164.
Proof. vm_refl. Qed.
Lemma D_7a164 : decode_any W_7a164 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a168 : bv 32 := 0x7d213823.
Lemma F_7a168 : fetch_word Asan.M.loaded_segments (0x7a1b8 : word) = Some W_7a168.
Proof. vm_refl. Qed.
Lemma D_7a168 : decode_any W_7a168 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a16c : bv 32 := 0x7d313423.
Lemma F_7a16c : fetch_word Asan.M.loaded_segments (0x7a1bc : word) = Some W_7a16c.
Proof. vm_refl. Qed.
Lemma D_7a16c : decode_any W_7a16c = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a170 : bv 32 := 0x7d413023.
Lemma F_7a170 : fetch_word Asan.M.loaded_segments (0x7a1c0 : word) = Some W_7a170.
Proof. vm_refl. Qed.
Lemma D_7a170 : decode_any W_7a170 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a174 : bv 32 := 0x7b513c23.
Lemma F_7a174 : fetch_word Asan.M.loaded_segments (0x7a1c4 : word) = Some W_7a174.
Proof. vm_refl. Qed.
Lemma D_7a174 : decode_any W_7a174 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a178 : bv 32 := 0x7f010413.
Lemma F_7a178 : fetch_word Asan.M.loaded_segments (0x7a1c8 : word) = Some W_7a178.
Proof. vm_refl. Qed.
Lemma D_7a178 : decode_any W_7a178 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a17c : bv 32 := 0xfa010113.
Lemma F_7a17c : fetch_word Asan.M.loaded_segments (0x7a1cc : word) = Some W_7a17c.
Proof. vm_refl. Qed.
Lemma D_7a17c : decode_any W_7a17c = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a180 : bv 32 := 0x00008913.
Lemma F_7a180 : fetch_word Asan.M.loaded_segments (0x7a1d0 : word) = Some W_7a180.
Proof. vm_refl. Qed.
Lemma D_7a180 : decode_any W_7a180 = Some (OpImm ALU_ADD 18 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a184 : bv 32 := 0x00050493.
Lemma F_7a184 : fetch_word Asan.M.loaded_segments (0x7a1d4 : word) = Some W_7a184.
Proof. vm_refl. Qed.
Lemma D_7a184 : decode_any W_7a184 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a188 : bv 32 := 0x10c0c0ef.
Lemma F_7a188 : fetch_word Asan.M.loaded_segments (0x7a1d8 : word) = Some W_7a188.
Proof. vm_refl. Qed.
Lemma D_7a188 : decode_any W_7a188 = Some (Jal 1 49420, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a18c : bv 32 := 0x02f4d593.
Lemma F_7a18c : fetch_word Asan.M.loaded_segments (0x7a1dc : word) = Some W_7a18c.
Proof. vm_refl. Qed.
Lemma D_7a18c : decode_any W_7a18c = Some (ShiftImm ALU_SRL 11 9 47, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a190 : bv 32 := 0x0a059063.
Lemma F_7a190 : fetch_word Asan.M.loaded_segments (0x7a1e0 : word) = Some W_7a190.
Proof. vm_refl. Qed.
Lemma D_7a190 : decode_any W_7a190 = Some (Branch BC_NE 11 0 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a194 : bv 32 := 0x0204d593.
Lemma F_7a194 : fetch_word Asan.M.loaded_segments (0x7a1e4 : word) = Some W_7a194.
Proof. vm_refl. Qed.
Lemma D_7a194 : decode_any W_7a194 = Some (ShiftImm ALU_SRL 11 9 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a198 : bv 32 := 0x00359613.
Lemma F_7a198 : fetch_word Asan.M.loaded_segments (0x7a1e8 : word) = Some W_7a198.
Proof. vm_refl. Qed.
Lemma D_7a198 : decode_any W_7a198 = Some (ShiftImm ALU_SLL 12 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a19c : bv 32 := 0x00c50633.
Lemma F_7a19c : fetch_word Asan.M.loaded_segments (0x7a1ec : word) = Some W_7a19c.
Proof. vm_refl. Qed.
Lemma D_7a19c : decode_any W_7a19c = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a1a0 : bv 32 := 0x00863683.
Lemma F_7a1a0 : fetch_word Asan.M.loaded_segments (0x7a1f0 : word) = Some W_7a1a0.
Proof. vm_refl. Qed.
Lemma D_7a1a0 : decode_any W_7a1a0 = Some (Load SZ8 true 13 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a1a4 : bv 32 := 0x0230000f.
Lemma F_7a1a4 : fetch_word Asan.M.loaded_segments (0x7a1f4 : word) = Some W_7a1a4.
Proof. vm_refl. Qed.
Lemma D_7a1a4 : decode_any W_7a1a4 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a1a8 : bv 32 := 0x08068463.
Lemma F_7a1a8 : fetch_word Asan.M.loaded_segments (0x7a1f8 : word) = Some W_7a1a8.
Proof. vm_refl. Qed.
Lemma D_7a1a8 : decode_any W_7a1a8 = Some (Branch BC_EQ 13 0 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a230 : bv 32 := 0x80040a13.
Lemma F_7a230 : fetch_word Asan.M.loaded_segments (0x7a280 : word) = Some W_7a230.
Proof. vm_refl. Qed.
Lemma D_7a230 : decode_any W_7a230 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a234 : bv 32 := 0xfb0a0a13.
Lemma F_7a234 : fetch_word Asan.M.loaded_segments (0x7a284 : word) = Some W_7a234.
Proof. vm_refl. Qed.
Lemma D_7a234 : decode_any W_7a234 = Some (OpImm ALU_ADD 20 20 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a238 : bv 32 := 0x80040513.
Lemma F_7a238 : fetch_word Asan.M.loaded_segments (0x7a288 : word) = Some W_7a238.
Proof. vm_refl. Qed.
Lemma D_7a238 : decode_any W_7a238 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a23c : bv 32 := 0xfc050513.
Lemma F_7a23c : fetch_word Asan.M.loaded_segments (0x7a28c : word) = Some W_7a23c.
Proof. vm_refl. Qed.
Lemma D_7a23c : decode_any W_7a23c = Some (OpImm ALU_ADD 10 10 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a240 : bv 32 := 0x7ffa0a93.
Lemma F_7a240 : fetch_word Asan.M.loaded_segments (0x7a290 : word) = Some W_7a240.
Proof. vm_refl. Qed.
Lemma D_7a240 : decode_any W_7a240 = Some (OpImm ALU_ADD 21 20 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a244 : bv 32 := 0x000ab4a3.
Lemma F_7a244 : fetch_word Asan.M.loaded_segments (0x7a294 : word) = Some W_7a244.
Proof. vm_refl. Qed.
Lemma D_7a244 : decode_any W_7a244 = Some (Store SZ8 21 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a248 : bv 32 := 0x00aa3023.
Lemma F_7a248 : fetch_word Asan.M.loaded_segments (0x7a298 : word) = Some W_7a248.
Proof. vm_refl. Qed.
Lemma D_7a248 : decode_any W_7a248 = Some (Store SZ8 20 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a24c : bv 32 := 0x000a3423.
Lemma F_7a24c : fetch_word Asan.M.loaded_segments (0x7a29c : word) = Some W_7a24c.
Proof. vm_refl. Qed.
Lemma D_7a24c : decode_any W_7a24c = Some (Store SZ8 20 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a250 : bv 32 := 0x550080ef.
Lemma F_7a250 : fetch_word Asan.M.loaded_segments (0x7a2a0 : word) = Some W_7a250.
Proof. vm_refl. Qed.
Lemma D_7a250 : decode_any W_7a250 = Some (Jal 1 34128, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a254 : bv 32 := 0x00200593.
Lemma F_7a254 : fetch_word Asan.M.loaded_segments (0x7a2a4 : word) = Some W_7a254.
Proof. vm_refl. Qed.
Lemma D_7a254 : decode_any W_7a254 = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a258 : bv 32 := 0x02a5ea63.
Lemma F_7a258 : fetch_word Asan.M.loaded_segments (0x7a2a8 : word) = Some W_7a258.
Proof. vm_refl. Qed.
Lemma D_7a258 : decode_any W_7a258 = Some (Branch BC_LTU 11 10 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a28c : bv 32 := 0x7f1200ef.
Lemma F_7a28c : fetch_word Asan.M.loaded_segments (0x7a2dc : word) = Some W_7a28c.
Proof. vm_refl. Qed.
Lemma D_7a28c : decode_any W_7a28c = Some (Jal 1 135152, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a290 : bv 32 := 0x000bf597.
Lemma F_7a290 : fetch_word Asan.M.loaded_segments (0x7a2e0 : word) = Some W_7a290.
Proof. vm_refl. Qed.
Lemma D_7a290 : decode_any W_7a290 = Some (Auipc 11 191, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a294 : bv 32 := 0xec85b583.
Lemma F_7a294 : fetch_word Asan.M.loaded_segments (0x7a2e4 : word) = Some W_7a294.
Proof. vm_refl. Qed.
Lemma D_7a294 : decode_any W_7a294 = Some (Load SZ8 true 11 11 3784, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a298 : bv 32 := 0x0225c983.
Lemma F_7a298 : fetch_word Asan.M.loaded_segments (0x7a2e8 : word) = Some W_7a298.
Proof. vm_refl. Qed.
Lemma D_7a298 : decode_any W_7a298 = Some (Load SZ1 false 19 11 34, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a29c : bv 32 := 0x00050913.
Lemma F_7a29c : fetch_word Asan.M.loaded_segments (0x7a2ec : word) = Some W_7a29c.
Proof. vm_refl. Qed.
Lemma D_7a29c : decode_any W_7a29c = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a2a0 : bv 32 := 0x500080ef.
Lemma F_7a2a0 : fetch_word Asan.M.loaded_segments (0x7a2f0 : word) = Some W_7a2a0.
Proof. vm_refl. Qed.
Lemma D_7a2a0 : decode_any W_7a2a0 = Some (Jal 1 34048, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a2a4 : bv 32 := 0x00050793.
Lemma F_7a2a4 : fetch_word Asan.M.loaded_segments (0x7a2f4 : word) = Some W_7a2a4.
Proof. vm_refl. Qed.
Lemma D_7a2a4 : decode_any W_7a2a4 = Some (OpImm ALU_ADD 15 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a2a8 : bv 32 := 0x00153513.
Lemma F_7a2a8 : fetch_word Asan.M.loaded_segments (0x7a2f8 : word) = Some W_7a2a8.
Proof. vm_refl. Qed.
Lemma D_7a2a8 : decode_any W_7a2a8 = Some (OpImm ALU_SLTU 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a2ac : bv 32 := 0xfff50513.
Lemma F_7a2ac : fetch_word Asan.M.loaded_segments (0x7a2fc : word) = Some W_7a2ac.
Proof. vm_refl. Qed.
Lemma D_7a2ac : decode_any W_7a2ac = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a2b0 : bv 32 := 0x008575b3.
Lemma F_7a2b0 : fetch_word Asan.M.loaded_segments (0x7a300 : word) = Some W_7a2b0.
Proof. vm_refl. Qed.
Lemma D_7a2b0 : decode_any W_7a2b0 = Some (Op ALU_AND 11 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a2b4 : bv 32 := 0x00100513.
Lemma F_7a2b4 : fetch_word Asan.M.loaded_segments (0x7a304 : word) = Some W_7a2b4.
Proof. vm_refl. Qed.
Lemma D_7a2b4 : decode_any W_7a2b4 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a2b8 : bv 32 := 0x00bab4a3.
Lemma F_7a2b8 : fetch_word Asan.M.loaded_segments (0x7a308 : word) = Some W_7a2b8.
Proof. vm_refl. Qed.
Lemma D_7a2b8 : decode_any W_7a2b8 = Some (Store SZ8 21 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a2bc : bv 32 := 0x00f56a63.
Lemma F_7a2bc : fetch_word Asan.M.loaded_segments (0x7a30c : word) = Some W_7a2bc.
Proof. vm_refl. Qed.
Lemma D_7a2bc : decode_any W_7a2bc = Some (Branch BC_LTU 10 15 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a2d0 : bv 32 := 0x80040513.
Lemma F_7a2d0 : fetch_word Asan.M.loaded_segments (0x7a320 : word) = Some W_7a2d0.
Proof. vm_refl. Qed.
Lemma D_7a2d0 : decode_any W_7a2d0 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a2d4 : bv 32 := 0xfb050513.
Lemma F_7a2d4 : fetch_word Asan.M.loaded_segments (0x7a324 : word) = Some W_7a2d4.
Proof. vm_refl. Qed.
Lemma D_7a2d4 : decode_any W_7a2d4 = Some (OpImm ALU_ADD 10 10 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a2d8 : bv 32 := 0x00090593.
Lemma F_7a2d8 : fetch_word Asan.M.loaded_segments (0x7a328 : word) = Some W_7a2d8.
Proof. vm_refl. Qed.
Lemma D_7a2d8 : decode_any W_7a2d8 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a2dc : bv 32 := 0x00040613.
Lemma F_7a2dc : fetch_word Asan.M.loaded_segments (0x7a32c : word) = Some W_7a2dc.
Proof. vm_refl. Qed.
Lemma D_7a2dc : decode_any W_7a2dc = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a2e0 : bv 32 := 0x00000693.
Lemma F_7a2e0 : fetch_word Asan.M.loaded_segments (0x7a330 : word) = Some W_7a2e0.
Proof. vm_refl. Qed.
Lemma D_7a2e0 : decode_any W_7a2e0 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a2e4 : bv 32 := 0x00098713.
Lemma F_7a2e4 : fetch_word Asan.M.loaded_segments (0x7a334 : word) = Some W_7a2e4.
Proof. vm_refl. Qed.
Lemma D_7a2e4 : decode_any W_7a2e4 = Some (OpImm ALU_ADD 14 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a2e8 : bv 32 := 0x4c8080ef.
Lemma F_7a2e8 : fetch_word Asan.M.loaded_segments (0x7a338 : word) = Some W_7a2e8.
Proof. vm_refl. Qed.
Lemma D_7a2e8 : decode_any W_7a2e8 = Some (Jal 1 33992, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a2ec : bv 32 := 0x80040593.
Lemma F_7a2ec : fetch_word Asan.M.loaded_segments (0x7a33c : word) = Some W_7a2ec.
Proof. vm_refl. Qed.
Lemma D_7a2ec : decode_any W_7a2ec = Some (OpImm ALU_ADD 11 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a2f0 : bv 32 := 0xfb058593.
Lemma F_7a2f0 : fetch_word Asan.M.loaded_segments (0x7a340 : word) = Some W_7a2f0.
Proof. vm_refl. Qed.
Lemma D_7a2f0 : decode_any W_7a2f0 = Some (OpImm ALU_ADD 11 11 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a2f4 : bv 32 := 0x00100613.
Lemma F_7a2f4 : fetch_word Asan.M.loaded_segments (0x7a344 : word) = Some W_7a2f4.
Proof. vm_refl. Qed.
Lemma D_7a2f4 : decode_any W_7a2f4 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a2f8 : bv 32 := 0x00048513.
Lemma F_7a2f8 : fetch_word Asan.M.loaded_segments (0x7a348 : word) = Some W_7a2f8.
Proof. vm_refl. Qed.
Lemma D_7a2f8 : decode_any W_7a2f8 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a2fc : bv 32 := 0xf44d80ef.
Lemma F_7a2fc : fetch_word Asan.M.loaded_segments (0x7a34c : word) = Some W_7a2fc.
Proof. vm_refl. Qed.
Lemma D_7a2fc : decode_any W_7a2fc = Some (Jal 1 1935172, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a300 : bv 32 := 0x06010113.
Lemma F_7a300 : fetch_word Asan.M.loaded_segments (0x7a350 : word) = Some W_7a300.
Proof. vm_refl. Qed.
Lemma D_7a300 : decode_any W_7a300 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a304 : bv 32 := 0x7e813083.
Lemma F_7a304 : fetch_word Asan.M.loaded_segments (0x7a354 : word) = Some W_7a304.
Proof. vm_refl. Qed.
Lemma D_7a304 : decode_any W_7a304 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a308 : bv 32 := 0x7e013403.
Lemma F_7a308 : fetch_word Asan.M.loaded_segments (0x7a358 : word) = Some W_7a308.
Proof. vm_refl. Qed.
Lemma D_7a308 : decode_any W_7a308 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a30c : bv 32 := 0x7d813483.
Lemma F_7a30c : fetch_word Asan.M.loaded_segments (0x7a35c : word) = Some W_7a30c.
Proof. vm_refl. Qed.
Lemma D_7a30c : decode_any W_7a30c = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a310 : bv 32 := 0x7d013903.
Lemma F_7a310 : fetch_word Asan.M.loaded_segments (0x7a360 : word) = Some W_7a310.
Proof. vm_refl. Qed.
Lemma D_7a310 : decode_any W_7a310 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a314 : bv 32 := 0x7c813983.
Lemma F_7a314 : fetch_word Asan.M.loaded_segments (0x7a364 : word) = Some W_7a314.
Proof. vm_refl. Qed.
Lemma D_7a314 : decode_any W_7a314 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a318 : bv 32 := 0x7c013a03.
Lemma F_7a318 : fetch_word Asan.M.loaded_segments (0x7a368 : word) = Some W_7a318.
Proof. vm_refl. Qed.
Lemma D_7a318 : decode_any W_7a318 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a31c : bv 32 := 0x7b813a83.
Lemma F_7a31c : fetch_word Asan.M.loaded_segments (0x7a36c : word) = Some W_7a31c.
Proof. vm_refl. Qed.
Lemma D_7a31c : decode_any W_7a31c = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a320 : bv 32 := 0x7f010113.
Lemma F_7a320 : fetch_word Asan.M.loaded_segments (0x7a370 : word) = Some W_7a320.
Proof. vm_refl. Qed.
Lemma D_7a320 : decode_any W_7a320 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a324 : bv 32 := 0x00008067.
Lemma F_7a324 : fetch_word Asan.M.loaded_segments (0x7a374 : word) = Some W_7a324.
Proof. vm_refl. Qed.
Lemma D_7a324 : decode_any W_7a324 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a328 : bv 32 := 0x81010113.
Lemma F_7a328 : fetch_word Asan.M.loaded_segments (0x7a378 : word) = Some W_7a328.
Proof. vm_refl. Qed.
Lemma D_7a328 : decode_any W_7a328 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a32c : bv 32 := 0x7e113423.
Lemma F_7a32c : fetch_word Asan.M.loaded_segments (0x7a37c : word) = Some W_7a32c.
Proof. vm_refl. Qed.
Lemma D_7a32c : decode_any W_7a32c = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a330 : bv 32 := 0x7e813023.
Lemma F_7a330 : fetch_word Asan.M.loaded_segments (0x7a380 : word) = Some W_7a330.
Proof. vm_refl. Qed.
Lemma D_7a330 : decode_any W_7a330 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a334 : bv 32 := 0x7c913c23.
Lemma F_7a334 : fetch_word Asan.M.loaded_segments (0x7a384 : word) = Some W_7a334.
Proof. vm_refl. Qed.
Lemma D_7a334 : decode_any W_7a334 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a338 : bv 32 := 0x7d213823.
Lemma F_7a338 : fetch_word Asan.M.loaded_segments (0x7a388 : word) = Some W_7a338.
Proof. vm_refl. Qed.
Lemma D_7a338 : decode_any W_7a338 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a33c : bv 32 := 0x7d313423.
Lemma F_7a33c : fetch_word Asan.M.loaded_segments (0x7a38c : word) = Some W_7a33c.
Proof. vm_refl. Qed.
Lemma D_7a33c : decode_any W_7a33c = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a340 : bv 32 := 0x7d413023.
Lemma F_7a340 : fetch_word Asan.M.loaded_segments (0x7a390 : word) = Some W_7a340.
Proof. vm_refl. Qed.
Lemma D_7a340 : decode_any W_7a340 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a344 : bv 32 := 0x7b513c23.
Lemma F_7a344 : fetch_word Asan.M.loaded_segments (0x7a394 : word) = Some W_7a344.
Proof. vm_refl. Qed.
Lemma D_7a344 : decode_any W_7a344 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a348 : bv 32 := 0x7f010413.
Lemma F_7a348 : fetch_word Asan.M.loaded_segments (0x7a398 : word) = Some W_7a348.
Proof. vm_refl. Qed.
Lemma D_7a348 : decode_any W_7a348 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a34c : bv 32 := 0xfa010113.
Lemma F_7a34c : fetch_word Asan.M.loaded_segments (0x7a39c : word) = Some W_7a34c.
Proof. vm_refl. Qed.
Lemma D_7a34c : decode_any W_7a34c = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a350 : bv 32 := 0x00008913.
Lemma F_7a350 : fetch_word Asan.M.loaded_segments (0x7a3a0 : word) = Some W_7a350.
Proof. vm_refl. Qed.
Lemma D_7a350 : decode_any W_7a350 = Some (OpImm ALU_ADD 18 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a354 : bv 32 := 0x00050493.
Lemma F_7a354 : fetch_word Asan.M.loaded_segments (0x7a3a4 : word) = Some W_7a354.
Proof. vm_refl. Qed.
Lemma D_7a354 : decode_any W_7a354 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a358 : bv 32 := 0x6c0070ef.
Lemma F_7a358 : fetch_word Asan.M.loaded_segments (0x7a3a8 : word) = Some W_7a358.
Proof. vm_refl. Qed.
Lemma D_7a358 : decode_any W_7a358 = Some (Jal 1 30400, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a35c : bv 32 := 0x06050063.
Lemma F_7a35c : fetch_word Asan.M.loaded_segments (0x7a3ac : word) = Some W_7a35c.
Proof. vm_refl. Qed.
Lemma D_7a35c : decode_any W_7a35c = Some (Branch BC_EQ 10 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a360 : bv 32 := 0x80040a13.
Lemma F_7a360 : fetch_word Asan.M.loaded_segments (0x7a3b0 : word) = Some W_7a360.
Proof. vm_refl. Qed.
Lemma D_7a360 : decode_any W_7a360 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a364 : bv 32 := 0xfb0a0a13.
Lemma F_7a364 : fetch_word Asan.M.loaded_segments (0x7a3b4 : word) = Some W_7a364.
Proof. vm_refl. Qed.
Lemma D_7a364 : decode_any W_7a364 = Some (OpImm ALU_ADD 20 20 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a368 : bv 32 := 0x80040513.
Lemma F_7a368 : fetch_word Asan.M.loaded_segments (0x7a3b8 : word) = Some W_7a368.
Proof. vm_refl. Qed.
Lemma D_7a368 : decode_any W_7a368 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a36c : bv 32 := 0xfc050513.
Lemma F_7a36c : fetch_word Asan.M.loaded_segments (0x7a3bc : word) = Some W_7a36c.
Proof. vm_refl. Qed.
Lemma D_7a36c : decode_any W_7a36c = Some (OpImm ALU_ADD 10 10 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a370 : bv 32 := 0x7ffa0a93.
Lemma F_7a370 : fetch_word Asan.M.loaded_segments (0x7a3c0 : word) = Some W_7a370.
Proof. vm_refl. Qed.
Lemma D_7a370 : decode_any W_7a370 = Some (OpImm ALU_ADD 21 20 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a374 : bv 32 := 0x000ab4a3.
Lemma F_7a374 : fetch_word Asan.M.loaded_segments (0x7a3c4 : word) = Some W_7a374.
Proof. vm_refl. Qed.
Lemma D_7a374 : decode_any W_7a374 = Some (Store SZ8 21 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a378 : bv 32 := 0x00aa3023.
Lemma F_7a378 : fetch_word Asan.M.loaded_segments (0x7a3c8 : word) = Some W_7a378.
Proof. vm_refl. Qed.
Lemma D_7a378 : decode_any W_7a378 = Some (Store SZ8 20 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a37c : bv 32 := 0x000a3423.
Lemma F_7a37c : fetch_word Asan.M.loaded_segments (0x7a3cc : word) = Some W_7a37c.
Proof. vm_refl. Qed.
Lemma D_7a37c : decode_any W_7a37c = Some (Store SZ8 20 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a380 : bv 32 := 0x420080ef.
Lemma F_7a380 : fetch_word Asan.M.loaded_segments (0x7a3d0 : word) = Some W_7a380.
Proof. vm_refl. Qed.
Lemma D_7a380 : decode_any W_7a380 = Some (Jal 1 33824, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a384 : bv 32 := 0x00200593.
Lemma F_7a384 : fetch_word Asan.M.loaded_segments (0x7a3d4 : word) = Some W_7a384.
Proof. vm_refl. Qed.
Lemma D_7a384 : decode_any W_7a384 = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a388 : bv 32 := 0x06a5e263.
Lemma F_7a388 : fetch_word Asan.M.loaded_segments (0x7a3d8 : word) = Some W_7a388.
Proof. vm_refl. Qed.
Lemma D_7a388 : decode_any W_7a388 = Some (Branch BC_LTU 11 10 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a3ec : bv 32 := 0x691200ef.
Lemma F_7a3ec : fetch_word Asan.M.loaded_segments (0x7a43c : word) = Some W_7a3ec.
Proof. vm_refl. Qed.
Lemma D_7a3ec : decode_any W_7a3ec = Some (Jal 1 134800, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a3f0 : bv 32 := 0x000bf597.
Lemma F_7a3f0 : fetch_word Asan.M.loaded_segments (0x7a440 : word) = Some W_7a3f0.
Proof. vm_refl. Qed.
Lemma D_7a3f0 : decode_any W_7a3f0 = Some (Auipc 11 191, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a3f4 : bv 32 := 0xd685b583.
Lemma F_7a3f4 : fetch_word Asan.M.loaded_segments (0x7a444 : word) = Some W_7a3f4.
Proof. vm_refl. Qed.
Lemma D_7a3f4 : decode_any W_7a3f4 = Some (Load SZ8 true 11 11 3432, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a3f8 : bv 32 := 0x0225c983.
Lemma F_7a3f8 : fetch_word Asan.M.loaded_segments (0x7a448 : word) = Some W_7a3f8.
Proof. vm_refl. Qed.
Lemma D_7a3f8 : decode_any W_7a3f8 = Some (Load SZ1 false 19 11 34, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a3fc : bv 32 := 0x00050913.
Lemma F_7a3fc : fetch_word Asan.M.loaded_segments (0x7a44c : word) = Some W_7a3fc.
Proof. vm_refl. Qed.
Lemma D_7a3fc : decode_any W_7a3fc = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a400 : bv 32 := 0x3a0080ef.
Lemma F_7a400 : fetch_word Asan.M.loaded_segments (0x7a450 : word) = Some W_7a400.
Proof. vm_refl. Qed.
Lemma D_7a400 : decode_any W_7a400 = Some (Jal 1 33696, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a404 : bv 32 := 0x00050793.
Lemma F_7a404 : fetch_word Asan.M.loaded_segments (0x7a454 : word) = Some W_7a404.
Proof. vm_refl. Qed.
Lemma D_7a404 : decode_any W_7a404 = Some (OpImm ALU_ADD 15 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a408 : bv 32 := 0x00153513.
Lemma F_7a408 : fetch_word Asan.M.loaded_segments (0x7a458 : word) = Some W_7a408.
Proof. vm_refl. Qed.
Lemma D_7a408 : decode_any W_7a408 = Some (OpImm ALU_SLTU 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a40c : bv 32 := 0xfff50513.
Lemma F_7a40c : fetch_word Asan.M.loaded_segments (0x7a45c : word) = Some W_7a40c.
Proof. vm_refl. Qed.
Lemma D_7a40c : decode_any W_7a40c = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a410 : bv 32 := 0x008575b3.
Lemma F_7a410 : fetch_word Asan.M.loaded_segments (0x7a460 : word) = Some W_7a410.
Proof. vm_refl. Qed.
Lemma D_7a410 : decode_any W_7a410 = Some (Op ALU_AND 11 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a414 : bv 32 := 0x00100513.
Lemma F_7a414 : fetch_word Asan.M.loaded_segments (0x7a464 : word) = Some W_7a414.
Proof. vm_refl. Qed.
Lemma D_7a414 : decode_any W_7a414 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a418 : bv 32 := 0x00bab4a3.
Lemma F_7a418 : fetch_word Asan.M.loaded_segments (0x7a468 : word) = Some W_7a418.
Proof. vm_refl. Qed.
Lemma D_7a418 : decode_any W_7a418 = Some (Store SZ8 21 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a41c : bv 32 := 0x00f56a63.
Lemma F_7a41c : fetch_word Asan.M.loaded_segments (0x7a46c : word) = Some W_7a41c.
Proof. vm_refl. Qed.
Lemma D_7a41c : decode_any W_7a41c = Some (Branch BC_LTU 10 15 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a430 : bv 32 := 0x80040513.
Lemma F_7a430 : fetch_word Asan.M.loaded_segments (0x7a480 : word) = Some W_7a430.
Proof. vm_refl. Qed.
Lemma D_7a430 : decode_any W_7a430 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a434 : bv 32 := 0xfb050513.
Lemma F_7a434 : fetch_word Asan.M.loaded_segments (0x7a484 : word) = Some W_7a434.
Proof. vm_refl. Qed.
Lemma D_7a434 : decode_any W_7a434 = Some (OpImm ALU_ADD 10 10 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a438 : bv 32 := 0x00090593.
Lemma F_7a438 : fetch_word Asan.M.loaded_segments (0x7a488 : word) = Some W_7a438.
Proof. vm_refl. Qed.
Lemma D_7a438 : decode_any W_7a438 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a43c : bv 32 := 0x00040613.
Lemma F_7a43c : fetch_word Asan.M.loaded_segments (0x7a48c : word) = Some W_7a43c.
Proof. vm_refl. Qed.
Lemma D_7a43c : decode_any W_7a43c = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a440 : bv 32 := 0x00000693.
Lemma F_7a440 : fetch_word Asan.M.loaded_segments (0x7a490 : word) = Some W_7a440.
Proof. vm_refl. Qed.
Lemma D_7a440 : decode_any W_7a440 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a444 : bv 32 := 0x00098713.
Lemma F_7a444 : fetch_word Asan.M.loaded_segments (0x7a494 : word) = Some W_7a444.
Proof. vm_refl. Qed.
Lemma D_7a444 : decode_any W_7a444 = Some (OpImm ALU_ADD 14 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a448 : bv 32 := 0x368080ef.
Lemma F_7a448 : fetch_word Asan.M.loaded_segments (0x7a498 : word) = Some W_7a448.
Proof. vm_refl. Qed.
Lemma D_7a448 : decode_any W_7a448 = Some (Jal 1 33640, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a44c : bv 32 := 0x80040593.
Lemma F_7a44c : fetch_word Asan.M.loaded_segments (0x7a49c : word) = Some W_7a44c.
Proof. vm_refl. Qed.
Lemma D_7a44c : decode_any W_7a44c = Some (OpImm ALU_ADD 11 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a450 : bv 32 := 0xfb058593.
Lemma F_7a450 : fetch_word Asan.M.loaded_segments (0x7a4a0 : word) = Some W_7a450.
Proof. vm_refl. Qed.
Lemma D_7a450 : decode_any W_7a450 = Some (OpImm ALU_ADD 11 11 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a454 : bv 32 := 0x00048513.
Lemma F_7a454 : fetch_word Asan.M.loaded_segments (0x7a4a4 : word) = Some W_7a454.
Proof. vm_refl. Qed.
Lemma D_7a454 : decode_any W_7a454 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a458 : bv 32 := 0x8c9d80ef.
Lemma F_7a458 : fetch_word Asan.M.loaded_segments (0x7a4a8 : word) = Some W_7a458.
Proof. vm_refl. Qed.
Lemma D_7a458 : decode_any W_7a458 = Some (Jal 1 1935560, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a45c : bv 32 := 0x06010113.
Lemma F_7a45c : fetch_word Asan.M.loaded_segments (0x7a4ac : word) = Some W_7a45c.
Proof. vm_refl. Qed.
Lemma D_7a45c : decode_any W_7a45c = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a460 : bv 32 := 0x7e813083.
Lemma F_7a460 : fetch_word Asan.M.loaded_segments (0x7a4b0 : word) = Some W_7a460.
Proof. vm_refl. Qed.
Lemma D_7a460 : decode_any W_7a460 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a464 : bv 32 := 0x7e013403.
Lemma F_7a464 : fetch_word Asan.M.loaded_segments (0x7a4b4 : word) = Some W_7a464.
Proof. vm_refl. Qed.
Lemma D_7a464 : decode_any W_7a464 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a468 : bv 32 := 0x7d813483.
Lemma F_7a468 : fetch_word Asan.M.loaded_segments (0x7a4b8 : word) = Some W_7a468.
Proof. vm_refl. Qed.
Lemma D_7a468 : decode_any W_7a468 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a46c : bv 32 := 0x7d013903.
Lemma F_7a46c : fetch_word Asan.M.loaded_segments (0x7a4bc : word) = Some W_7a46c.
Proof. vm_refl. Qed.
Lemma D_7a46c : decode_any W_7a46c = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a470 : bv 32 := 0x7c813983.
Lemma F_7a470 : fetch_word Asan.M.loaded_segments (0x7a4c0 : word) = Some W_7a470.
Proof. vm_refl. Qed.
Lemma D_7a470 : decode_any W_7a470 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a474 : bv 32 := 0x7c013a03.
Lemma F_7a474 : fetch_word Asan.M.loaded_segments (0x7a4c4 : word) = Some W_7a474.
Proof. vm_refl. Qed.
Lemma D_7a474 : decode_any W_7a474 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a478 : bv 32 := 0x7b813a83.
Lemma F_7a478 : fetch_word Asan.M.loaded_segments (0x7a4c8 : word) = Some W_7a478.
Proof. vm_refl. Qed.
Lemma D_7a478 : decode_any W_7a478 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a47c : bv 32 := 0x7f010113.
Lemma F_7a47c : fetch_word Asan.M.loaded_segments (0x7a4cc : word) = Some W_7a47c.
Proof. vm_refl. Qed.
Lemma D_7a47c : decode_any W_7a47c = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a480 : bv 32 := 0x00008067.
Lemma F_7a480 : fetch_word Asan.M.loaded_segments (0x7a4d0 : word) = Some W_7a480.
Proof. vm_refl. Qed.
Lemma D_7a480 : decode_any W_7a480 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a894 : bv 32 := 0x81010113.
Lemma F_7a894 : fetch_word Asan.M.loaded_segments (0x7a8e4 : word) = Some W_7a894.
Proof. vm_refl. Qed.
Lemma D_7a894 : decode_any W_7a894 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a898 : bv 32 := 0x7e113423.
Lemma F_7a898 : fetch_word Asan.M.loaded_segments (0x7a8e8 : word) = Some W_7a898.
Proof. vm_refl. Qed.
Lemma D_7a898 : decode_any W_7a898 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a89c : bv 32 := 0x7e813023.
Lemma F_7a89c : fetch_word Asan.M.loaded_segments (0x7a8ec : word) = Some W_7a89c.
Proof. vm_refl. Qed.
Lemma D_7a89c : decode_any W_7a89c = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a8a0 : bv 32 := 0x7c913c23.
Lemma F_7a8a0 : fetch_word Asan.M.loaded_segments (0x7a8f0 : word) = Some W_7a8a0.
Proof. vm_refl. Qed.
Lemma D_7a8a0 : decode_any W_7a8a0 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a8a4 : bv 32 := 0x7d213823.
Lemma F_7a8a4 : fetch_word Asan.M.loaded_segments (0x7a8f4 : word) = Some W_7a8a4.
Proof. vm_refl. Qed.
Lemma D_7a8a4 : decode_any W_7a8a4 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a8a8 : bv 32 := 0x7d313423.
Lemma F_7a8a8 : fetch_word Asan.M.loaded_segments (0x7a8f8 : word) = Some W_7a8a8.
Proof. vm_refl. Qed.
Lemma D_7a8a8 : decode_any W_7a8a8 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a8ac : bv 32 := 0x7d413023.
Lemma F_7a8ac : fetch_word Asan.M.loaded_segments (0x7a8fc : word) = Some W_7a8ac.
Proof. vm_refl. Qed.
Lemma D_7a8ac : decode_any W_7a8ac = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a8b0 : bv 32 := 0x7b513c23.
Lemma F_7a8b0 : fetch_word Asan.M.loaded_segments (0x7a900 : word) = Some W_7a8b0.
Proof. vm_refl. Qed.
Lemma D_7a8b0 : decode_any W_7a8b0 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a8b4 : bv 32 := 0x7b613823.
Lemma F_7a8b4 : fetch_word Asan.M.loaded_segments (0x7a904 : word) = Some W_7a8b4.
Proof. vm_refl. Qed.
Lemma D_7a8b4 : decode_any W_7a8b4 = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a8b8 : bv 32 := 0x7f010413.
Lemma F_7a8b8 : fetch_word Asan.M.loaded_segments (0x7a908 : word) = Some W_7a8b8.
Proof. vm_refl. Qed.
Lemma D_7a8b8 : decode_any W_7a8b8 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a8bc : bv 32 := 0xf9010113.
Lemma F_7a8bc : fetch_word Asan.M.loaded_segments (0x7a90c : word) = Some W_7a8bc.
Proof. vm_refl. Qed.
Lemma D_7a8bc : decode_any W_7a8bc = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a8c0 : bv 32 := 0x00008993.
Lemma F_7a8c0 : fetch_word Asan.M.loaded_segments (0x7a910 : word) = Some W_7a8c0.
Proof. vm_refl. Qed.
Lemma D_7a8c0 : decode_any W_7a8c0 = Some (OpImm ALU_ADD 19 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a8c4 : bv 32 := 0x00058493.
Lemma F_7a8c4 : fetch_word Asan.M.loaded_segments (0x7a914 : word) = Some W_7a8c4.
Proof. vm_refl. Qed.
Lemma D_7a8c4 : decode_any W_7a8c4 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a8c8 : bv 32 := 0x00050913.
Lemma F_7a8c8 : fetch_word Asan.M.loaded_segments (0x7a918 : word) = Some W_7a8c8.
Proof. vm_refl. Qed.
Lemma D_7a8c8 : decode_any W_7a8c8 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a8cc : bv 32 := 0x80040a93.
Lemma F_7a8cc : fetch_word Asan.M.loaded_segments (0x7a91c : word) = Some W_7a8cc.
Proof. vm_refl. Qed.
Lemma D_7a8cc : decode_any W_7a8cc = Some (OpImm ALU_ADD 21 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a8d0 : bv 32 := 0xfa8a8a93.
Lemma F_7a8d0 : fetch_word Asan.M.loaded_segments (0x7a920 : word) = Some W_7a8d0.
Proof. vm_refl. Qed.
Lemma D_7a8d0 : decode_any W_7a8d0 = Some (OpImm ALU_ADD 21 21 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a8d4 : bv 32 := 0x80040513.
Lemma F_7a8d4 : fetch_word Asan.M.loaded_segments (0x7a924 : word) = Some W_7a8d4.
Proof. vm_refl. Qed.
Lemma D_7a8d4 : decode_any W_7a8d4 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a8d8 : bv 32 := 0xfb850513.
Lemma F_7a8d8 : fetch_word Asan.M.loaded_segments (0x7a928 : word) = Some W_7a8d8.
Proof. vm_refl. Qed.
Lemma D_7a8d8 : decode_any W_7a8d8 = Some (OpImm ALU_ADD 10 10 4024, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a8dc : bv 32 := 0x7ffa8b13.
Lemma F_7a8dc : fetch_word Asan.M.loaded_segments (0x7a92c : word) = Some W_7a8dc.
Proof. vm_refl. Qed.
Lemma D_7a8dc : decode_any W_7a8dc = Some (OpImm ALU_ADD 22 21 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a8e0 : bv 32 := 0x000b34a3.
Lemma F_7a8e0 : fetch_word Asan.M.loaded_segments (0x7a930 : word) = Some W_7a8e0.
Proof. vm_refl. Qed.
Lemma D_7a8e0 : decode_any W_7a8e0 = Some (Store SZ8 22 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a8e4 : bv 32 := 0x00aab023.
Lemma F_7a8e4 : fetch_word Asan.M.loaded_segments (0x7a934 : word) = Some W_7a8e4.
Proof. vm_refl. Qed.
Lemma D_7a8e4 : decode_any W_7a8e4 = Some (Store SZ8 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a8e8 : bv 32 := 0x000ab423.
Lemma F_7a8e8 : fetch_word Asan.M.loaded_segments (0x7a938 : word) = Some W_7a8e8.
Proof. vm_refl. Qed.
Lemma D_7a8e8 : decode_any W_7a8e8 = Some (Store SZ8 21 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a8ec : bv 32 := 0x6b5070ef.
Lemma F_7a8ec : fetch_word Asan.M.loaded_segments (0x7a93c : word) = Some W_7a8ec.
Proof. vm_refl. Qed.
Lemma D_7a8ec : decode_any W_7a8ec = Some (Jal 1 32436, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a8f0 : bv 32 := 0x00200593.
Lemma F_7a8f0 : fetch_word Asan.M.loaded_segments (0x7a940 : word) = Some W_7a8f0.
Proof. vm_refl. Qed.
Lemma D_7a8f0 : decode_any W_7a8f0 = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a8f4 : bv 32 := 0x02a5ea63.
Lemma F_7a8f4 : fetch_word Asan.M.loaded_segments (0x7a944 : word) = Some W_7a8f4.
Proof. vm_refl. Qed.
Lemma D_7a8f4 : decode_any W_7a8f4 = Some (Branch BC_LTU 11 10 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a928 : bv 32 := 0x155200ef.
Lemma F_7a928 : fetch_word Asan.M.loaded_segments (0x7a978 : word) = Some W_7a928.
Proof. vm_refl. Qed.
Lemma D_7a928 : decode_any W_7a928 = Some (Jal 1 133460, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a92c : bv 32 := 0x000bf597.
Lemma F_7a92c : fetch_word Asan.M.loaded_segments (0x7a97c : word) = Some W_7a92c.
Proof. vm_refl. Qed.
Lemma D_7a92c : decode_any W_7a92c = Some (Auipc 11 191, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a930 : bv 32 := 0x82c5b583.
Lemma F_7a930 : fetch_word Asan.M.loaded_segments (0x7a980 : word) = Some W_7a930.
Proof. vm_refl. Qed.
Lemma D_7a930 : decode_any W_7a930 = Some (Load SZ8 true 11 11 2092, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a934 : bv 32 := 0x0225ca03.
Lemma F_7a934 : fetch_word Asan.M.loaded_segments (0x7a984 : word) = Some W_7a934.
Proof. vm_refl. Qed.
Lemma D_7a934 : decode_any W_7a934 = Some (Load SZ1 false 20 11 34, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a938 : bv 32 := 0x00050993.
Lemma F_7a938 : fetch_word Asan.M.loaded_segments (0x7a988 : word) = Some W_7a938.
Proof. vm_refl. Qed.
Lemma D_7a938 : decode_any W_7a938 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a93c : bv 32 := 0x665070ef.
Lemma F_7a93c : fetch_word Asan.M.loaded_segments (0x7a98c : word) = Some W_7a93c.
Proof. vm_refl. Qed.
Lemma D_7a93c : decode_any W_7a93c = Some (Jal 1 32356, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a940 : bv 32 := 0x00050793.
Lemma F_7a940 : fetch_word Asan.M.loaded_segments (0x7a990 : word) = Some W_7a940.
Proof. vm_refl. Qed.
Lemma D_7a940 : decode_any W_7a940 = Some (OpImm ALU_ADD 15 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a944 : bv 32 := 0x00153513.
Lemma F_7a944 : fetch_word Asan.M.loaded_segments (0x7a994 : word) = Some W_7a944.
Proof. vm_refl. Qed.
Lemma D_7a944 : decode_any W_7a944 = Some (OpImm ALU_SLTU 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a948 : bv 32 := 0xfff50513.
Lemma F_7a948 : fetch_word Asan.M.loaded_segments (0x7a998 : word) = Some W_7a948.
Proof. vm_refl. Qed.
Lemma D_7a948 : decode_any W_7a948 = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a94c : bv 32 := 0x008575b3.
Lemma F_7a94c : fetch_word Asan.M.loaded_segments (0x7a99c : word) = Some W_7a94c.
Proof. vm_refl. Qed.
Lemma D_7a94c : decode_any W_7a94c = Some (Op ALU_AND 11 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a950 : bv 32 := 0x00100513.
Lemma F_7a950 : fetch_word Asan.M.loaded_segments (0x7a9a0 : word) = Some W_7a950.
Proof. vm_refl. Qed.
Lemma D_7a950 : decode_any W_7a950 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a954 : bv 32 := 0x00bb34a3.
Lemma F_7a954 : fetch_word Asan.M.loaded_segments (0x7a9a4 : word) = Some W_7a954.
Proof. vm_refl. Qed.
Lemma D_7a954 : decode_any W_7a954 = Some (Store SZ8 22 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a958 : bv 32 := 0x00f56a63.
Lemma F_7a958 : fetch_word Asan.M.loaded_segments (0x7a9a8 : word) = Some W_7a958.
Proof. vm_refl. Qed.
Lemma D_7a958 : decode_any W_7a958 = Some (Branch BC_LTU 10 15 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a96c : bv 32 := 0x80040513.
Lemma F_7a96c : fetch_word Asan.M.loaded_segments (0x7a9bc : word) = Some W_7a96c.
Proof. vm_refl. Qed.
Lemma D_7a96c : decode_any W_7a96c = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a970 : bv 32 := 0xfa850513.
Lemma F_7a970 : fetch_word Asan.M.loaded_segments (0x7a9c0 : word) = Some W_7a970.
Proof. vm_refl. Qed.
Lemma D_7a970 : decode_any W_7a970 = Some (OpImm ALU_ADD 10 10 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a974 : bv 32 := 0x00098593.
Lemma F_7a974 : fetch_word Asan.M.loaded_segments (0x7a9c4 : word) = Some W_7a974.
Proof. vm_refl. Qed.
Lemma D_7a974 : decode_any W_7a974 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a978 : bv 32 := 0x00040613.
Lemma F_7a978 : fetch_word Asan.M.loaded_segments (0x7a9c8 : word) = Some W_7a978.
Proof. vm_refl. Qed.
Lemma D_7a978 : decode_any W_7a978 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a97c : bv 32 := 0x00000693.
Lemma F_7a97c : fetch_word Asan.M.loaded_segments (0x7a9cc : word) = Some W_7a97c.
Proof. vm_refl. Qed.
Lemma D_7a97c : decode_any W_7a97c = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a980 : bv 32 := 0x000a0713.
Lemma F_7a980 : fetch_word Asan.M.loaded_segments (0x7a9d0 : word) = Some W_7a980.
Proof. vm_refl. Qed.
Lemma D_7a980 : decode_any W_7a980 = Some (OpImm ALU_ADD 14 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a984 : bv 32 := 0x62d070ef.
Lemma F_7a984 : fetch_word Asan.M.loaded_segments (0x7a9d4 : word) = Some W_7a984.
Proof. vm_refl. Qed.
Lemma D_7a984 : decode_any W_7a984 = Some (Jal 1 32300, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a988 : bv 32 := 0x80040613.
Lemma F_7a988 : fetch_word Asan.M.loaded_segments (0x7a9d8 : word) = Some W_7a988.
Proof. vm_refl. Qed.
Lemma D_7a988 : decode_any W_7a988 = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a98c : bv 32 := 0xfa860613.
Lemma F_7a98c : fetch_word Asan.M.loaded_segments (0x7a9dc : word) = Some W_7a98c.
Proof. vm_refl. Qed.
Lemma D_7a98c : decode_any W_7a98c = Some (OpImm ALU_ADD 12 12 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a990 : bv 32 := 0x00090513.
Lemma F_7a990 : fetch_word Asan.M.loaded_segments (0x7a9e0 : word) = Some W_7a990.
Proof. vm_refl. Qed.
Lemma D_7a990 : decode_any W_7a990 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a994 : bv 32 := 0x00048593.
Lemma F_7a994 : fetch_word Asan.M.loaded_segments (0x7a9e4 : word) = Some W_7a994.
Proof. vm_refl. Qed.
Lemma D_7a994 : decode_any W_7a994 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a998 : bv 32 := 0xf79d80ef.
Lemma F_7a998 : fetch_word Asan.M.loaded_segments (0x7a9e8 : word) = Some W_7a998.
Proof. vm_refl. Qed.
Lemma D_7a998 : decode_any W_7a998 = Some (Jal 1 1937272, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a99c : bv 32 := 0x07010113.
Lemma F_7a99c : fetch_word Asan.M.loaded_segments (0x7a9ec : word) = Some W_7a99c.
Proof. vm_refl. Qed.
Lemma D_7a99c : decode_any W_7a99c = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a9a0 : bv 32 := 0x7e813083.
Lemma F_7a9a0 : fetch_word Asan.M.loaded_segments (0x7a9f0 : word) = Some W_7a9a0.
Proof. vm_refl. Qed.
Lemma D_7a9a0 : decode_any W_7a9a0 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a9a4 : bv 32 := 0x7e013403.
Lemma F_7a9a4 : fetch_word Asan.M.loaded_segments (0x7a9f4 : word) = Some W_7a9a4.
Proof. vm_refl. Qed.
Lemma D_7a9a4 : decode_any W_7a9a4 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a9a8 : bv 32 := 0x7d813483.
Lemma F_7a9a8 : fetch_word Asan.M.loaded_segments (0x7a9f8 : word) = Some W_7a9a8.
Proof. vm_refl. Qed.
Lemma D_7a9a8 : decode_any W_7a9a8 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a9ac : bv 32 := 0x7d013903.
Lemma F_7a9ac : fetch_word Asan.M.loaded_segments (0x7a9fc : word) = Some W_7a9ac.
Proof. vm_refl. Qed.
Lemma D_7a9ac : decode_any W_7a9ac = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a9b0 : bv 32 := 0x7c813983.
Lemma F_7a9b0 : fetch_word Asan.M.loaded_segments (0x7aa00 : word) = Some W_7a9b0.
Proof. vm_refl. Qed.
Lemma D_7a9b0 : decode_any W_7a9b0 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a9b4 : bv 32 := 0x7c013a03.
Lemma F_7a9b4 : fetch_word Asan.M.loaded_segments (0x7aa04 : word) = Some W_7a9b4.
Proof. vm_refl. Qed.
Lemma D_7a9b4 : decode_any W_7a9b4 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a9b8 : bv 32 := 0x7b813a83.
Lemma F_7a9b8 : fetch_word Asan.M.loaded_segments (0x7aa08 : word) = Some W_7a9b8.
Proof. vm_refl. Qed.
Lemma D_7a9b8 : decode_any W_7a9b8 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a9bc : bv 32 := 0x7b013b03.
Lemma F_7a9bc : fetch_word Asan.M.loaded_segments (0x7aa0c : word) = Some W_7a9bc.
Proof. vm_refl. Qed.
Lemma D_7a9bc : decode_any W_7a9bc = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a9c0 : bv 32 := 0x7f010113.
Lemma F_7a9c0 : fetch_word Asan.M.loaded_segments (0x7aa10 : word) = Some W_7a9c0.
Proof. vm_refl. Qed.
Lemma D_7a9c0 : decode_any W_7a9c0 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a9c4 : bv 32 := 0x00008067.
Lemma F_7a9c4 : fetch_word Asan.M.loaded_segments (0x7aa14 : word) = Some W_7a9c4.
Proof. vm_refl. Qed.
Lemma D_7a9c4 : decode_any W_7a9c4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
