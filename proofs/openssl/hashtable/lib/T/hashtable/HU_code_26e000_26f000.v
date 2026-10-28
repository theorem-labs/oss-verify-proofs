(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.openssl.hashtable.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_26e170 : bv 32 := 0xfc010113.
Lemma F_26e170 : fetch_word Ubsan.M.loaded_segments (0x2b3d5c : word) = Some W_26e170.
Proof. vm_refl. Qed.
Lemma D_26e170 : decode_any W_26e170 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e174 : bv 32 := 0x02113c23.
Lemma F_26e174 : fetch_word Ubsan.M.loaded_segments (0x2b3d60 : word) = Some W_26e174.
Proof. vm_refl. Qed.
Lemma D_26e174 : decode_any W_26e174 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e178 : bv 32 := 0x02813823.
Lemma F_26e178 : fetch_word Ubsan.M.loaded_segments (0x2b3d64 : word) = Some W_26e178.
Proof. vm_refl. Qed.
Lemma D_26e178 : decode_any W_26e178 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e17c : bv 32 := 0x02913423.
Lemma F_26e17c : fetch_word Ubsan.M.loaded_segments (0x2b3d68 : word) = Some W_26e17c.
Proof. vm_refl. Qed.
Lemma D_26e17c : decode_any W_26e17c = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e180 : bv 32 := 0x03213023.
Lemma F_26e180 : fetch_word Ubsan.M.loaded_segments (0x2b3d6c : word) = Some W_26e180.
Proof. vm_refl. Qed.
Lemma D_26e180 : decode_any W_26e180 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e184 : bv 32 := 0x01313c23.
Lemma F_26e184 : fetch_word Ubsan.M.loaded_segments (0x2b3d70 : word) = Some W_26e184.
Proof. vm_refl. Qed.
Lemma D_26e184 : decode_any W_26e184 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e188 : bv 32 := 0x01413823.
Lemma F_26e188 : fetch_word Ubsan.M.loaded_segments (0x2b3d74 : word) = Some W_26e188.
Proof. vm_refl. Qed.
Lemma D_26e188 : decode_any W_26e188 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e18c : bv 32 := 0x01513423.
Lemma F_26e18c : fetch_word Ubsan.M.loaded_segments (0x2b3d78 : word) = Some W_26e18c.
Proof. vm_refl. Qed.
Lemma D_26e18c : decode_any W_26e18c = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e190 : bv 32 := 0x03479813.
Lemma F_26e190 : fetch_word Ubsan.M.loaded_segments (0x2b3d7c : word) = Some W_26e190.
Proof. vm_refl. Qed.
Lemma D_26e190 : decode_any W_26e190 = Some (ShiftImm ALU_SLL 16 15 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e194 : bv 32 := 0x00080863.
Lemma F_26e194 : fetch_word Ubsan.M.loaded_segments (0x2b3d80 : word) = Some W_26e194.
Proof. vm_refl. Qed.
Lemma D_26e194 : decode_any W_26e194 = Some (Branch BC_EQ 16 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e198 : bv 32 := 0xfc8fd0ef.
Lemma F_26e198 : fetch_word Ubsan.M.loaded_segments (0x2b3d84 : word) = Some W_26e198.
Proof. vm_refl. Qed.
Lemma D_26e198 : decode_any W_26e198 = Some (Jal 1 2086856, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e19c : bv 32 := 0x01600593.
Lemma F_26e19c : fetch_word Ubsan.M.loaded_segments (0x2b3d88 : word) = Some W_26e19c.
Proof. vm_refl. Qed.
Lemma D_26e19c : decode_any W_26e19c = Some (OpImm ALU_ADD 11 0 22, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e1a0 : bv 32 := 0x0180006f.
Lemma F_26e1a0 : fetch_word Ubsan.M.loaded_segments (0x2b3d8c : word) = Some W_26e1a0.
Proof. vm_refl. Qed.
Lemma D_26e1a0 : decode_any W_26e1a0 = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e1a4 : bv 32 := 0xfff00813.
Lemma F_26e1a4 : fetch_word Ubsan.M.loaded_segments (0x2b3d90 : word) = Some W_26e1a4.
Proof. vm_refl. Qed.
Lemma D_26e1a4 : decode_any W_26e1a4 = Some (OpImm ALU_ADD 16 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e1a8 : bv 32 := 0x00185813.
Lemma F_26e1a8 : fetch_word Ubsan.M.loaded_segments (0x2b3d94 : word) = Some W_26e1a8.
Proof. vm_refl. Qed.
Lemma D_26e1a8 : decode_any W_26e1a8 = Some (ShiftImm ALU_SRL 16 16 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e1ac : bv 32 := 0x0305ec63.
Lemma F_26e1ac : fetch_word Ubsan.M.loaded_segments (0x2b3d98 : word) = Some W_26e1ac.
Proof. vm_refl. Qed.
Lemma D_26e1ac : decode_any W_26e1ac = Some (Branch BC_LTU 11 16 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e1b0 : bv 32 := 0xfb0fd0ef.
Lemma F_26e1b0 : fetch_word Ubsan.M.loaded_segments (0x2b3d9c : word) = Some W_26e1b0.
Proof. vm_refl. Qed.
Lemma D_26e1b0 : decode_any W_26e1b0 = Some (Jal 1 2086832, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e1b4 : bv 32 := 0x00c00593.
Lemma F_26e1b4 : fetch_word Ubsan.M.loaded_segments (0x2b3da0 : word) = Some W_26e1b4.
Proof. vm_refl. Qed.
Lemma D_26e1b4 : decode_any W_26e1b4 = Some (OpImm ALU_ADD 11 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e1b8 : bv 32 := 0x00b52023.
Lemma F_26e1b8 : fetch_word Ubsan.M.loaded_segments (0x2b3da4 : word) = Some W_26e1b8.
Proof. vm_refl. Qed.
Lemma D_26e1b8 : decode_any W_26e1b8 = Some (Store SZ4 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e1bc : bv 32 := 0xfff00513.
Lemma F_26e1bc : fetch_word Ubsan.M.loaded_segments (0x2b3da8 : word) = Some W_26e1bc.
Proof. vm_refl. Qed.
Lemma D_26e1bc : decode_any W_26e1bc = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e1c0 : bv 32 := 0x03813083.
Lemma F_26e1c0 : fetch_word Ubsan.M.loaded_segments (0x2b3dac : word) = Some W_26e1c0.
Proof. vm_refl. Qed.
Lemma D_26e1c0 : decode_any W_26e1c0 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e1c4 : bv 32 := 0x03013403.
Lemma F_26e1c4 : fetch_word Ubsan.M.loaded_segments (0x2b3db0 : word) = Some W_26e1c4.
Proof. vm_refl. Qed.
Lemma D_26e1c4 : decode_any W_26e1c4 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e1c8 : bv 32 := 0x02813483.
Lemma F_26e1c8 : fetch_word Ubsan.M.loaded_segments (0x2b3db4 : word) = Some W_26e1c8.
Proof. vm_refl. Qed.
Lemma D_26e1c8 : decode_any W_26e1c8 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e1cc : bv 32 := 0x02013903.
Lemma F_26e1cc : fetch_word Ubsan.M.loaded_segments (0x2b3db8 : word) = Some W_26e1cc.
Proof. vm_refl. Qed.
Lemma D_26e1cc : decode_any W_26e1cc = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e1d0 : bv 32 := 0x01813983.
Lemma F_26e1d0 : fetch_word Ubsan.M.loaded_segments (0x2b3dbc : word) = Some W_26e1d0.
Proof. vm_refl. Qed.
Lemma D_26e1d0 : decode_any W_26e1d0 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e1d4 : bv 32 := 0x01013a03.
Lemma F_26e1d4 : fetch_word Ubsan.M.loaded_segments (0x2b3dc0 : word) = Some W_26e1d4.
Proof. vm_refl. Qed.
Lemma D_26e1d4 : decode_any W_26e1d4 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e1d8 : bv 32 := 0x00813a83.
Lemma F_26e1d8 : fetch_word Ubsan.M.loaded_segments (0x2b3dc4 : word) = Some W_26e1d8.
Proof. vm_refl. Qed.
Lemma D_26e1d8 : decode_any W_26e1d8 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e1dc : bv 32 := 0x04010113.
Lemma F_26e1dc : fetch_word Ubsan.M.loaded_segments (0x2b3dc8 : word) = Some W_26e1dc.
Proof. vm_refl. Qed.
Lemma D_26e1dc : decode_any W_26e1dc = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e1e0 : bv 32 := 0x00008067.
Lemma F_26e1e0 : fetch_word Ubsan.M.loaded_segments (0x2b3dcc : word) = Some W_26e1e0.
Proof. vm_refl. Qed.
Lemma D_26e1e0 : decode_any W_26e1e0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e1e4 : bv 32 := 0x0106f813.
Lemma F_26e1e4 : fetch_word Ubsan.M.loaded_segments (0x2b3dd0 : word) = Some W_26e1e4.
Proof. vm_refl. Qed.
Lemma D_26e1e4 : decode_any W_26e1e4 = Some (OpImm ALU_AND 16 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e1e8 : bv 32 := 0x00081663.
Lemma F_26e1e8 : fetch_word Ubsan.M.loaded_segments (0x2b3dd4 : word) = Some W_26e1e8.
Proof. vm_refl. Qed.
Lemma D_26e1e8 : decode_any W_26e1e8 = Some (Branch BC_NE 16 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e1ec : bv 32 := 0xff400293.
Lemma F_26e1ec : fetch_word Ubsan.M.loaded_segments (0x2b3dd8 : word) = Some W_26e1ec.
Proof. vm_refl. Qed.
Lemma D_26e1ec : decode_any W_26e1ec = Some (OpImm ALU_ADD 5 0 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e1f0 : bv 32 := 0x03c0006f.
Lemma F_26e1f0 : fetch_word Ubsan.M.loaded_segments (0x2b3ddc : word) = Some W_26e1f0.
Proof. vm_refl. Qed.
Lemma D_26e1f0 : decode_any W_26e1f0 = Some (Jal 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e1f4 : bv 32 := 0x00068413.
Lemma F_26e1f4 : fetch_word Ubsan.M.loaded_segments (0x2b3de0 : word) = Some W_26e1f4.
Proof. vm_refl. Qed.
Lemma D_26e1f4 : decode_any W_26e1f4 = Some (OpImm ALU_ADD 8 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e1f8 : bv 32 := 0x00078993.
Lemma F_26e1f8 : fetch_word Ubsan.M.loaded_segments (0x2b3de4 : word) = Some W_26e1f8.
Proof. vm_refl. Qed.
Lemma D_26e1f8 : decode_any W_26e1f8 = Some (OpImm ALU_ADD 19 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e1fc : bv 32 := 0x00050493.
Lemma F_26e1fc : fetch_word Ubsan.M.loaded_segments (0x2b3de8 : word) = Some W_26e1fc.
Proof. vm_refl. Qed.
Lemma D_26e1fc : decode_any W_26e1fc = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e200 : bv 32 := 0x00070a13.
Lemma F_26e200 : fetch_word Ubsan.M.loaded_segments (0x2b3dec : word) = Some W_26e200.
Proof. vm_refl. Qed.
Lemma D_26e200 : decode_any W_26e200 = Some (OpImm ALU_ADD 20 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e204 : bv 32 := 0x00060913.
Lemma F_26e204 : fetch_word Ubsan.M.loaded_segments (0x2b3df0 : word) = Some W_26e204.
Proof. vm_refl. Qed.
Lemma D_26e204 : decode_any W_26e204 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e208 : bv 32 := 0x00058a93.
Lemma F_26e208 : fetch_word Ubsan.M.loaded_segments (0x2b3df4 : word) = Some W_26e208.
Proof. vm_refl. Qed.
Lemma D_26e208 : decode_any W_26e208 = Some (OpImm ALU_ADD 21 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e20c : bv 32 := 0x1c00c0ef.
Lemma F_26e20c : fetch_word Ubsan.M.loaded_segments (0x2b3df8 : word) = Some W_26e20c.
Proof. vm_refl. Qed.
Lemma D_26e20c : decode_any W_26e20c = Some (Jal 1 49600, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e210 : bv 32 := 0x000a8593.
Lemma F_26e210 : fetch_word Ubsan.M.loaded_segments (0x2b3dfc : word) = Some W_26e210.
Proof. vm_refl. Qed.
Lemma D_26e210 : decode_any W_26e210 = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e214 : bv 32 := 0x00090613.
Lemma F_26e214 : fetch_word Ubsan.M.loaded_segments (0x2b3e00 : word) = Some W_26e214.
Proof. vm_refl. Qed.
Lemma D_26e214 : decode_any W_26e214 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e218 : bv 32 := 0x000a0713.
Lemma F_26e218 : fetch_word Ubsan.M.loaded_segments (0x2b3e04 : word) = Some W_26e218.
Proof. vm_refl. Qed.
Lemma D_26e218 : decode_any W_26e218 = Some (OpImm ALU_ADD 14 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e21c : bv 32 := 0x00048513.
Lemma F_26e21c : fetch_word Ubsan.M.loaded_segments (0x2b3e08 : word) = Some W_26e21c.
Proof. vm_refl. Qed.
Lemma D_26e21c : decode_any W_26e21c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e220 : bv 32 := 0x00098793.
Lemma F_26e220 : fetch_word Ubsan.M.loaded_segments (0x2b3e0c : word) = Some W_26e220.
Proof. vm_refl. Qed.
Lemma D_26e220 : decode_any W_26e220 = Some (OpImm ALU_ADD 15 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e224 : bv 32 := 0x00040693.
Lemma F_26e224 : fetch_word Ubsan.M.loaded_segments (0x2b3e10 : word) = Some W_26e224.
Proof. vm_refl. Qed.
Lemma D_26e224 : decode_any W_26e224 = Some (OpImm ALU_ADD 13 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e228 : bv 32 := 0xfff00293.
Lemma F_26e228 : fetch_word Ubsan.M.loaded_segments (0x2b3e14 : word) = Some W_26e228.
Proof. vm_refl. Qed.
Lemma D_26e228 : decode_any W_26e228 = Some (OpImm ALU_ADD 5 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e22c : bv 32 := 0x0de00893.
Lemma F_26e22c : fetch_word Ubsan.M.loaded_segments (0x2b3e18 : word) = Some W_26e22c.
Proof. vm_refl. Qed.
Lemma D_26e22c : decode_any W_26e22c = Some (OpImm ALU_ADD 17 0 222, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e230 : bv 32 := 0x00050813.
Lemma F_26e230 : fetch_word Ubsan.M.loaded_segments (0x2b3e1c : word) = Some W_26e230.
Proof. vm_refl. Qed.
Lemma D_26e230 : decode_any W_26e230 = Some (OpImm ALU_ADD 16 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e234 : bv 32 := 0x00000073.
Lemma F_26e234 : fetch_word Ubsan.M.loaded_segments (0x2b3e20 : word) = Some W_26e234.
Proof. vm_refl. Qed.
Lemma D_26e234 : decode_any W_26e234 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_26e234 : is_ecall W_26e234 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_26e238 : bv 32 := 0xfff54593.
Lemma F_26e238 : fetch_word Ubsan.M.loaded_segments (0x2b3e24 : word) = Some W_26e238.
Proof. vm_refl. Qed.
Lemma D_26e238 : decode_any W_26e238 = Some (OpImm ALU_XOR 11 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e23c : bv 32 := 0x00b865b3.
Lemma F_26e23c : fetch_word Ubsan.M.loaded_segments (0x2b3e28 : word) = Some W_26e23c.
Proof. vm_refl. Qed.
Lemma D_26e23c : decode_any W_26e23c = Some (Op ALU_OR 11 16 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e240 : bv 32 := 0x00059a63.
Lemma F_26e240 : fetch_word Ubsan.M.loaded_segments (0x2b3e2c : word) = Some W_26e240.
Proof. vm_refl. Qed.
Lemma D_26e240 : decode_any W_26e240 = Some (Branch BC_NE 11 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e244 : bv 32 := 0x03a69313.
Lemma F_26e244 : fetch_word Ubsan.M.loaded_segments (0x2b3e30 : word) = Some W_26e244.
Proof. vm_refl. Qed.
Lemma D_26e244 : decode_any W_26e244 = Some (ShiftImm ALU_SLL 6 13 58, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e248 : bv 32 := 0x03f35513.
Lemma F_26e248 : fetch_word Ubsan.M.loaded_segments (0x2b3e34 : word) = Some W_26e248.
Proof. vm_refl. Qed.
Lemma D_26e248 : decode_any W_26e248 = Some (ShiftImm ALU_SRL 10 6 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e24c : bv 32 := 0xfff50513.
Lemma F_26e24c : fetch_word Ubsan.M.loaded_segments (0x2b3e38 : word) = Some W_26e24c.
Proof. vm_refl. Qed.
Lemma D_26e24c : decode_any W_26e24c = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e250 : bv 32 := 0x00556533.
Lemma F_26e250 : fetch_word Ubsan.M.loaded_segments (0x2b3e3c : word) = Some W_26e250.
Proof. vm_refl. Qed.
Lemma D_26e250 : decode_any W_26e250 = Some (Op ALU_OR 10 10 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e254 : bv 32 := 0xb05fd0ef.
Lemma F_26e254 : fetch_word Ubsan.M.loaded_segments (0x2b3e40 : word) = Some W_26e254.
Proof. vm_refl. Qed.
Lemma D_26e254 : decode_any W_26e254 = Some (Jal 1 2087684, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e258 : bv 32 := 0xf69ff06f.
Lemma F_26e258 : fetch_word Ubsan.M.loaded_segments (0x2b3e44 : word) = Some W_26e258.
Proof. vm_refl. Qed.
Lemma D_26e258 : decode_any W_26e258 = Some (Jal 0 2097000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e25c : bv 32 := 0xff010113.
Lemma F_26e25c : fetch_word Ubsan.M.loaded_segments (0x2b3e48 : word) = Some W_26e25c.
Proof. vm_refl. Qed.
Lemma D_26e25c : decode_any W_26e25c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e260 : bv 32 := 0x00113423.
Lemma F_26e260 : fetch_word Ubsan.M.loaded_segments (0x2b3e4c : word) = Some W_26e260.
Proof. vm_refl. Qed.
Lemma D_26e260 : decode_any W_26e260 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e264 : bv 32 := 0x0009e697.
Lemma F_26e264 : fetch_word Ubsan.M.loaded_segments (0x2b3e50 : word) = Some W_26e264.
Proof. vm_refl. Qed.
Lemma D_26e264 : decode_any W_26e264 = Some (Auipc 13 158, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e268 : bv 32 := 0xf586b683.
Lemma F_26e268 : fetch_word Ubsan.M.loaded_segments (0x2b3e54 : word) = Some W_26e268.
Proof. vm_refl. Qed.
Lemma D_26e268 : decode_any W_26e268 = Some (Load SZ8 true 13 13 3928, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e26c : bv 32 := 0x00b505b3.
Lemma F_26e26c : fetch_word Ubsan.M.loaded_segments (0x2b3e58 : word) = Some W_26e26c.
Proof. vm_refl. Qed.
Lemma D_26e26c : decode_any W_26e26c = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e270 : bv 32 := 0x40d00733.
Lemma F_26e270 : fetch_word Ubsan.M.loaded_segments (0x2b3e5c : word) = Some W_26e270.
Proof. vm_refl. Qed.
Lemma D_26e270 : decode_any W_26e270 = Some (Op ALU_SUB 14 0 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e274 : bv 32 := 0x00d585b3.
Lemma F_26e274 : fetch_word Ubsan.M.loaded_segments (0x2b3e60 : word) = Some W_26e274.
Proof. vm_refl. Qed.
Lemma D_26e274 : decode_any W_26e274 = Some (Op ALU_ADD 11 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e278 : bv 32 := 0x00a77533.
Lemma F_26e278 : fetch_word Ubsan.M.loaded_segments (0x2b3e64 : word) = Some W_26e278.
Proof. vm_refl. Qed.
Lemma D_26e278 : decode_any W_26e278 = Some (Op ALU_AND 10 14 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e27c : bv 32 := 0xfff58593.
Lemma F_26e27c : fetch_word Ubsan.M.loaded_segments (0x2b3e68 : word) = Some W_26e27c.
Proof. vm_refl. Qed.
Lemma D_26e27c : decode_any W_26e27c = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e280 : bv 32 := 0x00e5f5b3.
Lemma F_26e280 : fetch_word Ubsan.M.loaded_segments (0x2b3e6c : word) = Some W_26e280.
Proof. vm_refl. Qed.
Lemma D_26e280 : decode_any W_26e280 = Some (Op ALU_AND 11 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e284 : bv 32 := 0x40a585b3.
Lemma F_26e284 : fetch_word Ubsan.M.loaded_segments (0x2b3e70 : word) = Some W_26e284.
Proof. vm_refl. Qed.
Lemma D_26e284 : decode_any W_26e284 = Some (Op ALU_SUB 11 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e288 : bv 32 := 0x0e200893.
Lemma F_26e288 : fetch_word Ubsan.M.loaded_segments (0x2b3e74 : word) = Some W_26e288.
Proof. vm_refl. Qed.
Lemma D_26e288 : decode_any W_26e288 = Some (OpImm ALU_ADD 17 0 226, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e28c : bv 32 := 0x00000073.
Lemma F_26e28c : fetch_word Ubsan.M.loaded_segments (0x2b3e78 : word) = Some W_26e28c.
Proof. vm_refl. Qed.
Lemma D_26e28c : decode_any W_26e28c = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_26e28c : is_ecall W_26e28c = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_26e290 : bv 32 := 0xac9fd0ef.
Lemma F_26e290 : fetch_word Ubsan.M.loaded_segments (0x2b3e7c : word) = Some W_26e290.
Proof. vm_refl. Qed.
Lemma D_26e290 : decode_any W_26e290 = Some (Jal 1 2087624, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e294 : bv 32 := 0x0005051b.
Lemma F_26e294 : fetch_word Ubsan.M.loaded_segments (0x2b3e80 : word) = Some W_26e294.
Proof. vm_refl. Qed.
Lemma D_26e294 : decode_any W_26e294 = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e298 : bv 32 := 0x00813083.
Lemma F_26e298 : fetch_word Ubsan.M.loaded_segments (0x2b3e84 : word) = Some W_26e298.
Proof. vm_refl. Qed.
Lemma D_26e298 : decode_any W_26e298 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e29c : bv 32 := 0x01010113.
Lemma F_26e29c : fetch_word Ubsan.M.loaded_segments (0x2b3e88 : word) = Some W_26e29c.
Proof. vm_refl. Qed.
Lemma D_26e29c : decode_any W_26e29c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e2a0 : bv 32 := 0x00008067.
Lemma F_26e2a0 : fetch_word Ubsan.M.loaded_segments (0x2b3e8c : word) = Some W_26e2a0.
Proof. vm_refl. Qed.
Lemma D_26e2a0 : decode_any W_26e2a0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e378 : bv 32 := 0xfe010113.
Lemma F_26e378 : fetch_word Ubsan.M.loaded_segments (0x2b3f64 : word) = Some W_26e378.
Proof. vm_refl. Qed.
Lemma D_26e378 : decode_any W_26e378 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e37c : bv 32 := 0x00113c23.
Lemma F_26e37c : fetch_word Ubsan.M.loaded_segments (0x2b3f68 : word) = Some W_26e37c.
Proof. vm_refl. Qed.
Lemma D_26e37c : decode_any W_26e37c = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e380 : bv 32 := 0x00813823.
Lemma F_26e380 : fetch_word Ubsan.M.loaded_segments (0x2b3f6c : word) = Some W_26e380.
Proof. vm_refl. Qed.
Lemma D_26e380 : decode_any W_26e380 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e384 : bv 32 := 0x00913423.
Lemma F_26e384 : fetch_word Ubsan.M.loaded_segments (0x2b3f70 : word) = Some W_26e384.
Proof. vm_refl. Qed.
Lemma D_26e384 : decode_any W_26e384 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e388 : bv 32 := 0x00058413.
Lemma F_26e388 : fetch_word Ubsan.M.loaded_segments (0x2b3f74 : word) = Some W_26e388.
Proof. vm_refl. Qed.
Lemma D_26e388 : decode_any W_26e388 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e38c : bv 32 := 0x00050493.
Lemma F_26e38c : fetch_word Ubsan.M.loaded_segments (0x2b3f78 : word) = Some W_26e38c.
Proof. vm_refl. Qed.
Lemma D_26e38c : decode_any W_26e38c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e390 : bv 32 := 0x03c0c0ef.
Lemma F_26e390 : fetch_word Ubsan.M.loaded_segments (0x2b3f7c : word) = Some W_26e390.
Proof. vm_refl. Qed.
Lemma D_26e390 : decode_any W_26e390 = Some (Jal 1 49212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e394 : bv 32 := 0x0d700893.
Lemma F_26e394 : fetch_word Ubsan.M.loaded_segments (0x2b3f80 : word) = Some W_26e394.
Proof. vm_refl. Qed.
Lemma D_26e394 : decode_any W_26e394 = Some (OpImm ALU_ADD 17 0 215, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e398 : bv 32 := 0x00048513.
Lemma F_26e398 : fetch_word Ubsan.M.loaded_segments (0x2b3f84 : word) = Some W_26e398.
Proof. vm_refl. Qed.
Lemma D_26e398 : decode_any W_26e398 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e39c : bv 32 := 0x00040593.
Lemma F_26e39c : fetch_word Ubsan.M.loaded_segments (0x2b3f88 : word) = Some W_26e39c.
Proof. vm_refl. Qed.
Lemma D_26e39c : decode_any W_26e39c = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e3a0 : bv 32 := 0x00000073.
Lemma F_26e3a0 : fetch_word Ubsan.M.loaded_segments (0x2b3f8c : word) = Some W_26e3a0.
Proof. vm_refl. Qed.
Lemma D_26e3a0 : decode_any W_26e3a0 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_26e3a0 : is_ecall W_26e3a0 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_26e3a4 : bv 32 := 0x9b5fd0ef.
Lemma F_26e3a4 : fetch_word Ubsan.M.loaded_segments (0x2b3f90 : word) = Some W_26e3a4.
Proof. vm_refl. Qed.
Lemma D_26e3a4 : decode_any W_26e3a4 = Some (Jal 1 2087348, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e3a8 : bv 32 := 0x0005051b.
Lemma F_26e3a8 : fetch_word Ubsan.M.loaded_segments (0x2b3f94 : word) = Some W_26e3a8.
Proof. vm_refl. Qed.
Lemma D_26e3a8 : decode_any W_26e3a8 = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e3ac : bv 32 := 0x01813083.
Lemma F_26e3ac : fetch_word Ubsan.M.loaded_segments (0x2b3f98 : word) = Some W_26e3ac.
Proof. vm_refl. Qed.
Lemma D_26e3ac : decode_any W_26e3ac = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e3b0 : bv 32 := 0x01013403.
Lemma F_26e3b0 : fetch_word Ubsan.M.loaded_segments (0x2b3f9c : word) = Some W_26e3b0.
Proof. vm_refl. Qed.
Lemma D_26e3b0 : decode_any W_26e3b0 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e3b4 : bv 32 := 0x00813483.
Lemma F_26e3b4 : fetch_word Ubsan.M.loaded_segments (0x2b3fa0 : word) = Some W_26e3b4.
Proof. vm_refl. Qed.
Lemma D_26e3b4 : decode_any W_26e3b4 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e3b8 : bv 32 := 0x02010113.
Lemma F_26e3b8 : fetch_word Ubsan.M.loaded_segments (0x2b3fa4 : word) = Some W_26e3b8.
Proof. vm_refl. Qed.
Lemma D_26e3b8 : decode_any W_26e3b8 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e3bc : bv 32 := 0x00008067.
Lemma F_26e3bc : fetch_word Ubsan.M.loaded_segments (0x2b3fa8 : word) = Some W_26e3bc.
Proof. vm_refl. Qed.
Lemma D_26e3bc : decode_any W_26e3bc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e4c4 : bv 32 := 0x00050613.
Lemma F_26e4c4 : fetch_word Ubsan.M.loaded_segments (0x2b40b0 : word) = Some W_26e4c4.
Proof. vm_refl. Qed.
Lemma D_26e4c4 : decode_any W_26e4c4 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e4c8 : bv 32 := 0xffdbe517.
Lemma F_26e4c8 : fetch_word Ubsan.M.loaded_segments (0x2b40b4 : word) = Some W_26e4c8.
Proof. vm_refl. Qed.
Lemma D_26e4c8 : decode_any W_26e4c8 = Some (Auipc 10 1047998, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e4cc : bv 32 := 0x08700893.
Lemma F_26e4cc : fetch_word Ubsan.M.loaded_segments (0x2b40b8 : word) = Some W_26e4cc.
Proof. vm_refl. Qed.
Lemma D_26e4cc : decode_any W_26e4cc = Some (OpImm ALU_ADD 17 0 135, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e4d0 : bv 32 := 0x20450593.
Lemma F_26e4d0 : fetch_word Ubsan.M.loaded_segments (0x2b40bc : word) = Some W_26e4d0.
Proof. vm_refl. Qed.
Lemma D_26e4d0 : decode_any W_26e4d0 = Some (OpImm ALU_ADD 11 10 516, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e4d4 : bv 32 := 0x00800693.
Lemma F_26e4d4 : fetch_word Ubsan.M.loaded_segments (0x2b40c0 : word) = Some W_26e4d4.
Proof. vm_refl. Qed.
Lemma D_26e4d4 : decode_any W_26e4d4 = Some (OpImm ALU_ADD 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e4d8 : bv 32 := 0x00000513.
Lemma F_26e4d8 : fetch_word Ubsan.M.loaded_segments (0x2b40c4 : word) = Some W_26e4d8.
Proof. vm_refl. Qed.
Lemma D_26e4d8 : decode_any W_26e4d8 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e4dc : bv 32 := 0x00000073.
Lemma F_26e4dc : fetch_word Ubsan.M.loaded_segments (0x2b40c8 : word) = Some W_26e4dc.
Proof. vm_refl. Qed.
Lemma D_26e4dc : decode_any W_26e4dc = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_26e4dc : is_ecall W_26e4dc = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_26e4e0 : bv 32 := 0x00008067.
Lemma F_26e4e0 : fetch_word Ubsan.M.loaded_segments (0x2b40cc : word) = Some W_26e4e0.
Proof. vm_refl. Qed.
Lemma D_26e4e0 : decode_any W_26e4e0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e4e4 : bv 32 := 0x00050613.
Lemma F_26e4e4 : fetch_word Ubsan.M.loaded_segments (0x2b40d0 : word) = Some W_26e4e4.
Proof. vm_refl. Qed.
Lemma D_26e4e4 : decode_any W_26e4e4 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e4e8 : bv 32 := 0xffdbe517.
Lemma F_26e4e8 : fetch_word Ubsan.M.loaded_segments (0x2b40d4 : word) = Some W_26e4e8.
Proof. vm_refl. Qed.
Lemma D_26e4e8 : decode_any W_26e4e8 = Some (Auipc 10 1047998, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e4ec : bv 32 := 0x08700893.
Lemma F_26e4ec : fetch_word Ubsan.M.loaded_segments (0x2b40d8 : word) = Some W_26e4ec.
Proof. vm_refl. Qed.
Lemma D_26e4ec : decode_any W_26e4ec = Some (OpImm ALU_ADD 17 0 135, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e4f0 : bv 32 := 0x1ec50593.
Lemma F_26e4f0 : fetch_word Ubsan.M.loaded_segments (0x2b40dc : word) = Some W_26e4f0.
Proof. vm_refl. Qed.
Lemma D_26e4f0 : decode_any W_26e4f0 = Some (OpImm ALU_ADD 11 10 492, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e4f4 : bv 32 := 0x00800693.
Lemma F_26e4f4 : fetch_word Ubsan.M.loaded_segments (0x2b40e0 : word) = Some W_26e4f4.
Proof. vm_refl. Qed.
Lemma D_26e4f4 : decode_any W_26e4f4 = Some (OpImm ALU_ADD 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e4f8 : bv 32 := 0x00000513.
Lemma F_26e4f8 : fetch_word Ubsan.M.loaded_segments (0x2b40e4 : word) = Some W_26e4f8.
Proof. vm_refl. Qed.
Lemma D_26e4f8 : decode_any W_26e4f8 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e4fc : bv 32 := 0x00000073.
Lemma F_26e4fc : fetch_word Ubsan.M.loaded_segments (0x2b40e8 : word) = Some W_26e4fc.
Proof. vm_refl. Qed.
Lemma D_26e4fc : decode_any W_26e4fc = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_26e4fc : is_ecall W_26e4fc = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_26e500 : bv 32 := 0x00008067.
Lemma F_26e500 : fetch_word Ubsan.M.loaded_segments (0x2b40ec : word) = Some W_26e500.
Proof. vm_refl. Qed.
Lemma D_26e500 : decode_any W_26e500 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e504 : bv 32 := 0x00050593.
Lemma F_26e504 : fetch_word Ubsan.M.loaded_segments (0x2b40f0 : word) = Some W_26e504.
Proof. vm_refl. Qed.
Lemma D_26e504 : decode_any W_26e504 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e508 : bv 32 := 0x08700893.
Lemma F_26e508 : fetch_word Ubsan.M.loaded_segments (0x2b40f4 : word) = Some W_26e508.
Proof. vm_refl. Qed.
Lemma D_26e508 : decode_any W_26e508 = Some (OpImm ALU_ADD 17 0 135, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e50c : bv 32 := 0x00200513.
Lemma F_26e50c : fetch_word Ubsan.M.loaded_segments (0x2b40f8 : word) = Some W_26e50c.
Proof. vm_refl. Qed.
Lemma D_26e50c : decode_any W_26e50c = Some (OpImm ALU_ADD 10 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e510 : bv 32 := 0x00800693.
Lemma F_26e510 : fetch_word Ubsan.M.loaded_segments (0x2b40fc : word) = Some W_26e510.
Proof. vm_refl. Qed.
Lemma D_26e510 : decode_any W_26e510 = Some (OpImm ALU_ADD 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e514 : bv 32 := 0x00000613.
Lemma F_26e514 : fetch_word Ubsan.M.loaded_segments (0x2b4100 : word) = Some W_26e514.
Proof. vm_refl. Qed.
Lemma D_26e514 : decode_any W_26e514 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e518 : bv 32 := 0x00000073.
Lemma F_26e518 : fetch_word Ubsan.M.loaded_segments (0x2b4104 : word) = Some W_26e518.
Proof. vm_refl. Qed.
Lemma D_26e518 : decode_any W_26e518 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_26e518 : is_ecall W_26e518 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_26e51c : bv 32 := 0x00008067.
Lemma F_26e51c : fetch_word Ubsan.M.loaded_segments (0x2b4108 : word) = Some W_26e51c.
Proof. vm_refl. Qed.
Lemma D_26e51c : decode_any W_26e51c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e520 : bv 32 := 0xf6010113.
Lemma F_26e520 : fetch_word Ubsan.M.loaded_segments (0x2b410c : word) = Some W_26e520.
Proof. vm_refl. Qed.
Lemma D_26e520 : decode_any W_26e520 = Some (OpImm ALU_ADD 2 2 3936, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e524 : bv 32 := 0x08113c23.
Lemma F_26e524 : fetch_word Ubsan.M.loaded_segments (0x2b4110 : word) = Some W_26e524.
Proof. vm_refl. Qed.
Lemma D_26e524 : decode_any W_26e524 = Some (Store SZ8 2 1 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e528 : bv 32 := 0x08813823.
Lemma F_26e528 : fetch_word Ubsan.M.loaded_segments (0x2b4114 : word) = Some W_26e528.
Proof. vm_refl. Qed.
Lemma D_26e528 : decode_any W_26e528 = Some (Store SZ8 2 8 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e52c : bv 32 := 0x08913423.
Lemma F_26e52c : fetch_word Ubsan.M.loaded_segments (0x2b4118 : word) = Some W_26e52c.
Proof. vm_refl. Qed.
Lemma D_26e52c : decode_any W_26e52c = Some (Store SZ8 2 9 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e530 : bv 32 := 0x00050413.
Lemma F_26e530 : fetch_word Ubsan.M.loaded_segments (0x2b411c : word) = Some W_26e530.
Proof. vm_refl. Qed.
Lemma D_26e530 : decode_any W_26e530 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e534 : bv 32 := 0x00069517.
Lemma F_26e534 : fetch_word Ubsan.M.loaded_segments (0x2b4120 : word) = Some W_26e534.
Proof. vm_refl. Qed.
Lemma D_26e534 : decode_any W_26e534 = Some (Auipc 10 105, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e538 : bv 32 := 0x46853483.
Lemma F_26e538 : fetch_word Ubsan.M.loaded_segments (0x2b4124 : word) = Some W_26e538.
Proof. vm_refl. Qed.
Lemma D_26e538 : decode_any W_26e538 = Some (Load SZ8 true 9 10 1128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e53c : bv 32 := 0x0004b503.
Lemma F_26e53c : fetch_word Ubsan.M.loaded_segments (0x2b4128 : word) = Some W_26e53c.
Proof. vm_refl. Qed.
Lemma D_26e53c : decode_any W_26e53c = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e540 : bv 32 := 0x08a13023.
Lemma F_26e540 : fetch_word Ubsan.M.loaded_segments (0x2b412c : word) = Some W_26e540.
Proof. vm_refl. Qed.
Lemma D_26e540 : decode_any W_26e540 = Some (Store SZ8 2 10 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e544 : bv 32 := 0x00010513.
Lemma F_26e544 : fetch_word Ubsan.M.loaded_segments (0x2b4130 : word) = Some W_26e544.
Proof. vm_refl. Qed.
Lemma D_26e544 : decode_any W_26e544 = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e548 : bv 32 := 0xf9dff0ef.
Lemma F_26e548 : fetch_word Ubsan.M.loaded_segments (0x2b4134 : word) = Some W_26e548.
Proof. vm_refl. Qed.
Lemma D_26e548 : decode_any W_26e548 = Some (Jal 1 2097052, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e54c : bv 32 := 0x00020513.
Lemma F_26e54c : fetch_word Ubsan.M.loaded_segments (0x2b4138 : word) = Some W_26e54c.
Proof. vm_refl. Qed.
Lemma D_26e54c : decode_any W_26e54c = Some (OpImm ALU_ADD 10 4 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e550 : bv 32 := 0xf5852503.
Lemma F_26e550 : fetch_word Ubsan.M.loaded_segments (0x2b413c : word) = Some W_26e550.
Proof. vm_refl. Qed.
Lemma D_26e550 : decode_any W_26e550 = Some (Load SZ4 true 10 10 3928, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e554 : bv 32 := 0x08200893.
Lemma F_26e554 : fetch_word Ubsan.M.loaded_segments (0x2b4140 : word) = Some W_26e554.
Proof. vm_refl. Qed.
Lemma D_26e554 : decode_any W_26e554 = Some (OpImm ALU_ADD 17 0 130, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e558 : bv 32 := 0x00040593.
Lemma F_26e558 : fetch_word Ubsan.M.loaded_segments (0x2b4144 : word) = Some W_26e558.
Proof. vm_refl. Qed.
Lemma D_26e558 : decode_any W_26e558 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e55c : bv 32 := 0x00000073.
Lemma F_26e55c : fetch_word Ubsan.M.loaded_segments (0x2b4148 : word) = Some W_26e55c.
Proof. vm_refl. Qed.
Lemma D_26e55c : decode_any W_26e55c = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_26e55c : is_ecall W_26e55c = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_26e560 : bv 32 := 0xff8fd0ef.
Lemma F_26e560 : fetch_word Ubsan.M.loaded_segments (0x2b414c : word) = Some W_26e560.
Proof. vm_refl. Qed.
Lemma D_26e560 : decode_any W_26e560 = Some (Jal 1 2086904, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e564 : bv 32 := 0x00050413.
Lemma F_26e564 : fetch_word Ubsan.M.loaded_segments (0x2b4150 : word) = Some W_26e564.
Proof. vm_refl. Qed.
Lemma D_26e564 : decode_any W_26e564 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e568 : bv 32 := 0x00010513.
Lemma F_26e568 : fetch_word Ubsan.M.loaded_segments (0x2b4154 : word) = Some W_26e568.
Proof. vm_refl. Qed.
Lemma D_26e568 : decode_any W_26e568 = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e56c : bv 32 := 0xf99ff0ef.
Lemma F_26e56c : fetch_word Ubsan.M.loaded_segments (0x2b4158 : word) = Some W_26e56c.
Proof. vm_refl. Qed.
Lemma D_26e56c : decode_any W_26e56c = Some (Jal 1 2097048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e570 : bv 32 := 0x0004b503.
Lemma F_26e570 : fetch_word Ubsan.M.loaded_segments (0x2b415c : word) = Some W_26e570.
Proof. vm_refl. Qed.
Lemma D_26e570 : decode_any W_26e570 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e574 : bv 32 := 0x08013583.
Lemma F_26e574 : fetch_word Ubsan.M.loaded_segments (0x2b4160 : word) = Some W_26e574.
Proof. vm_refl. Qed.
Lemma D_26e574 : decode_any W_26e574 = Some (Load SZ8 true 11 2 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e578 : bv 32 := 0x00b51e63.
Lemma F_26e578 : fetch_word Ubsan.M.loaded_segments (0x2b4164 : word) = Some W_26e578.
Proof. vm_refl. Qed.
Lemma D_26e578 : decode_any W_26e578 = Some (Branch BC_NE 10 11 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e57c : bv 32 := 0x0004051b.
Lemma F_26e57c : fetch_word Ubsan.M.loaded_segments (0x2b4168 : word) = Some W_26e57c.
Proof. vm_refl. Qed.
Lemma D_26e57c : decode_any W_26e57c = Some (OpImm32 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e580 : bv 32 := 0x09813083.
Lemma F_26e580 : fetch_word Ubsan.M.loaded_segments (0x2b416c : word) = Some W_26e580.
Proof. vm_refl. Qed.
Lemma D_26e580 : decode_any W_26e580 = Some (Load SZ8 true 1 2 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e584 : bv 32 := 0x09013403.
Lemma F_26e584 : fetch_word Ubsan.M.loaded_segments (0x2b4170 : word) = Some W_26e584.
Proof. vm_refl. Qed.
Lemma D_26e584 : decode_any W_26e584 = Some (Load SZ8 true 8 2 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e588 : bv 32 := 0x08813483.
Lemma F_26e588 : fetch_word Ubsan.M.loaded_segments (0x2b4174 : word) = Some W_26e588.
Proof. vm_refl. Qed.
Lemma D_26e588 : decode_any W_26e588 = Some (Load SZ8 true 9 2 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e58c : bv 32 := 0x0a010113.
Lemma F_26e58c : fetch_word Ubsan.M.loaded_segments (0x2b4178 : word) = Some W_26e58c.
Proof. vm_refl. Qed.
Lemma D_26e58c : decode_any W_26e58c = Some (OpImm ALU_ADD 2 2 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e590 : bv 32 := 0x00008067.
Lemma F_26e590 : fetch_word Ubsan.M.loaded_segments (0x2b417c : word) = Some W_26e590.
Proof. vm_refl. Qed.
Lemma D_26e590 : decode_any W_26e590 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e594 : bv 32 := 0xbc4fd0ef.
Lemma F_26e594 : fetch_word Ubsan.M.loaded_segments (0x2b4180 : word) = Some W_26e594.
Proof. vm_refl. Qed.
Lemma D_26e594 : decode_any W_26e594 = Some (Jal 1 2085828, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e598 : bv 32 := 0xf9010113.
Lemma F_26e598 : fetch_word Ubsan.M.loaded_segments (0x2b4184 : word) = Some W_26e598.
Proof. vm_refl. Qed.
Lemma D_26e598 : decode_any W_26e598 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e59c : bv 32 := 0x06113423.
Lemma F_26e59c : fetch_word Ubsan.M.loaded_segments (0x2b4188 : word) = Some W_26e59c.
Proof. vm_refl. Qed.
Lemma D_26e59c : decode_any W_26e59c = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e5a0 : bv 32 := 0x06813023.
Lemma F_26e5a0 : fetch_word Ubsan.M.loaded_segments (0x2b418c : word) = Some W_26e5a0.
Proof. vm_refl. Qed.
Lemma D_26e5a0 : decode_any W_26e5a0 = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e5a4 : bv 32 := 0x04913c23.
Lemma F_26e5a4 : fetch_word Ubsan.M.loaded_segments (0x2b4190 : word) = Some W_26e5a4.
Proof. vm_refl. Qed.
Lemma D_26e5a4 : decode_any W_26e5a4 = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e5a8 : bv 32 := 0x05213823.
Lemma F_26e5a8 : fetch_word Ubsan.M.loaded_segments (0x2b4194 : word) = Some W_26e5a8.
Proof. vm_refl. Qed.
Lemma D_26e5a8 : decode_any W_26e5a8 = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e5ac : bv 32 := 0x00060413.
Lemma F_26e5ac : fetch_word Ubsan.M.loaded_segments (0x2b4198 : word) = Some W_26e5ac.
Proof. vm_refl. Qed.
Lemma D_26e5ac : decode_any W_26e5ac = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e5b0 : bv 32 := 0x00050493.
Lemma F_26e5b0 : fetch_word Ubsan.M.loaded_segments (0x2b419c : word) = Some W_26e5b0.
Proof. vm_refl. Qed.
Lemma D_26e5b0 : decode_any W_26e5b0 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e5b4 : bv 32 := 0x00069517.
Lemma F_26e5b4 : fetch_word Ubsan.M.loaded_segments (0x2b41a0 : word) = Some W_26e5b4.
Proof. vm_refl. Qed.
Lemma D_26e5b4 : decode_any W_26e5b4 = Some (Auipc 10 105, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e5b8 : bv 32 := 0x3e853903.
Lemma F_26e5b8 : fetch_word Ubsan.M.loaded_segments (0x2b41a4 : word) = Some W_26e5b8.
Proof. vm_refl. Qed.
Lemma D_26e5b8 : decode_any W_26e5b8 = Some (Load SZ8 true 18 10 1000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e5bc : bv 32 := 0x00093503.
Lemma F_26e5bc : fetch_word Ubsan.M.loaded_segments (0x2b41a8 : word) = Some W_26e5bc.
Proof. vm_refl. Qed.
Lemma D_26e5bc : decode_any W_26e5bc = Some (Load SZ8 true 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e5c0 : bv 32 := 0x04a13423.
Lemma F_26e5c0 : fetch_word Ubsan.M.loaded_segments (0x2b41ac : word) = Some W_26e5c0.
Proof. vm_refl. Qed.
Lemma D_26e5c0 : decode_any W_26e5c0 = Some (Store SZ8 2 10 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e5c4 : bv 32 := 0x12058063.
Lemma F_26e5c4 : fetch_word Ubsan.M.loaded_segments (0x2b41b0 : word) = Some W_26e5c4.
Proof. vm_refl. Qed.
Lemma D_26e5c4 : decode_any W_26e5c4 = Some (Branch BC_EQ 11 0 288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e5c8 : bv 32 := 0x0005b503.
Lemma F_26e5c8 : fetch_word Ubsan.M.loaded_segments (0x2b41b4 : word) = Some W_26e5c8.
Proof. vm_refl. Qed.
Lemma D_26e5c8 : decode_any W_26e5c8 = Some (Load SZ8 true 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e5cc : bv 32 := 0x00200613.
Lemma F_26e5cc : fetch_word Ubsan.M.loaded_segments (0x2b41b8 : word) = Some W_26e5cc.
Proof. vm_refl. Qed.
Lemma D_26e5cc : decode_any W_26e5cc = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e5d0 : bv 32 := 0x0ec56863.
Lemma F_26e5d0 : fetch_word Ubsan.M.loaded_segments (0x2b41bc : word) = Some W_26e5d0.
Proof. vm_refl. Qed.
Lemma D_26e5d0 : decode_any W_26e5d0 = Some (Branch BC_LTU 10 12 240, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e5d4 : bv 32 := 0xfff4851b.
Lemma F_26e5d4 : fetch_word Ubsan.M.loaded_segments (0x2b41c0 : word) = Some W_26e5d4.
Proof. vm_refl. Qed.
Lemma D_26e5d4 : decode_any W_26e5d4 = Some (OpImm32 10 9 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e5d8 : bv 32 := 0x0009e617.
Lemma F_26e5d8 : fetch_word Ubsan.M.loaded_segments (0x2b41c4 : word) = Some W_26e5d8.
Proof. vm_refl. Qed.
Lemma D_26e5d8 : decode_any W_26e5d8 = Some (Auipc 12 158, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e5dc : bv 32 := 0x00100693.
Lemma F_26e5dc : fetch_word Ubsan.M.loaded_segments (0x2b41c8 : word) = Some W_26e5dc.
Proof. vm_refl. Qed.
Lemma D_26e5dc : decode_any W_26e5dc = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e5e0 : bv 32 := 0x00355793.
Lemma F_26e5e0 : fetch_word Ubsan.M.loaded_segments (0x2b41cc : word) = Some W_26e5e0.
Proof. vm_refl. Qed.
Lemma D_26e5e0 : decode_any W_26e5e0 = Some (ShiftImm ALU_SRL 15 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e5e4 : bv 32 := 0xfd460713.
Lemma F_26e5e4 : fetch_word Ubsan.M.loaded_segments (0x2b41d0 : word) = Some W_26e5e4.
Proof. vm_refl. Qed.
Lemma D_26e5e4 : decode_any W_26e5e4 = Some (OpImm ALU_ADD 14 12 4052, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e5e8 : bv 32 := 0x03f57813.
Lemma F_26e5e8 : fetch_word Ubsan.M.loaded_segments (0x2b41d4 : word) = Some W_26e5e8.
Proof. vm_refl. Qed.
Lemma D_26e5e8 : decode_any W_26e5e8 = Some (OpImm ALU_AND 16 10 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e5ec : bv 32 := 0x00a69533.
Lemma F_26e5ec : fetch_word Ubsan.M.loaded_segments (0x2b41d8 : word) = Some W_26e5ec.
Proof. vm_refl. Qed.
Lemma D_26e5ec : decode_any W_26e5ec = Some (Op ALU_SLL 10 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e5f0 : bv 32 := 0xff87f793.
Lemma F_26e5f0 : fetch_word Ubsan.M.loaded_segments (0x2b41dc : word) = Some W_26e5f0.
Proof. vm_refl. Qed.
Lemma D_26e5f0 : decode_any W_26e5f0 = Some (OpImm ALU_AND 15 15 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e5f4 : bv 32 := 0x00f70633.
Lemma F_26e5f4 : fetch_word Ubsan.M.loaded_segments (0x2b41e0 : word) = Some W_26e5f4.
Proof. vm_refl. Qed.
Lemma D_26e5f4 : decode_any W_26e5f4 = Some (Op ALU_ADD 12 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e5f8 : bv 32 := 0x01f00693.
Lemma F_26e5f8 : fetch_word Ubsan.M.loaded_segments (0x2b41e4 : word) = Some W_26e5f8.
Proof. vm_refl. Qed.
Lemma D_26e5f8 : decode_any W_26e5f8 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e5fc : bv 32 := 0x00860613.
Lemma F_26e5fc : fetch_word Ubsan.M.loaded_segments (0x2b41e8 : word) = Some W_26e5fc.
Proof. vm_refl. Qed.
Lemma D_26e5fc : decode_any W_26e5fc = Some (OpImm ALU_ADD 12 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e600 : bv 32 := 0x0306fa63.
Lemma F_26e600 : fetch_word Ubsan.M.loaded_segments (0x2b41ec : word) = Some W_26e600.
Proof. vm_refl. Qed.
Lemma D_26e600 : decode_any W_26e600 = Some (Branch BC_GEU 13 16 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e604 : bv 32 := 0x02055513.
Lemma F_26e604 : fetch_word Ubsan.M.loaded_segments (0x2b41f0 : word) = Some W_26e604.
Proof. vm_refl. Qed.
Lemma D_26e604 : decode_any W_26e604 = Some (ShiftImm ALU_SRL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e608 : bv 32 := 0x00460613.
Lemma F_26e608 : fetch_word Ubsan.M.loaded_segments (0x2b41f4 : word) = Some W_26e608.
Proof. vm_refl. Qed.
Lemma D_26e608 : decode_any W_26e608 = Some (OpImm ALU_ADD 12 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e60c : bv 32 := 0x00062683.
Lemma F_26e60c : fetch_word Ubsan.M.loaded_segments (0x2b41f8 : word) = Some W_26e60c.
Proof. vm_refl. Qed.
Lemma D_26e60c : decode_any W_26e60c = Some (Load SZ4 true 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e610 : bv 32 := 0x00a6e7b3.
Lemma F_26e610 : fetch_word Ubsan.M.loaded_segments (0x2b41fc : word) = Some W_26e610.
Proof. vm_refl. Qed.
Lemma D_26e610 : decode_any W_26e610 = Some (Op ALU_OR 15 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e614 : bv 32 := 0x0007879b.
Lemma F_26e614 : fetch_word Ubsan.M.loaded_segments (0x2b4200 : word) = Some W_26e614.
Proof. vm_refl. Qed.
Lemma D_26e614 : decode_any W_26e614 = Some (OpImm32 15 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e618 : bv 32 := 0x1606282f.
Lemma F_26e618 : fetch_word Ubsan.M.loaded_segments (0x2b4204 : word) = Some W_26e618.
Proof. vm_refl. Qed.
Lemma D_26e618 : decode_any W_26e618 = Some (Lr AW true true 16 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e61c : bv 32 := 0x00d81663.
Lemma F_26e61c : fetch_word Ubsan.M.loaded_segments (0x2b4208 : word) = Some W_26e61c.
Proof. vm_refl. Qed.
Lemma D_26e61c : decode_any W_26e61c = Some (Branch BC_NE 16 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e620 : bv 32 := 0x1ef628af.
Lemma F_26e620 : fetch_word Ubsan.M.loaded_segments (0x2b420c : word) = Some W_26e620.
Proof. vm_refl. Qed.
Lemma D_26e620 : decode_any W_26e620 = Some (Sc AW true true 17 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e624 : bv 32 := 0xfe089ae3.
Lemma F_26e624 : fetch_word Ubsan.M.loaded_segments (0x2b4210 : word) = Some W_26e624.
Proof. vm_refl. Qed.
Lemma D_26e624 : decode_any W_26e624 = Some (Branch BC_NE 17 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e628 : bv 32 := 0x0008081b.
Lemma F_26e628 : fetch_word Ubsan.M.loaded_segments (0x2b4214 : word) = Some W_26e628.
Proof. vm_refl. Qed.
Lemma D_26e628 : decode_any W_26e628 = Some (OpImm32 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e62c : bv 32 := 0xfed810e3.
Lemma F_26e62c : fetch_word Ubsan.M.loaded_segments (0x2b4218 : word) = Some W_26e62c.
Proof. vm_refl. Qed.
Lemma D_26e62c : decode_any W_26e62c = Some (Branch BC_NE 16 13 8160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e630 : bv 32 := 0x0280006f.
Lemma F_26e630 : fetch_word Ubsan.M.loaded_segments (0x2b421c : word) = Some W_26e630.
Proof. vm_refl. Qed.
Lemma D_26e630 : decode_any W_26e630 = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e634 : bv 32 := 0x00062683.
Lemma F_26e634 : fetch_word Ubsan.M.loaded_segments (0x2b4220 : word) = Some W_26e634.
Proof. vm_refl. Qed.
Lemma D_26e634 : decode_any W_26e634 = Some (Load SZ4 true 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e638 : bv 32 := 0x00a6e7b3.
Lemma F_26e638 : fetch_word Ubsan.M.loaded_segments (0x2b4224 : word) = Some W_26e638.
Proof. vm_refl. Qed.
Lemma D_26e638 : decode_any W_26e638 = Some (Op ALU_OR 15 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e63c : bv 32 := 0x0007879b.
Lemma F_26e63c : fetch_word Ubsan.M.loaded_segments (0x2b4228 : word) = Some W_26e63c.
Proof. vm_refl. Qed.
Lemma D_26e63c : decode_any W_26e63c = Some (OpImm32 15 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e640 : bv 32 := 0x1606282f.
Lemma F_26e640 : fetch_word Ubsan.M.loaded_segments (0x2b422c : word) = Some W_26e640.
Proof. vm_refl. Qed.
Lemma D_26e640 : decode_any W_26e640 = Some (Lr AW true true 16 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e644 : bv 32 := 0x00d81663.
Lemma F_26e644 : fetch_word Ubsan.M.loaded_segments (0x2b4230 : word) = Some W_26e644.
Proof. vm_refl. Qed.
Lemma D_26e644 : decode_any W_26e644 = Some (Branch BC_NE 16 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e648 : bv 32 := 0x1ef628af.
Lemma F_26e648 : fetch_word Ubsan.M.loaded_segments (0x2b4234 : word) = Some W_26e648.
Proof. vm_refl. Qed.
Lemma D_26e648 : decode_any W_26e648 = Some (Sc AW true true 17 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e64c : bv 32 := 0xfe089ae3.
Lemma F_26e64c : fetch_word Ubsan.M.loaded_segments (0x2b4238 : word) = Some W_26e64c.
Proof. vm_refl. Qed.
Lemma D_26e64c : decode_any W_26e64c = Some (Branch BC_NE 17 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e650 : bv 32 := 0x0008081b.
Lemma F_26e650 : fetch_word Ubsan.M.loaded_segments (0x2b423c : word) = Some W_26e650.
Proof. vm_refl. Qed.
Lemma D_26e650 : decode_any W_26e650 = Some (OpImm32 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e654 : bv 32 := 0xfed810e3.
Lemma F_26e654 : fetch_word Ubsan.M.loaded_segments (0x2b4240 : word) = Some W_26e654.
Proof. vm_refl. Qed.
Lemma D_26e654 : decode_any W_26e654 = Some (Branch BC_NE 16 13 8160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e658 : bv 32 := 0x0009e517.
Lemma F_26e658 : fetch_word Ubsan.M.loaded_segments (0x2b4244 : word) = Some W_26e658.
Proof. vm_refl. Qed.
Lemma D_26e658 : decode_any W_26e658 = Some (Auipc 10 158, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e65c : bv 32 := 0xb3554503.
Lemma F_26e65c : fetch_word Ubsan.M.loaded_segments (0x2b4248 : word) = Some W_26e65c.
Proof. vm_refl. Qed.
Lemma D_26e65c : decode_any W_26e65c = Some (Load SZ1 false 10 10 2869, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e660 : bv 32 := 0x04051263.
Lemma F_26e660 : fetch_word Ubsan.M.loaded_segments (0x2b424c : word) = Some W_26e660.
Proof. vm_refl. Qed.
Lemma D_26e660 : decode_any W_26e660 = Some (Branch BC_NE 10 0 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e664 : bv 32 := 0x00074503.
Lemma F_26e664 : fetch_word Ubsan.M.loaded_segments (0x2b4250 : word) = Some W_26e664.
Proof. vm_refl. Qed.
Lemma D_26e664 : decode_any W_26e664 = Some (Load SZ1 false 10 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e668 : bv 32 := 0x00157513.
Lemma F_26e668 : fetch_word Ubsan.M.loaded_segments (0x2b4254 : word) = Some W_26e668.
Proof. vm_refl. Qed.
Lemma D_26e668 : decode_any W_26e668 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e66c : bv 32 := 0x02051c63.
Lemma F_26e66c : fetch_word Ubsan.M.loaded_segments (0x2b4258 : word) = Some W_26e66c.
Proof. vm_refl. Qed.
Lemma D_26e66c : decode_any W_26e66c = Some (Branch BC_NE 10 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e670 : bv 32 := 0x00300613.
Lemma F_26e670 : fetch_word Ubsan.M.loaded_segments (0x2b425c : word) = Some W_26e670.
Proof. vm_refl. Qed.
Lemma D_26e670 : decode_any W_26e670 = Some (OpImm ALU_ADD 12 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e674 : bv 32 := 0x08700893.
Lemma F_26e674 : fetch_word Ubsan.M.loaded_segments (0x2b4260 : word) = Some W_26e674.
Proof. vm_refl. Qed.
Lemma D_26e674 : decode_any W_26e674 = Some (OpImm ALU_ADD 17 0 135, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e678 : bv 32 := 0x00100513.
Lemma F_26e678 : fetch_word Ubsan.M.loaded_segments (0x2b4264 : word) = Some W_26e678.
Proof. vm_refl. Qed.
Lemma D_26e678 : decode_any W_26e678 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e67c : bv 32 := 0x00058793.
Lemma F_26e67c : fetch_word Ubsan.M.loaded_segments (0x2b4268 : word) = Some W_26e67c.
Proof. vm_refl. Qed.
Lemma D_26e67c : decode_any W_26e67c = Some (OpImm ALU_ADD 15 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e680 : bv 32 := 0x00010593.
Lemma F_26e680 : fetch_word Ubsan.M.loaded_segments (0x2b426c : word) = Some W_26e680.
Proof. vm_refl. Qed.
Lemma D_26e680 : decode_any W_26e680 = Some (OpImm ALU_ADD 11 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e684 : bv 32 := 0x02061613.
Lemma F_26e684 : fetch_word Ubsan.M.loaded_segments (0x2b4270 : word) = Some W_26e684.
Proof. vm_refl. Qed.
Lemma D_26e684 : decode_any W_26e684 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e688 : bv 32 := 0x00c13023.
Lemma F_26e688 : fetch_word Ubsan.M.loaded_segments (0x2b4274 : word) = Some W_26e688.
Proof. vm_refl. Qed.
Lemma D_26e688 : decode_any W_26e688 = Some (Store SZ8 2 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e68c : bv 32 := 0x00800693.
Lemma F_26e68c : fetch_word Ubsan.M.loaded_segments (0x2b4278 : word) = Some W_26e68c.
Proof. vm_refl. Qed.
Lemma D_26e68c : decode_any W_26e68c = Some (OpImm ALU_ADD 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e690 : bv 32 := 0x00000613.
Lemma F_26e690 : fetch_word Ubsan.M.loaded_segments (0x2b427c : word) = Some W_26e690.
Proof. vm_refl. Qed.
Lemma D_26e690 : decode_any W_26e690 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e694 : bv 32 := 0x00000073.
Lemma F_26e694 : fetch_word Ubsan.M.loaded_segments (0x2b4280 : word) = Some W_26e694.
Proof. vm_refl. Qed.
Lemma D_26e694 : decode_any W_26e694 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_26e694 : is_ecall W_26e694 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_26e698 : bv 32 := 0x00078593.
Lemma F_26e698 : fetch_word Ubsan.M.loaded_segments (0x2b4284 : word) = Some W_26e698.
Proof. vm_refl. Qed.
Lemma D_26e698 : decode_any W_26e698 = Some (OpImm ALU_ADD 11 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e69c : bv 32 := 0x00100513.
Lemma F_26e69c : fetch_word Ubsan.M.loaded_segments (0x2b4288 : word) = Some W_26e69c.
Proof. vm_refl. Qed.
Lemma D_26e69c : decode_any W_26e69c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e6a0 : bv 32 := 0x00a70023.
Lemma F_26e6a0 : fetch_word Ubsan.M.loaded_segments (0x2b428c : word) = Some W_26e6a0.
Proof. vm_refl. Qed.
Lemma D_26e6a0 : decode_any W_26e6a0 = Some (Store SZ1 14 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e6a4 : bv 32 := 0x08b5c503.
Lemma F_26e6a4 : fetch_word Ubsan.M.loaded_segments (0x2b4290 : word) = Some W_26e6a4.
Proof. vm_refl. Qed.
Lemma D_26e6a4 : decode_any W_26e6a4 = Some (Load SZ1 false 10 11 139, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e6a8 : bv 32 := 0x01057513.
Lemma F_26e6a8 : fetch_word Ubsan.M.loaded_segments (0x2b4294 : word) = Some W_26e6a8.
Proof. vm_refl. Qed.
Lemma D_26e6a8 : decode_any W_26e6a8 = Some (OpImm ALU_AND 10 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e6ac : bv 32 := 0x00051a63.
Lemma F_26e6ac : fetch_word Ubsan.M.loaded_segments (0x2b4298 : word) = Some W_26e6ac.
Proof. vm_refl. Qed.
Lemma D_26e6ac : decode_any W_26e6ac = Some (Branch BC_NE 10 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e6b0 : bv 32 := 0x0330000f.
Lemma F_26e6b0 : fetch_word Ubsan.M.loaded_segments (0x2b429c : word) = Some W_26e6b0.
Proof. vm_refl. Qed.
Lemma D_26e6b0 : decode_any W_26e6b0 = Some (Fence 0 3 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e6b4 : bv 32 := 0x00100513.
Lemma F_26e6b4 : fetch_word Ubsan.M.loaded_segments (0x2b42a0 : word) = Some W_26e6b4.
Proof. vm_refl. Qed.
Lemma D_26e6b4 : decode_any W_26e6b4 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e6b8 : bv 32 := 0x00a72223.
Lemma F_26e6b8 : fetch_word Ubsan.M.loaded_segments (0x2b42a4 : word) = Some W_26e6b8.
Proof. vm_refl. Qed.
Lemma D_26e6b8 : decode_any W_26e6b8 = Some (Store SZ4 14 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e6bc : bv 32 := 0x0330000f.
Lemma F_26e6bc : fetch_word Ubsan.M.loaded_segments (0x2b42a8 : word) = Some W_26e6bc.
Proof. vm_refl. Qed.
Lemma D_26e6bc : decode_any W_26e6bc = Some (Fence 0 3 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e6c0 : bv 32 := 0x0005b503.
Lemma F_26e6c0 : fetch_word Ubsan.M.loaded_segments (0x2b42ac : word) = Some W_26e6c0.
Proof. vm_refl. Qed.
Lemma D_26e6c0 : decode_any W_26e6c0 = Some (Load SZ8 true 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e6c4 : bv 32 := 0x0885a603.
Lemma F_26e6c4 : fetch_word Ubsan.M.loaded_segments (0x2b42b0 : word) = Some W_26e6c4.
Proof. vm_refl. Qed.
Lemma D_26e6c4 : decode_any W_26e6c4 = Some (Load SZ4 true 12 11 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e6c8 : bv 32 := 0x02a13423.
Lemma F_26e6c8 : fetch_word Ubsan.M.loaded_segments (0x2b42b4 : word) = Some W_26e6c8.
Proof. vm_refl. Qed.
Lemma D_26e6c8 : decode_any W_26e6c8 = Some (Store SZ8 2 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e6cc : bv 32 := 0x02c13823.
Lemma F_26e6cc : fetch_word Ubsan.M.loaded_segments (0x2b42b8 : word) = Some W_26e6cc.
Proof. vm_refl. Qed.
Lemma D_26e6cc : decode_any W_26e6cc = Some (Store SZ8 2 12 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e6d0 : bv 32 := 0x03810513.
Lemma F_26e6d0 : fetch_word Ubsan.M.loaded_segments (0x2b42bc : word) = Some W_26e6d0.
Proof. vm_refl. Qed.
Lemma D_26e6d0 : decode_any W_26e6d0 = Some (OpImm ALU_ADD 10 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e6d4 : bv 32 := 0x00858593.
Lemma F_26e6d4 : fetch_word Ubsan.M.loaded_segments (0x2b42c0 : word) = Some W_26e6d4.
Proof. vm_refl. Qed.
Lemma D_26e6d4 : decode_any W_26e6d4 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e6d8 : bv 32 := 0x00800613.
Lemma F_26e6d8 : fetch_word Ubsan.M.loaded_segments (0x2b42c4 : word) = Some W_26e6d8.
Proof. vm_refl. Qed.
Lemma D_26e6d8 : decode_any W_26e6d8 = Some (OpImm ALU_ADD 12 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e6dc : bv 32 := 0x55d070ef.
Lemma F_26e6dc : fetch_word Ubsan.M.loaded_segments (0x2b42c8 : word) = Some W_26e6dc.
Proof. vm_refl. Qed.
Lemma D_26e6dc : decode_any W_26e6dc = Some (Jal 1 32092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e6e0 : bv 32 := 0x02810593.
Lemma F_26e6e0 : fetch_word Ubsan.M.loaded_segments (0x2b42cc : word) = Some W_26e6e0.
Proof. vm_refl. Qed.
Lemma D_26e6e0 : decode_any W_26e6e0 = Some (OpImm ALU_ADD 11 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e6e4 : bv 32 := 0x00143513.
Lemma F_26e6e4 : fetch_word Ubsan.M.loaded_segments (0x2b42d0 : word) = Some W_26e6e4.
Proof. vm_refl. Qed.
Lemma D_26e6e4 : decode_any W_26e6e4 = Some (OpImm ALU_SLTU 10 8 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e6e8 : bv 32 := 0x00810613.
Lemma F_26e6e8 : fetch_word Ubsan.M.loaded_segments (0x2b42d4 : word) = Some W_26e6e8.
Proof. vm_refl. Qed.
Lemma D_26e6e8 : decode_any W_26e6e8 = Some (OpImm ALU_ADD 12 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e6ec : bv 32 := 0x08600893.
Lemma F_26e6ec : fetch_word Ubsan.M.loaded_segments (0x2b42d8 : word) = Some W_26e6ec.
Proof. vm_refl. Qed.
Lemma D_26e6ec : decode_any W_26e6ec = Some (OpImm ALU_ADD 17 0 134, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e6f0 : bv 32 := 0xfff50513.
Lemma F_26e6f0 : fetch_word Ubsan.M.loaded_segments (0x2b42dc : word) = Some W_26e6f0.
Proof. vm_refl. Qed.
Lemma D_26e6f0 : decode_any W_26e6f0 = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e6f4 : bv 32 := 0x00c57633.
Lemma F_26e6f4 : fetch_word Ubsan.M.loaded_segments (0x2b42e0 : word) = Some W_26e6f4.
Proof. vm_refl. Qed.
Lemma D_26e6f4 : decode_any W_26e6f4 = Some (Op ALU_AND 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e6f8 : bv 32 := 0x00800693.
Lemma F_26e6f8 : fetch_word Ubsan.M.loaded_segments (0x2b42e4 : word) = Some W_26e6f8.
Proof. vm_refl. Qed.
Lemma D_26e6f8 : decode_any W_26e6f8 = Some (OpImm ALU_ADD 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e6fc : bv 32 := 0x00048513.
Lemma F_26e6fc : fetch_word Ubsan.M.loaded_segments (0x2b42e8 : word) = Some W_26e6fc.
Proof. vm_refl. Qed.
Lemma D_26e6fc : decode_any W_26e6fc = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e700 : bv 32 := 0x00000073.
Lemma F_26e700 : fetch_word Ubsan.M.loaded_segments (0x2b42ec : word) = Some W_26e700.
Proof. vm_refl. Qed.
Lemma D_26e700 : decode_any W_26e700 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_26e700 : is_ecall W_26e700 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_26e704 : bv 32 := 0x00050493.
Lemma F_26e704 : fetch_word Ubsan.M.loaded_segments (0x2b42f0 : word) = Some W_26e704.
Proof. vm_refl. Qed.
Lemma D_26e704 : decode_any W_26e704 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e708 : bv 32 := 0x02040863.
Lemma F_26e708 : fetch_word Ubsan.M.loaded_segments (0x2b42f4 : word) = Some W_26e708.
Proof. vm_refl. Qed.
Lemma D_26e708 : decode_any W_26e708 = Some (Branch BC_EQ 8 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e70c : bv 32 := 0x02049513.
Lemma F_26e70c : fetch_word Ubsan.M.loaded_segments (0x2b42f8 : word) = Some W_26e70c.
Proof. vm_refl. Qed.
Lemma D_26e70c : decode_any W_26e70c = Some (ShiftImm ALU_SLL 10 9 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e710 : bv 32 := 0x02055513.
Lemma F_26e710 : fetch_word Ubsan.M.loaded_segments (0x2b42fc : word) = Some W_26e710.
Proof. vm_refl. Qed.
Lemma D_26e710 : decode_any W_26e710 = Some (ShiftImm ALU_SRL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e714 : bv 32 := 0x02051263.
Lemma F_26e714 : fetch_word Ubsan.M.loaded_segments (0x2b4300 : word) = Some W_26e714.
Proof. vm_refl. Qed.
Lemma D_26e714 : decode_any W_26e714 = Some (Branch BC_NE 10 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e718 : bv 32 := 0x00813503.
Lemma F_26e718 : fetch_word Ubsan.M.loaded_segments (0x2b4304 : word) = Some W_26e718.
Proof. vm_refl. Qed.
Lemma D_26e718 : decode_any W_26e718 = Some (Load SZ8 true 10 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e71c : bv 32 := 0x01013583.
Lemma F_26e71c : fetch_word Ubsan.M.loaded_segments (0x2b4308 : word) = Some W_26e71c.
Proof. vm_refl. Qed.
Lemma D_26e71c : decode_any W_26e71c = Some (Load SZ8 true 11 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e720 : bv 32 := 0x00a43023.
Lemma F_26e720 : fetch_word Ubsan.M.loaded_segments (0x2b430c : word) = Some W_26e720.
Proof. vm_refl. Qed.
Lemma D_26e720 : decode_any W_26e720 = Some (Store SZ8 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e724 : bv 32 := 0x08b42423.
Lemma F_26e724 : fetch_word Ubsan.M.loaded_segments (0x2b4310 : word) = Some W_26e724.
Proof. vm_refl. Qed.
Lemma D_26e724 : decode_any W_26e724 = Some (Store SZ4 8 11 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e728 : bv 32 := 0x00840513.
Lemma F_26e728 : fetch_word Ubsan.M.loaded_segments (0x2b4314 : word) = Some W_26e728.
Proof. vm_refl. Qed.
Lemma D_26e728 : decode_any W_26e728 = Some (OpImm ALU_ADD 10 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e72c : bv 32 := 0x01810593.
Lemma F_26e72c : fetch_word Ubsan.M.loaded_segments (0x2b4318 : word) = Some W_26e72c.
Proof. vm_refl. Qed.
Lemma D_26e72c : decode_any W_26e72c = Some (OpImm ALU_ADD 11 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e730 : bv 32 := 0x00800613.
Lemma F_26e730 : fetch_word Ubsan.M.loaded_segments (0x2b431c : word) = Some W_26e730.
Proof. vm_refl. Qed.
Lemma D_26e730 : decode_any W_26e730 = Some (OpImm ALU_ADD 12 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e734 : bv 32 := 0x505070ef.
Lemma F_26e734 : fetch_word Ubsan.M.loaded_segments (0x2b4320 : word) = Some W_26e734.
Proof. vm_refl. Qed.
Lemma D_26e734 : decode_any W_26e734 = Some (Jal 1 32004, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e738 : bv 32 := 0x0004851b.
Lemma F_26e738 : fetch_word Ubsan.M.loaded_segments (0x2b4324 : word) = Some W_26e738.
Proof. vm_refl. Qed.
Lemma D_26e738 : decode_any W_26e738 = Some (OpImm32 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e73c : bv 32 := 0xe1cfd0ef.
Lemma F_26e73c : fetch_word Ubsan.M.loaded_segments (0x2b4328 : word) = Some W_26e73c.
Proof. vm_refl. Qed.
Lemma D_26e73c : decode_any W_26e73c = Some (Jal 1 2086428, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e740 : bv 32 := 0x00093583.
Lemma F_26e740 : fetch_word Ubsan.M.loaded_segments (0x2b432c : word) = Some W_26e740.
Proof. vm_refl. Qed.
Lemma D_26e740 : decode_any W_26e740 = Some (Load SZ8 true 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e744 : bv 32 := 0x04813603.
Lemma F_26e744 : fetch_word Ubsan.M.loaded_segments (0x2b4330 : word) = Some W_26e744.
Proof. vm_refl. Qed.
Lemma D_26e744 : decode_any W_26e744 = Some (Load SZ8 true 12 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e748 : bv 32 := 0x02c59063.
Lemma F_26e748 : fetch_word Ubsan.M.loaded_segments (0x2b4334 : word) = Some W_26e748.
Proof. vm_refl. Qed.
Lemma D_26e748 : decode_any W_26e748 = Some (Branch BC_NE 11 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e74c : bv 32 := 0x0005051b.
Lemma F_26e74c : fetch_word Ubsan.M.loaded_segments (0x2b4338 : word) = Some W_26e74c.
Proof. vm_refl. Qed.
Lemma D_26e74c : decode_any W_26e74c = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e750 : bv 32 := 0x06813083.
Lemma F_26e750 : fetch_word Ubsan.M.loaded_segments (0x2b433c : word) = Some W_26e750.
Proof. vm_refl. Qed.
Lemma D_26e750 : decode_any W_26e750 = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e754 : bv 32 := 0x06013403.
Lemma F_26e754 : fetch_word Ubsan.M.loaded_segments (0x2b4340 : word) = Some W_26e754.
Proof. vm_refl. Qed.
Lemma D_26e754 : decode_any W_26e754 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e758 : bv 32 := 0x05813483.
Lemma F_26e758 : fetch_word Ubsan.M.loaded_segments (0x2b4344 : word) = Some W_26e758.
Proof. vm_refl. Qed.
Lemma D_26e758 : decode_any W_26e758 = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e75c : bv 32 := 0x05013903.
Lemma F_26e75c : fetch_word Ubsan.M.loaded_segments (0x2b4348 : word) = Some W_26e75c.
Proof. vm_refl. Qed.
Lemma D_26e75c : decode_any W_26e75c = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e760 : bv 32 := 0x07010113.
Lemma F_26e760 : fetch_word Ubsan.M.loaded_segments (0x2b434c : word) = Some W_26e760.
Proof. vm_refl. Qed.
Lemma D_26e760 : decode_any W_26e760 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e764 : bv 32 := 0x00008067.
Lemma F_26e764 : fetch_word Ubsan.M.loaded_segments (0x2b4350 : word) = Some W_26e764.
Proof. vm_refl. Qed.
Lemma D_26e764 : decode_any W_26e764 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26e768 : bv 32 := 0x9f0fd0ef.
Lemma F_26e768 : fetch_word Ubsan.M.loaded_segments (0x2b4354 : word) = Some W_26e768.
Proof. vm_refl. Qed.
Lemma D_26e768 : decode_any W_26e768 = Some (Jal 1 2085360, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ebd0 : bv 32 := 0x00008067.
Lemma F_26ebd0 : fetch_word Ubsan.M.loaded_segments (0x2b47bc : word) = Some W_26ebd0.
Proof. vm_refl. Qed.
Lemma D_26ebd0 : decode_any W_26ebd0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ebd4 : bv 32 := 0xff010113.
Lemma F_26ebd4 : fetch_word Ubsan.M.loaded_segments (0x2b47c0 : word) = Some W_26ebd4.
Proof. vm_refl. Qed.
Lemma D_26ebd4 : decode_any W_26ebd4 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ebd8 : bv 32 := 0x00113423.
Lemma F_26ebd8 : fetch_word Ubsan.M.loaded_segments (0x2b47c4 : word) = Some W_26ebd8.
Proof. vm_refl. Qed.
Lemma D_26ebd8 : decode_any W_26ebd8 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ebdc : bv 32 := 0x07852503.
Lemma F_26ebdc : fetch_word Ubsan.M.loaded_segments (0x2b47c8 : word) = Some W_26ebdc.
Proof. vm_refl. Qed.
Lemma D_26ebdc : decode_any W_26ebdc = Some (Load SZ4 true 10 10 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ebe0 : bv 32 := 0xff1ff0ef.
Lemma F_26ebe0 : fetch_word Ubsan.M.loaded_segments (0x2b47cc : word) = Some W_26ebe0.
Proof. vm_refl. Qed.
Lemma D_26ebe0 : decode_any W_26ebe0 = Some (Jal 1 2097136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ebe4 : bv 32 := 0x03900893.
Lemma F_26ebe4 : fetch_word Ubsan.M.loaded_segments (0x2b47d0 : word) = Some W_26ebe4.
Proof. vm_refl. Qed.
Lemma D_26ebe4 : decode_any W_26ebe4 = Some (OpImm ALU_ADD 17 0 57, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ebe8 : bv 32 := 0x00000073.
Lemma F_26ebe8 : fetch_word Ubsan.M.loaded_segments (0x2b47d4 : word) = Some W_26ebe8.
Proof. vm_refl. Qed.
Lemma D_26ebe8 : decode_any W_26ebe8 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_26ebe8 : is_ecall W_26ebe8 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_26ebec : bv 32 := 0x96cfd0ef.
Lemma F_26ebec : fetch_word Ubsan.M.loaded_segments (0x2b47d8 : word) = Some W_26ebec.
Proof. vm_refl. Qed.
Lemma D_26ebec : decode_any W_26ebec = Some (Jal 1 2085228, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ebf0 : bv 32 := 0x0005051b.
Lemma F_26ebf0 : fetch_word Ubsan.M.loaded_segments (0x2b47dc : word) = Some W_26ebf0.
Proof. vm_refl. Qed.
Lemma D_26ebf0 : decode_any W_26ebf0 = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ebf4 : bv 32 := 0x00813083.
Lemma F_26ebf4 : fetch_word Ubsan.M.loaded_segments (0x2b47e0 : word) = Some W_26ebf4.
Proof. vm_refl. Qed.
Lemma D_26ebf4 : decode_any W_26ebf4 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ebf8 : bv 32 := 0x01010113.
Lemma F_26ebf8 : fetch_word Ubsan.M.loaded_segments (0x2b47e4 : word) = Some W_26ebf8.
Proof. vm_refl. Qed.
Lemma D_26ebf8 : decode_any W_26ebf8 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ebfc : bv 32 := 0x00008067.
Lemma F_26ebfc : fetch_word Ubsan.M.loaded_segments (0x2b47e8 : word) = Some W_26ebfc.
Proof. vm_refl. Qed.
Lemma D_26ebfc : decode_any W_26ebfc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ed18 : bv 32 := 0x07852503.
Lemma F_26ed18 : fetch_word Ubsan.M.loaded_segments (0x2b4904 : word) = Some W_26ed18.
Proof. vm_refl. Qed.
Lemma D_26ed18 : decode_any W_26ed18 = Some (Load SZ4 true 10 10 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ed1c : bv 32 := 0x5e10b06f.
Lemma F_26ed1c : fetch_word Ubsan.M.loaded_segments (0x2b4908 : word) = Some W_26ed1c.
Proof. vm_refl. Qed.
Lemma D_26ed1c : decode_any W_26ed1c = Some (Jal 0 48608, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ee48 : bv 32 := 0x08c52603.
Lemma F_26ee48 : fetch_word Ubsan.M.loaded_segments (0x2b4a34 : word) = Some W_26ee48.
Proof. vm_refl. Qed.
Lemma D_26ee48 : decode_any W_26ee48 = Some (Load SZ4 true 12 10 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ee4c : bv 32 := 0x00020593.
Lemma F_26ee4c : fetch_word Ubsan.M.loaded_segments (0x2b4a38 : word) = Some W_26ee4c.
Proof. vm_refl. Qed.
Lemma D_26ee4c : decode_any W_26ee4c = Some (OpImm ALU_ADD 11 4 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ee50 : bv 32 := 0xf585a583.
Lemma F_26ee50 : fetch_word Ubsan.M.loaded_segments (0x2b4a3c : word) = Some W_26ee50.
Proof. vm_refl. Qed.
Lemma D_26ee50 : decode_any W_26ee50 = Some (Load SZ4 true 11 11 3928, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ee54 : bv 32 := 0xc00006b7.
Lemma F_26ee54 : fetch_word Ubsan.M.loaded_segments (0x2b4a40 : word) = Some W_26ee54.
Proof. vm_refl. Qed.
Lemma D_26ee54 : decode_any W_26ee54 = Some (Lui 13 786432, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ee58 : bv 32 := 0xfff6869b.
Lemma F_26ee58 : fetch_word Ubsan.M.loaded_segments (0x2b4a44 : word) = Some W_26ee58.
Proof. vm_refl. Qed.
Lemma D_26ee58 : decode_any W_26ee58 = Some (OpImm32 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ee5c : bv 32 := 0x00d67633.
Lemma F_26ee5c : fetch_word Ubsan.M.loaded_segments (0x2b4a48 : word) = Some W_26ee5c.
Proof. vm_refl. Qed.
Lemma D_26ee5c : decode_any W_26ee5c = Some (Op ALU_AND 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ee60 : bv 32 := 0x00b61663.
Lemma F_26ee60 : fetch_word Ubsan.M.loaded_segments (0x2b4a4c : word) = Some W_26ee60.
Proof. vm_refl. Qed.
Lemma D_26ee60 : decode_any W_26ee60 = Some (Branch BC_NE 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ee64 : bv 32 := 0x00000513.
Lemma F_26ee64 : fetch_word Ubsan.M.loaded_segments (0x2b4a50 : word) = Some W_26ee64.
Proof. vm_refl. Qed.
Lemma D_26ee64 : decode_any W_26ee64 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ee68 : bv 32 := 0x00008067.
Lemma F_26ee68 : fetch_word Ubsan.M.loaded_segments (0x2b4a54 : word) = Some W_26ee68.
Proof. vm_refl. Qed.
Lemma D_26ee68 : decode_any W_26ee68 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ee6c : bv 32 := 0x00000613.
Lemma F_26ee6c : fetch_word Ubsan.M.loaded_segments (0x2b4a58 : word) = Some W_26ee6c.
Proof. vm_refl. Qed.
Lemma D_26ee6c : decode_any W_26ee6c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ee70 : bv 32 := 0x08c50713.
Lemma F_26ee70 : fetch_word Ubsan.M.loaded_segments (0x2b4a5c : word) = Some W_26ee70.
Proof. vm_refl. Qed.
Lemma D_26ee70 : decode_any W_26ee70 = Some (OpImm ALU_ADD 14 10 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ee74 : bv 32 := 0x1607252f.
Lemma F_26ee74 : fetch_word Ubsan.M.loaded_segments (0x2b4a60 : word) = Some W_26ee74.
Proof. vm_refl. Qed.
Lemma D_26ee74 : decode_any W_26ee74 = Some (Lr AW true true 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ee78 : bv 32 := 0x00c51663.
Lemma F_26ee78 : fetch_word Ubsan.M.loaded_segments (0x2b4a64 : word) = Some W_26ee78.
Proof. vm_refl. Qed.
Lemma D_26ee78 : decode_any W_26ee78 = Some (Branch BC_NE 10 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ee7c : bv 32 := 0x1eb726af.
Lemma F_26ee7c : fetch_word Ubsan.M.loaded_segments (0x2b4a68 : word) = Some W_26ee7c.
Proof. vm_refl. Qed.
Lemma D_26ee7c : decode_any W_26ee7c = Some (Sc AW true true 13 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ee80 : bv 32 := 0xfe069ae3.
Lemma F_26ee80 : fetch_word Ubsan.M.loaded_segments (0x2b4a6c : word) = Some W_26ee80.
Proof. vm_refl. Qed.
Lemma D_26ee80 : decode_any W_26ee80 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ee84 : bv 32 := 0x0005061b.
Lemma F_26ee84 : fetch_word Ubsan.M.loaded_segments (0x2b4a70 : word) = Some W_26ee84.
Proof. vm_refl. Qed.
Lemma D_26ee84 : decode_any W_26ee84 = Some (OpImm32 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ee88 : bv 32 := 0x00100513.
Lemma F_26ee88 : fetch_word Ubsan.M.loaded_segments (0x2b4a74 : word) = Some W_26ee88.
Proof. vm_refl. Qed.
Lemma D_26ee88 : decode_any W_26ee88 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ee8c : bv 32 := 0x0a060a63.
Lemma F_26ee8c : fetch_word Ubsan.M.loaded_segments (0x2b4a78 : word) = Some W_26ee8c.
Proof. vm_refl. Qed.
Lemma D_26ee8c : decode_any W_26ee8c = Some (Branch BC_EQ 12 0 180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ee90 : bv 32 := 0x00000693.
Lemma F_26ee90 : fetch_word Ubsan.M.loaded_segments (0x2b4a7c : word) = Some W_26ee90.
Proof. vm_refl. Qed.
Lemma D_26ee90 : decode_any W_26ee90 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ee94 : bv 32 := 0x400007b7.
Lemma F_26ee94 : fetch_word Ubsan.M.loaded_segments (0x2b4a80 : word) = Some W_26ee94.
Proof. vm_refl. Qed.
Lemma D_26ee94 : decode_any W_26ee94 = Some (Lui 15 262144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ee98 : bv 32 := 0x00f5e833.
Lemma F_26ee98 : fetch_word Ubsan.M.loaded_segments (0x2b4a84 : word) = Some W_26ee98.
Proof. vm_refl. Qed.
Lemma D_26ee98 : decode_any W_26ee98 = Some (Op ALU_OR 16 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ee9c : bv 32 := 0x1607262f.
Lemma F_26ee9c : fetch_word Ubsan.M.loaded_segments (0x2b4a88 : word) = Some W_26ee9c.
Proof. vm_refl. Qed.
Lemma D_26ee9c : decode_any W_26ee9c = Some (Lr AW true true 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eea0 : bv 32 := 0x00d61663.
Lemma F_26eea0 : fetch_word Ubsan.M.loaded_segments (0x2b4a8c : word) = Some W_26eea0.
Proof. vm_refl. Qed.
Lemma D_26eea0 : decode_any W_26eea0 = Some (Branch BC_NE 12 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eea4 : bv 32 := 0x1f0725af.
Lemma F_26eea4 : fetch_word Ubsan.M.loaded_segments (0x2b4a90 : word) = Some W_26eea4.
Proof. vm_refl. Qed.
Lemma D_26eea4 : decode_any W_26eea4 = Some (Sc AW true true 11 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eea8 : bv 32 := 0xfe059ae3.
Lemma F_26eea8 : fetch_word Ubsan.M.loaded_segments (0x2b4a94 : word) = Some W_26eea8.
Proof. vm_refl. Qed.
Lemma D_26eea8 : decode_any W_26eea8 = Some (Branch BC_NE 11 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eeac : bv 32 := 0x0006059b.
Lemma F_26eeac : fetch_word Ubsan.M.loaded_segments (0x2b4a98 : word) = Some W_26eeac.
Proof. vm_refl. Qed.
Lemma D_26eeac : decode_any W_26eeac = Some (OpImm32 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eeb0 : bv 32 := 0x08058863.
Lemma F_26eeb0 : fetch_word Ubsan.M.loaded_segments (0x2b4a9c : word) = Some W_26eeb0.
Proof. vm_refl. Qed.
Lemma D_26eeb0 : decode_any W_26eeb0 = Some (Branch BC_EQ 11 0 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eeb4 : bv 32 := 0x00000293.
Lemma F_26eeb4 : fetch_word Ubsan.M.loaded_segments (0x2b4aa0 : word) = Some W_26eeb4.
Proof. vm_refl. Qed.
Lemma D_26eeb4 : decode_any W_26eeb4 = Some (OpImm ALU_ADD 5 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eeb8 : bv 32 := 0xfda00313.
Lemma F_26eeb8 : fetch_word Ubsan.M.loaded_segments (0x2b4aa4 : word) = Some W_26eeb8.
Proof. vm_refl. Qed.
Lemma D_26eeb8 : decode_any W_26eeb8 = Some (OpImm ALU_ADD 6 0 4058, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eebc : bv 32 := 0x01c0006f.
Lemma F_26eebc : fetch_word Ubsan.M.loaded_segments (0x2b4aa8 : word) = Some W_26eebc.
Proof. vm_refl. Qed.
Lemma D_26eebc : decode_any W_26eebc = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eec0 : bv 32 := 0x1607262f.
Lemma F_26eec0 : fetch_word Ubsan.M.loaded_segments (0x2b4aac : word) = Some W_26eec0.
Proof. vm_refl. Qed.
Lemma D_26eec0 : decode_any W_26eec0 = Some (Lr AW true true 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eec4 : bv 32 := 0x00561663.
Lemma F_26eec4 : fetch_word Ubsan.M.loaded_segments (0x2b4ab0 : word) = Some W_26eec4.
Proof. vm_refl. Qed.
Lemma D_26eec4 : decode_any W_26eec4 = Some (Branch BC_NE 12 5 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eec8 : bv 32 := 0x1f07252f.
Lemma F_26eec8 : fetch_word Ubsan.M.loaded_segments (0x2b4ab4 : word) = Some W_26eec8.
Proof. vm_refl. Qed.
Lemma D_26eec8 : decode_any W_26eec8 = Some (Sc AW true true 10 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eecc : bv 32 := 0xfe051ae3.
Lemma F_26eecc : fetch_word Ubsan.M.loaded_segments (0x2b4ab8 : word) = Some W_26eecc.
Proof. vm_refl. Qed.
Lemma D_26eecc : decode_any W_26eecc = Some (Branch BC_NE 10 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eed0 : bv 32 := 0x0006051b.
Lemma F_26eed0 : fetch_word Ubsan.M.loaded_segments (0x2b4abc : word) = Some W_26eed0.
Proof. vm_refl. Qed.
Lemma D_26eed0 : decode_any W_26eed0 = Some (OpImm32 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eed4 : bv 32 := 0x06050463.
Lemma F_26eed4 : fetch_word Ubsan.M.loaded_segments (0x2b4ac0 : word) = Some W_26eed4.
Proof. vm_refl. Qed.
Lemma D_26eed4 : decode_any W_26eed4 = Some (Branch BC_EQ 10 0 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eed8 : bv 32 := 0x02161513.
Lemma F_26eed8 : fetch_word Ubsan.M.loaded_segments (0x2b4ac4 : word) = Some W_26eed8.
Proof. vm_refl. Qed.
Lemma D_26eed8 : decode_any W_26eed8 = Some (ShiftImm ALU_SLL 10 12 33, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eedc : bv 32 := 0x02054663.
Lemma F_26eedc : fetch_word Ubsan.M.loaded_segments (0x2b4ac8 : word) = Some W_26eedc.
Proof. vm_refl. Qed.
Lemma D_26eedc : decode_any W_26eedc = Some (Branch BC_LT 10 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eee0 : bv 32 := 0x00f66533.
Lemma F_26eee0 : fetch_word Ubsan.M.loaded_segments (0x2b4acc : word) = Some W_26eee0.
Proof. vm_refl. Qed.
Lemma D_26eee0 : decode_any W_26eee0 = Some (Op ALU_OR 10 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eee4 : bv 32 := 0x0006059b.
Lemma F_26eee4 : fetch_word Ubsan.M.loaded_segments (0x2b4ad0 : word) = Some W_26eee4.
Proof. vm_refl. Qed.
Lemma D_26eee4 : decode_any W_26eee4 = Some (OpImm32 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eee8 : bv 32 := 0x0005061b.
Lemma F_26eee8 : fetch_word Ubsan.M.loaded_segments (0x2b4ad4 : word) = Some W_26eee8.
Proof. vm_refl. Qed.
Lemma D_26eee8 : decode_any W_26eee8 = Some (OpImm32 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eeec : bv 32 := 0x1607252f.
Lemma F_26eeec : fetch_word Ubsan.M.loaded_segments (0x2b4ad8 : word) = Some W_26eeec.
Proof. vm_refl. Qed.
Lemma D_26eeec : decode_any W_26eeec = Some (Lr AW true true 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eef0 : bv 32 := 0x00b51663.
Lemma F_26eef0 : fetch_word Ubsan.M.loaded_segments (0x2b4adc : word) = Some W_26eef0.
Proof. vm_refl. Qed.
Lemma D_26eef0 : decode_any W_26eef0 = Some (Branch BC_NE 10 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eef4 : bv 32 := 0x1ec726af.
Lemma F_26eef4 : fetch_word Ubsan.M.loaded_segments (0x2b4ae0 : word) = Some W_26eef4.
Proof. vm_refl. Qed.
Lemma D_26eef4 : decode_any W_26eef4 = Some (Sc AW true true 13 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eef8 : bv 32 := 0xfe069ae3.
Lemma F_26eef8 : fetch_word Ubsan.M.loaded_segments (0x2b4ae4 : word) = Some W_26eef8.
Proof. vm_refl. Qed.
Lemma D_26eef8 : decode_any W_26eef8 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26eefc : bv 32 := 0x0005051b.
Lemma F_26eefc : fetch_word Ubsan.M.loaded_segments (0x2b4ae8 : word) = Some W_26eefc.
Proof. vm_refl. Qed.
Lemma D_26eefc : decode_any W_26eefc = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef00 : bv 32 := 0xfcb510e3.
Lemma F_26ef00 : fetch_word Ubsan.M.loaded_segments (0x2b4aec : word) = Some W_26ef00.
Proof. vm_refl. Qed.
Lemma D_26ef00 : decode_any W_26ef00 = Some (Branch BC_NE 10 11 8128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef04 : bv 32 := 0x0080006f.
Lemma F_26ef04 : fetch_word Ubsan.M.loaded_segments (0x2b4af0 : word) = Some W_26ef04.
Proof. vm_refl. Qed.
Lemma D_26ef04 : decode_any W_26ef04 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef08 : bv 32 := 0x0006061b.
Lemma F_26ef08 : fetch_word Ubsan.M.loaded_segments (0x2b4af4 : word) = Some W_26ef08.
Proof. vm_refl. Qed.
Lemma D_26ef08 : decode_any W_26ef08 = Some (OpImm32 12 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef0c : bv 32 := 0x06200893.
Lemma F_26ef0c : fetch_word Ubsan.M.loaded_segments (0x2b4af8 : word) = Some W_26ef0c.
Proof. vm_refl. Qed.
Lemma D_26ef0c : decode_any W_26ef0c = Some (OpImm ALU_ADD 17 0 98, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef10 : bv 32 := 0x08000593.
Lemma F_26ef10 : fetch_word Ubsan.M.loaded_segments (0x2b4afc : word) = Some W_26ef10.
Proof. vm_refl. Qed.
Lemma D_26ef10 : decode_any W_26ef10 = Some (OpImm ALU_ADD 11 0 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef14 : bv 32 := 0x00070513.
Lemma F_26ef14 : fetch_word Ubsan.M.loaded_segments (0x2b4b00 : word) = Some W_26ef14.
Proof. vm_refl. Qed.
Lemma D_26ef14 : decode_any W_26ef14 = Some (OpImm ALU_ADD 10 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef18 : bv 32 := 0x00000693.
Lemma F_26ef18 : fetch_word Ubsan.M.loaded_segments (0x2b4b04 : word) = Some W_26ef18.
Proof. vm_refl. Qed.
Lemma D_26ef18 : decode_any W_26ef18 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef1c : bv 32 := 0x00000073.
Lemma F_26ef1c : fetch_word Ubsan.M.loaded_segments (0x2b4b08 : word) = Some W_26ef1c.
Proof. vm_refl. Qed.
Lemma D_26ef1c : decode_any W_26ef1c = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_26ef1c : is_ecall W_26ef1c = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_26ef20 : bv 32 := 0xfa6510e3.
Lemma F_26ef20 : fetch_word Ubsan.M.loaded_segments (0x2b4b0c : word) = Some W_26ef20.
Proof. vm_refl. Qed.
Lemma D_26ef20 : decode_any W_26ef20 = Some (Branch BC_NE 10 6 8096, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef24 : bv 32 := 0x06200893.
Lemma F_26ef24 : fetch_word Ubsan.M.loaded_segments (0x2b4b10 : word) = Some W_26ef24.
Proof. vm_refl. Qed.
Lemma D_26ef24 : decode_any W_26ef24 = Some (OpImm ALU_ADD 17 0 98, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef28 : bv 32 := 0x00070513.
Lemma F_26ef28 : fetch_word Ubsan.M.loaded_segments (0x2b4b14 : word) = Some W_26ef28.
Proof. vm_refl. Qed.
Lemma D_26ef28 : decode_any W_26ef28 = Some (OpImm ALU_ADD 10 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef2c : bv 32 := 0x00000593.
Lemma F_26ef2c : fetch_word Ubsan.M.loaded_segments (0x2b4b18 : word) = Some W_26ef2c.
Proof. vm_refl. Qed.
Lemma D_26ef2c : decode_any W_26ef2c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef30 : bv 32 := 0x00000693.
Lemma F_26ef30 : fetch_word Ubsan.M.loaded_segments (0x2b4b1c : word) = Some W_26ef30.
Proof. vm_refl. Qed.
Lemma D_26ef30 : decode_any W_26ef30 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef34 : bv 32 := 0x00000073.
Lemma F_26ef34 : fetch_word Ubsan.M.loaded_segments (0x2b4b20 : word) = Some W_26ef34.
Proof. vm_refl. Qed.
Lemma D_26ef34 : decode_any W_26ef34 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_26ef34 : is_ecall W_26ef34 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_26ef38 : bv 32 := 0xf89ff06f.
Lemma F_26ef38 : fetch_word Ubsan.M.loaded_segments (0x2b4b24 : word) = Some W_26ef38.
Proof. vm_refl. Qed.
Lemma D_26ef38 : decode_any W_26ef38 = Some (Jal 0 2097032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef3c : bv 32 := 0x00100513.
Lemma F_26ef3c : fetch_word Ubsan.M.loaded_segments (0x2b4b28 : word) = Some W_26ef3c.
Proof. vm_refl. Qed.
Lemma D_26ef3c : decode_any W_26ef3c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef40 : bv 32 := 0x00008067.
Lemma F_26ef40 : fetch_word Ubsan.M.loaded_segments (0x2b4b2c : word) = Some W_26ef40.
Proof. vm_refl. Qed.
Lemma D_26ef40 : decode_any W_26ef40 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef44 : bv 32 := 0x00000593.
Lemma F_26ef44 : fetch_word Ubsan.M.loaded_segments (0x2b4b30 : word) = Some W_26ef44.
Proof. vm_refl. Qed.
Lemma D_26ef44 : decode_any W_26ef44 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef48 : bv 32 := 0x08c50693.
Lemma F_26ef48 : fetch_word Ubsan.M.loaded_segments (0x2b4b34 : word) = Some W_26ef48.
Proof. vm_refl. Qed.
Lemma D_26ef48 : decode_any W_26ef48 = Some (OpImm ALU_ADD 13 10 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef4c : bv 32 := 0x0006a503.
Lemma F_26ef4c : fetch_word Ubsan.M.loaded_segments (0x2b4b38 : word) = Some W_26ef4c.
Proof. vm_refl. Qed.
Lemma D_26ef4c : decode_any W_26ef4c = Some (Load SZ4 true 10 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef50 : bv 32 := 0x1606a62f.
Lemma F_26ef50 : fetch_word Ubsan.M.loaded_segments (0x2b4b3c : word) = Some W_26ef50.
Proof. vm_refl. Qed.
Lemma D_26ef50 : decode_any W_26ef50 = Some (Lr AW true true 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef54 : bv 32 := 0x00a61663.
Lemma F_26ef54 : fetch_word Ubsan.M.loaded_segments (0x2b4b40 : word) = Some W_26ef54.
Proof. vm_refl. Qed.
Lemma D_26ef54 : decode_any W_26ef54 = Some (Branch BC_NE 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef58 : bv 32 := 0x1eb6a72f.
Lemma F_26ef58 : fetch_word Ubsan.M.loaded_segments (0x2b4b44 : word) = Some W_26ef58.
Proof. vm_refl. Qed.
Lemma D_26ef58 : decode_any W_26ef58 = Some (Sc AW true true 14 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef5c : bv 32 := 0xfe071ae3.
Lemma F_26ef5c : fetch_word Ubsan.M.loaded_segments (0x2b4b48 : word) = Some W_26ef5c.
Proof. vm_refl. Qed.
Lemma D_26ef5c : decode_any W_26ef5c = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef60 : bv 32 := 0x0006061b.
Lemma F_26ef60 : fetch_word Ubsan.M.loaded_segments (0x2b4b4c : word) = Some W_26ef60.
Proof. vm_refl. Qed.
Lemma D_26ef60 : decode_any W_26ef60 = Some (OpImm32 12 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef64 : bv 32 := 0xfea614e3.
Lemma F_26ef64 : fetch_word Ubsan.M.loaded_segments (0x2b4b50 : word) = Some W_26ef64.
Proof. vm_refl. Qed.
Lemma D_26ef64 : decode_any W_26ef64 = Some (Branch BC_NE 12 10 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef68 : bv 32 := 0x02151513.
Lemma F_26ef68 : fetch_word Ubsan.M.loaded_segments (0x2b4b54 : word) = Some W_26ef68.
Proof. vm_refl. Qed.
Lemma D_26ef68 : decode_any W_26ef68 = Some (ShiftImm ALU_SLL 10 10 33, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef6c : bv 32 := 0x02055a63.
Lemma F_26ef6c : fetch_word Ubsan.M.loaded_segments (0x2b4b58 : word) = Some W_26ef6c.
Proof. vm_refl. Qed.
Lemma D_26ef6c : decode_any W_26ef6c = Some (Branch BC_GE 10 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef70 : bv 32 := 0x06200893.
Lemma F_26ef70 : fetch_word Ubsan.M.loaded_segments (0x2b4b5c : word) = Some W_26ef70.
Proof. vm_refl. Qed.
Lemma D_26ef70 : decode_any W_26ef70 = Some (OpImm ALU_ADD 17 0 98, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef74 : bv 32 := 0x08100593.
Lemma F_26ef74 : fetch_word Ubsan.M.loaded_segments (0x2b4b60 : word) = Some W_26ef74.
Proof. vm_refl. Qed.
Lemma D_26ef74 : decode_any W_26ef74 = Some (OpImm ALU_ADD 11 0 129, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef78 : bv 32 := 0x00100613.
Lemma F_26ef78 : fetch_word Ubsan.M.loaded_segments (0x2b4b64 : word) = Some W_26ef78.
Proof. vm_refl. Qed.
Lemma D_26ef78 : decode_any W_26ef78 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef7c : bv 32 := 0xfda00713.
Lemma F_26ef7c : fetch_word Ubsan.M.loaded_segments (0x2b4b68 : word) = Some W_26ef7c.
Proof. vm_refl. Qed.
Lemma D_26ef7c : decode_any W_26ef7c = Some (OpImm ALU_ADD 14 0 4058, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef80 : bv 32 := 0x00068513.
Lemma F_26ef80 : fetch_word Ubsan.M.loaded_segments (0x2b4b6c : word) = Some W_26ef80.
Proof. vm_refl. Qed.
Lemma D_26ef80 : decode_any W_26ef80 = Some (OpImm ALU_ADD 10 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef84 : bv 32 := 0x00000073.
Lemma F_26ef84 : fetch_word Ubsan.M.loaded_segments (0x2b4b70 : word) = Some W_26ef84.
Proof. vm_refl. Qed.
Lemma D_26ef84 : decode_any W_26ef84 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_26ef84 : is_ecall W_26ef84 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_26ef88 : bv 32 := 0x00e51c63.
Lemma F_26ef88 : fetch_word Ubsan.M.loaded_segments (0x2b4b74 : word) = Some W_26ef88.
Proof. vm_refl. Qed.
Lemma D_26ef88 : decode_any W_26ef88 = Some (Branch BC_NE 10 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef8c : bv 32 := 0x06200893.
Lemma F_26ef8c : fetch_word Ubsan.M.loaded_segments (0x2b4b78 : word) = Some W_26ef8c.
Proof. vm_refl. Qed.
Lemma D_26ef8c : decode_any W_26ef8c = Some (OpImm ALU_ADD 17 0 98, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef90 : bv 32 := 0x00100593.
Lemma F_26ef90 : fetch_word Ubsan.M.loaded_segments (0x2b4b7c : word) = Some W_26ef90.
Proof. vm_refl. Qed.
Lemma D_26ef90 : decode_any W_26ef90 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef94 : bv 32 := 0x00100613.
Lemma F_26ef94 : fetch_word Ubsan.M.loaded_segments (0x2b4b80 : word) = Some W_26ef94.
Proof. vm_refl. Qed.
Lemma D_26ef94 : decode_any W_26ef94 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef98 : bv 32 := 0x00068513.
Lemma F_26ef98 : fetch_word Ubsan.M.loaded_segments (0x2b4b84 : word) = Some W_26ef98.
Proof. vm_refl. Qed.
Lemma D_26ef98 : decode_any W_26ef98 = Some (OpImm ALU_ADD 10 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26ef9c : bv 32 := 0x00000073.
Lemma F_26ef9c : fetch_word Ubsan.M.loaded_segments (0x2b4b88 : word) = Some W_26ef9c.
Proof. vm_refl. Qed.
Lemma D_26ef9c : decode_any W_26ef9c = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_26ef9c : is_ecall W_26ef9c = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_26efa0 : bv 32 := 0x00008067.
Lemma F_26efa0 : fetch_word Ubsan.M.loaded_segments (0x2b4b8c : word) = Some W_26efa0.
Proof. vm_refl. Qed.
Lemma D_26efa0 : decode_any W_26efa0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
