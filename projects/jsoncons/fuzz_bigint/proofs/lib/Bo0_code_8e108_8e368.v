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

Definition W_8e108 : bv 32 := 0xf4010113.
Lemma F_8e108 : fetch_word AsanUbsan.M.loaded_segments (0x8e108 : word) = Some W_8e108.
Proof. vm_refl. Qed.
Lemma D_8e108 : decode_any W_8e108 = Some (OpImm ALU_ADD 2 2 3904, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e10c : bv 32 := 0x00013023.
Lemma F_8e10c : fetch_word AsanUbsan.M.loaded_segments (0x8e10c : word) = Some W_8e10c.
Proof. vm_refl. Qed.
Lemma D_8e10c : decode_any W_8e10c = Some (Store SZ8 2 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e110 : bv 32 := 0x0a113c23.
Lemma F_8e110 : fetch_word AsanUbsan.M.loaded_segments (0x8e110 : word) = Some W_8e110.
Proof. vm_refl. Qed.
Lemma D_8e110 : decode_any W_8e110 = Some (Store SZ8 2 1 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e114 : bv 32 := 0x0a813823.
Lemma F_8e114 : fetch_word AsanUbsan.M.loaded_segments (0x8e114 : word) = Some W_8e114.
Proof. vm_refl. Qed.
Lemma D_8e114 : decode_any W_8e114 = Some (Store SZ8 2 8 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e118 : bv 32 := 0x0a913423.
Lemma F_8e118 : fetch_word AsanUbsan.M.loaded_segments (0x8e118 : word) = Some W_8e118.
Proof. vm_refl. Qed.
Lemma D_8e118 : decode_any W_8e118 = Some (Store SZ8 2 9 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e11c : bv 32 := 0x0b213023.
Lemma F_8e11c : fetch_word AsanUbsan.M.loaded_segments (0x8e11c : word) = Some W_8e11c.
Proof. vm_refl. Qed.
Lemma D_8e11c : decode_any W_8e11c = Some (Store SZ8 2 18 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e120 : bv 32 := 0x09313c23.
Lemma F_8e120 : fetch_word AsanUbsan.M.loaded_segments (0x8e120 : word) = Some W_8e120.
Proof. vm_refl. Qed.
Lemma D_8e120 : decode_any W_8e120 = Some (Store SZ8 2 19 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e124 : bv 32 := 0x09413823.
Lemma F_8e124 : fetch_word AsanUbsan.M.loaded_segments (0x8e124 : word) = Some W_8e124.
Proof. vm_refl. Qed.
Lemma D_8e124 : decode_any W_8e124 = Some (Store SZ8 2 20 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e128 : bv 32 := 0x09513423.
Lemma F_8e128 : fetch_word AsanUbsan.M.loaded_segments (0x8e128 : word) = Some W_8e128.
Proof. vm_refl. Qed.
Lemma D_8e128 : decode_any W_8e128 = Some (Store SZ8 2 21 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e12c : bv 32 := 0x09613023.
Lemma F_8e12c : fetch_word AsanUbsan.M.loaded_segments (0x8e12c : word) = Some W_8e12c.
Proof. vm_refl. Qed.
Lemma D_8e12c : decode_any W_8e12c = Some (Store SZ8 2 22 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e130 : bv 32 := 0x07713c23.
Lemma F_8e130 : fetch_word AsanUbsan.M.loaded_segments (0x8e130 : word) = Some W_8e130.
Proof. vm_refl. Qed.
Lemma D_8e130 : decode_any W_8e130 = Some (Store SZ8 2 23 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e134 : bv 32 := 0x07813823.
Lemma F_8e134 : fetch_word AsanUbsan.M.loaded_segments (0x8e134 : word) = Some W_8e134.
Proof. vm_refl. Qed.
Lemma D_8e134 : decode_any W_8e134 = Some (Store SZ8 2 24 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e138 : bv 32 := 0x07913423.
Lemma F_8e138 : fetch_word AsanUbsan.M.loaded_segments (0x8e138 : word) = Some W_8e138.
Proof. vm_refl. Qed.
Lemma D_8e138 : decode_any W_8e138 = Some (Store SZ8 2 25 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e13c : bv 32 := 0x07a13023.
Lemma F_8e13c : fetch_word AsanUbsan.M.loaded_segments (0x8e13c : word) = Some W_8e13c.
Proof. vm_refl. Qed.
Lemma D_8e13c : decode_any W_8e13c = Some (Store SZ8 2 26 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e140 : bv 32 := 0x05b13c23.
Lemma F_8e140 : fetch_word AsanUbsan.M.loaded_segments (0x8e140 : word) = Some W_8e140.
Proof. vm_refl. Qed.
Lemma D_8e140 : decode_any W_8e140 = Some (Store SZ8 2 27 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e144 : bv 32 := 0x0c010413.
Lemma F_8e144 : fetch_word AsanUbsan.M.loaded_segments (0x8e144 : word) = Some W_8e144.
Proof. vm_refl. Qed.
Lemma D_8e144 : decode_any W_8e144 = Some (OpImm ALU_ADD 8 2 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e148 : bv 32 := 0xfe017113.
Lemma F_8e148 : fetch_word AsanUbsan.M.loaded_segments (0x8e148 : word) = Some W_8e148.
Proof. vm_refl. Qed.
Lemma D_8e148 : decode_any W_8e148 = Some (OpImm ALU_AND 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e14c : bv 32 := 0x00010493.
Lemma F_8e14c : fetch_word AsanUbsan.M.loaded_segments (0x8e14c : word) = Some W_8e14c.
Proof. vm_refl. Qed.
Lemma D_8e14c : decode_any W_8e14c = Some (OpImm ALU_ADD 9 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e150 : bv 32 := 0x00058a93.
Lemma F_8e150 : fetch_word AsanUbsan.M.loaded_segments (0x8e150 : word) = Some W_8e150.
Proof. vm_refl. Qed.
Lemma D_8e150 : decode_any W_8e150 = Some (OpImm ALU_ADD 21 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e154 : bv 32 := 0x00048597.
Lemma F_8e154 : fetch_word AsanUbsan.M.loaded_segments (0x8e154 : word) = Some W_8e154.
Proof. vm_refl. Qed.
Lemma D_8e154 : decode_any W_8e154 = Some (Auipc 11 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e158 : bv 32 := 0x00048617.
Lemma F_8e158 : fetch_word AsanUbsan.M.loaded_segments (0x8e158 : word) = Some W_8e158.
Proof. vm_refl. Qed.
Lemma D_8e158 : decode_any W_8e158 = Some (Auipc 12 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e15c : bv 32 := 0x3c863603.
Lemma F_8e15c : fetch_word AsanUbsan.M.loaded_segments (0x8e15c : word) = Some W_8e15c.
Proof. vm_refl. Qed.
Lemma D_8e15c : decode_any W_8e15c = Some (Load SZ8 true 12 12 968, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e160 : bv 32 := 0x3745b583.
Lemma F_8e160 : fetch_word AsanUbsan.M.loaded_segments (0x8e160 : word) = Some W_8e160.
Proof. vm_refl. Qed.
Lemma D_8e160 : decode_any W_8e160 = Some (Load SZ8 true 11 11 884, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e164 : bv 32 := 0x00062603.
Lemma F_8e164 : fetch_word AsanUbsan.M.loaded_segments (0x8e164 : word) = Some W_8e164.
Proof. vm_refl. Qed.
Lemma D_8e164 : decode_any W_8e164 = Some (Load SZ4 true 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e168 : bv 32 := 0x0005b903.
Lemma F_8e168 : fetch_word AsanUbsan.M.loaded_segments (0x8e168 : word) = Some W_8e168.
Proof. vm_refl. Qed.
Lemma D_8e168 : decode_any W_8e168 = Some (Load SZ8 true 18 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e16c : bv 32 := 0x00050b13.
Lemma F_8e16c : fetch_word AsanUbsan.M.loaded_segments (0x8e16c : word) = Some W_8e16c.
Proof. vm_refl. Qed.
Lemma D_8e16c : decode_any W_8e16c = Some (OpImm ALU_ADD 22 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e170 : bv 32 := 0x00060a63.
Lemma F_8e170 : fetch_word AsanUbsan.M.loaded_segments (0x8e170 : word) = Some W_8e170.
Proof. vm_refl. Qed.
Lemma D_8e170 : decode_any W_8e170 = Some (Branch BC_EQ 12 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e174 : bv 32 := 0x16000513.
Lemma F_8e174 : fetch_word AsanUbsan.M.loaded_segments (0x8e174 : word) = Some W_8e174.
Proof. vm_refl. Qed.
Lemma D_8e174 : decode_any W_8e174 = Some (OpImm ALU_ADD 10 0 352, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e178 : bv 32 := 0xdedba0ef.
Lemma F_8e178 : fetch_word AsanUbsan.M.loaded_segments (0x8e178 : word) = Some W_8e178.
Proof. vm_refl. Qed.
Lemma D_8e178 : decode_any W_8e178 = Some (Jal 1 1813996, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e17c : bv 32 := 0x00050993.
Lemma F_8e17c : fetch_word AsanUbsan.M.loaded_segments (0x8e17c : word) = Some W_8e17c.
Proof. vm_refl. Qed.
Lemma D_8e17c : decode_any W_8e17c = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e180 : bv 32 := 0x0080006f.
Lemma F_8e180 : fetch_word AsanUbsan.M.loaded_segments (0x8e180 : word) = Some W_8e180.
Proof. vm_refl. Qed.
Lemma D_8e180 : decode_any W_8e180 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e184 : bv 32 := 0x00000993.
Lemma F_8e184 : fetch_word AsanUbsan.M.loaded_segments (0x8e184 : word) = Some W_8e184.
Proof. vm_refl. Qed.
Lemma D_8e184 : decode_any W_8e184 = Some (OpImm ALU_ADD 19 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e188 : bv 32 := 0x00098d93.
Lemma F_8e188 : fetch_word AsanUbsan.M.loaded_segments (0x8e188 : word) = Some W_8e188.
Proof. vm_refl. Qed.
Lemma D_8e188 : decode_any W_8e188 = Some (OpImm ALU_ADD 27 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e18c : bv 32 := 0x02099063.
Lemma F_8e18c : fetch_word AsanUbsan.M.loaded_segments (0x8e18c : word) = Some W_8e18c.
Proof. vm_refl. Qed.
Lemma D_8e18c : decode_any W_8e18c = Some (Branch BC_NE 19 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e190 : bv 32 := 0xea010513.
Lemma F_8e190 : fetch_word AsanUbsan.M.loaded_segments (0x8e190 : word) = Some W_8e190.
Proof. vm_refl. Qed.
Lemma D_8e190 : decode_any W_8e190 = Some (OpImm ALU_ADD 10 2 3744, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e194 : bv 32 := 0xfe057d93.
Lemma F_8e194 : fetch_word AsanUbsan.M.loaded_segments (0x8e194 : word) = Some W_8e194.
Proof. vm_refl. Qed.
Lemma D_8e194 : decode_any W_8e194 = Some (OpImm ALU_AND 27 10 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e198 : bv 32 := 0x00001537.
Lemma F_8e198 : fetch_word AsanUbsan.M.loaded_segments (0x8e198 : word) = Some W_8e198.
Proof. vm_refl. Qed.
Lemma D_8e198 : decode_any W_8e198 = Some (Lui 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e19c : bv 32 := 0x40a10133.
Lemma F_8e19c : fetch_word AsanUbsan.M.loaded_segments (0x8e19c : word) = Some W_8e19c.
Proof. vm_refl. Qed.
Lemma D_8e19c : decode_any W_8e19c = Some (Op ALU_SUB 2 2 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e1a0 : bv 32 := 0x00013023.
Lemma F_8e1a0 : fetch_word AsanUbsan.M.loaded_segments (0x8e1a0 : word) = Some W_8e1a0.
Proof. vm_refl. Qed.
Lemma D_8e1a0 : decode_any W_8e1a0 = Some (Store SZ8 2 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e1a4 : bv 32 := 0xfe2dcce3.
Lemma F_8e1a4 : fetch_word AsanUbsan.M.loaded_segments (0x8e1a4 : word) = Some W_8e1a4.
Proof. vm_refl. Qed.
Lemma D_8e1a4 : decode_any W_8e1a4 = Some (Branch BC_LT 27 2 8184, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e1a8 : bv 32 := 0x000d8113.
Lemma F_8e1a8 : fetch_word AsanUbsan.M.loaded_segments (0x8e1a8 : word) = Some W_8e1a8.
Proof. vm_refl. Qed.
Lemma D_8e1a8 : decode_any W_8e1a8 = Some (OpImm ALU_ADD 2 27 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e1ac : bv 32 := 0x01b4b823.
Lemma F_8e1ac : fetch_word AsanUbsan.M.loaded_segments (0x8e1ac : word) = Some W_8e1ac.
Proof. vm_refl. Qed.
Lemma D_8e1ac : decode_any W_8e1ac = Some (Store SZ8 9 27 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e1b0 : bv 32 := 0x020d8a13.
Lemma F_8e1b0 : fetch_word AsanUbsan.M.loaded_segments (0x8e1b0 : word) = Some W_8e1b0.
Proof. vm_refl. Qed.
Lemma D_8e1b0 : decode_any W_8e1b0 = Some (OpImm ALU_ADD 20 27 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e1b4 : bv 32 := 0x41b595b7.
Lemma F_8e1b4 : fetch_word AsanUbsan.M.loaded_segments (0x8e1b4 : word) = Some W_8e1b4.
Proof. vm_refl. Qed.
Lemma D_8e1b4 : decode_any W_8e1b4 = Some (Lui 11 269145, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e1b8 : bv 32 := 0xfff8a617.
Lemma F_8e1b8 : fetch_word AsanUbsan.M.loaded_segments (0x8e1b8 : word) = Some W_8e1b8.
Proof. vm_refl. Qed.
Lemma D_8e1b8 : decode_any W_8e1b8 = Some (Auipc 12 1048458, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e1bc : bv 32 := 0x00000697.
Lemma F_8e1bc : fetch_word AsanUbsan.M.loaded_segments (0x8e1bc : word) = Some W_8e1bc.
Proof. vm_refl. Qed.
Lemma D_8e1bc : decode_any W_8e1bc = Some (Auipc 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e1c0 : bv 32 := 0x003dd513.
Lemma F_8e1c0 : fetch_word AsanUbsan.M.loaded_segments (0x8e1c0 : word) = Some W_8e1c0.
Proof. vm_refl. Qed.
Lemma D_8e1c0 : decode_any W_8e1c0 = Some (ShiftImm ALU_SRL 10 27 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e1c4 : bv 32 := 0x01250933.
Lemma F_8e1c4 : fetch_word AsanUbsan.M.loaded_segments (0x8e1c4 : word) = Some W_8e1c4.
Proof. vm_refl. Qed.
Lemma D_8e1c4 : decode_any W_8e1c4 = Some (Op ALU_ADD 18 10 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e1c8 : bv 32 := 0xff200513.
Lemma F_8e1c8 : fetch_word AsanUbsan.M.loaded_segments (0x8e1c8 : word) = Some W_8e1c8.
Proof. vm_refl. Qed.
Lemma D_8e1c8 : decode_any W_8e1c8 = Some (OpImm ALU_ADD 10 0 4082, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e1cc : bv 32 := 0xab35859b.
Lemma F_8e1cc : fetch_word AsanUbsan.M.loaded_segments (0x8e1cc : word) = Some W_8e1cc.
Proof. vm_refl. Qed.
Lemma D_8e1cc : decode_any W_8e1cc = Some (OpImm32 11 11 2739, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e1d0 : bv 32 := 0xcb360613.
Lemma F_8e1d0 : fetch_word AsanUbsan.M.loaded_segments (0x8e1d0 : word) = Some W_8e1d0.
Proof. vm_refl. Qed.
Lemma D_8e1d0 : decode_any W_8e1d0 = Some (OpImm ALU_ADD 12 12 3251, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e1d4 : bv 32 := 0xf4c68693.
Lemma F_8e1d4 : fetch_word AsanUbsan.M.loaded_segments (0x8e1d4 : word) = Some W_8e1d4.
Proof. vm_refl. Qed.
Lemma D_8e1d4 : decode_any W_8e1d4 = Some (OpImm ALU_ADD 13 13 3916, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e1d8 : bv 32 := 0x00bdb023.
Lemma F_8e1d8 : fetch_word AsanUbsan.M.loaded_segments (0x8e1d8 : word) = Some W_8e1d8.
Proof. vm_refl. Qed.
Lemma D_8e1d8 : decode_any W_8e1d8 = Some (Store SZ8 27 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e1dc : bv 32 := 0x00cdb423.
Lemma F_8e1dc : fetch_word AsanUbsan.M.loaded_segments (0x8e1dc : word) = Some W_8e1dc.
Proof. vm_refl. Qed.
Lemma D_8e1dc : decode_any W_8e1dc = Some (Store SZ8 27 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e1e0 : bv 32 := 0x00ddb823.
Lemma F_8e1e0 : fetch_word AsanUbsan.M.loaded_segments (0x8e1e0 : word) = Some W_8e1e0.
Proof. vm_refl. Qed.
Lemma D_8e1e0 : decode_any W_8e1e0 = Some (Store SZ8 27 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e1e4 : bv 32 := 0xff100593.
Lemma F_8e1e4 : fetch_word AsanUbsan.M.loaded_segments (0x8e1e4 : word) = Some W_8e1e4.
Proof. vm_refl. Qed.
Lemma D_8e1e4 : decode_any W_8e1e4 = Some (OpImm ALU_ADD 11 0 4081, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e1e8 : bv 32 := 0x00b90023.
Lemma F_8e1e8 : fetch_word AsanUbsan.M.loaded_segments (0x8e1e8 : word) = Some W_8e1e8.
Proof. vm_refl. Qed.
Lemma D_8e1e8 : decode_any W_8e1e8 = Some (Store SZ1 18 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e1ec : bv 32 := 0x00b900a3.
Lemma F_8e1ec : fetch_word AsanUbsan.M.loaded_segments (0x8e1ec : word) = Some W_8e1ec.
Proof. vm_refl. Qed.
Lemma D_8e1ec : decode_any W_8e1ec = Some (Store SZ1 18 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e1f0 : bv 32 := 0x00b90123.
Lemma F_8e1f0 : fetch_word AsanUbsan.M.loaded_segments (0x8e1f0 : word) = Some W_8e1f0.
Proof. vm_refl. Qed.
Lemma D_8e1f0 : decode_any W_8e1f0 = Some (Store SZ1 18 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e1f4 : bv 32 := 0x00b901a3.
Lemma F_8e1f4 : fetch_word AsanUbsan.M.loaded_segments (0x8e1f4 : word) = Some W_8e1f4.
Proof. vm_refl. Qed.
Lemma D_8e1f4 : decode_any W_8e1f4 = Some (Store SZ1 18 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e1f8 : bv 32 := 0xff800593.
Lemma F_8e1f8 : fetch_word AsanUbsan.M.loaded_segments (0x8e1f8 : word) = Some W_8e1f8.
Proof. vm_refl. Qed.
Lemma D_8e1f8 : decode_any W_8e1f8 = Some (OpImm ALU_ADD 11 0 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e1fc : bv 32 := 0x00b90623.
Lemma F_8e1fc : fetch_word AsanUbsan.M.loaded_segments (0x8e1fc : word) = Some W_8e1fc.
Proof. vm_refl. Qed.
Lemma D_8e1fc : decode_any W_8e1fc = Some (Store SZ1 18 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e200 : bv 32 := 0x00b906a3.
Lemma F_8e200 : fetch_word AsanUbsan.M.loaded_segments (0x8e200 : word) = Some W_8e200.
Proof. vm_refl. Qed.
Lemma D_8e200 : decode_any W_8e200 = Some (Store SZ1 18 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e204 : bv 32 := 0x00b90723.
Lemma F_8e204 : fetch_word AsanUbsan.M.loaded_segments (0x8e204 : word) = Some W_8e204.
Proof. vm_refl. Qed.
Lemma D_8e204 : decode_any W_8e204 = Some (Store SZ1 18 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e208 : bv 32 := 0x00b907a3.
Lemma F_8e208 : fetch_word AsanUbsan.M.loaded_segments (0x8e208 : word) = Some W_8e208.
Proof. vm_refl. Qed.
Lemma D_8e208 : decode_any W_8e208 = Some (Store SZ1 18 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e20c : bv 32 := 0x00b90a23.
Lemma F_8e20c : fetch_word AsanUbsan.M.loaded_segments (0x8e20c : word) = Some W_8e20c.
Proof. vm_refl. Qed.
Lemma D_8e20c : decode_any W_8e20c = Some (Store SZ1 18 11 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e210 : bv 32 := 0x00b90aa3.
Lemma F_8e210 : fetch_word AsanUbsan.M.loaded_segments (0x8e210 : word) = Some W_8e210.
Proof. vm_refl. Qed.
Lemma D_8e210 : decode_any W_8e210 = Some (Store SZ1 18 11 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e214 : bv 32 := 0x00b90b23.
Lemma F_8e214 : fetch_word AsanUbsan.M.loaded_segments (0x8e214 : word) = Some W_8e214.
Proof. vm_refl. Qed.
Lemma D_8e214 : decode_any W_8e214 = Some (Store SZ1 18 11 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e218 : bv 32 := 0x00b90ba3.
Lemma F_8e218 : fetch_word AsanUbsan.M.loaded_segments (0x8e218 : word) = Some W_8e218.
Proof. vm_refl. Qed.
Lemma D_8e218 : decode_any W_8e218 = Some (Store SZ1 18 11 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e21c : bv 32 := 0xff300593.
Lemma F_8e21c : fetch_word AsanUbsan.M.loaded_segments (0x8e21c : word) = Some W_8e21c.
Proof. vm_refl. Qed.
Lemma D_8e21c : decode_any W_8e21c = Some (OpImm ALU_ADD 11 0 4083, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e220 : bv 32 := 0x00090223.
Lemma F_8e220 : fetch_word AsanUbsan.M.loaded_segments (0x8e220 : word) = Some W_8e220.
Proof. vm_refl. Qed.
Lemma D_8e220 : decode_any W_8e220 = Some (Store SZ1 18 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e224 : bv 32 := 0x000902a3.
Lemma F_8e224 : fetch_word AsanUbsan.M.loaded_segments (0x8e224 : word) = Some W_8e224.
Proof. vm_refl. Qed.
Lemma D_8e224 : decode_any W_8e224 = Some (Store SZ1 18 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e228 : bv 32 := 0x00090323.
Lemma F_8e228 : fetch_word AsanUbsan.M.loaded_segments (0x8e228 : word) = Some W_8e228.
Proof. vm_refl. Qed.
Lemma D_8e228 : decode_any W_8e228 = Some (Store SZ1 18 0 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e22c : bv 32 := 0x00a903a3.
Lemma F_8e22c : fetch_word AsanUbsan.M.loaded_segments (0x8e22c : word) = Some W_8e22c.
Proof. vm_refl. Qed.
Lemma D_8e22c : decode_any W_8e22c = Some (Store SZ1 18 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e230 : bv 32 := 0x00a90423.
Lemma F_8e230 : fetch_word AsanUbsan.M.loaded_segments (0x8e230 : word) = Some W_8e230.
Proof. vm_refl. Qed.
Lemma D_8e230 : decode_any W_8e230 = Some (Store SZ1 18 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e234 : bv 32 := 0x00a904a3.
Lemma F_8e234 : fetch_word AsanUbsan.M.loaded_segments (0x8e234 : word) = Some W_8e234.
Proof. vm_refl. Qed.
Lemma D_8e234 : decode_any W_8e234 = Some (Store SZ1 18 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e238 : bv 32 := 0x00a90523.
Lemma F_8e238 : fetch_word AsanUbsan.M.loaded_segments (0x8e238 : word) = Some W_8e238.
Proof. vm_refl. Qed.
Lemma D_8e238 : decode_any W_8e238 = Some (Store SZ1 18 10 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e23c : bv 32 := 0x00a905a3.
Lemma F_8e23c : fetch_word AsanUbsan.M.loaded_segments (0x8e23c : word) = Some W_8e23c.
Proof. vm_refl. Qed.
Lemma D_8e23c : decode_any W_8e23c = Some (Store SZ1 18 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e240 : bv 32 := 0x00a90823.
Lemma F_8e240 : fetch_word AsanUbsan.M.loaded_segments (0x8e240 : word) = Some W_8e240.
Proof. vm_refl. Qed.
Lemma D_8e240 : decode_any W_8e240 = Some (Store SZ1 18 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e244 : bv 32 := 0x00a908a3.
Lemma F_8e244 : fetch_word AsanUbsan.M.loaded_segments (0x8e244 : word) = Some W_8e244.
Proof. vm_refl. Qed.
Lemma D_8e244 : decode_any W_8e244 = Some (Store SZ1 18 10 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e248 : bv 32 := 0x00a90923.
Lemma F_8e248 : fetch_word AsanUbsan.M.loaded_segments (0x8e248 : word) = Some W_8e248.
Proof. vm_refl. Qed.
Lemma D_8e248 : decode_any W_8e248 = Some (Store SZ1 18 10 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e24c : bv 32 := 0x00a909a3.
Lemma F_8e24c : fetch_word AsanUbsan.M.loaded_segments (0x8e24c : word) = Some W_8e24c.
Proof. vm_refl. Qed.
Lemma D_8e24c : decode_any W_8e24c = Some (Store SZ1 18 10 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e250 : bv 32 := 0x00a90c23.
Lemma F_8e250 : fetch_word AsanUbsan.M.loaded_segments (0x8e250 : word) = Some W_8e250.
Proof. vm_refl. Qed.
Lemma D_8e250 : decode_any W_8e250 = Some (Store SZ1 18 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e254 : bv 32 := 0x00a90ca3.
Lemma F_8e254 : fetch_word AsanUbsan.M.loaded_segments (0x8e254 : word) = Some W_8e254.
Proof. vm_refl. Qed.
Lemma D_8e254 : decode_any W_8e254 = Some (Store SZ1 18 10 25, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e258 : bv 32 := 0x00a90d23.
Lemma F_8e258 : fetch_word AsanUbsan.M.loaded_segments (0x8e258 : word) = Some W_8e258.
Proof. vm_refl. Qed.
Lemma D_8e258 : decode_any W_8e258 = Some (Store SZ1 18 10 26, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e25c : bv 32 := 0x00a90da3.
Lemma F_8e25c : fetch_word AsanUbsan.M.loaded_segments (0x8e25c : word) = Some W_8e25c.
Proof. vm_refl. Qed.
Lemma D_8e25c : decode_any W_8e25c = Some (Store SZ1 18 10 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e260 : bv 32 := 0x02a90023.
Lemma F_8e260 : fetch_word AsanUbsan.M.loaded_segments (0x8e260 : word) = Some W_8e260.
Proof. vm_refl. Qed.
Lemma D_8e260 : decode_any W_8e260 = Some (Store SZ1 18 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e264 : bv 32 := 0x02a900a3.
Lemma F_8e264 : fetch_word AsanUbsan.M.loaded_segments (0x8e264 : word) = Some W_8e264.
Proof. vm_refl. Qed.
Lemma D_8e264 : decode_any W_8e264 = Some (Store SZ1 18 10 33, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e268 : bv 32 := 0x02a90123.
Lemma F_8e268 : fetch_word AsanUbsan.M.loaded_segments (0x8e268 : word) = Some W_8e268.
Proof. vm_refl. Qed.
Lemma D_8e268 : decode_any W_8e268 = Some (Store SZ1 18 10 34, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e26c : bv 32 := 0x02a901a3.
Lemma F_8e26c : fetch_word AsanUbsan.M.loaded_segments (0x8e26c : word) = Some W_8e26c.
Proof. vm_refl. Qed.
Lemma D_8e26c : decode_any W_8e26c = Some (Store SZ1 18 10 35, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e270 : bv 32 := 0x02b90423.
Lemma F_8e270 : fetch_word AsanUbsan.M.loaded_segments (0x8e270 : word) = Some W_8e270.
Proof. vm_refl. Qed.
Lemma D_8e270 : decode_any W_8e270 = Some (Store SZ1 18 11 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e274 : bv 32 := 0x02b904a3.
Lemma F_8e274 : fetch_word AsanUbsan.M.loaded_segments (0x8e274 : word) = Some W_8e274.
Proof. vm_refl. Qed.
Lemma D_8e274 : decode_any W_8e274 = Some (Store SZ1 18 11 41, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e278 : bv 32 := 0x02b90523.
Lemma F_8e278 : fetch_word AsanUbsan.M.loaded_segments (0x8e278 : word) = Some W_8e278.
Proof. vm_refl. Qed.
Lemma D_8e278 : decode_any W_8e278 = Some (Store SZ1 18 11 42, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e27c : bv 32 := 0x02b905a3.
Lemma F_8e27c : fetch_word AsanUbsan.M.loaded_segments (0x8e27c : word) = Some W_8e27c.
Proof. vm_refl. Qed.
Lemma D_8e27c : decode_any W_8e27c = Some (Store SZ1 18 11 43, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e280 : bv 32 := 0x000a0513.
Lemma F_8e280 : fetch_word AsanUbsan.M.loaded_segments (0x8e280 : word) = Some W_8e280.
Proof. vm_refl. Qed.
Lemma D_8e280 : decode_any W_8e280 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e284 : bv 32 := 0x000b0593.
Lemma F_8e284 : fetch_word AsanUbsan.M.loaded_segments (0x8e284 : word) = Some W_8e284.
Proof. vm_refl. Qed.
Lemma D_8e284 : decode_any W_8e284 = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e288 : bv 32 := 0x000a8613.
Lemma F_8e288 : fetch_word AsanUbsan.M.loaded_segments (0x8e288 : word) = Some W_8e288.
Proof. vm_refl. Qed.
Lemma D_8e288 : decode_any W_8e288 = Some (OpImm ALU_ADD 12 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e28c : bv 32 := 0x4b4000ef.
Lemma F_8e28c : fetch_word AsanUbsan.M.loaded_segments (0x8e28c : word) = Some W_8e28c.
Proof. vm_refl. Qed.
Lemma D_8e28c : decode_any W_8e28c = Some (Jal 1 1204, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e290 : bv 32 := 0x003ad513.
Lemma F_8e290 : fetch_word AsanUbsan.M.loaded_segments (0x8e290 : word) = Some W_8e290.
Proof. vm_refl. Qed.
Lemma D_8e290 : decode_any W_8e290 = Some (ShiftImm ALU_SRL 10 21 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e294 : bv 32 := 0x27000593.
Lemma F_8e294 : fetch_word AsanUbsan.M.loaded_segments (0x8e294 : word) = Some W_8e294.
Proof. vm_refl. Qed.
Lemma D_8e294 : decode_any W_8e294 = Some (OpImm ALU_ADD 11 0 624, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e298 : bv 32 := 0x16a5e863.
Lemma F_8e298 : fetch_word AsanUbsan.M.loaded_segments (0x8e298 : word) = Some W_8e298.
Proof. vm_refl. Qed.
Lemma D_8e298 : decode_any W_8e298 = Some (Branch BC_LTU 11 10 368, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e29c : bv 32 := 0x060d8a93.
Lemma F_8e29c : fetch_word AsanUbsan.M.loaded_segments (0x8e29c : word) = Some W_8e29c.
Proof. vm_refl. Qed.
Lemma D_8e29c : decode_any W_8e29c = Some (OpImm ALU_ADD 21 27 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e2a0 : bv 32 := 0x00090623.
Lemma F_8e2a0 : fetch_word AsanUbsan.M.loaded_segments (0x8e2a0 : word) = Some W_8e2a0.
Proof. vm_refl. Qed.
Lemma D_8e2a0 : decode_any W_8e2a0 = Some (Store SZ1 18 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e2a4 : bv 32 := 0x000906a3.
Lemma F_8e2a4 : fetch_word AsanUbsan.M.loaded_segments (0x8e2a4 : word) = Some W_8e2a4.
Proof. vm_refl. Qed.
Lemma D_8e2a4 : decode_any W_8e2a4 = Some (Store SZ1 18 0 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e2a8 : bv 32 := 0x00090723.
Lemma F_8e2a8 : fetch_word AsanUbsan.M.loaded_segments (0x8e2a8 : word) = Some W_8e2a8.
Proof. vm_refl. Qed.
Lemma D_8e2a8 : decode_any W_8e2a8 = Some (Store SZ1 18 0 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e2ac : bv 32 := 0x000907a3.
Lemma F_8e2ac : fetch_word AsanUbsan.M.loaded_segments (0x8e2ac : word) = Some W_8e2ac.
Proof. vm_refl. Qed.
Lemma D_8e2ac : decode_any W_8e2ac = Some (Store SZ1 18 0 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e2b0 : bv 32 := 0xfff94517.
Lemma F_8e2b0 : fetch_word AsanUbsan.M.loaded_segments (0x8e2b0 : word) = Some W_8e2b0.
Proof. vm_refl. Qed.
Lemma D_8e2b0 : decode_any W_8e2b0 = Some (Auipc 10 1048468, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e2b4 : bv 32 := 0x6b050593.
Lemma F_8e2b4 : fetch_word AsanUbsan.M.loaded_segments (0x8e2b4 : word) = Some W_8e2b4.
Proof. vm_refl. Qed.
Lemma D_8e2b4 : decode_any W_8e2b4 = Some (OpImm ALU_ADD 11 10 1712, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e2b8 : bv 32 := 0x03848613.
Lemma F_8e2b8 : fetch_word AsanUbsan.M.loaded_segments (0x8e2b8 : word) = Some W_8e2b8.
Proof. vm_refl. Qed.
Lemma D_8e2b8 : decode_any W_8e2b8 = Some (OpImm ALU_ADD 12 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e2bc : bv 32 := 0x000a8513.
Lemma F_8e2bc : fetch_word AsanUbsan.M.loaded_segments (0x8e2bc : word) = Some W_8e2bc.
Proof. vm_refl. Qed.
Lemma D_8e2bc : decode_any W_8e2bc = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e2c0 : bv 32 := 0x5e8000ef.
Lemma F_8e2c0 : fetch_word AsanUbsan.M.loaded_segments (0x8e2c0 : word) = Some W_8e2c0.
Proof. vm_refl. Qed.
Lemma D_8e2c0 : decode_any W_8e2c0 = Some (Jal 1 1512, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e2c4 : bv 32 := 0x0a0d8b93.
Lemma F_8e2c4 : fetch_word AsanUbsan.M.loaded_segments (0x8e2c4 : word) = Some W_8e2c4.
Proof. vm_refl. Qed.
Lemma D_8e2c4 : decode_any W_8e2c4 = Some (OpImm ALU_ADD 23 27 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e2c8 : bv 32 := 0x00090a23.
Lemma F_8e2c8 : fetch_word AsanUbsan.M.loaded_segments (0x8e2c8 : word) = Some W_8e2c8.
Proof. vm_refl. Qed.
Lemma D_8e2c8 : decode_any W_8e2c8 = Some (Store SZ1 18 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e2cc : bv 32 := 0x00090aa3.
Lemma F_8e2cc : fetch_word AsanUbsan.M.loaded_segments (0x8e2cc : word) = Some W_8e2cc.
Proof. vm_refl. Qed.
Lemma D_8e2cc : decode_any W_8e2cc = Some (Store SZ1 18 0 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e2d0 : bv 32 := 0x00090b23.
Lemma F_8e2d0 : fetch_word AsanUbsan.M.loaded_segments (0x8e2d0 : word) = Some W_8e2d0.
Proof. vm_refl. Qed.
Lemma D_8e2d0 : decode_any W_8e2d0 = Some (Store SZ1 18 0 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e2d4 : bv 32 := 0x00090ba3.
Lemma F_8e2d4 : fetch_word AsanUbsan.M.loaded_segments (0x8e2d4 : word) = Some W_8e2d4.
Proof. vm_refl. Qed.
Lemma D_8e2d4 : decode_any W_8e2d4 = Some (Store SZ1 18 0 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e2d8 : bv 32 := 0x000b8513.
Lemma F_8e2d8 : fetch_word AsanUbsan.M.loaded_segments (0x8e2d8 : word) = Some W_8e2d8.
Proof. vm_refl. Qed.
Lemma D_8e2d8 : decode_any W_8e2d8 = Some (OpImm ALU_ADD 10 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e2dc : bv 32 := 0x000a0593.
Lemma F_8e2dc : fetch_word AsanUbsan.M.loaded_segments (0x8e2dc : word) = Some W_8e2dc.
Proof. vm_refl. Qed.
Lemma D_8e2dc : decode_any W_8e2dc = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e2e0 : bv 32 := 0x6cc000ef.
Lemma F_8e2e0 : fetch_word AsanUbsan.M.loaded_segments (0x8e2e0 : word) = Some W_8e2e0.
Proof. vm_refl. Qed.
Lemma D_8e2e0 : decode_any W_8e2e0 = Some (Jal 1 1740, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e2e4 : bv 32 := 0x0e0d8d13.
Lemma F_8e2e4 : fetch_word AsanUbsan.M.loaded_segments (0x8e2e4 : word) = Some W_8e2e4.
Proof. vm_refl. Qed.
Lemma D_8e2e4 : decode_any W_8e2e4 = Some (OpImm ALU_ADD 26 27 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e2e8 : bv 32 := 0x000d0513.
Lemma F_8e2e8 : fetch_word AsanUbsan.M.loaded_segments (0x8e2e8 : word) = Some W_8e2e8.
Proof. vm_refl. Qed.
Lemma D_8e2e8 : decode_any W_8e2e8 = Some (OpImm ALU_ADD 10 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e2ec : bv 32 := 0x000a8593.
Lemma F_8e2ec : fetch_word AsanUbsan.M.loaded_segments (0x8e2ec : word) = Some W_8e2ec.
Proof. vm_refl. Qed.
Lemma D_8e2ec : decode_any W_8e2ec = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e2f0 : bv 32 := 0x5d5030ef.
Lemma F_8e2f0 : fetch_word AsanUbsan.M.loaded_segments (0x8e2f0 : word) = Some W_8e2f0.
Proof. vm_refl. Qed.
Lemma D_8e2f0 : decode_any W_8e2f0 = Some (Jal 1 15828, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e2f4 : bv 32 := 0x03848513.
Lemma F_8e2f4 : fetch_word AsanUbsan.M.loaded_segments (0x8e2f4 : word) = Some W_8e2f4.
Proof. vm_refl. Qed.
Lemma D_8e2f4 : decode_any W_8e2f4 = Some (OpImm ALU_ADD 10 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e2f8 : bv 32 := 0x000d0593.
Lemma F_8e2f8 : fetch_word AsanUbsan.M.loaded_segments (0x8e2f8 : word) = Some W_8e2f8.
Proof. vm_refl. Qed.
Lemma D_8e2f8 : decode_any W_8e2f8 = Some (OpImm ALU_ADD 11 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e2fc : bv 32 := 0x000b8613.
Lemma F_8e2fc : fetch_word AsanUbsan.M.loaded_segments (0x8e2fc : word) = Some W_8e2fc.
Proof. vm_refl. Qed.
Lemma D_8e2fc : decode_any W_8e2fc = Some (OpImm ALU_ADD 12 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e300 : bv 32 := 0x00d000ef.
Lemma F_8e300 : fetch_word AsanUbsan.M.loaded_segments (0x8e300 : word) = Some W_8e300.
Proof. vm_refl. Qed.
Lemma D_8e300 : decode_any W_8e300 = Some (Jal 1 2060, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e304 : bv 32 := 0x000d4503.
Lemma F_8e304 : fetch_word AsanUbsan.M.loaded_segments (0x8e304 : word) = Some W_8e304.
Proof. vm_refl. Qed.
Lemma D_8e304 : decode_any W_8e304 = Some (Load SZ1 false 10 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e308 : bv 32 := 0x00157513.
Lemma F_8e308 : fetch_word AsanUbsan.M.loaded_segments (0x8e308 : word) = Some W_8e308.
Proof. vm_refl. Qed.
Lemma D_8e308 : decode_any W_8e308 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e30c : bv 32 := 0x120d8c93.
Lemma F_8e30c : fetch_word AsanUbsan.M.loaded_segments (0x8e30c : word) = Some W_8e30c.
Proof. vm_refl. Qed.
Lemma D_8e30c : decode_any W_8e30c = Some (OpImm ALU_ADD 25 27 288, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e310 : bv 32 := 0x00050c63.
Lemma F_8e310 : fetch_word AsanUbsan.M.loaded_segments (0x8e310 : word) = Some W_8e310.
Proof. vm_refl. Qed.
Lemma D_8e310 : decode_any W_8e310 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e314 : bv 32 := 0x018d3503.
Lemma F_8e314 : fetch_word AsanUbsan.M.loaded_segments (0x8e314 : word) = Some W_8e314.
Proof. vm_refl. Qed.
Lemma D_8e314 : decode_any W_8e314 = Some (Load SZ8 true 10 26 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e318 : bv 32 := 0x00050863.
Lemma F_8e318 : fetch_word AsanUbsan.M.loaded_segments (0x8e318 : word) = Some W_8e318.
Proof. vm_refl. Qed.
Lemma D_8e318 : decode_any W_8e318 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e31c : bv 32 := 0x010d3583.
Lemma F_8e31c : fetch_word AsanUbsan.M.loaded_segments (0x8e31c : word) = Some W_8e31c.
Proof. vm_refl. Qed.
Lemma D_8e31c : decode_any W_8e31c = Some (Load SZ8 true 11 26 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e320 : bv 32 := 0x00359593.
Lemma F_8e320 : fetch_word AsanUbsan.M.loaded_segments (0x8e320 : word) = Some W_8e320.
Proof. vm_refl. Qed.
Lemma D_8e320 : decode_any W_8e320 = Some (ShiftImm ALU_SLL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e324 : bv 32 := 0x525220ef.
Lemma F_8e324 : fetch_word AsanUbsan.M.loaded_segments (0x8e324 : word) = Some W_8e324.
Proof. vm_refl. Qed.
Lemma D_8e324 : decode_any W_8e324 = Some (Jal 1 142628, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e328 : bv 32 := 0x000c8513.
Lemma F_8e328 : fetch_word AsanUbsan.M.loaded_segments (0x8e328 : word) = Some W_8e328.
Proof. vm_refl. Qed.
Lemma D_8e328 : decode_any W_8e328 = Some (OpImm ALU_ADD 10 25 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e32c : bv 32 := 0x000b8593.
Lemma F_8e32c : fetch_word AsanUbsan.M.loaded_segments (0x8e32c : word) = Some W_8e32c.
Proof. vm_refl. Qed.
Lemma D_8e32c : decode_any W_8e32c = Some (OpImm ALU_ADD 11 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e330 : bv 32 := 0x595030ef.
Lemma F_8e330 : fetch_word AsanUbsan.M.loaded_segments (0x8e330 : word) = Some W_8e330.
Proof. vm_refl. Qed.
Lemma D_8e330 : decode_any W_8e330 = Some (Jal 1 15764, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e334 : bv 32 := 0x01848513.
Lemma F_8e334 : fetch_word AsanUbsan.M.loaded_segments (0x8e334 : word) = Some W_8e334.
Proof. vm_refl. Qed.
Lemma D_8e334 : decode_any W_8e334 = Some (OpImm ALU_ADD 10 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e338 : bv 32 := 0x000c8593.
Lemma F_8e338 : fetch_word AsanUbsan.M.loaded_segments (0x8e338 : word) = Some W_8e338.
Proof. vm_refl. Qed.
Lemma D_8e338 : decode_any W_8e338 = Some (OpImm ALU_ADD 11 25 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e33c : bv 32 := 0x000a8613.
Lemma F_8e33c : fetch_word AsanUbsan.M.loaded_segments (0x8e33c : word) = Some W_8e33c.
Proof. vm_refl. Qed.
Lemma D_8e33c : decode_any W_8e33c = Some (OpImm ALU_ADD 12 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e340 : bv 32 := 0x7cc000ef.
Lemma F_8e340 : fetch_word AsanUbsan.M.loaded_segments (0x8e340 : word) = Some W_8e340.
Proof. vm_refl. Qed.
Lemma D_8e340 : decode_any W_8e340 = Some (Jal 1 1996, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e344 : bv 32 := 0x000cc503.
Lemma F_8e344 : fetch_word AsanUbsan.M.loaded_segments (0x8e344 : word) = Some W_8e344.
Proof. vm_refl. Qed.
Lemma D_8e344 : decode_any W_8e344 = Some (Load SZ1 false 10 25 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e348 : bv 32 := 0x00157513.
Lemma F_8e348 : fetch_word AsanUbsan.M.loaded_segments (0x8e348 : word) = Some W_8e348.
Proof. vm_refl. Qed.
Lemma D_8e348 : decode_any W_8e348 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e34c : bv 32 := 0x00050c63.
Lemma F_8e34c : fetch_word AsanUbsan.M.loaded_segments (0x8e34c : word) = Some W_8e34c.
Proof. vm_refl. Qed.
Lemma D_8e34c : decode_any W_8e34c = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e350 : bv 32 := 0x018cb503.
Lemma F_8e350 : fetch_word AsanUbsan.M.loaded_segments (0x8e350 : word) = Some W_8e350.
Proof. vm_refl. Qed.
Lemma D_8e350 : decode_any W_8e350 = Some (Load SZ8 true 10 25 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e354 : bv 32 := 0x00050863.
Lemma F_8e354 : fetch_word AsanUbsan.M.loaded_segments (0x8e354 : word) = Some W_8e354.
Proof. vm_refl. Qed.
Lemma D_8e354 : decode_any W_8e354 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e358 : bv 32 := 0x010cb583.
Lemma F_8e358 : fetch_word AsanUbsan.M.loaded_segments (0x8e358 : word) = Some W_8e358.
Proof. vm_refl. Qed.
Lemma D_8e358 : decode_any W_8e358 = Some (Load SZ8 true 11 25 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e35c : bv 32 := 0x00359593.
Lemma F_8e35c : fetch_word AsanUbsan.M.loaded_segments (0x8e35c : word) = Some W_8e35c.
Proof. vm_refl. Qed.
Lemma D_8e35c : decode_any W_8e35c = Some (ShiftImm ALU_SLL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e360 : bv 32 := 0x4e9220ef.
Lemma F_8e360 : fetch_word AsanUbsan.M.loaded_segments (0x8e360 : word) = Some W_8e360.
Proof. vm_refl. Qed.
Lemma D_8e360 : decode_any W_8e360 = Some (Jal 1 142568, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e364 : bv 32 := 0x0184c503.
Lemma F_8e364 : fetch_word AsanUbsan.M.loaded_segments (0x8e364 : word) = Some W_8e364.
Proof. vm_refl. Qed.
Lemma D_8e364 : decode_any W_8e364 = Some (Load SZ1 false 10 9 24, 4%Z).
Proof. vm_refl. Qed.
