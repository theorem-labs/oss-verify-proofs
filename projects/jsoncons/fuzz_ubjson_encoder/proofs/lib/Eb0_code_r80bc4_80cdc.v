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

Definition W_9c108 : bv 32 := 0xfc010113.
Lemma F_9c108 : fetch_word AsanUbsan.M.loaded_segments (0x9c158 : word) = Some W_9c108.
Proof. vm_refl. Qed.
Lemma D_9c108 : decode_any W_9c108 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c10c : bv 32 := 0x02113c23.
Lemma F_9c10c : fetch_word AsanUbsan.M.loaded_segments (0x9c15c : word) = Some W_9c10c.
Proof. vm_refl. Qed.
Lemma D_9c10c : decode_any W_9c10c = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c110 : bv 32 := 0x02813823.
Lemma F_9c110 : fetch_word AsanUbsan.M.loaded_segments (0x9c160 : word) = Some W_9c110.
Proof. vm_refl. Qed.
Lemma D_9c110 : decode_any W_9c110 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c114 : bv 32 := 0x02913423.
Lemma F_9c114 : fetch_word AsanUbsan.M.loaded_segments (0x9c164 : word) = Some W_9c114.
Proof. vm_refl. Qed.
Lemma D_9c114 : decode_any W_9c114 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c118 : bv 32 := 0x03213023.
Lemma F_9c118 : fetch_word AsanUbsan.M.loaded_segments (0x9c168 : word) = Some W_9c118.
Proof. vm_refl. Qed.
Lemma D_9c118 : decode_any W_9c118 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c11c : bv 32 := 0x01313c23.
Lemma F_9c11c : fetch_word AsanUbsan.M.loaded_segments (0x9c16c : word) = Some W_9c11c.
Proof. vm_refl. Qed.
Lemma D_9c11c : decode_any W_9c11c = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c120 : bv 32 := 0x01413823.
Lemma F_9c120 : fetch_word AsanUbsan.M.loaded_segments (0x9c170 : word) = Some W_9c120.
Proof. vm_refl. Qed.
Lemma D_9c120 : decode_any W_9c120 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c124 : bv 32 := 0x01513423.
Lemma F_9c124 : fetch_word AsanUbsan.M.loaded_segments (0x9c174 : word) = Some W_9c124.
Proof. vm_refl. Qed.
Lemma D_9c124 : decode_any W_9c124 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c128 : bv 32 := 0x00058413.
Lemma F_9c128 : fetch_word AsanUbsan.M.loaded_segments (0x9c178 : word) = Some W_9c128.
Proof. vm_refl. Qed.
Lemma D_9c128 : decode_any W_9c128 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c12c : bv 32 := 0x0015b593.
Lemma F_9c12c : fetch_word AsanUbsan.M.loaded_segments (0x9c17c : word) = Some W_9c12c.
Proof. vm_refl. Qed.
Lemma D_9c12c : decode_any W_9c12c = Some (OpImm ALU_SLTU 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c130 : bv 32 := 0x7ff50293.
Lemma F_9c130 : fetch_word AsanUbsan.M.loaded_segments (0x9c180 : word) = Some W_9c130.
Proof. vm_refl. Qed.
Lemma D_9c130 : decode_any W_9c130 = Some (OpImm ALU_ADD 5 10 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c134 : bv 32 := 0xfff58593.
Lemma F_9c134 : fetch_word AsanUbsan.M.loaded_segments (0x9c184 : word) = Some W_9c134.
Proof. vm_refl. Qed.
Lemma D_9c134 : decode_any W_9c134 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c138 : bv 32 := 0x00d5f333.
Lemma F_9c138 : fetch_word AsanUbsan.M.loaded_segments (0x9c188 : word) = Some W_9c138.
Proof. vm_refl. Qed.
Lemma D_9c138 : decode_any W_9c138 = Some (Op ALU_AND 6 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c13c : bv 32 := 0x00100593.
Lemma F_9c13c : fetch_word AsanUbsan.M.loaded_segments (0x9c18c : word) = Some W_9c13c.
Proof. vm_refl. Qed.
Lemma D_9c13c : decode_any W_9c13c = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c140 : bv 32 := 0x0062b4a3.
Lemma F_9c140 : fetch_word AsanUbsan.M.loaded_segments (0x9c190 : word) = Some W_9c140.
Proof. vm_refl. Qed.
Lemma D_9c140 : decode_any W_9c140 = Some (Store SZ8 5 6 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c144 : bv 32 := 0x00b40863.
Lemma F_9c144 : fetch_word AsanUbsan.M.loaded_segments (0x9c194 : word) = Some W_9c144.
Proof. vm_refl. Qed.
Lemma D_9c144 : decode_any W_9c144 = Some (Branch BC_EQ 8 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c148 : bv 32 := 0x02041c63.
Lemma F_9c148 : fetch_word AsanUbsan.M.loaded_segments (0x9c198 : word) = Some W_9c148.
Proof. vm_refl. Qed.
Lemma D_9c148 : decode_any W_9c148 = Some (Branch BC_NE 8 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c180 : bv 32 := 0x06089463.
Lemma F_9c180 : fetch_word AsanUbsan.M.loaded_segments (0x9c1d0 : word) = Some W_9c180.
Proof. vm_refl. Qed.
Lemma D_9c180 : decode_any W_9c180 = Some (Branch BC_NE 17 0 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c1e8 : bv 32 := 0x00060593.
Lemma F_9c1e8 : fetch_word AsanUbsan.M.loaded_segments (0x9c238 : word) = Some W_9c1e8.
Proof. vm_refl. Qed.
Lemma D_9c1e8 : decode_any W_9c1e8 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c1ec : bv 32 := 0x00068613.
Lemma F_9c1ec : fetch_word AsanUbsan.M.loaded_segments (0x9c23c : word) = Some W_9c1ec.
Proof. vm_refl. Qed.
Lemma D_9c1ec : decode_any W_9c1ec = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c1f0 : bv 32 := 0x00078693.
Lemma F_9c1f0 : fetch_word AsanUbsan.M.loaded_segments (0x9c240 : word) = Some W_9c1f0.
Proof. vm_refl. Qed.
Lemma D_9c1f0 : decode_any W_9c1f0 = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c1f4 : bv 32 := 0x00080713.
Lemma F_9c1f4 : fetch_word AsanUbsan.M.loaded_segments (0x9c244 : word) = Some W_9c1f4.
Proof. vm_refl. Qed.
Lemma D_9c1f4 : decode_any W_9c1f4 = Some (OpImm ALU_ADD 14 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c1f8 : bv 32 := 0x00040793.
Lemma F_9c1f8 : fetch_word AsanUbsan.M.loaded_segments (0x9c248 : word) = Some W_9c1f8.
Proof. vm_refl. Qed.
Lemma D_9c1f8 : decode_any W_9c1f8 = Some (OpImm ALU_ADD 15 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c1fc : bv 32 := 0x03813083.
Lemma F_9c1fc : fetch_word AsanUbsan.M.loaded_segments (0x9c24c : word) = Some W_9c1fc.
Proof. vm_refl. Qed.
Lemma D_9c1fc : decode_any W_9c1fc = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c200 : bv 32 := 0x03013403.
Lemma F_9c200 : fetch_word AsanUbsan.M.loaded_segments (0x9c250 : word) = Some W_9c200.
Proof. vm_refl. Qed.
Lemma D_9c200 : decode_any W_9c200 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c204 : bv 32 := 0x02813483.
Lemma F_9c204 : fetch_word AsanUbsan.M.loaded_segments (0x9c254 : word) = Some W_9c204.
Proof. vm_refl. Qed.
Lemma D_9c204 : decode_any W_9c204 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c208 : bv 32 := 0x02013903.
Lemma F_9c208 : fetch_word AsanUbsan.M.loaded_segments (0x9c258 : word) = Some W_9c208.
Proof. vm_refl. Qed.
Lemma D_9c208 : decode_any W_9c208 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c20c : bv 32 := 0x01813983.
Lemma F_9c20c : fetch_word AsanUbsan.M.loaded_segments (0x9c25c : word) = Some W_9c20c.
Proof. vm_refl. Qed.
Lemma D_9c20c : decode_any W_9c20c = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c210 : bv 32 := 0x01013a03.
Lemma F_9c210 : fetch_word AsanUbsan.M.loaded_segments (0x9c260 : word) = Some W_9c210.
Proof. vm_refl. Qed.
Lemma D_9c210 : decode_any W_9c210 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c214 : bv 32 := 0x00813a83.
Lemma F_9c214 : fetch_word AsanUbsan.M.loaded_segments (0x9c264 : word) = Some W_9c214.
Proof. vm_refl. Qed.
Lemma D_9c214 : decode_any W_9c214 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c218 : bv 32 := 0x04010113.
Lemma F_9c218 : fetch_word AsanUbsan.M.loaded_segments (0x9c268 : word) = Some W_9c218.
Proof. vm_refl. Qed.
Lemma D_9c218 : decode_any W_9c218 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c21c : bv 32 := 0x891ff06f.
Lemma F_9c21c : fetch_word AsanUbsan.M.loaded_segments (0x9c26c : word) = Some W_9c21c.
Proof. vm_refl. Qed.
Lemma D_9c21c : decode_any W_9c21c = Some (Jal 0 2095248, 4%Z).
Proof. vm_refl. Qed.
