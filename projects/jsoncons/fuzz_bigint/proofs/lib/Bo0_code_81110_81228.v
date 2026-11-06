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

Definition W_81110 : bv 32 := 0xfc010113.
Lemma F_81110 : fetch_word AsanUbsan.M.loaded_segments (0x81110 : word) = Some W_81110.
Proof. vm_refl. Qed.
Lemma D_81110 : decode_any W_81110 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_81114 : bv 32 := 0x02113c23.
Lemma F_81114 : fetch_word AsanUbsan.M.loaded_segments (0x81114 : word) = Some W_81114.
Proof. vm_refl. Qed.
Lemma D_81114 : decode_any W_81114 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_81118 : bv 32 := 0x02813823.
Lemma F_81118 : fetch_word AsanUbsan.M.loaded_segments (0x81118 : word) = Some W_81118.
Proof. vm_refl. Qed.
Lemma D_81118 : decode_any W_81118 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_8111c : bv 32 := 0x02913423.
Lemma F_8111c : fetch_word AsanUbsan.M.loaded_segments (0x8111c : word) = Some W_8111c.
Proof. vm_refl. Qed.
Lemma D_8111c : decode_any W_8111c = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_81120 : bv 32 := 0x03213023.
Lemma F_81120 : fetch_word AsanUbsan.M.loaded_segments (0x81120 : word) = Some W_81120.
Proof. vm_refl. Qed.
Lemma D_81120 : decode_any W_81120 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_81124 : bv 32 := 0x01313c23.
Lemma F_81124 : fetch_word AsanUbsan.M.loaded_segments (0x81124 : word) = Some W_81124.
Proof. vm_refl. Qed.
Lemma D_81124 : decode_any W_81124 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_81128 : bv 32 := 0x01413823.
Lemma F_81128 : fetch_word AsanUbsan.M.loaded_segments (0x81128 : word) = Some W_81128.
Proof. vm_refl. Qed.
Lemma D_81128 : decode_any W_81128 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8112c : bv 32 := 0x01513423.
Lemma F_8112c : fetch_word AsanUbsan.M.loaded_segments (0x8112c : word) = Some W_8112c.
Proof. vm_refl. Qed.
Lemma D_8112c : decode_any W_8112c = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_81130 : bv 32 := 0x00058413.
Lemma F_81130 : fetch_word AsanUbsan.M.loaded_segments (0x81130 : word) = Some W_81130.
Proof. vm_refl. Qed.
Lemma D_81130 : decode_any W_81130 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81134 : bv 32 := 0x0015b593.
Lemma F_81134 : fetch_word AsanUbsan.M.loaded_segments (0x81134 : word) = Some W_81134.
Proof. vm_refl. Qed.
Lemma D_81134 : decode_any W_81134 = Some (OpImm ALU_SLTU 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_81138 : bv 32 := 0x7ff50293.
Lemma F_81138 : fetch_word AsanUbsan.M.loaded_segments (0x81138 : word) = Some W_81138.
Proof. vm_refl. Qed.
Lemma D_81138 : decode_any W_81138 = Some (OpImm ALU_ADD 5 10 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_8113c : bv 32 := 0xfff58593.
Lemma F_8113c : fetch_word AsanUbsan.M.loaded_segments (0x8113c : word) = Some W_8113c.
Proof. vm_refl. Qed.
Lemma D_8113c : decode_any W_8113c = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_81140 : bv 32 := 0x00d5f333.
Lemma F_81140 : fetch_word AsanUbsan.M.loaded_segments (0x81140 : word) = Some W_81140.
Proof. vm_refl. Qed.
Lemma D_81140 : decode_any W_81140 = Some (Op ALU_AND 6 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_81144 : bv 32 := 0x00100593.
Lemma F_81144 : fetch_word AsanUbsan.M.loaded_segments (0x81144 : word) = Some W_81144.
Proof. vm_refl. Qed.
Lemma D_81144 : decode_any W_81144 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_81148 : bv 32 := 0x0062b4a3.
Lemma F_81148 : fetch_word AsanUbsan.M.loaded_segments (0x81148 : word) = Some W_81148.
Proof. vm_refl. Qed.
Lemma D_81148 : decode_any W_81148 = Some (Store SZ8 5 6 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_8114c : bv 32 := 0x00b40863.
Lemma F_8114c : fetch_word AsanUbsan.M.loaded_segments (0x8114c : word) = Some W_8114c.
Proof. vm_refl. Qed.
Lemma D_8114c : decode_any W_8114c = Some (Branch BC_EQ 8 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_81150 : bv 32 := 0x02041c63.
Lemma F_81150 : fetch_word AsanUbsan.M.loaded_segments (0x81150 : word) = Some W_81150.
Proof. vm_refl. Qed.
Lemma D_81150 : decode_any W_81150 = Some (Branch BC_NE 8 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_81154 : bv 32 := 0x00052423.
Lemma F_81154 : fetch_word AsanUbsan.M.loaded_segments (0x81154 : word) = Some W_81154.
Proof. vm_refl. Qed.
Lemma D_81154 : decode_any W_81154 = Some (Store SZ4 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_81158 : bv 32 := 0x00c0006f.
Lemma F_81158 : fetch_word AsanUbsan.M.loaded_segments (0x81158 : word) = Some W_81158.
Proof. vm_refl. Qed.
Lemma D_81158 : decode_any W_81158 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_8115c : bv 32 := 0x00b52423.
Lemma F_8115c : fetch_word AsanUbsan.M.loaded_segments (0x8115c : word) = Some W_8115c.
Proof. vm_refl. Qed.
Lemma D_8115c : decode_any W_8115c = Some (Store SZ4 10 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_81160 : bv 32 := 0x00c53823.
Lemma F_81160 : fetch_word AsanUbsan.M.loaded_segments (0x81160 : word) = Some W_81160.
Proof. vm_refl. Qed.
Lemma D_81160 : decode_any W_81160 = Some (Store SZ8 10 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_81164 : bv 32 := 0x03813083.
Lemma F_81164 : fetch_word AsanUbsan.M.loaded_segments (0x81164 : word) = Some W_81164.
Proof. vm_refl. Qed.
Lemma D_81164 : decode_any W_81164 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_81168 : bv 32 := 0x03013403.
Lemma F_81168 : fetch_word AsanUbsan.M.loaded_segments (0x81168 : word) = Some W_81168.
Proof. vm_refl. Qed.
Lemma D_81168 : decode_any W_81168 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_8116c : bv 32 := 0x02813483.
Lemma F_8116c : fetch_word AsanUbsan.M.loaded_segments (0x8116c : word) = Some W_8116c.
Proof. vm_refl. Qed.
Lemma D_8116c : decode_any W_8116c = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_81170 : bv 32 := 0x02013903.
Lemma F_81170 : fetch_word AsanUbsan.M.loaded_segments (0x81170 : word) = Some W_81170.
Proof. vm_refl. Qed.
Lemma D_81170 : decode_any W_81170 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_81174 : bv 32 := 0x01813983.
Lemma F_81174 : fetch_word AsanUbsan.M.loaded_segments (0x81174 : word) = Some W_81174.
Proof. vm_refl. Qed.
Lemma D_81174 : decode_any W_81174 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_81178 : bv 32 := 0x01013a03.
Lemma F_81178 : fetch_word AsanUbsan.M.loaded_segments (0x81178 : word) = Some W_81178.
Proof. vm_refl. Qed.
Lemma D_81178 : decode_any W_81178 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8117c : bv 32 := 0x00813a83.
Lemma F_8117c : fetch_word AsanUbsan.M.loaded_segments (0x8117c : word) = Some W_8117c.
Proof. vm_refl. Qed.
Lemma D_8117c : decode_any W_8117c = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_81180 : bv 32 := 0x04010113.
Lemma F_81180 : fetch_word AsanUbsan.M.loaded_segments (0x81180 : word) = Some W_81180.
Proof. vm_refl. Qed.
Lemma D_81180 : decode_any W_81180 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_81184 : bv 32 := 0x00008067.
Lemma F_81184 : fetch_word AsanUbsan.M.loaded_segments (0x81184 : word) = Some W_81184.
Proof. vm_refl. Qed.
Lemma D_81184 : decode_any W_81184 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81188 : bv 32 := 0x06089463.
Lemma F_81188 : fetch_word AsanUbsan.M.loaded_segments (0x81188 : word) = Some W_81188.
Proof. vm_refl. Qed.
Lemma D_81188 : decode_any W_81188 = Some (Branch BC_NE 17 0 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_8118c : bv 32 := 0x00068493.
Lemma F_8118c : fetch_word AsanUbsan.M.loaded_segments (0x8118c : word) = Some W_8118c.
Proof. vm_refl. Qed.
Lemma D_8118c : decode_any W_8118c = Some (OpImm ALU_ADD 9 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81190 : bv 32 := 0x00078913.
Lemma F_81190 : fetch_word AsanUbsan.M.loaded_segments (0x81190 : word) = Some W_81190.
Proof. vm_refl. Qed.
Lemma D_81190 : decode_any W_81190 = Some (OpImm ALU_ADD 18 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81194 : bv 32 := 0x00080993.
Lemma F_81194 : fetch_word AsanUbsan.M.loaded_segments (0x81194 : word) = Some W_81194.
Proof. vm_refl. Qed.
Lemma D_81194 : decode_any W_81194 = Some (OpImm ALU_ADD 19 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81198 : bv 32 := 0x00050a93.
Lemma F_81198 : fetch_word AsanUbsan.M.loaded_segments (0x81198 : word) = Some W_81198.
Proof. vm_refl. Qed.
Lemma D_81198 : decode_any W_81198 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8119c : bv 32 := 0x00060a13.
Lemma F_8119c : fetch_word AsanUbsan.M.loaded_segments (0x8119c : word) = Some W_8119c.
Proof. vm_refl. Qed.
Lemma D_8119c : decode_any W_8119c = Some (OpImm ALU_ADD 20 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_811a0 : bv 32 := 0x00060593.
Lemma F_811a0 : fetch_word AsanUbsan.M.loaded_segments (0x811a0 : word) = Some W_811a0.
Proof. vm_refl. Qed.
Lemma D_811a0 : decode_any W_811a0 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_811a4 : bv 32 := 0x02070063.
Lemma F_811a4 : fetch_word AsanUbsan.M.loaded_segments (0x811a4 : word) = Some W_811a4.
Proof. vm_refl. Qed.
Lemma D_811a4 : decode_any W_811a4 = Some (Branch BC_EQ 14 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_811a8 : bv 32 := 0x00070613.
Lemma F_811a8 : fetch_word AsanUbsan.M.loaded_segments (0x811a8 : word) = Some W_811a8.
Proof. vm_refl. Qed.
Lemma D_811a8 : decode_any W_811a8 = Some (OpImm ALU_ADD 12 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_811ac : bv 32 := 0x00040693.
Lemma F_811ac : fetch_word AsanUbsan.M.loaded_segments (0x811ac : word) = Some W_811ac.
Proof. vm_refl. Qed.
Lemma D_811ac : decode_any W_811ac = Some (OpImm ALU_ADD 13 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_811b0 : bv 32 := 0x45c060ef.
Lemma F_811b0 : fetch_word AsanUbsan.M.loaded_segments (0x811b0 : word) = Some W_811b0.
Proof. vm_refl. Qed.
Lemma D_811b0 : decode_any W_811b0 = Some (Jal 1 25692, 4%Z).
Proof. vm_refl. Qed.

Definition W_811b4 : bv 32 := 0x008aa583.
Lemma F_811b4 : fetch_word AsanUbsan.M.loaded_segments (0x811b4 : word) = Some W_811b4.
Proof. vm_refl. Qed.
Lemma D_811b4 : decode_any W_811b4 = Some (Load SZ4 true 11 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_811b8 : bv 32 := 0x00200713.
Lemma F_811b8 : fetch_word AsanUbsan.M.loaded_segments (0x811b8 : word) = Some W_811b8.
Proof. vm_refl. Qed.
Lemma D_811b8 : decode_any W_811b8 = Some (OpImm ALU_ADD 14 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_811bc : bv 32 := 0x00b77e63.
Lemma F_811bc : fetch_word AsanUbsan.M.loaded_segments (0x811bc : word) = Some W_811bc.
Proof. vm_refl. Qed.
Lemma D_811bc : decode_any W_811bc = Some (Branch BC_GEU 14 11 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_811c0 : bv 32 := 0xfa5ff06f.
Lemma F_811c0 : fetch_word AsanUbsan.M.loaded_segments (0x811c0 : word) = Some W_811c0.
Proof. vm_refl. Qed.
Lemma D_811c0 : decode_any W_811c0 = Some (Jal 0 2097060, 4%Z).
Proof. vm_refl. Qed.

Definition W_811c4 : bv 32 := 0x00040613.
Lemma F_811c4 : fetch_word AsanUbsan.M.loaded_segments (0x811c4 : word) = Some W_811c4.
Proof. vm_refl. Qed.
Lemma D_811c4 : decode_any W_811c4 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_811c8 : bv 32 := 0x2b0060ef.
Lemma F_811c8 : fetch_word AsanUbsan.M.loaded_segments (0x811c8 : word) = Some W_811c8.
Proof. vm_refl. Qed.
Lemma D_811c8 : decode_any W_811c8 = Some (Jal 1 25264, 4%Z).
Proof. vm_refl. Qed.

Definition W_811cc : bv 32 := 0x008aa583.
Lemma F_811cc : fetch_word AsanUbsan.M.loaded_segments (0x811cc : word) = Some W_811cc.
Proof. vm_refl. Qed.
Lemma D_811cc : decode_any W_811cc = Some (Load SZ4 true 11 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_811d0 : bv 32 := 0x00200713.
Lemma F_811d0 : fetch_word AsanUbsan.M.loaded_segments (0x811d0 : word) = Some W_811d0.
Proof. vm_refl. Qed.
Lemma D_811d0 : decode_any W_811d0 = Some (OpImm ALU_ADD 14 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_811d4 : bv 32 := 0xf8b768e3.
Lemma F_811d4 : fetch_word AsanUbsan.M.loaded_segments (0x811d4 : word) = Some W_811d4.
Proof. vm_refl. Qed.
Lemma D_811d4 : decode_any W_811d4 = Some (Branch BC_LTU 14 11 8080, 4%Z).
Proof. vm_refl. Qed.

Definition W_811d8 : bv 32 := 0x000a8513.
Lemma F_811d8 : fetch_word AsanUbsan.M.loaded_segments (0x811d8 : word) = Some W_811d8.
Proof. vm_refl. Qed.
Lemma D_811d8 : decode_any W_811d8 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_811dc : bv 32 := 0x00098813.
Lemma F_811dc : fetch_word AsanUbsan.M.loaded_segments (0x811dc : word) = Some W_811dc.
Proof. vm_refl. Qed.
Lemma D_811dc : decode_any W_811dc = Some (OpImm ALU_ADD 16 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_811e0 : bv 32 := 0x00090793.
Lemma F_811e0 : fetch_word AsanUbsan.M.loaded_segments (0x811e0 : word) = Some W_811e0.
Proof. vm_refl. Qed.
Lemma D_811e0 : decode_any W_811e0 = Some (OpImm ALU_ADD 15 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_811e4 : bv 32 := 0x000a0613.
Lemma F_811e4 : fetch_word AsanUbsan.M.loaded_segments (0x811e4 : word) = Some W_811e4.
Proof. vm_refl. Qed.
Lemma D_811e4 : decode_any W_811e4 = Some (OpImm ALU_ADD 12 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_811e8 : bv 32 := 0x00048693.
Lemma F_811e8 : fetch_word AsanUbsan.M.loaded_segments (0x811e8 : word) = Some W_811e8.
Proof. vm_refl. Qed.
Lemma D_811e8 : decode_any W_811e8 = Some (OpImm ALU_ADD 13 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_811ec : bv 32 := 0xf685fce3.
Lemma F_811ec : fetch_word AsanUbsan.M.loaded_segments (0x811ec : word) = Some W_811ec.
Proof. vm_refl. Qed.
Lemma D_811ec : decode_any W_811ec = Some (Branch BC_GEU 11 8 8056, 4%Z).
Proof. vm_refl. Qed.

Definition W_811f0 : bv 32 := 0x00060593.
Lemma F_811f0 : fetch_word AsanUbsan.M.loaded_segments (0x811f0 : word) = Some W_811f0.
Proof. vm_refl. Qed.
Lemma D_811f0 : decode_any W_811f0 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_811f4 : bv 32 := 0x00068613.
Lemma F_811f4 : fetch_word AsanUbsan.M.loaded_segments (0x811f4 : word) = Some W_811f4.
Proof. vm_refl. Qed.
Lemma D_811f4 : decode_any W_811f4 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_811f8 : bv 32 := 0x00078693.
Lemma F_811f8 : fetch_word AsanUbsan.M.loaded_segments (0x811f8 : word) = Some W_811f8.
Proof. vm_refl. Qed.
Lemma D_811f8 : decode_any W_811f8 = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_811fc : bv 32 := 0x00080713.
Lemma F_811fc : fetch_word AsanUbsan.M.loaded_segments (0x811fc : word) = Some W_811fc.
Proof. vm_refl. Qed.
Lemma D_811fc : decode_any W_811fc = Some (OpImm ALU_ADD 14 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81200 : bv 32 := 0x00040793.
Lemma F_81200 : fetch_word AsanUbsan.M.loaded_segments (0x81200 : word) = Some W_81200.
Proof. vm_refl. Qed.
Lemma D_81200 : decode_any W_81200 = Some (OpImm ALU_ADD 15 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81204 : bv 32 := 0x03813083.
Lemma F_81204 : fetch_word AsanUbsan.M.loaded_segments (0x81204 : word) = Some W_81204.
Proof. vm_refl. Qed.
Lemma D_81204 : decode_any W_81204 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_81208 : bv 32 := 0x03013403.
Lemma F_81208 : fetch_word AsanUbsan.M.loaded_segments (0x81208 : word) = Some W_81208.
Proof. vm_refl. Qed.
Lemma D_81208 : decode_any W_81208 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_8120c : bv 32 := 0x02813483.
Lemma F_8120c : fetch_word AsanUbsan.M.loaded_segments (0x8120c : word) = Some W_8120c.
Proof. vm_refl. Qed.
Lemma D_8120c : decode_any W_8120c = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_81210 : bv 32 := 0x02013903.
Lemma F_81210 : fetch_word AsanUbsan.M.loaded_segments (0x81210 : word) = Some W_81210.
Proof. vm_refl. Qed.
Lemma D_81210 : decode_any W_81210 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_81214 : bv 32 := 0x01813983.
Lemma F_81214 : fetch_word AsanUbsan.M.loaded_segments (0x81214 : word) = Some W_81214.
Proof. vm_refl. Qed.
Lemma D_81214 : decode_any W_81214 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_81218 : bv 32 := 0x01013a03.
Lemma F_81218 : fetch_word AsanUbsan.M.loaded_segments (0x81218 : word) = Some W_81218.
Proof. vm_refl. Qed.
Lemma D_81218 : decode_any W_81218 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8121c : bv 32 := 0x00813a83.
Lemma F_8121c : fetch_word AsanUbsan.M.loaded_segments (0x8121c : word) = Some W_8121c.
Proof. vm_refl. Qed.
Lemma D_8121c : decode_any W_8121c = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_81220 : bv 32 := 0x04010113.
Lemma F_81220 : fetch_word AsanUbsan.M.loaded_segments (0x81220 : word) = Some W_81220.
Proof. vm_refl. Qed.
Lemma D_81220 : decode_any W_81220 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_81224 : bv 32 := 0x891ff06f.
Lemma F_81224 : fetch_word AsanUbsan.M.loaded_segments (0x81224 : word) = Some W_81224.
Proof. vm_refl. Qed.
Lemma D_81224 : decode_any W_81224 = Some (Jal 0 2095248, 4%Z).
Proof. vm_refl. Qed.
