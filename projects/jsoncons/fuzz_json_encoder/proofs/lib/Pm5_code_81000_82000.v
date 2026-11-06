(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_81000 : bv 32 := 0x06010113.
Lemma F_81000 : fetch_word AsanUbsan.M.loaded_segments (0x81048 : word) = Some W_81000.
Proof. vm_refl. Qed.
Lemma D_81000 : decode_any W_81000 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81004 : bv 32 := 0x7e813083.
Lemma F_81004 : fetch_word AsanUbsan.M.loaded_segments (0x8104c : word) = Some W_81004.
Proof. vm_refl. Qed.
Lemma D_81004 : decode_any W_81004 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81008 : bv 32 := 0x7e013403.
Lemma F_81008 : fetch_word AsanUbsan.M.loaded_segments (0x81050 : word) = Some W_81008.
Proof. vm_refl. Qed.
Lemma D_81008 : decode_any W_81008 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8100c : bv 32 := 0x7d813483.
Lemma F_8100c : fetch_word AsanUbsan.M.loaded_segments (0x81054 : word) = Some W_8100c.
Proof. vm_refl. Qed.
Lemma D_8100c : decode_any W_8100c = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81010 : bv 32 := 0x7d013903.
Lemma F_81010 : fetch_word AsanUbsan.M.loaded_segments (0x81058 : word) = Some W_81010.
Proof. vm_refl. Qed.
Lemma D_81010 : decode_any W_81010 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81014 : bv 32 := 0x7c813983.
Lemma F_81014 : fetch_word AsanUbsan.M.loaded_segments (0x8105c : word) = Some W_81014.
Proof. vm_refl. Qed.
Lemma D_81014 : decode_any W_81014 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81018 : bv 32 := 0x7c013a03.
Lemma F_81018 : fetch_word AsanUbsan.M.loaded_segments (0x81060 : word) = Some W_81018.
Proof. vm_refl. Qed.
Lemma D_81018 : decode_any W_81018 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8101c : bv 32 := 0x7b813a83.
Lemma F_8101c : fetch_word AsanUbsan.M.loaded_segments (0x81064 : word) = Some W_8101c.
Proof. vm_refl. Qed.
Lemma D_8101c : decode_any W_8101c = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81020 : bv 32 := 0x7f010113.
Lemma F_81020 : fetch_word AsanUbsan.M.loaded_segments (0x81068 : word) = Some W_81020.
Proof. vm_refl. Qed.
Lemma D_81020 : decode_any W_81020 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81024 : bv 32 := 0x00008067.
Lemma F_81024 : fetch_word AsanUbsan.M.loaded_segments (0x8106c : word) = Some W_81024.
Proof. vm_refl. Qed.
Lemma D_81024 : decode_any W_81024 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_810fc : bv 32 := 0x02061e63.
Lemma F_810fc : fetch_word AsanUbsan.M.loaded_segments (0x81144 : word) = Some W_810fc.
Proof. vm_refl. Qed.
Lemma D_810fc : decode_any W_810fc = Some (Branch BC_NE 12 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81100 : bv 32 := 0xef5ff06f.
Lemma F_81100 : fetch_word AsanUbsan.M.loaded_segments (0x81148 : word) = Some W_81100.
Proof. vm_refl. Qed.
Lemma D_81100 : decode_any W_81100 = Some (Jal 0 2096884, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81104 : bv 32 := 0x00070803.
Lemma F_81104 : fetch_word AsanUbsan.M.loaded_segments (0x8114c : word) = Some W_81104.
Proof. vm_refl. Qed.
Lemma D_81104 : decode_any W_81104 = Some (Load SZ1 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81108 : bv 32 := 0x0077f793.
Lemma F_81108 : fetch_word AsanUbsan.M.loaded_segments (0x81150 : word) = Some W_81108.
Proof. vm_refl. Qed.
Lemma D_81108 : decode_any W_81108 = Some (OpImm ALU_AND 15 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8110c : bv 32 := 0x010038b3.
Lemma F_8110c : fetch_word AsanUbsan.M.loaded_segments (0x81154 : word) = Some W_8110c.
Proof. vm_refl. Qed.
Lemma D_8110c : decode_any W_8110c = Some (Op ALU_SLTU 17 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81110 : bv 32 := 0x0107a7b3.
Lemma F_81110 : fetch_word AsanUbsan.M.loaded_segments (0x81158 : word) = Some W_81110.
Proof. vm_refl. Qed.
Lemma D_81110 : decode_any W_81110 = Some (Op ALU_SLT 15 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81114 : bv 32 := 0x0017c793.
Lemma F_81114 : fetch_word AsanUbsan.M.loaded_segments (0x8115c : word) = Some W_81114.
Proof. vm_refl. Qed.
Lemma D_81114 : decode_any W_81114 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81118 : bv 32 := 0x00f8f7b3.
Lemma F_81118 : fetch_word AsanUbsan.M.loaded_segments (0x81160 : word) = Some W_81118.
Proof. vm_refl. Qed.
Lemma D_81118 : decode_any W_81118 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8111c : bv 32 := 0x00e6fa63.
Lemma F_8111c : fetch_word AsanUbsan.M.loaded_segments (0x81164 : word) = Some W_8111c.
Proof. vm_refl. Qed.
Lemma D_8111c : decode_any W_8111c = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81120 : bv 32 := 0x0006c803.
Lemma F_81120 : fetch_word AsanUbsan.M.loaded_segments (0x81168 : word) = Some W_81120.
Proof. vm_refl. Qed.
Lemma D_81120 : decode_any W_81120 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81124 : bv 32 := 0x00168693.
Lemma F_81124 : fetch_word AsanUbsan.M.loaded_segments (0x8116c : word) = Some W_81124.
Proof. vm_refl. Qed.
Lemma D_81124 : decode_any W_81124 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81128 : bv 32 := 0x00f867b3.
Lemma F_81128 : fetch_word AsanUbsan.M.loaded_segments (0x81170 : word) = Some W_81128.
Proof. vm_refl. Qed.
Lemma D_81128 : decode_any W_81128 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8112c : bv 32 := 0xfee69ae3.
Lemma F_8112c : fetch_word AsanUbsan.M.loaded_segments (0x81174 : word) = Some W_8112c.
Proof. vm_refl. Qed.
Lemma D_8112c : decode_any W_8112c = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81130 : bv 32 := 0x0ff7f693.
Lemma F_81130 : fetch_word AsanUbsan.M.loaded_segments (0x81178 : word) = Some W_81130.
Proof. vm_refl. Qed.
Lemma D_81130 : decode_any W_81130 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81134 : bv 32 := 0xec0680e3.
Lemma F_81134 : fetch_word AsanUbsan.M.loaded_segments (0x8117c : word) = Some W_81134.
Proof. vm_refl. Qed.
Lemma D_81134 : decode_any W_81134 = Some (Branch BC_EQ 13 0 7872, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81138 : bv 32 := 0x00050493.
Lemma F_81138 : fetch_word AsanUbsan.M.loaded_segments (0x81180 : word) = Some W_81138.
Proof. vm_refl. Qed.
Lemma D_81138 : decode_any W_81138 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8113c : bv 32 := 0x00058a93.
Lemma F_8113c : fetch_word AsanUbsan.M.loaded_segments (0x81184 : word) = Some W_8113c.
Proof. vm_refl. Qed.
Lemma D_8113c : decode_any W_8113c = Some (OpImm ALU_ADD 21 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81140 : bv 32 := 0x00060593.
Lemma F_81140 : fetch_word AsanUbsan.M.loaded_segments (0x81188 : word) = Some W_81140.
Proof. vm_refl. Qed.
Lemma D_81140 : decode_any W_81140 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81144 : bv 32 := 0x00060913.
Lemma F_81144 : fetch_word AsanUbsan.M.loaded_segments (0x8118c : word) = Some W_81144.
Proof. vm_refl. Qed.
Lemma D_81144 : decode_any W_81144 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81148 : bv 32 := 0x1ac030ef.
Lemma F_81148 : fetch_word AsanUbsan.M.loaded_segments (0x81190 : word) = Some W_81148.
Proof. vm_refl. Qed.
Lemma D_81148 : decode_any W_81148 = Some (Jal 1 12716, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8114c : bv 32 := 0x000a8593.
Lemma F_8114c : fetch_word AsanUbsan.M.loaded_segments (0x81194 : word) = Some W_8114c.
Proof. vm_refl. Qed.
Lemma D_8114c : decode_any W_8114c = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81150 : bv 32 := 0x00090613.
Lemma F_81150 : fetch_word AsanUbsan.M.loaded_segments (0x81198 : word) = Some W_81150.
Proof. vm_refl. Qed.
Lemma D_81150 : decode_any W_81150 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81154 : bv 32 := 0x00050993.
Lemma F_81154 : fetch_word AsanUbsan.M.loaded_segments (0x8119c : word) = Some W_81154.
Proof. vm_refl. Qed.
Lemma D_81154 : decode_any W_81154 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81158 : bv 32 := 0x00048513.
Lemma F_81158 : fetch_word AsanUbsan.M.loaded_segments (0x811a0 : word) = Some W_81158.
Proof. vm_refl. Qed.
Lemma D_81158 : decode_any W_81158 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8115c : bv 32 := 0xe8098ce3.
Lemma F_8115c : fetch_word AsanUbsan.M.loaded_segments (0x811a4 : word) = Some W_8115c.
Proof. vm_refl. Qed.
Lemma D_8115c : decode_any W_8115c = Some (Branch BC_EQ 19 0 7832, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_811a4 : bv 32 := 0x81010113.
Lemma F_811a4 : fetch_word AsanUbsan.M.loaded_segments (0x811ec : word) = Some W_811a4.
Proof. vm_refl. Qed.
Lemma D_811a4 : decode_any W_811a4 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_811a8 : bv 32 := 0x7e113423.
Lemma F_811a8 : fetch_word AsanUbsan.M.loaded_segments (0x811f0 : word) = Some W_811a8.
Proof. vm_refl. Qed.
Lemma D_811a8 : decode_any W_811a8 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_811ac : bv 32 := 0x7e813023.
Lemma F_811ac : fetch_word AsanUbsan.M.loaded_segments (0x811f4 : word) = Some W_811ac.
Proof. vm_refl. Qed.
Lemma D_811ac : decode_any W_811ac = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_811b0 : bv 32 := 0x7c913c23.
Lemma F_811b0 : fetch_word AsanUbsan.M.loaded_segments (0x811f8 : word) = Some W_811b0.
Proof. vm_refl. Qed.
Lemma D_811b0 : decode_any W_811b0 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_811b4 : bv 32 := 0x7d213823.
Lemma F_811b4 : fetch_word AsanUbsan.M.loaded_segments (0x811fc : word) = Some W_811b4.
Proof. vm_refl. Qed.
Lemma D_811b4 : decode_any W_811b4 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_811b8 : bv 32 := 0x7d313423.
Lemma F_811b8 : fetch_word AsanUbsan.M.loaded_segments (0x81200 : word) = Some W_811b8.
Proof. vm_refl. Qed.
Lemma D_811b8 : decode_any W_811b8 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_811bc : bv 32 := 0x7d413023.
Lemma F_811bc : fetch_word AsanUbsan.M.loaded_segments (0x81204 : word) = Some W_811bc.
Proof. vm_refl. Qed.
Lemma D_811bc : decode_any W_811bc = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_811c0 : bv 32 := 0x7b513c23.
Lemma F_811c0 : fetch_word AsanUbsan.M.loaded_segments (0x81208 : word) = Some W_811c0.
Proof. vm_refl. Qed.
Lemma D_811c0 : decode_any W_811c0 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_811c4 : bv 32 := 0x7b613823.
Lemma F_811c4 : fetch_word AsanUbsan.M.loaded_segments (0x8120c : word) = Some W_811c4.
Proof. vm_refl. Qed.
Lemma D_811c4 : decode_any W_811c4 = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_811c8 : bv 32 := 0x7f010413.
Lemma F_811c8 : fetch_word AsanUbsan.M.loaded_segments (0x81210 : word) = Some W_811c8.
Proof. vm_refl. Qed.
Lemma D_811c8 : decode_any W_811c8 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_811cc : bv 32 := 0xf9010113.
Lemma F_811cc : fetch_word AsanUbsan.M.loaded_segments (0x81214 : word) = Some W_811cc.
Proof. vm_refl. Qed.
Lemma D_811cc : decode_any W_811cc = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_811d0 : bv 32 := 0x000e4697.
Lemma F_811d0 : fetch_word AsanUbsan.M.loaded_segments (0x81218 : word) = Some W_811d0.
Proof. vm_refl. Qed.
Lemma D_811d0 : decode_any W_811d0 = Some (Auipc 13 228, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_811d4 : bv 32 := 0xe686b683.
Lemma F_811d4 : fetch_word AsanUbsan.M.loaded_segments (0x8121c : word) = Some W_811d4.
Proof. vm_refl. Qed.
Lemma D_811d4 : decode_any W_811d4 = Some (Load SZ8 true 13 13 3688, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_811d8 : bv 32 := 0x0006c683.
Lemma F_811d8 : fetch_word AsanUbsan.M.loaded_segments (0x81220 : word) = Some W_811d8.
Proof. vm_refl. Qed.
Lemma D_811d8 : decode_any W_811d8 = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_811dc : bv 32 := 0x0a068463.
Lemma F_811dc : fetch_word AsanUbsan.M.loaded_segments (0x81224 : word) = Some W_811dc.
Proof. vm_refl. Qed.
Lemma D_811dc : decode_any W_811dc = Some (Branch BC_EQ 13 0 168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_811e0 : bv 32 := 0xfff5c693.
Lemma F_811e0 : fetch_word AsanUbsan.M.loaded_segments (0x81228 : word) = Some W_811e0.
Proof. vm_refl. Qed.
Lemma D_811e0 : decode_any W_811e0 = Some (OpImm ALU_XOR 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_811e4 : bv 32 := 0x80040a13.
Lemma F_811e4 : fetch_word AsanUbsan.M.loaded_segments (0x8122c : word) = Some W_811e4.
Proof. vm_refl. Qed.
Lemma D_811e4 : decode_any W_811e4 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_811e8 : bv 32 := 0xfa8a0a13.
Lemma F_811e8 : fetch_word AsanUbsan.M.loaded_segments (0x81230 : word) = Some W_811e8.
Proof. vm_refl. Qed.
Lemma D_811e8 : decode_any W_811e8 = Some (OpImm ALU_ADD 20 20 4008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_811ec : bv 32 := 0x0cc6e463.
Lemma F_811ec : fetch_word AsanUbsan.M.loaded_segments (0x81234 : word) = Some W_811ec.
Proof. vm_refl. Qed.
Lemma D_811ec : decode_any W_811ec = Some (Branch BC_LTU 13 12 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_811f0 : bv 32 := 0xfbf60993.
Lemma F_811f0 : fetch_word AsanUbsan.M.loaded_segments (0x81238 : word) = Some W_811f0.
Proof. vm_refl. Qed.
Lemma D_811f0 : decode_any W_811f0 = Some (OpImm ALU_ADD 19 12 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_811f4 : bv 32 := 0xfbf00693.
Lemma F_811f4 : fetch_word AsanUbsan.M.loaded_segments (0x8123c : word) = Some W_811f4.
Proof. vm_refl. Qed.
Lemma D_811f4 : decode_any W_811f4 = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_811f8 : bv 32 := 0x1536f263.
Lemma F_811f8 : fetch_word AsanUbsan.M.loaded_segments (0x81240 : word) = Some W_811f8.
Proof. vm_refl. Qed.
Lemma D_811f8 : decode_any W_811f8 = Some (Branch BC_GEU 13 19 324, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_811fc : bv 32 := 0x000e3697.
Lemma F_811fc : fetch_word AsanUbsan.M.loaded_segments (0x81244 : word) = Some W_811fc.
Proof. vm_refl. Qed.
Lemma D_811fc : decode_any W_811fc = Some (Auipc 13 227, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81200 : bv 32 := 0x2d46b683.
Lemma F_81200 : fetch_word AsanUbsan.M.loaded_segments (0x81248 : word) = Some W_81200.
Proof. vm_refl. Qed.
Lemma D_81200 : decode_any W_81200 = Some (Load SZ8 true 13 13 724, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81204 : bv 32 := 0x00c587b3.
Lemma F_81204 : fetch_word AsanUbsan.M.loaded_segments (0x8124c : word) = Some W_81204.
Proof. vm_refl. Qed.
Lemma D_81204 : decode_any W_81204 = Some (Op ALU_ADD 15 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81208 : bv 32 := 0x0006b703.
Lemma F_81208 : fetch_word AsanUbsan.M.loaded_segments (0x81250 : word) = Some W_81208.
Proof. vm_refl. Qed.
Lemma D_81208 : decode_any W_81208 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8120c : bv 32 := 0x0035d693.
Lemma F_8120c : fetch_word AsanUbsan.M.loaded_segments (0x81254 : word) = Some W_8120c.
Proof. vm_refl. Qed.
Lemma D_8120c : decode_any W_8120c = Some (ShiftImm ALU_SRL 13 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81210 : bv 32 := 0xfff78793.
Lemma F_81210 : fetch_word AsanUbsan.M.loaded_segments (0x81258 : word) = Some W_81210.
Proof. vm_refl. Qed.
Lemma D_81210 : decode_any W_81210 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81214 : bv 32 := 0x0037d813.
Lemma F_81214 : fetch_word AsanUbsan.M.loaded_segments (0x8125c : word) = Some W_81214.
Proof. vm_refl. Qed.
Lemma D_81214 : decode_any W_81214 = Some (ShiftImm ALU_SRL 16 15 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81218 : bv 32 := 0x00d706b3.
Lemma F_81218 : fetch_word AsanUbsan.M.loaded_segments (0x81260 : word) = Some W_81218.
Proof. vm_refl. Qed.
Lemma D_81218 : decode_any W_81218 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8121c : bv 32 := 0x01070733.
Lemma F_8121c : fetch_word AsanUbsan.M.loaded_segments (0x81264 : word) = Some W_8121c.
Proof. vm_refl. Qed.
Lemma D_8121c : decode_any W_8121c = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81220 : bv 32 := 0xff86f813.
Lemma F_81220 : fetch_word AsanUbsan.M.loaded_segments (0x81268 : word) = Some W_81220.
Proof. vm_refl. Qed.
Lemma D_81220 : decode_any W_81220 = Some (OpImm ALU_AND 16 13 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81224 : bv 32 := 0xff877893.
Lemma F_81224 : fetch_word AsanUbsan.M.loaded_segments (0x8126c : word) = Some W_81224.
Proof. vm_refl. Qed.
Lemma D_81224 : decode_any W_81224 = Some (OpImm ALU_AND 17 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81228 : bv 32 := 0x00083803.
Lemma F_81228 : fetch_word AsanUbsan.M.loaded_segments (0x81270 : word) = Some W_81228.
Proof. vm_refl. Qed.
Lemma D_81228 : decode_any W_81228 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8122c : bv 32 := 0x0008b883.
Lemma F_8122c : fetch_word AsanUbsan.M.loaded_segments (0x81274 : word) = Some W_8122c.
Proof. vm_refl. Qed.
Lemma D_8122c : decode_any W_8122c = Some (Load SZ8 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81230 : bv 32 := 0x0108e833.
Lemma F_81230 : fetch_word AsanUbsan.M.loaded_segments (0x81278 : word) = Some W_81230.
Proof. vm_refl. Qed.
Lemma D_81230 : decode_any W_81230 = Some (Op ALU_OR 16 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81234 : bv 32 := 0x18081e63.
Lemma F_81234 : fetch_word AsanUbsan.M.loaded_segments (0x8127c : word) = Some W_81234.
Proof. vm_refl. Qed.
Lemma D_81234 : decode_any W_81234 = Some (Branch BC_NE 16 0 412, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81238 : bv 32 := 0xfff54693.
Lemma F_81238 : fetch_word AsanUbsan.M.loaded_segments (0x81280 : word) = Some W_81238.
Proof. vm_refl. Qed.
Lemma D_81238 : decode_any W_81238 = Some (OpImm ALU_XOR 13 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8123c : bv 32 := 0x10c6e463.
Lemma F_8123c : fetch_word AsanUbsan.M.loaded_segments (0x81284 : word) = Some W_8123c.
Proof. vm_refl. Qed.
Lemma D_8123c : decode_any W_8123c = Some (Branch BC_LTU 13 12 264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81240 : bv 32 := 0xfbf00693.
Lemma F_81240 : fetch_word AsanUbsan.M.loaded_segments (0x81288 : word) = Some W_81240.
Proof. vm_refl. Qed.
Lemma D_81240 : decode_any W_81240 = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81244 : bv 32 := 0x1936f263.
Lemma F_81244 : fetch_word AsanUbsan.M.loaded_segments (0x8128c : word) = Some W_81244.
Proof. vm_refl. Qed.
Lemma D_81244 : decode_any W_81244 = Some (Branch BC_GEU 13 19 388, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81248 : bv 32 := 0x000e3697.
Lemma F_81248 : fetch_word AsanUbsan.M.loaded_segments (0x81290 : word) = Some W_81248.
Proof. vm_refl. Qed.
Lemma D_81248 : decode_any W_81248 = Some (Auipc 13 227, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8124c : bv 32 := 0x2886b683.
Lemma F_8124c : fetch_word AsanUbsan.M.loaded_segments (0x81294 : word) = Some W_8124c.
Proof. vm_refl. Qed.
Lemma D_8124c : decode_any W_8124c = Some (Load SZ8 true 13 13 648, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81250 : bv 32 := 0x00c507b3.
Lemma F_81250 : fetch_word AsanUbsan.M.loaded_segments (0x81298 : word) = Some W_81250.
Proof. vm_refl. Qed.
Lemma D_81250 : decode_any W_81250 = Some (Op ALU_ADD 15 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81254 : bv 32 := 0x0006b703.
Lemma F_81254 : fetch_word AsanUbsan.M.loaded_segments (0x8129c : word) = Some W_81254.
Proof. vm_refl. Qed.
Lemma D_81254 : decode_any W_81254 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81258 : bv 32 := 0x00355693.
Lemma F_81258 : fetch_word AsanUbsan.M.loaded_segments (0x812a0 : word) = Some W_81258.
Proof. vm_refl. Qed.
Lemma D_81258 : decode_any W_81258 = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8125c : bv 32 := 0xfff78793.
Lemma F_8125c : fetch_word AsanUbsan.M.loaded_segments (0x812a4 : word) = Some W_8125c.
Proof. vm_refl. Qed.
Lemma D_8125c : decode_any W_8125c = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81260 : bv 32 := 0x0037d813.
Lemma F_81260 : fetch_word AsanUbsan.M.loaded_segments (0x812a8 : word) = Some W_81260.
Proof. vm_refl. Qed.
Lemma D_81260 : decode_any W_81260 = Some (ShiftImm ALU_SRL 16 15 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81264 : bv 32 := 0x00d706b3.
Lemma F_81264 : fetch_word AsanUbsan.M.loaded_segments (0x812ac : word) = Some W_81264.
Proof. vm_refl. Qed.
Lemma D_81264 : decode_any W_81264 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81268 : bv 32 := 0x01070733.
Lemma F_81268 : fetch_word AsanUbsan.M.loaded_segments (0x812b0 : word) = Some W_81268.
Proof. vm_refl. Qed.
Lemma D_81268 : decode_any W_81268 = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8126c : bv 32 := 0xff86f813.
Lemma F_8126c : fetch_word AsanUbsan.M.loaded_segments (0x812b4 : word) = Some W_8126c.
Proof. vm_refl. Qed.
Lemma D_8126c : decode_any W_8126c = Some (OpImm ALU_AND 16 13 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81270 : bv 32 := 0xff877893.
Lemma F_81270 : fetch_word AsanUbsan.M.loaded_segments (0x812b8 : word) = Some W_81270.
Proof. vm_refl. Qed.
Lemma D_81270 : decode_any W_81270 = Some (OpImm ALU_AND 17 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81274 : bv 32 := 0x00083803.
Lemma F_81274 : fetch_word AsanUbsan.M.loaded_segments (0x812bc : word) = Some W_81274.
Proof. vm_refl. Qed.
Lemma D_81274 : decode_any W_81274 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81278 : bv 32 := 0x0008b883.
Lemma F_81278 : fetch_word AsanUbsan.M.loaded_segments (0x812c0 : word) = Some W_81278.
Proof. vm_refl. Qed.
Lemma D_81278 : decode_any W_81278 = Some (Load SZ8 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8127c : bv 32 := 0x0108e833.
Lemma F_8127c : fetch_word AsanUbsan.M.loaded_segments (0x812c4 : word) = Some W_8127c.
Proof. vm_refl. Qed.
Lemma D_8127c : decode_any W_8127c = Some (Op ALU_OR 16 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81280 : bv 32 := 0x1e081a63.
Lemma F_81280 : fetch_word AsanUbsan.M.loaded_segments (0x812c8 : word) = Some W_81280.
Proof. vm_refl. Qed.
Lemma D_81280 : decode_any W_81280 = Some (Branch BC_NE 16 0 500, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81284 : bv 32 := 0x7b9120ef.
Lemma F_81284 : fetch_word AsanUbsan.M.loaded_segments (0x812cc : word) = Some W_81284.
Proof. vm_refl. Qed.
Lemma D_81284 : decode_any W_81284 = Some (Jal 1 77752, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81288 : bv 32 := 0x07010113.
Lemma F_81288 : fetch_word AsanUbsan.M.loaded_segments (0x812d0 : word) = Some W_81288.
Proof. vm_refl. Qed.
Lemma D_81288 : decode_any W_81288 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8128c : bv 32 := 0x7e813083.
Lemma F_8128c : fetch_word AsanUbsan.M.loaded_segments (0x812d4 : word) = Some W_8128c.
Proof. vm_refl. Qed.
Lemma D_8128c : decode_any W_8128c = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81290 : bv 32 := 0x7e013403.
Lemma F_81290 : fetch_word AsanUbsan.M.loaded_segments (0x812d8 : word) = Some W_81290.
Proof. vm_refl. Qed.
Lemma D_81290 : decode_any W_81290 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81294 : bv 32 := 0x7d813483.
Lemma F_81294 : fetch_word AsanUbsan.M.loaded_segments (0x812dc : word) = Some W_81294.
Proof. vm_refl. Qed.
Lemma D_81294 : decode_any W_81294 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81298 : bv 32 := 0x7d013903.
Lemma F_81298 : fetch_word AsanUbsan.M.loaded_segments (0x812e0 : word) = Some W_81298.
Proof. vm_refl. Qed.
Lemma D_81298 : decode_any W_81298 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8129c : bv 32 := 0x7c813983.
Lemma F_8129c : fetch_word AsanUbsan.M.loaded_segments (0x812e4 : word) = Some W_8129c.
Proof. vm_refl. Qed.
Lemma D_8129c : decode_any W_8129c = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_812a0 : bv 32 := 0x7c013a03.
Lemma F_812a0 : fetch_word AsanUbsan.M.loaded_segments (0x812e8 : word) = Some W_812a0.
Proof. vm_refl. Qed.
Lemma D_812a0 : decode_any W_812a0 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_812a4 : bv 32 := 0x7b813a83.
Lemma F_812a4 : fetch_word AsanUbsan.M.loaded_segments (0x812ec : word) = Some W_812a4.
Proof. vm_refl. Qed.
Lemma D_812a4 : decode_any W_812a4 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_812a8 : bv 32 := 0x7b013b03.
Lemma F_812a8 : fetch_word AsanUbsan.M.loaded_segments (0x812f0 : word) = Some W_812a8.
Proof. vm_refl. Qed.
Lemma D_812a8 : decode_any W_812a8 = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_812ac : bv 32 := 0x7f010113.
Lemma F_812ac : fetch_word AsanUbsan.M.loaded_segments (0x812f4 : word) = Some W_812ac.
Proof. vm_refl. Qed.
Lemma D_812ac : decode_any W_812ac = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_812b0 : bv 32 := 0x00008067.
Lemma F_812b0 : fetch_word AsanUbsan.M.loaded_segments (0x812f8 : word) = Some W_812b0.
Proof. vm_refl. Qed.
Lemma D_812b0 : decode_any W_812b0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8133c : bv 32 := 0x0c061463.
Lemma F_8133c : fetch_word AsanUbsan.M.loaded_segments (0x81384 : word) = Some W_8133c.
Proof. vm_refl. Qed.
Lemma D_8133c : decode_any W_8133c = Some (Branch BC_NE 12 0 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81340 : bv 32 := 0xef9ff06f.
Lemma F_81340 : fetch_word AsanUbsan.M.loaded_segments (0x81388 : word) = Some W_81340.
Proof. vm_refl. Qed.
Lemma D_81340 : decode_any W_81340 = Some (Jal 0 2096888, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_813c8 : bv 32 := 0x0e061063.
Lemma F_813c8 : fetch_word AsanUbsan.M.loaded_segments (0x81410 : word) = Some W_813c8.
Proof. vm_refl. Qed.
Lemma D_813c8 : decode_any W_813c8 = Some (Branch BC_NE 12 0 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_813cc : bv 32 := 0xeb9ff06f.
Lemma F_813cc : fetch_word AsanUbsan.M.loaded_segments (0x81414 : word) = Some W_813cc.
Proof. vm_refl. Qed.
Lemma D_813cc : decode_any W_813cc = Some (Jal 0 2096824, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_813d0 : bv 32 := 0x00070803.
Lemma F_813d0 : fetch_word AsanUbsan.M.loaded_segments (0x81418 : word) = Some W_813d0.
Proof. vm_refl. Qed.
Lemma D_813d0 : decode_any W_813d0 = Some (Load SZ1 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_813d4 : bv 32 := 0x0077f793.
Lemma F_813d4 : fetch_word AsanUbsan.M.loaded_segments (0x8141c : word) = Some W_813d4.
Proof. vm_refl. Qed.
Lemma D_813d4 : decode_any W_813d4 = Some (OpImm ALU_AND 15 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_813d8 : bv 32 := 0x010038b3.
Lemma F_813d8 : fetch_word AsanUbsan.M.loaded_segments (0x81420 : word) = Some W_813d8.
Proof. vm_refl. Qed.
Lemma D_813d8 : decode_any W_813d8 = Some (Op ALU_SLTU 17 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_813dc : bv 32 := 0x0107a7b3.
Lemma F_813dc : fetch_word AsanUbsan.M.loaded_segments (0x81424 : word) = Some W_813dc.
Proof. vm_refl. Qed.
Lemma D_813dc : decode_any W_813dc = Some (Op ALU_SLT 15 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_813e0 : bv 32 := 0x0017c793.
Lemma F_813e0 : fetch_word AsanUbsan.M.loaded_segments (0x81428 : word) = Some W_813e0.
Proof. vm_refl. Qed.
Lemma D_813e0 : decode_any W_813e0 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_813e4 : bv 32 := 0x00f8f7b3.
Lemma F_813e4 : fetch_word AsanUbsan.M.loaded_segments (0x8142c : word) = Some W_813e4.
Proof. vm_refl. Qed.
Lemma D_813e4 : decode_any W_813e4 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_813e8 : bv 32 := 0x00e6fa63.
Lemma F_813e8 : fetch_word AsanUbsan.M.loaded_segments (0x81430 : word) = Some W_813e8.
Proof. vm_refl. Qed.
Lemma D_813e8 : decode_any W_813e8 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_813ec : bv 32 := 0x0006c803.
Lemma F_813ec : fetch_word AsanUbsan.M.loaded_segments (0x81434 : word) = Some W_813ec.
Proof. vm_refl. Qed.
Lemma D_813ec : decode_any W_813ec = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_813f0 : bv 32 := 0x00168693.
Lemma F_813f0 : fetch_word AsanUbsan.M.loaded_segments (0x81438 : word) = Some W_813f0.
Proof. vm_refl. Qed.
Lemma D_813f0 : decode_any W_813f0 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_813f4 : bv 32 := 0x00f867b3.
Lemma F_813f4 : fetch_word AsanUbsan.M.loaded_segments (0x8143c : word) = Some W_813f4.
Proof. vm_refl. Qed.
Lemma D_813f4 : decode_any W_813f4 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_813f8 : bv 32 := 0xfee69ae3.
Lemma F_813f8 : fetch_word AsanUbsan.M.loaded_segments (0x81440 : word) = Some W_813f8.
Proof. vm_refl. Qed.
Lemma D_813f8 : decode_any W_813f8 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_813fc : bv 32 := 0x0ff7f693.
Lemma F_813fc : fetch_word AsanUbsan.M.loaded_segments (0x81444 : word) = Some W_813fc.
Proof. vm_refl. Qed.
Lemma D_813fc : decode_any W_813fc = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81400 : bv 32 := 0xe2068ce3.
Lemma F_81400 : fetch_word AsanUbsan.M.loaded_segments (0x81448 : word) = Some W_81400.
Proof. vm_refl. Qed.
Lemma D_81400 : decode_any W_81400 = Some (Branch BC_EQ 13 0 7736, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81404 : bv 32 := 0x00050a93.
Lemma F_81404 : fetch_word AsanUbsan.M.loaded_segments (0x8144c : word) = Some W_81404.
Proof. vm_refl. Qed.
Lemma D_81404 : decode_any W_81404 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81408 : bv 32 := 0x00058513.
Lemma F_81408 : fetch_word AsanUbsan.M.loaded_segments (0x81450 : word) = Some W_81408.
Proof. vm_refl. Qed.
Lemma D_81408 : decode_any W_81408 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8140c : bv 32 := 0x00058b13.
Lemma F_8140c : fetch_word AsanUbsan.M.loaded_segments (0x81454 : word) = Some W_8140c.
Proof. vm_refl. Qed.
Lemma D_8140c : decode_any W_8140c = Some (OpImm ALU_ADD 22 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81410 : bv 32 := 0x00060593.
Lemma F_81410 : fetch_word AsanUbsan.M.loaded_segments (0x81458 : word) = Some W_81410.
Proof. vm_refl. Qed.
Lemma D_81410 : decode_any W_81410 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81414 : bv 32 := 0x00060493.
Lemma F_81414 : fetch_word AsanUbsan.M.loaded_segments (0x8145c : word) = Some W_81414.
Proof. vm_refl. Qed.
Lemma D_81414 : decode_any W_81414 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81418 : bv 32 := 0x6dd020ef.
Lemma F_81418 : fetch_word AsanUbsan.M.loaded_segments (0x81460 : word) = Some W_81418.
Proof. vm_refl. Qed.
Lemma D_81418 : decode_any W_81418 = Some (Jal 1 11996, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8141c : bv 32 := 0x000b0593.
Lemma F_8141c : fetch_word AsanUbsan.M.loaded_segments (0x81464 : word) = Some W_8141c.
Proof. vm_refl. Qed.
Lemma D_8141c : decode_any W_8141c = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81420 : bv 32 := 0x00048613.
Lemma F_81420 : fetch_word AsanUbsan.M.loaded_segments (0x81468 : word) = Some W_81420.
Proof. vm_refl. Qed.
Lemma D_81420 : decode_any W_81420 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81424 : bv 32 := 0x00050913.
Lemma F_81424 : fetch_word AsanUbsan.M.loaded_segments (0x8146c : word) = Some W_81424.
Proof. vm_refl. Qed.
Lemma D_81424 : decode_any W_81424 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81428 : bv 32 := 0x000a8513.
Lemma F_81428 : fetch_word AsanUbsan.M.loaded_segments (0x81470 : word) = Some W_81428.
Proof. vm_refl. Qed.
Lemma D_81428 : decode_any W_81428 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8142c : bv 32 := 0xe00906e3.
Lemma F_8142c : fetch_word AsanUbsan.M.loaded_segments (0x81474 : word) = Some W_8142c.
Proof. vm_refl. Qed.
Lemma D_8142c : decode_any W_8142c = Some (Branch BC_EQ 18 0 7692, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81474 : bv 32 := 0x00070803.
Lemma F_81474 : fetch_word AsanUbsan.M.loaded_segments (0x814bc : word) = Some W_81474.
Proof. vm_refl. Qed.
Lemma D_81474 : decode_any W_81474 = Some (Load SZ1 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81478 : bv 32 := 0x0077f793.
Lemma F_81478 : fetch_word AsanUbsan.M.loaded_segments (0x814c0 : word) = Some W_81478.
Proof. vm_refl. Qed.
Lemma D_81478 : decode_any W_81478 = Some (OpImm ALU_AND 15 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8147c : bv 32 := 0x010038b3.
Lemma F_8147c : fetch_word AsanUbsan.M.loaded_segments (0x814c4 : word) = Some W_8147c.
Proof. vm_refl. Qed.
Lemma D_8147c : decode_any W_8147c = Some (Op ALU_SLTU 17 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81480 : bv 32 := 0x0107a7b3.
Lemma F_81480 : fetch_word AsanUbsan.M.loaded_segments (0x814c8 : word) = Some W_81480.
Proof. vm_refl. Qed.
Lemma D_81480 : decode_any W_81480 = Some (Op ALU_SLT 15 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81484 : bv 32 := 0x0017c793.
Lemma F_81484 : fetch_word AsanUbsan.M.loaded_segments (0x814cc : word) = Some W_81484.
Proof. vm_refl. Qed.
Lemma D_81484 : decode_any W_81484 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81488 : bv 32 := 0x00f8f7b3.
Lemma F_81488 : fetch_word AsanUbsan.M.loaded_segments (0x814d0 : word) = Some W_81488.
Proof. vm_refl. Qed.
Lemma D_81488 : decode_any W_81488 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8148c : bv 32 := 0x00e6fa63.
Lemma F_8148c : fetch_word AsanUbsan.M.loaded_segments (0x814d4 : word) = Some W_8148c.
Proof. vm_refl. Qed.
Lemma D_8148c : decode_any W_8148c = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81490 : bv 32 := 0x0006c803.
Lemma F_81490 : fetch_word AsanUbsan.M.loaded_segments (0x814d8 : word) = Some W_81490.
Proof. vm_refl. Qed.
Lemma D_81490 : decode_any W_81490 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81494 : bv 32 := 0x00168693.
Lemma F_81494 : fetch_word AsanUbsan.M.loaded_segments (0x814dc : word) = Some W_81494.
Proof. vm_refl. Qed.
Lemma D_81494 : decode_any W_81494 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81498 : bv 32 := 0x00f867b3.
Lemma F_81498 : fetch_word AsanUbsan.M.loaded_segments (0x814e0 : word) = Some W_81498.
Proof. vm_refl. Qed.
Lemma D_81498 : decode_any W_81498 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8149c : bv 32 := 0xfee69ae3.
Lemma F_8149c : fetch_word AsanUbsan.M.loaded_segments (0x814e4 : word) = Some W_8149c.
Proof. vm_refl. Qed.
Lemma D_8149c : decode_any W_8149c = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_814a0 : bv 32 := 0x0ff7f693.
Lemma F_814a0 : fetch_word AsanUbsan.M.loaded_segments (0x814e8 : word) = Some W_814a0.
Proof. vm_refl. Qed.
Lemma D_814a0 : decode_any W_814a0 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_814a4 : bv 32 := 0xde0680e3.
Lemma F_814a4 : fetch_word AsanUbsan.M.loaded_segments (0x814ec : word) = Some W_814a4.
Proof. vm_refl. Qed.
Lemma D_814a4 : decode_any W_814a4 = Some (Branch BC_EQ 13 0 7648, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_814a8 : bv 32 := 0x00050493.
Lemma F_814a8 : fetch_word AsanUbsan.M.loaded_segments (0x814f0 : word) = Some W_814a8.
Proof. vm_refl. Qed.
Lemma D_814a8 : decode_any W_814a8 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_814ac : bv 32 := 0x00058a93.
Lemma F_814ac : fetch_word AsanUbsan.M.loaded_segments (0x814f4 : word) = Some W_814ac.
Proof. vm_refl. Qed.
Lemma D_814ac : decode_any W_814ac = Some (OpImm ALU_ADD 21 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_814b0 : bv 32 := 0x00060593.
Lemma F_814b0 : fetch_word AsanUbsan.M.loaded_segments (0x814f8 : word) = Some W_814b0.
Proof. vm_refl. Qed.
Lemma D_814b0 : decode_any W_814b0 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_814b4 : bv 32 := 0x00060913.
Lemma F_814b4 : fetch_word AsanUbsan.M.loaded_segments (0x814fc : word) = Some W_814b4.
Proof. vm_refl. Qed.
Lemma D_814b4 : decode_any W_814b4 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_814b8 : bv 32 := 0x63d020ef.
Lemma F_814b8 : fetch_word AsanUbsan.M.loaded_segments (0x81500 : word) = Some W_814b8.
Proof. vm_refl. Qed.
Lemma D_814b8 : decode_any W_814b8 = Some (Jal 1 11836, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_814bc : bv 32 := 0x000a8593.
Lemma F_814bc : fetch_word AsanUbsan.M.loaded_segments (0x81504 : word) = Some W_814bc.
Proof. vm_refl. Qed.
Lemma D_814bc : decode_any W_814bc = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_814c0 : bv 32 := 0x00090613.
Lemma F_814c0 : fetch_word AsanUbsan.M.loaded_segments (0x81508 : word) = Some W_814c0.
Proof. vm_refl. Qed.
Lemma D_814c0 : decode_any W_814c0 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_814c4 : bv 32 := 0x00050993.
Lemma F_814c4 : fetch_word AsanUbsan.M.loaded_segments (0x8150c : word) = Some W_814c4.
Proof. vm_refl. Qed.
Lemma D_814c4 : decode_any W_814c4 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_814c8 : bv 32 := 0x00048513.
Lemma F_814c8 : fetch_word AsanUbsan.M.loaded_segments (0x81510 : word) = Some W_814c8.
Proof. vm_refl. Qed.
Lemma D_814c8 : decode_any W_814c8 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_814cc : bv 32 := 0xda098ce3.
Lemma F_814cc : fetch_word AsanUbsan.M.loaded_segments (0x81514 : word) = Some W_814cc.
Proof. vm_refl. Qed.
Lemma D_814cc : decode_any W_814cc = Some (Branch BC_EQ 19 0 7608, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81804 : bv 32 := 0x81010113.
Lemma F_81804 : fetch_word AsanUbsan.M.loaded_segments (0x8184c : word) = Some W_81804.
Proof. vm_refl. Qed.
Lemma D_81804 : decode_any W_81804 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81808 : bv 32 := 0x7e113423.
Lemma F_81808 : fetch_word AsanUbsan.M.loaded_segments (0x81850 : word) = Some W_81808.
Proof. vm_refl. Qed.
Lemma D_81808 : decode_any W_81808 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8180c : bv 32 := 0x7e813023.
Lemma F_8180c : fetch_word AsanUbsan.M.loaded_segments (0x81854 : word) = Some W_8180c.
Proof. vm_refl. Qed.
Lemma D_8180c : decode_any W_8180c = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81810 : bv 32 := 0x7c913c23.
Lemma F_81810 : fetch_word AsanUbsan.M.loaded_segments (0x81858 : word) = Some W_81810.
Proof. vm_refl. Qed.
Lemma D_81810 : decode_any W_81810 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81814 : bv 32 := 0x7d213823.
Lemma F_81814 : fetch_word AsanUbsan.M.loaded_segments (0x8185c : word) = Some W_81814.
Proof. vm_refl. Qed.
Lemma D_81814 : decode_any W_81814 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81818 : bv 32 := 0x7d313423.
Lemma F_81818 : fetch_word AsanUbsan.M.loaded_segments (0x81860 : word) = Some W_81818.
Proof. vm_refl. Qed.
Lemma D_81818 : decode_any W_81818 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8181c : bv 32 := 0x7d413023.
Lemma F_8181c : fetch_word AsanUbsan.M.loaded_segments (0x81864 : word) = Some W_8181c.
Proof. vm_refl. Qed.
Lemma D_8181c : decode_any W_8181c = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81820 : bv 32 := 0x7b513c23.
Lemma F_81820 : fetch_word AsanUbsan.M.loaded_segments (0x81868 : word) = Some W_81820.
Proof. vm_refl. Qed.
Lemma D_81820 : decode_any W_81820 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81824 : bv 32 := 0x7b613823.
Lemma F_81824 : fetch_word AsanUbsan.M.loaded_segments (0x8186c : word) = Some W_81824.
Proof. vm_refl. Qed.
Lemma D_81824 : decode_any W_81824 = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81828 : bv 32 := 0x7b713423.
Lemma F_81828 : fetch_word AsanUbsan.M.loaded_segments (0x81870 : word) = Some W_81828.
Proof. vm_refl. Qed.
Lemma D_81828 : decode_any W_81828 = Some (Store SZ8 2 23 1960, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8182c : bv 32 := 0x7f010413.
Lemma F_8182c : fetch_word AsanUbsan.M.loaded_segments (0x81874 : word) = Some W_8182c.
Proof. vm_refl. Qed.
Lemma D_8182c : decode_any W_8182c = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81830 : bv 32 := 0xf9010113.
Lemma F_81830 : fetch_word AsanUbsan.M.loaded_segments (0x81878 : word) = Some W_81830.
Proof. vm_refl. Qed.
Lemma D_81830 : decode_any W_81830 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81834 : bv 32 := 0x000e4697.
Lemma F_81834 : fetch_word AsanUbsan.M.loaded_segments (0x8187c : word) = Some W_81834.
Proof. vm_refl. Qed.
Lemma D_81834 : decode_any W_81834 = Some (Auipc 13 228, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81838 : bv 32 := 0x8046b683.
Lemma F_81838 : fetch_word AsanUbsan.M.loaded_segments (0x81880 : word) = Some W_81838.
Proof. vm_refl. Qed.
Lemma D_81838 : decode_any W_81838 = Some (Load SZ8 true 13 13 2052, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8183c : bv 32 := 0x0006c683.
Lemma F_8183c : fetch_word AsanUbsan.M.loaded_segments (0x81884 : word) = Some W_8183c.
Proof. vm_refl. Qed.
Lemma D_8183c : decode_any W_8183c = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81840 : bv 32 := 0x0a068463.
Lemma F_81840 : fetch_word AsanUbsan.M.loaded_segments (0x81888 : word) = Some W_81840.
Proof. vm_refl. Qed.
Lemma D_81840 : decode_any W_81840 = Some (Branch BC_EQ 13 0 168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81844 : bv 32 := 0xfff5c693.
Lemma F_81844 : fetch_word AsanUbsan.M.loaded_segments (0x8188c : word) = Some W_81844.
Proof. vm_refl. Qed.
Lemma D_81844 : decode_any W_81844 = Some (OpImm ALU_XOR 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81848 : bv 32 := 0x80040a93.
Lemma F_81848 : fetch_word AsanUbsan.M.loaded_segments (0x81890 : word) = Some W_81848.
Proof. vm_refl. Qed.
Lemma D_81848 : decode_any W_81848 = Some (OpImm ALU_ADD 21 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8184c : bv 32 := 0xfa0a8a93.
Lemma F_8184c : fetch_word AsanUbsan.M.loaded_segments (0x81894 : word) = Some W_8184c.
Proof. vm_refl. Qed.
Lemma D_8184c : decode_any W_8184c = Some (OpImm ALU_ADD 21 21 4000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81850 : bv 32 := 0x0cc6e663.
Lemma F_81850 : fetch_word AsanUbsan.M.loaded_segments (0x81898 : word) = Some W_81850.
Proof. vm_refl. Qed.
Lemma D_81850 : decode_any W_81850 = Some (Branch BC_LTU 13 12 204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81854 : bv 32 := 0xfbf60a13.
Lemma F_81854 : fetch_word AsanUbsan.M.loaded_segments (0x8189c : word) = Some W_81854.
Proof. vm_refl. Qed.
Lemma D_81854 : decode_any W_81854 = Some (OpImm ALU_ADD 20 12 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81858 : bv 32 := 0xfbf00693.
Lemma F_81858 : fetch_word AsanUbsan.M.loaded_segments (0x818a0 : word) = Some W_81858.
Proof. vm_refl. Qed.
Lemma D_81858 : decode_any W_81858 = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8185c : bv 32 := 0x1546f463.
Lemma F_8185c : fetch_word AsanUbsan.M.loaded_segments (0x818a4 : word) = Some W_8185c.
Proof. vm_refl. Qed.
Lemma D_8185c : decode_any W_8185c = Some (Branch BC_GEU 13 20 328, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81860 : bv 32 := 0x000e3697.
Lemma F_81860 : fetch_word AsanUbsan.M.loaded_segments (0x818a8 : word) = Some W_81860.
Proof. vm_refl. Qed.
Lemma D_81860 : decode_any W_81860 = Some (Auipc 13 227, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81864 : bv 32 := 0xc706b683.
Lemma F_81864 : fetch_word AsanUbsan.M.loaded_segments (0x818ac : word) = Some W_81864.
Proof. vm_refl. Qed.
Lemma D_81864 : decode_any W_81864 = Some (Load SZ8 true 13 13 3184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81868 : bv 32 := 0x00c587b3.
Lemma F_81868 : fetch_word AsanUbsan.M.loaded_segments (0x818b0 : word) = Some W_81868.
Proof. vm_refl. Qed.
Lemma D_81868 : decode_any W_81868 = Some (Op ALU_ADD 15 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8186c : bv 32 := 0x0006b703.
Lemma F_8186c : fetch_word AsanUbsan.M.loaded_segments (0x818b4 : word) = Some W_8186c.
Proof. vm_refl. Qed.
Lemma D_8186c : decode_any W_8186c = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81870 : bv 32 := 0x0035d693.
Lemma F_81870 : fetch_word AsanUbsan.M.loaded_segments (0x818b8 : word) = Some W_81870.
Proof. vm_refl. Qed.
Lemma D_81870 : decode_any W_81870 = Some (ShiftImm ALU_SRL 13 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81874 : bv 32 := 0xfff78793.
Lemma F_81874 : fetch_word AsanUbsan.M.loaded_segments (0x818bc : word) = Some W_81874.
Proof. vm_refl. Qed.
Lemma D_81874 : decode_any W_81874 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81878 : bv 32 := 0x0037d813.
Lemma F_81878 : fetch_word AsanUbsan.M.loaded_segments (0x818c0 : word) = Some W_81878.
Proof. vm_refl. Qed.
Lemma D_81878 : decode_any W_81878 = Some (ShiftImm ALU_SRL 16 15 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8187c : bv 32 := 0x00d706b3.
Lemma F_8187c : fetch_word AsanUbsan.M.loaded_segments (0x818c4 : word) = Some W_8187c.
Proof. vm_refl. Qed.
Lemma D_8187c : decode_any W_8187c = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81880 : bv 32 := 0x01070733.
Lemma F_81880 : fetch_word AsanUbsan.M.loaded_segments (0x818c8 : word) = Some W_81880.
Proof. vm_refl. Qed.
Lemma D_81880 : decode_any W_81880 = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81884 : bv 32 := 0xff86f813.
Lemma F_81884 : fetch_word AsanUbsan.M.loaded_segments (0x818cc : word) = Some W_81884.
Proof. vm_refl. Qed.
Lemma D_81884 : decode_any W_81884 = Some (OpImm ALU_AND 16 13 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81888 : bv 32 := 0xff877893.
Lemma F_81888 : fetch_word AsanUbsan.M.loaded_segments (0x818d0 : word) = Some W_81888.
Proof. vm_refl. Qed.
Lemma D_81888 : decode_any W_81888 = Some (OpImm ALU_AND 17 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8188c : bv 32 := 0x00083803.
Lemma F_8188c : fetch_word AsanUbsan.M.loaded_segments (0x818d4 : word) = Some W_8188c.
Proof. vm_refl. Qed.
Lemma D_8188c : decode_any W_8188c = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81890 : bv 32 := 0x0008b883.
Lemma F_81890 : fetch_word AsanUbsan.M.loaded_segments (0x818d8 : word) = Some W_81890.
Proof. vm_refl. Qed.
Lemma D_81890 : decode_any W_81890 = Some (Load SZ8 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81894 : bv 32 := 0x0108e833.
Lemma F_81894 : fetch_word AsanUbsan.M.loaded_segments (0x818dc : word) = Some W_81894.
Proof. vm_refl. Qed.
Lemma D_81894 : decode_any W_81894 = Some (Op ALU_OR 16 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81898 : bv 32 := 0x1a081063.
Lemma F_81898 : fetch_word AsanUbsan.M.loaded_segments (0x818e0 : word) = Some W_81898.
Proof. vm_refl. Qed.
Lemma D_81898 : decode_any W_81898 = Some (Branch BC_NE 16 0 416, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8189c : bv 32 := 0xfff54693.
Lemma F_8189c : fetch_word AsanUbsan.M.loaded_segments (0x818e4 : word) = Some W_8189c.
Proof. vm_refl. Qed.
Lemma D_8189c : decode_any W_8189c = Some (OpImm ALU_XOR 13 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_818a0 : bv 32 := 0x10c6e663.
Lemma F_818a0 : fetch_word AsanUbsan.M.loaded_segments (0x818e8 : word) = Some W_818a0.
Proof. vm_refl. Qed.
Lemma D_818a0 : decode_any W_818a0 = Some (Branch BC_LTU 13 12 268, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_818a4 : bv 32 := 0xfbf00693.
Lemma F_818a4 : fetch_word AsanUbsan.M.loaded_segments (0x818ec : word) = Some W_818a4.
Proof. vm_refl. Qed.
Lemma D_818a4 : decode_any W_818a4 = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_818a8 : bv 32 := 0x1946f463.
Lemma F_818a8 : fetch_word AsanUbsan.M.loaded_segments (0x818f0 : word) = Some W_818a8.
Proof. vm_refl. Qed.
Lemma D_818a8 : decode_any W_818a8 = Some (Branch BC_GEU 13 20 392, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_818ac : bv 32 := 0x000e3697.
Lemma F_818ac : fetch_word AsanUbsan.M.loaded_segments (0x818f4 : word) = Some W_818ac.
Proof. vm_refl. Qed.
Lemma D_818ac : decode_any W_818ac = Some (Auipc 13 227, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_818b0 : bv 32 := 0xc246b683.
Lemma F_818b0 : fetch_word AsanUbsan.M.loaded_segments (0x818f8 : word) = Some W_818b0.
Proof. vm_refl. Qed.
Lemma D_818b0 : decode_any W_818b0 = Some (Load SZ8 true 13 13 3108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_818b4 : bv 32 := 0x00c507b3.
Lemma F_818b4 : fetch_word AsanUbsan.M.loaded_segments (0x818fc : word) = Some W_818b4.
Proof. vm_refl. Qed.
Lemma D_818b4 : decode_any W_818b4 = Some (Op ALU_ADD 15 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_818b8 : bv 32 := 0x0006b703.
Lemma F_818b8 : fetch_word AsanUbsan.M.loaded_segments (0x81900 : word) = Some W_818b8.
Proof. vm_refl. Qed.
Lemma D_818b8 : decode_any W_818b8 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_818bc : bv 32 := 0x00355693.
Lemma F_818bc : fetch_word AsanUbsan.M.loaded_segments (0x81904 : word) = Some W_818bc.
Proof. vm_refl. Qed.
Lemma D_818bc : decode_any W_818bc = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_818c0 : bv 32 := 0xfff78793.
Lemma F_818c0 : fetch_word AsanUbsan.M.loaded_segments (0x81908 : word) = Some W_818c0.
Proof. vm_refl. Qed.
Lemma D_818c0 : decode_any W_818c0 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_818c4 : bv 32 := 0x0037d813.
Lemma F_818c4 : fetch_word AsanUbsan.M.loaded_segments (0x8190c : word) = Some W_818c4.
Proof. vm_refl. Qed.
Lemma D_818c4 : decode_any W_818c4 = Some (ShiftImm ALU_SRL 16 15 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_818c8 : bv 32 := 0x00d706b3.
Lemma F_818c8 : fetch_word AsanUbsan.M.loaded_segments (0x81910 : word) = Some W_818c8.
Proof. vm_refl. Qed.
Lemma D_818c8 : decode_any W_818c8 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_818cc : bv 32 := 0x01070733.
Lemma F_818cc : fetch_word AsanUbsan.M.loaded_segments (0x81914 : word) = Some W_818cc.
Proof. vm_refl. Qed.
Lemma D_818cc : decode_any W_818cc = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_818d0 : bv 32 := 0xff86f813.
Lemma F_818d0 : fetch_word AsanUbsan.M.loaded_segments (0x81918 : word) = Some W_818d0.
Proof. vm_refl. Qed.
Lemma D_818d0 : decode_any W_818d0 = Some (OpImm ALU_AND 16 13 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_818d4 : bv 32 := 0xff877893.
Lemma F_818d4 : fetch_word AsanUbsan.M.loaded_segments (0x8191c : word) = Some W_818d4.
Proof. vm_refl. Qed.
Lemma D_818d4 : decode_any W_818d4 = Some (OpImm ALU_AND 17 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_818d8 : bv 32 := 0x00083803.
Lemma F_818d8 : fetch_word AsanUbsan.M.loaded_segments (0x81920 : word) = Some W_818d8.
Proof. vm_refl. Qed.
Lemma D_818d8 : decode_any W_818d8 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_818dc : bv 32 := 0x0008b883.
Lemma F_818dc : fetch_word AsanUbsan.M.loaded_segments (0x81924 : word) = Some W_818dc.
Proof. vm_refl. Qed.
Lemma D_818dc : decode_any W_818dc = Some (Load SZ8 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_818e0 : bv 32 := 0x0108e833.
Lemma F_818e0 : fetch_word AsanUbsan.M.loaded_segments (0x81928 : word) = Some W_818e0.
Proof. vm_refl. Qed.
Lemma D_818e0 : decode_any W_818e0 = Some (Op ALU_OR 16 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_818e4 : bv 32 := 0x24081a63.
Lemma F_818e4 : fetch_word AsanUbsan.M.loaded_segments (0x8192c : word) = Some W_818e4.
Proof. vm_refl. Qed.
Lemma D_818e4 : decode_any W_818e4 = Some (Branch BC_NE 16 0 596, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_818e8 : bv 32 := 0x155120ef.
Lemma F_818e8 : fetch_word AsanUbsan.M.loaded_segments (0x81930 : word) = Some W_818e8.
Proof. vm_refl. Qed.
Lemma D_818e8 : decode_any W_818e8 = Some (Jal 1 76116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_818ec : bv 32 := 0x07010113.
Lemma F_818ec : fetch_word AsanUbsan.M.loaded_segments (0x81934 : word) = Some W_818ec.
Proof. vm_refl. Qed.
Lemma D_818ec : decode_any W_818ec = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_818f0 : bv 32 := 0x7e813083.
Lemma F_818f0 : fetch_word AsanUbsan.M.loaded_segments (0x81938 : word) = Some W_818f0.
Proof. vm_refl. Qed.
Lemma D_818f0 : decode_any W_818f0 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_818f4 : bv 32 := 0x7e013403.
Lemma F_818f4 : fetch_word AsanUbsan.M.loaded_segments (0x8193c : word) = Some W_818f4.
Proof. vm_refl. Qed.
Lemma D_818f4 : decode_any W_818f4 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_818f8 : bv 32 := 0x7d813483.
Lemma F_818f8 : fetch_word AsanUbsan.M.loaded_segments (0x81940 : word) = Some W_818f8.
Proof. vm_refl. Qed.
Lemma D_818f8 : decode_any W_818f8 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_818fc : bv 32 := 0x7d013903.
Lemma F_818fc : fetch_word AsanUbsan.M.loaded_segments (0x81944 : word) = Some W_818fc.
Proof. vm_refl. Qed.
Lemma D_818fc : decode_any W_818fc = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81900 : bv 32 := 0x7c813983.
Lemma F_81900 : fetch_word AsanUbsan.M.loaded_segments (0x81948 : word) = Some W_81900.
Proof. vm_refl. Qed.
Lemma D_81900 : decode_any W_81900 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81904 : bv 32 := 0x7c013a03.
Lemma F_81904 : fetch_word AsanUbsan.M.loaded_segments (0x8194c : word) = Some W_81904.
Proof. vm_refl. Qed.
Lemma D_81904 : decode_any W_81904 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81908 : bv 32 := 0x7b813a83.
Lemma F_81908 : fetch_word AsanUbsan.M.loaded_segments (0x81950 : word) = Some W_81908.
Proof. vm_refl. Qed.
Lemma D_81908 : decode_any W_81908 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8190c : bv 32 := 0x7b013b03.
Lemma F_8190c : fetch_word AsanUbsan.M.loaded_segments (0x81954 : word) = Some W_8190c.
Proof. vm_refl. Qed.
Lemma D_8190c : decode_any W_8190c = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81910 : bv 32 := 0x7a813b83.
Lemma F_81910 : fetch_word AsanUbsan.M.loaded_segments (0x81958 : word) = Some W_81910.
Proof. vm_refl. Qed.
Lemma D_81910 : decode_any W_81910 = Some (Load SZ8 true 23 2 1960, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81914 : bv 32 := 0x7f010113.
Lemma F_81914 : fetch_word AsanUbsan.M.loaded_segments (0x8195c : word) = Some W_81914.
Proof. vm_refl. Qed.
Lemma D_81914 : decode_any W_81914 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81918 : bv 32 := 0x00008067.
Lemma F_81918 : fetch_word AsanUbsan.M.loaded_segments (0x81960 : word) = Some W_81918.
Proof. vm_refl. Qed.
Lemma D_81918 : decode_any W_81918 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_819a4 : bv 32 := 0x0c061463.
Lemma F_819a4 : fetch_word AsanUbsan.M.loaded_segments (0x819ec : word) = Some W_819a4.
Proof. vm_refl. Qed.
Lemma D_819a4 : decode_any W_819a4 = Some (Branch BC_NE 12 0 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_819a8 : bv 32 := 0xef5ff06f.
Lemma F_819a8 : fetch_word AsanUbsan.M.loaded_segments (0x819f0 : word) = Some W_819a8.
Proof. vm_refl. Qed.
Lemma D_819a8 : decode_any W_819a8 = Some (Jal 0 2096884, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81a30 : bv 32 := 0x12061e63.
Lemma F_81a30 : fetch_word AsanUbsan.M.loaded_segments (0x81a78 : word) = Some W_81a30.
Proof. vm_refl. Qed.
Lemma D_81a30 : decode_any W_81a30 = Some (Branch BC_NE 12 0 316, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81a34 : bv 32 := 0xeb5ff06f.
Lemma F_81a34 : fetch_word AsanUbsan.M.loaded_segments (0x81a7c : word) = Some W_81a34.
Proof. vm_refl. Qed.
Lemma D_81a34 : decode_any W_81a34 = Some (Jal 0 2096820, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81a38 : bv 32 := 0x00070803.
Lemma F_81a38 : fetch_word AsanUbsan.M.loaded_segments (0x81a80 : word) = Some W_81a38.
Proof. vm_refl. Qed.
Lemma D_81a38 : decode_any W_81a38 = Some (Load SZ1 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81a3c : bv 32 := 0x0077f793.
Lemma F_81a3c : fetch_word AsanUbsan.M.loaded_segments (0x81a84 : word) = Some W_81a3c.
Proof. vm_refl. Qed.
Lemma D_81a3c : decode_any W_81a3c = Some (OpImm ALU_AND 15 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81a40 : bv 32 := 0x010038b3.
Lemma F_81a40 : fetch_word AsanUbsan.M.loaded_segments (0x81a88 : word) = Some W_81a40.
Proof. vm_refl. Qed.
Lemma D_81a40 : decode_any W_81a40 = Some (Op ALU_SLTU 17 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81a44 : bv 32 := 0x0107a7b3.
Lemma F_81a44 : fetch_word AsanUbsan.M.loaded_segments (0x81a8c : word) = Some W_81a44.
Proof. vm_refl. Qed.
Lemma D_81a44 : decode_any W_81a44 = Some (Op ALU_SLT 15 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81a48 : bv 32 := 0x0017c793.
Lemma F_81a48 : fetch_word AsanUbsan.M.loaded_segments (0x81a90 : word) = Some W_81a48.
Proof. vm_refl. Qed.
Lemma D_81a48 : decode_any W_81a48 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81a4c : bv 32 := 0x00f8f7b3.
Lemma F_81a4c : fetch_word AsanUbsan.M.loaded_segments (0x81a94 : word) = Some W_81a4c.
Proof. vm_refl. Qed.
Lemma D_81a4c : decode_any W_81a4c = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81a50 : bv 32 := 0x00e6fa63.
Lemma F_81a50 : fetch_word AsanUbsan.M.loaded_segments (0x81a98 : word) = Some W_81a50.
Proof. vm_refl. Qed.
Lemma D_81a50 : decode_any W_81a50 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81a54 : bv 32 := 0x0006c803.
Lemma F_81a54 : fetch_word AsanUbsan.M.loaded_segments (0x81a9c : word) = Some W_81a54.
Proof. vm_refl. Qed.
Lemma D_81a54 : decode_any W_81a54 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81a58 : bv 32 := 0x00168693.
Lemma F_81a58 : fetch_word AsanUbsan.M.loaded_segments (0x81aa0 : word) = Some W_81a58.
Proof. vm_refl. Qed.
Lemma D_81a58 : decode_any W_81a58 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81a5c : bv 32 := 0x00f867b3.
Lemma F_81a5c : fetch_word AsanUbsan.M.loaded_segments (0x81aa4 : word) = Some W_81a5c.
Proof. vm_refl. Qed.
Lemma D_81a5c : decode_any W_81a5c = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81a60 : bv 32 := 0xfee69ae3.
Lemma F_81a60 : fetch_word AsanUbsan.M.loaded_segments (0x81aa8 : word) = Some W_81a60.
Proof. vm_refl. Qed.
Lemma D_81a60 : decode_any W_81a60 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81a64 : bv 32 := 0x0ff7f693.
Lemma F_81a64 : fetch_word AsanUbsan.M.loaded_segments (0x81aac : word) = Some W_81a64.
Proof. vm_refl. Qed.
Lemma D_81a64 : decode_any W_81a64 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81a68 : bv 32 := 0xe2068ae3.
Lemma F_81a68 : fetch_word AsanUbsan.M.loaded_segments (0x81ab0 : word) = Some W_81a68.
Proof. vm_refl. Qed.
Lemma D_81a68 : decode_any W_81a68 = Some (Branch BC_EQ 13 0 7732, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81a6c : bv 32 := 0x00050b13.
Lemma F_81a6c : fetch_word AsanUbsan.M.loaded_segments (0x81ab4 : word) = Some W_81a6c.
Proof. vm_refl. Qed.
Lemma D_81a6c : decode_any W_81a6c = Some (OpImm ALU_ADD 22 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81a70 : bv 32 := 0x00058513.
Lemma F_81a70 : fetch_word AsanUbsan.M.loaded_segments (0x81ab8 : word) = Some W_81a70.
Proof. vm_refl. Qed.
Lemma D_81a70 : decode_any W_81a70 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81a74 : bv 32 := 0x00058b93.
Lemma F_81a74 : fetch_word AsanUbsan.M.loaded_segments (0x81abc : word) = Some W_81a74.
Proof. vm_refl. Qed.
Lemma D_81a74 : decode_any W_81a74 = Some (OpImm ALU_ADD 23 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81a78 : bv 32 := 0x00060593.
Lemma F_81a78 : fetch_word AsanUbsan.M.loaded_segments (0x81ac0 : word) = Some W_81a78.
Proof. vm_refl. Qed.
Lemma D_81a78 : decode_any W_81a78 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81a7c : bv 32 := 0x00060493.
Lemma F_81a7c : fetch_word AsanUbsan.M.loaded_segments (0x81ac4 : word) = Some W_81a7c.
Proof. vm_refl. Qed.
Lemma D_81a7c : decode_any W_81a7c = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81a80 : bv 32 := 0x075020ef.
Lemma F_81a80 : fetch_word AsanUbsan.M.loaded_segments (0x81ac8 : word) = Some W_81a80.
Proof. vm_refl. Qed.
Lemma D_81a80 : decode_any W_81a80 = Some (Jal 1 10356, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81a84 : bv 32 := 0x000b8593.
Lemma F_81a84 : fetch_word AsanUbsan.M.loaded_segments (0x81acc : word) = Some W_81a84.
Proof. vm_refl. Qed.
Lemma D_81a84 : decode_any W_81a84 = Some (OpImm ALU_ADD 11 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81a88 : bv 32 := 0x00048613.
Lemma F_81a88 : fetch_word AsanUbsan.M.loaded_segments (0x81ad0 : word) = Some W_81a88.
Proof. vm_refl. Qed.
Lemma D_81a88 : decode_any W_81a88 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81a8c : bv 32 := 0x00050913.
Lemma F_81a8c : fetch_word AsanUbsan.M.loaded_segments (0x81ad4 : word) = Some W_81a8c.
Proof. vm_refl. Qed.
Lemma D_81a8c : decode_any W_81a8c = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81a90 : bv 32 := 0x000b0513.
Lemma F_81a90 : fetch_word AsanUbsan.M.loaded_segments (0x81ad8 : word) = Some W_81a90.
Proof. vm_refl. Qed.
Lemma D_81a90 : decode_any W_81a90 = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81a94 : bv 32 := 0xe00904e3.
Lemma F_81a94 : fetch_word AsanUbsan.M.loaded_segments (0x81adc : word) = Some W_81a94.
Proof. vm_refl. Qed.
Lemma D_81a94 : decode_any W_81a94 = Some (Branch BC_EQ 18 0 7688, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81b38 : bv 32 := 0x00070803.
Lemma F_81b38 : fetch_word AsanUbsan.M.loaded_segments (0x81b80 : word) = Some W_81b38.
Proof. vm_refl. Qed.
Lemma D_81b38 : decode_any W_81b38 = Some (Load SZ1 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81b3c : bv 32 := 0x0077f793.
Lemma F_81b3c : fetch_word AsanUbsan.M.loaded_segments (0x81b84 : word) = Some W_81b3c.
Proof. vm_refl. Qed.
Lemma D_81b3c : decode_any W_81b3c = Some (OpImm ALU_AND 15 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81b40 : bv 32 := 0x010038b3.
Lemma F_81b40 : fetch_word AsanUbsan.M.loaded_segments (0x81b88 : word) = Some W_81b40.
Proof. vm_refl. Qed.
Lemma D_81b40 : decode_any W_81b40 = Some (Op ALU_SLTU 17 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81b44 : bv 32 := 0x0107a7b3.
Lemma F_81b44 : fetch_word AsanUbsan.M.loaded_segments (0x81b8c : word) = Some W_81b44.
Proof. vm_refl. Qed.
Lemma D_81b44 : decode_any W_81b44 = Some (Op ALU_SLT 15 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81b48 : bv 32 := 0x0017c793.
Lemma F_81b48 : fetch_word AsanUbsan.M.loaded_segments (0x81b90 : word) = Some W_81b48.
Proof. vm_refl. Qed.
Lemma D_81b48 : decode_any W_81b48 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81b4c : bv 32 := 0x00f8f7b3.
Lemma F_81b4c : fetch_word AsanUbsan.M.loaded_segments (0x81b94 : word) = Some W_81b4c.
Proof. vm_refl. Qed.
Lemma D_81b4c : decode_any W_81b4c = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81b50 : bv 32 := 0x00e6fa63.
Lemma F_81b50 : fetch_word AsanUbsan.M.loaded_segments (0x81b98 : word) = Some W_81b50.
Proof. vm_refl. Qed.
Lemma D_81b50 : decode_any W_81b50 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81b54 : bv 32 := 0x0006c803.
Lemma F_81b54 : fetch_word AsanUbsan.M.loaded_segments (0x81b9c : word) = Some W_81b54.
Proof. vm_refl. Qed.
Lemma D_81b54 : decode_any W_81b54 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81b58 : bv 32 := 0x00168693.
Lemma F_81b58 : fetch_word AsanUbsan.M.loaded_segments (0x81ba0 : word) = Some W_81b58.
Proof. vm_refl. Qed.
Lemma D_81b58 : decode_any W_81b58 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81b5c : bv 32 := 0x00f867b3.
Lemma F_81b5c : fetch_word AsanUbsan.M.loaded_segments (0x81ba4 : word) = Some W_81b5c.
Proof. vm_refl. Qed.
Lemma D_81b5c : decode_any W_81b5c = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81b60 : bv 32 := 0xfee69ae3.
Lemma F_81b60 : fetch_word AsanUbsan.M.loaded_segments (0x81ba8 : word) = Some W_81b60.
Proof. vm_refl. Qed.
Lemma D_81b60 : decode_any W_81b60 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81b64 : bv 32 := 0x0ff7f693.
Lemma F_81b64 : fetch_word AsanUbsan.M.loaded_segments (0x81bac : word) = Some W_81b64.
Proof. vm_refl. Qed.
Lemma D_81b64 : decode_any W_81b64 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81b68 : bv 32 := 0xd80680e3.
Lemma F_81b68 : fetch_word AsanUbsan.M.loaded_segments (0x81bb0 : word) = Some W_81b68.
Proof. vm_refl. Qed.
Lemma D_81b68 : decode_any W_81b68 = Some (Branch BC_EQ 13 0 7552, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81b6c : bv 32 := 0x00050493.
Lemma F_81b6c : fetch_word AsanUbsan.M.loaded_segments (0x81bb4 : word) = Some W_81b6c.
Proof. vm_refl. Qed.
Lemma D_81b6c : decode_any W_81b6c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81b70 : bv 32 := 0x00058b13.
Lemma F_81b70 : fetch_word AsanUbsan.M.loaded_segments (0x81bb8 : word) = Some W_81b70.
Proof. vm_refl. Qed.
Lemma D_81b70 : decode_any W_81b70 = Some (OpImm ALU_ADD 22 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81b74 : bv 32 := 0x00060593.
Lemma F_81b74 : fetch_word AsanUbsan.M.loaded_segments (0x81bbc : word) = Some W_81b74.
Proof. vm_refl. Qed.
Lemma D_81b74 : decode_any W_81b74 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81b78 : bv 32 := 0x00060913.
Lemma F_81b78 : fetch_word AsanUbsan.M.loaded_segments (0x81bc0 : word) = Some W_81b78.
Proof. vm_refl. Qed.
Lemma D_81b78 : decode_any W_81b78 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81b7c : bv 32 := 0x778020ef.
Lemma F_81b7c : fetch_word AsanUbsan.M.loaded_segments (0x81bc4 : word) = Some W_81b7c.
Proof. vm_refl. Qed.
Lemma D_81b7c : decode_any W_81b7c = Some (Jal 1 10104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81b80 : bv 32 := 0x000b0593.
Lemma F_81b80 : fetch_word AsanUbsan.M.loaded_segments (0x81bc8 : word) = Some W_81b80.
Proof. vm_refl. Qed.
Lemma D_81b80 : decode_any W_81b80 = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81b84 : bv 32 := 0x00090613.
Lemma F_81b84 : fetch_word AsanUbsan.M.loaded_segments (0x81bcc : word) = Some W_81b84.
Proof. vm_refl. Qed.
Lemma D_81b84 : decode_any W_81b84 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81b88 : bv 32 := 0x00050993.
Lemma F_81b88 : fetch_word AsanUbsan.M.loaded_segments (0x81bd0 : word) = Some W_81b88.
Proof. vm_refl. Qed.
Lemma D_81b88 : decode_any W_81b88 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81b8c : bv 32 := 0x00048513.
Lemma F_81b8c : fetch_word AsanUbsan.M.loaded_segments (0x81bd4 : word) = Some W_81b8c.
Proof. vm_refl. Qed.
Lemma D_81b8c : decode_any W_81b8c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81b90 : bv 32 := 0xd4098ce3.
Lemma F_81b90 : fetch_word AsanUbsan.M.loaded_segments (0x81bd8 : word) = Some W_81b90.
Proof. vm_refl. Qed.
Lemma D_81b90 : decode_any W_81b90 = Some (Branch BC_EQ 19 0 7512, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81cc4 : bv 32 := 0x81010113.
Lemma F_81cc4 : fetch_word AsanUbsan.M.loaded_segments (0x81d0c : word) = Some W_81cc4.
Proof. vm_refl. Qed.
Lemma D_81cc4 : decode_any W_81cc4 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81cc8 : bv 32 := 0x7e113423.
Lemma F_81cc8 : fetch_word AsanUbsan.M.loaded_segments (0x81d10 : word) = Some W_81cc8.
Proof. vm_refl. Qed.
Lemma D_81cc8 : decode_any W_81cc8 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81ccc : bv 32 := 0x7e813023.
Lemma F_81ccc : fetch_word AsanUbsan.M.loaded_segments (0x81d14 : word) = Some W_81ccc.
Proof. vm_refl. Qed.
Lemma D_81ccc : decode_any W_81ccc = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81cd0 : bv 32 := 0x7c913c23.
Lemma F_81cd0 : fetch_word AsanUbsan.M.loaded_segments (0x81d18 : word) = Some W_81cd0.
Proof. vm_refl. Qed.
Lemma D_81cd0 : decode_any W_81cd0 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81cd4 : bv 32 := 0x7d213823.
Lemma F_81cd4 : fetch_word AsanUbsan.M.loaded_segments (0x81d1c : word) = Some W_81cd4.
Proof. vm_refl. Qed.
Lemma D_81cd4 : decode_any W_81cd4 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81cd8 : bv 32 := 0x7d313423.
Lemma F_81cd8 : fetch_word AsanUbsan.M.loaded_segments (0x81d20 : word) = Some W_81cd8.
Proof. vm_refl. Qed.
Lemma D_81cd8 : decode_any W_81cd8 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81cdc : bv 32 := 0x7d413023.
Lemma F_81cdc : fetch_word AsanUbsan.M.loaded_segments (0x81d24 : word) = Some W_81cdc.
Proof. vm_refl. Qed.
Lemma D_81cdc : decode_any W_81cdc = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81ce0 : bv 32 := 0x7b513c23.
Lemma F_81ce0 : fetch_word AsanUbsan.M.loaded_segments (0x81d28 : word) = Some W_81ce0.
Proof. vm_refl. Qed.
Lemma D_81ce0 : decode_any W_81ce0 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81ce4 : bv 32 := 0x7b613823.
Lemma F_81ce4 : fetch_word AsanUbsan.M.loaded_segments (0x81d2c : word) = Some W_81ce4.
Proof. vm_refl. Qed.
Lemma D_81ce4 : decode_any W_81ce4 = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81ce8 : bv 32 := 0x7b713423.
Lemma F_81ce8 : fetch_word AsanUbsan.M.loaded_segments (0x81d30 : word) = Some W_81ce8.
Proof. vm_refl. Qed.
Lemma D_81ce8 : decode_any W_81ce8 = Some (Store SZ8 2 23 1960, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81cec : bv 32 := 0x7b813023.
Lemma F_81cec : fetch_word AsanUbsan.M.loaded_segments (0x81d34 : word) = Some W_81cec.
Proof. vm_refl. Qed.
Lemma D_81cec : decode_any W_81cec = Some (Store SZ8 2 24 1952, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81cf0 : bv 32 := 0x7f010413.
Lemma F_81cf0 : fetch_word AsanUbsan.M.loaded_segments (0x81d38 : word) = Some W_81cf0.
Proof. vm_refl. Qed.
Lemma D_81cf0 : decode_any W_81cf0 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81cf4 : bv 32 := 0xf8010113.
Lemma F_81cf4 : fetch_word AsanUbsan.M.loaded_segments (0x81d3c : word) = Some W_81cf4.
Proof. vm_refl. Qed.
Lemma D_81cf4 : decode_any W_81cf4 = Some (OpImm ALU_ADD 2 2 3968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81cf8 : bv 32 := 0x000e3697.
Lemma F_81cf8 : fetch_word AsanUbsan.M.loaded_segments (0x81d40 : word) = Some W_81cf8.
Proof. vm_refl. Qed.
Lemma D_81cf8 : decode_any W_81cf8 = Some (Auipc 13 227, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81cfc : bv 32 := 0x3406b683.
Lemma F_81cfc : fetch_word AsanUbsan.M.loaded_segments (0x81d44 : word) = Some W_81cfc.
Proof. vm_refl. Qed.
Lemma D_81cfc : decode_any W_81cfc = Some (Load SZ8 true 13 13 832, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81d00 : bv 32 := 0x0006c683.
Lemma F_81d00 : fetch_word AsanUbsan.M.loaded_segments (0x81d48 : word) = Some W_81d00.
Proof. vm_refl. Qed.
Lemma D_81d00 : decode_any W_81d00 = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81d04 : bv 32 := 0x0e068a63.
Lemma F_81d04 : fetch_word AsanUbsan.M.loaded_segments (0x81d4c : word) = Some W_81d04.
Proof. vm_refl. Qed.
Lemma D_81d04 : decode_any W_81d04 = Some (Branch BC_EQ 13 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81d08 : bv 32 := 0x80040a93.
Lemma F_81d08 : fetch_word AsanUbsan.M.loaded_segments (0x81d50 : word) = Some W_81d08.
Proof. vm_refl. Qed.
Lemma D_81d08 : decode_any W_81d08 = Some (OpImm ALU_ADD 21 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81d0c : bv 32 := 0xf98a8a93.
Lemma F_81d0c : fetch_word AsanUbsan.M.loaded_segments (0x81d54 : word) = Some W_81d0c.
Proof. vm_refl. Qed.
Lemma D_81d0c : decode_any W_81d0c = Some (OpImm ALU_ADD 21 21 3992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81d10 : bv 32 := 0x00c589b3.
Lemma F_81d10 : fetch_word AsanUbsan.M.loaded_segments (0x81d58 : word) = Some W_81d10.
Proof. vm_refl. Qed.
Lemma D_81d10 : decode_any W_81d10 = Some (Op ALU_ADD 19 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81d14 : bv 32 := 0x00c50a33.
Lemma F_81d14 : fetch_word AsanUbsan.M.loaded_segments (0x81d5c : word) = Some W_81d14.
Proof. vm_refl. Qed.
Lemma D_81d14 : decode_any W_81d14 = Some (Op ALU_ADD 20 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81d18 : bv 32 := 0x00b50663.
Lemma F_81d18 : fetch_word AsanUbsan.M.loaded_segments (0x81d60 : word) = Some W_81d18.
Proof. vm_refl. Qed.
Lemma D_81d18 : decode_any W_81d18 = Some (Branch BC_EQ 10 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81d1c : bv 32 := 0x0145f463.
Lemma F_81d1c : fetch_word AsanUbsan.M.loaded_segments (0x81d64 : word) = Some W_81d1c.
Proof. vm_refl. Qed.
Lemma D_81d1c : decode_any W_81d1c = Some (Branch BC_GEU 11 20 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81d20 : bv 32 := 0x1b356e63.
Lemma F_81d20 : fetch_word AsanUbsan.M.loaded_segments (0x81d68 : word) = Some W_81d20.
Proof. vm_refl. Qed.
Lemma D_81d20 : decode_any W_81d20 = Some (Branch BC_LTU 10 19 444, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81d24 : bv 32 := 0xfff5c693.
Lemma F_81d24 : fetch_word AsanUbsan.M.loaded_segments (0x81d6c : word) = Some W_81d24.
Proof. vm_refl. Qed.
Lemma D_81d24 : decode_any W_81d24 = Some (OpImm ALU_XOR 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81d28 : bv 32 := 0x26c6e863.
Lemma F_81d28 : fetch_word AsanUbsan.M.loaded_segments (0x81d70 : word) = Some W_81d28.
Proof. vm_refl. Qed.
Lemma D_81d28 : decode_any W_81d28 = Some (Branch BC_LTU 13 12 624, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81d2c : bv 32 := 0xfbf60b13.
Lemma F_81d2c : fetch_word AsanUbsan.M.loaded_segments (0x81d74 : word) = Some W_81d2c.
Proof. vm_refl. Qed.
Lemma D_81d2c : decode_any W_81d2c = Some (OpImm ALU_ADD 22 12 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81d30 : bv 32 := 0xfbf00693.
Lemma F_81d30 : fetch_word AsanUbsan.M.loaded_segments (0x81d78 : word) = Some W_81d30.
Proof. vm_refl. Qed.
Lemma D_81d30 : decode_any W_81d30 = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81d34 : bv 32 := 0x2f66f663.
Lemma F_81d34 : fetch_word AsanUbsan.M.loaded_segments (0x81d7c : word) = Some W_81d34.
Proof. vm_refl. Qed.
Lemma D_81d34 : decode_any W_81d34 = Some (Branch BC_GEU 13 22 748, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81d38 : bv 32 := 0x000e2697.
Lemma F_81d38 : fetch_word AsanUbsan.M.loaded_segments (0x81d80 : word) = Some W_81d38.
Proof. vm_refl. Qed.
Lemma D_81d38 : decode_any W_81d38 = Some (Auipc 13 226, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81d3c : bv 32 := 0x7986b683.
Lemma F_81d3c : fetch_word AsanUbsan.M.loaded_segments (0x81d84 : word) = Some W_81d3c.
Proof. vm_refl. Qed.
Lemma D_81d3c : decode_any W_81d3c = Some (Load SZ8 true 13 13 1944, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81d40 : bv 32 := 0x0006b703.
Lemma F_81d40 : fetch_word AsanUbsan.M.loaded_segments (0x81d88 : word) = Some W_81d40.
Proof. vm_refl. Qed.
Lemma D_81d40 : decode_any W_81d40 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81d44 : bv 32 := 0xfff98993.
Lemma F_81d44 : fetch_word AsanUbsan.M.loaded_segments (0x81d8c : word) = Some W_81d44.
Proof. vm_refl. Qed.
Lemma D_81d44 : decode_any W_81d44 = Some (OpImm ALU_ADD 19 19 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81d48 : bv 32 := 0x0035d693.
Lemma F_81d48 : fetch_word AsanUbsan.M.loaded_segments (0x81d90 : word) = Some W_81d48.
Proof. vm_refl. Qed.
Lemma D_81d48 : decode_any W_81d48 = Some (ShiftImm ALU_SRL 13 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81d4c : bv 32 := 0x0039d793.
Lemma F_81d4c : fetch_word AsanUbsan.M.loaded_segments (0x81d94 : word) = Some W_81d4c.
Proof. vm_refl. Qed.
Lemma D_81d4c : decode_any W_81d4c = Some (ShiftImm ALU_SRL 15 19 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81d50 : bv 32 := 0x00d706b3.
Lemma F_81d50 : fetch_word AsanUbsan.M.loaded_segments (0x81d98 : word) = Some W_81d50.
Proof. vm_refl. Qed.
Lemma D_81d50 : decode_any W_81d50 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81d54 : bv 32 := 0x00f70733.
Lemma F_81d54 : fetch_word AsanUbsan.M.loaded_segments (0x81d9c : word) = Some W_81d54.
Proof. vm_refl. Qed.
Lemma D_81d54 : decode_any W_81d54 = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81d58 : bv 32 := 0xff86f793.
Lemma F_81d58 : fetch_word AsanUbsan.M.loaded_segments (0x81da0 : word) = Some W_81d58.
Proof. vm_refl. Qed.
Lemma D_81d58 : decode_any W_81d58 = Some (OpImm ALU_AND 15 13 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81d5c : bv 32 := 0xff877813.
Lemma F_81d5c : fetch_word AsanUbsan.M.loaded_segments (0x81da4 : word) = Some W_81d5c.
Proof. vm_refl. Qed.
Lemma D_81d5c : decode_any W_81d5c = Some (OpImm ALU_AND 16 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81d60 : bv 32 := 0x0007b783.
Lemma F_81d60 : fetch_word AsanUbsan.M.loaded_segments (0x81da8 : word) = Some W_81d60.
Proof. vm_refl. Qed.
Lemma D_81d60 : decode_any W_81d60 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81d64 : bv 32 := 0x00083803.
Lemma F_81d64 : fetch_word AsanUbsan.M.loaded_segments (0x81dac : word) = Some W_81d64.
Proof. vm_refl. Qed.
Lemma D_81d64 : decode_any W_81d64 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81d68 : bv 32 := 0x00f867b3.
Lemma F_81d68 : fetch_word AsanUbsan.M.loaded_segments (0x81db0 : word) = Some W_81d68.
Proof. vm_refl. Qed.
Lemma D_81d68 : decode_any W_81d68 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81d6c : bv 32 := 0x2a079e63.
Lemma F_81d6c : fetch_word AsanUbsan.M.loaded_segments (0x81db4 : word) = Some W_81d6c.
Proof. vm_refl. Qed.
Lemma D_81d6c : decode_any W_81d6c = Some (Branch BC_NE 15 0 700, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81d70 : bv 32 := 0xfff54693.
Lemma F_81d70 : fetch_word AsanUbsan.M.loaded_segments (0x81db8 : word) = Some W_81d70.
Proof. vm_refl. Qed.
Lemma D_81d70 : decode_any W_81d70 = Some (OpImm ALU_XOR 13 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81d74 : bv 32 := 0x0cc6ee63.
Lemma F_81d74 : fetch_word AsanUbsan.M.loaded_segments (0x81dbc : word) = Some W_81d74.
Proof. vm_refl. Qed.
Lemma D_81d74 : decode_any W_81d74 = Some (Branch BC_LTU 13 12 220, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81d78 : bv 32 := 0xfbf00693.
Lemma F_81d78 : fetch_word AsanUbsan.M.loaded_segments (0x81dc0 : word) = Some W_81d78.
Proof. vm_refl. Qed.
Lemma D_81d78 : decode_any W_81d78 = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81d7c : bv 32 := 0x1566fc63.
Lemma F_81d7c : fetch_word AsanUbsan.M.loaded_segments (0x81dc4 : word) = Some W_81d7c.
Proof. vm_refl. Qed.
Lemma D_81d7c : decode_any W_81d7c = Some (Branch BC_GEU 13 22 344, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81d80 : bv 32 := 0x000e2697.
Lemma F_81d80 : fetch_word AsanUbsan.M.loaded_segments (0x81dc8 : word) = Some W_81d80.
Proof. vm_refl. Qed.
Lemma D_81d80 : decode_any W_81d80 = Some (Auipc 13 226, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81d84 : bv 32 := 0x7506b683.
Lemma F_81d84 : fetch_word AsanUbsan.M.loaded_segments (0x81dcc : word) = Some W_81d84.
Proof. vm_refl. Qed.
Lemma D_81d84 : decode_any W_81d84 = Some (Load SZ8 true 13 13 1872, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81d88 : bv 32 := 0x0006b703.
Lemma F_81d88 : fetch_word AsanUbsan.M.loaded_segments (0x81dd0 : word) = Some W_81d88.
Proof. vm_refl. Qed.
Lemma D_81d88 : decode_any W_81d88 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81d8c : bv 32 := 0xfffa0a13.
Lemma F_81d8c : fetch_word AsanUbsan.M.loaded_segments (0x81dd4 : word) = Some W_81d8c.
Proof. vm_refl. Qed.
Lemma D_81d8c : decode_any W_81d8c = Some (OpImm ALU_ADD 20 20 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81d90 : bv 32 := 0x00355693.
Lemma F_81d90 : fetch_word AsanUbsan.M.loaded_segments (0x81dd8 : word) = Some W_81d90.
Proof. vm_refl. Qed.
Lemma D_81d90 : decode_any W_81d90 = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81d94 : bv 32 := 0x003a5793.
Lemma F_81d94 : fetch_word AsanUbsan.M.loaded_segments (0x81ddc : word) = Some W_81d94.
Proof. vm_refl. Qed.
Lemma D_81d94 : decode_any W_81d94 = Some (ShiftImm ALU_SRL 15 20 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81d98 : bv 32 := 0x00d706b3.
Lemma F_81d98 : fetch_word AsanUbsan.M.loaded_segments (0x81de0 : word) = Some W_81d98.
Proof. vm_refl. Qed.
Lemma D_81d98 : decode_any W_81d98 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81d9c : bv 32 := 0x00f70733.
Lemma F_81d9c : fetch_word AsanUbsan.M.loaded_segments (0x81de4 : word) = Some W_81d9c.
Proof. vm_refl. Qed.
Lemma D_81d9c : decode_any W_81d9c = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81da0 : bv 32 := 0xff86f793.
Lemma F_81da0 : fetch_word AsanUbsan.M.loaded_segments (0x81de8 : word) = Some W_81da0.
Proof. vm_refl. Qed.
Lemma D_81da0 : decode_any W_81da0 = Some (OpImm ALU_AND 15 13 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81da4 : bv 32 := 0xff877813.
Lemma F_81da4 : fetch_word AsanUbsan.M.loaded_segments (0x81dec : word) = Some W_81da4.
Proof. vm_refl. Qed.
Lemma D_81da4 : decode_any W_81da4 = Some (OpImm ALU_AND 16 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81da8 : bv 32 := 0x0007b783.
Lemma F_81da8 : fetch_word AsanUbsan.M.loaded_segments (0x81df0 : word) = Some W_81da8.
Proof. vm_refl. Qed.
Lemma D_81da8 : decode_any W_81da8 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81dac : bv 32 := 0x00083803.
Lemma F_81dac : fetch_word AsanUbsan.M.loaded_segments (0x81df4 : word) = Some W_81dac.
Proof. vm_refl. Qed.
Lemma D_81dac : decode_any W_81dac = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81db0 : bv 32 := 0x00f867b3.
Lemma F_81db0 : fetch_word AsanUbsan.M.loaded_segments (0x81df8 : word) = Some W_81db0.
Proof. vm_refl. Qed.
Lemma D_81db0 : decode_any W_81db0 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81db4 : bv 32 := 0x36079a63.
Lemma F_81db4 : fetch_word AsanUbsan.M.loaded_segments (0x81dfc : word) = Some W_81db4.
Proof. vm_refl. Qed.
Lemma D_81db4 : decode_any W_81db4 = Some (Branch BC_NE 15 0 884, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81db8 : bv 32 := 0x000e4697.
Lemma F_81db8 : fetch_word AsanUbsan.M.loaded_segments (0x81e00 : word) = Some W_81db8.
Proof. vm_refl. Qed.
Lemma D_81db8 : decode_any W_81db8 = Some (Auipc 13 228, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81dbc : bv 32 := 0x7486b683.
Lemma F_81dbc : fetch_word AsanUbsan.M.loaded_segments (0x81e04 : word) = Some W_81dbc.
Proof. vm_refl. Qed.
Lemma D_81dbc : decode_any W_81dbc = Some (Load SZ8 true 13 13 1864, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81dc0 : bv 32 := 0x000680e7.
Lemma F_81dc0 : fetch_word AsanUbsan.M.loaded_segments (0x81e08 : word) = Some W_81dc0.
Proof. vm_refl. Qed.
Lemma D_81dc0 : decode_any W_81dc0 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81dc4 : bv 32 := 0x08010113.
Lemma F_81dc4 : fetch_word AsanUbsan.M.loaded_segments (0x81e0c : word) = Some W_81dc4.
Proof. vm_refl. Qed.
Lemma D_81dc4 : decode_any W_81dc4 = Some (OpImm ALU_ADD 2 2 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81dc8 : bv 32 := 0x7e813083.
Lemma F_81dc8 : fetch_word AsanUbsan.M.loaded_segments (0x81e10 : word) = Some W_81dc8.
Proof. vm_refl. Qed.
Lemma D_81dc8 : decode_any W_81dc8 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81dcc : bv 32 := 0x7e013403.
Lemma F_81dcc : fetch_word AsanUbsan.M.loaded_segments (0x81e14 : word) = Some W_81dcc.
Proof. vm_refl. Qed.
Lemma D_81dcc : decode_any W_81dcc = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81dd0 : bv 32 := 0x7d813483.
Lemma F_81dd0 : fetch_word AsanUbsan.M.loaded_segments (0x81e18 : word) = Some W_81dd0.
Proof. vm_refl. Qed.
Lemma D_81dd0 : decode_any W_81dd0 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81dd4 : bv 32 := 0x7d013903.
Lemma F_81dd4 : fetch_word AsanUbsan.M.loaded_segments (0x81e1c : word) = Some W_81dd4.
Proof. vm_refl. Qed.
Lemma D_81dd4 : decode_any W_81dd4 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81dd8 : bv 32 := 0x7c813983.
Lemma F_81dd8 : fetch_word AsanUbsan.M.loaded_segments (0x81e20 : word) = Some W_81dd8.
Proof. vm_refl. Qed.
Lemma D_81dd8 : decode_any W_81dd8 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81ddc : bv 32 := 0x7c013a03.
Lemma F_81ddc : fetch_word AsanUbsan.M.loaded_segments (0x81e24 : word) = Some W_81ddc.
Proof. vm_refl. Qed.
Lemma D_81ddc : decode_any W_81ddc = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81de0 : bv 32 := 0x7b813a83.
Lemma F_81de0 : fetch_word AsanUbsan.M.loaded_segments (0x81e28 : word) = Some W_81de0.
Proof. vm_refl. Qed.
Lemma D_81de0 : decode_any W_81de0 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81de4 : bv 32 := 0x7b013b03.
Lemma F_81de4 : fetch_word AsanUbsan.M.loaded_segments (0x81e2c : word) = Some W_81de4.
Proof. vm_refl. Qed.
Lemma D_81de4 : decode_any W_81de4 = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81de8 : bv 32 := 0x7a813b83.
Lemma F_81de8 : fetch_word AsanUbsan.M.loaded_segments (0x81e30 : word) = Some W_81de8.
Proof. vm_refl. Qed.
Lemma D_81de8 : decode_any W_81de8 = Some (Load SZ8 true 23 2 1960, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81dec : bv 32 := 0x7a013c03.
Lemma F_81dec : fetch_word AsanUbsan.M.loaded_segments (0x81e34 : word) = Some W_81dec.
Proof. vm_refl. Qed.
Lemma D_81dec : decode_any W_81dec = Some (Load SZ8 true 24 2 1952, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81df0 : bv 32 := 0x7f010113.
Lemma F_81df0 : fetch_word AsanUbsan.M.loaded_segments (0x81e38 : word) = Some W_81df0.
Proof. vm_refl. Qed.
Lemma D_81df0 : decode_any W_81df0 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81df4 : bv 32 := 0x00008067.
Lemma F_81df4 : fetch_word AsanUbsan.M.loaded_segments (0x81e3c : word) = Some W_81df4.
Proof. vm_refl. Qed.
Lemma D_81df4 : decode_any W_81df4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81ed4 : bv 32 := 0x28061463.
Lemma F_81ed4 : fetch_word AsanUbsan.M.loaded_segments (0x81f1c : word) = Some W_81ed4.
Proof. vm_refl. Qed.
Lemma D_81ed4 : decode_any W_81ed4 = Some (Branch BC_NE 12 0 648, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81ed8 : bv 32 := 0xee1ff06f.
Lemma F_81ed8 : fetch_word AsanUbsan.M.loaded_segments (0x81f20 : word) = Some W_81ed8.
Proof. vm_refl. Qed.
Lemma D_81ed8 : decode_any W_81ed8 = Some (Jal 0 2096864, 4%Z).
Proof. vm_refl. Qed.

