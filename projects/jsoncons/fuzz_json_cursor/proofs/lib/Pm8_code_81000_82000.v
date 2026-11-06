(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_810f0 : bv 32 := 0x81010113.
Lemma F_810f0 : fetch_word Asan.M.loaded_segments (0x81140 : word) = Some W_810f0.
Proof. vm_refl. Qed.
Lemma D_810f0 : decode_any W_810f0 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_810f4 : bv 32 := 0x7e113423.
Lemma F_810f4 : fetch_word Asan.M.loaded_segments (0x81144 : word) = Some W_810f4.
Proof. vm_refl. Qed.
Lemma D_810f4 : decode_any W_810f4 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_810f8 : bv 32 := 0x7e813023.
Lemma F_810f8 : fetch_word Asan.M.loaded_segments (0x81148 : word) = Some W_810f8.
Proof. vm_refl. Qed.
Lemma D_810f8 : decode_any W_810f8 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_810fc : bv 32 := 0x7c913c23.
Lemma F_810fc : fetch_word Asan.M.loaded_segments (0x8114c : word) = Some W_810fc.
Proof. vm_refl. Qed.
Lemma D_810fc : decode_any W_810fc = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_81100 : bv 32 := 0x7d213823.
Lemma F_81100 : fetch_word Asan.M.loaded_segments (0x81150 : word) = Some W_81100.
Proof. vm_refl. Qed.
Lemma D_81100 : decode_any W_81100 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_81104 : bv 32 := 0x7d313423.
Lemma F_81104 : fetch_word Asan.M.loaded_segments (0x81154 : word) = Some W_81104.
Proof. vm_refl. Qed.
Lemma D_81104 : decode_any W_81104 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_81108 : bv 32 := 0x7d413023.
Lemma F_81108 : fetch_word Asan.M.loaded_segments (0x81158 : word) = Some W_81108.
Proof. vm_refl. Qed.
Lemma D_81108 : decode_any W_81108 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_8110c : bv 32 := 0x7b513c23.
Lemma F_8110c : fetch_word Asan.M.loaded_segments (0x8115c : word) = Some W_8110c.
Proof. vm_refl. Qed.
Lemma D_8110c : decode_any W_8110c = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_81110 : bv 32 := 0x7b613823.
Lemma F_81110 : fetch_word Asan.M.loaded_segments (0x81160 : word) = Some W_81110.
Proof. vm_refl. Qed.
Lemma D_81110 : decode_any W_81110 = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_81114 : bv 32 := 0x7f010413.
Lemma F_81114 : fetch_word Asan.M.loaded_segments (0x81164 : word) = Some W_81114.
Proof. vm_refl. Qed.
Lemma D_81114 : decode_any W_81114 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_81118 : bv 32 := 0xf9010113.
Lemma F_81118 : fetch_word Asan.M.loaded_segments (0x81168 : word) = Some W_81118.
Proof. vm_refl. Qed.
Lemma D_81118 : decode_any W_81118 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_8111c : bv 32 := 0x00008993.
Lemma F_8111c : fetch_word Asan.M.loaded_segments (0x8116c : word) = Some W_8111c.
Proof. vm_refl. Qed.
Lemma D_8111c : decode_any W_8111c = Some (OpImm ALU_ADD 19 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81120 : bv 32 := 0x00058493.
Lemma F_81120 : fetch_word Asan.M.loaded_segments (0x81170 : word) = Some W_81120.
Proof. vm_refl. Qed.
Lemma D_81120 : decode_any W_81120 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81124 : bv 32 := 0x00050913.
Lemma F_81124 : fetch_word Asan.M.loaded_segments (0x81174 : word) = Some W_81124.
Proof. vm_refl. Qed.
Lemma D_81124 : decode_any W_81124 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81128 : bv 32 := 0x80040a93.
Lemma F_81128 : fetch_word Asan.M.loaded_segments (0x81178 : word) = Some W_81128.
Proof. vm_refl. Qed.
Lemma D_81128 : decode_any W_81128 = Some (OpImm ALU_ADD 21 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_8112c : bv 32 := 0xfa8a8a93.
Lemma F_8112c : fetch_word Asan.M.loaded_segments (0x8117c : word) = Some W_8112c.
Proof. vm_refl. Qed.
Lemma D_8112c : decode_any W_8112c = Some (OpImm ALU_ADD 21 21 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_81130 : bv 32 := 0x80040513.
Lemma F_81130 : fetch_word Asan.M.loaded_segments (0x81180 : word) = Some W_81130.
Proof. vm_refl. Qed.
Lemma D_81130 : decode_any W_81130 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_81134 : bv 32 := 0xfb850513.
Lemma F_81134 : fetch_word Asan.M.loaded_segments (0x81184 : word) = Some W_81134.
Proof. vm_refl. Qed.
Lemma D_81134 : decode_any W_81134 = Some (OpImm ALU_ADD 10 10 4024, 4%Z).
Proof. vm_refl. Qed.

Definition W_81138 : bv 32 := 0x7ffa8b13.
Lemma F_81138 : fetch_word Asan.M.loaded_segments (0x81188 : word) = Some W_81138.
Proof. vm_refl. Qed.
Lemma D_81138 : decode_any W_81138 = Some (OpImm ALU_ADD 22 21 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_8113c : bv 32 := 0x000b34a3.
Lemma F_8113c : fetch_word Asan.M.loaded_segments (0x8118c : word) = Some W_8113c.
Proof. vm_refl. Qed.
Lemma D_8113c : decode_any W_8113c = Some (Store SZ8 22 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_81140 : bv 32 := 0x00aab023.
Lemma F_81140 : fetch_word Asan.M.loaded_segments (0x81190 : word) = Some W_81140.
Proof. vm_refl. Qed.
Lemma D_81140 : decode_any W_81140 = Some (Store SZ8 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81144 : bv 32 := 0x000ab423.
Lemma F_81144 : fetch_word Asan.M.loaded_segments (0x81194 : word) = Some W_81144.
Proof. vm_refl. Qed.
Lemma D_81144 : decode_any W_81144 = Some (Store SZ8 21 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_81148 : bv 32 := 0x6b5070ef.
Lemma F_81148 : fetch_word Asan.M.loaded_segments (0x81198 : word) = Some W_81148.
Proof. vm_refl. Qed.
Lemma D_81148 : decode_any W_81148 = Some (Jal 1 32436, 4%Z).
Proof. vm_refl. Qed.

Definition W_8114c : bv 32 := 0x00200593.
Lemma F_8114c : fetch_word Asan.M.loaded_segments (0x8119c : word) = Some W_8114c.
Proof. vm_refl. Qed.
Lemma D_8114c : decode_any W_8114c = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_81150 : bv 32 := 0x02a5ea63.
Lemma F_81150 : fetch_word Asan.M.loaded_segments (0x811a0 : word) = Some W_81150.
Proof. vm_refl. Qed.
Lemma D_81150 : decode_any W_81150 = Some (Branch BC_LTU 11 10 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_81184 : bv 32 := 0x155200ef.
Lemma F_81184 : fetch_word Asan.M.loaded_segments (0x811d4 : word) = Some W_81184.
Proof. vm_refl. Qed.
Lemma D_81184 : decode_any W_81184 = Some (Jal 1 133460, 4%Z).
Proof. vm_refl. Qed.

Definition W_81188 : bv 32 := 0x000d2597.
Lemma F_81188 : fetch_word Asan.M.loaded_segments (0x811d8 : word) = Some W_81188.
Proof. vm_refl. Qed.
Lemma D_81188 : decode_any W_81188 = Some (Auipc 11 210, 4%Z).
Proof. vm_refl. Qed.

Definition W_8118c : bv 32 := 0xf505b583.
Lemma F_8118c : fetch_word Asan.M.loaded_segments (0x811dc : word) = Some W_8118c.
Proof. vm_refl. Qed.
Lemma D_8118c : decode_any W_8118c = Some (Load SZ8 true 11 11 3920, 4%Z).
Proof. vm_refl. Qed.

Definition W_81190 : bv 32 := 0x0225ca03.
Lemma F_81190 : fetch_word Asan.M.loaded_segments (0x811e0 : word) = Some W_81190.
Proof. vm_refl. Qed.
Lemma D_81190 : decode_any W_81190 = Some (Load SZ1 false 20 11 34, 4%Z).
Proof. vm_refl. Qed.

Definition W_81194 : bv 32 := 0x00050993.
Lemma F_81194 : fetch_word Asan.M.loaded_segments (0x811e4 : word) = Some W_81194.
Proof. vm_refl. Qed.
Lemma D_81194 : decode_any W_81194 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81198 : bv 32 := 0x665070ef.
Lemma F_81198 : fetch_word Asan.M.loaded_segments (0x811e8 : word) = Some W_81198.
Proof. vm_refl. Qed.
Lemma D_81198 : decode_any W_81198 = Some (Jal 1 32356, 4%Z).
Proof. vm_refl. Qed.

Definition W_8119c : bv 32 := 0x00050793.
Lemma F_8119c : fetch_word Asan.M.loaded_segments (0x811ec : word) = Some W_8119c.
Proof. vm_refl. Qed.
Lemma D_8119c : decode_any W_8119c = Some (OpImm ALU_ADD 15 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_811a0 : bv 32 := 0x00153513.
Lemma F_811a0 : fetch_word Asan.M.loaded_segments (0x811f0 : word) = Some W_811a0.
Proof. vm_refl. Qed.
Lemma D_811a0 : decode_any W_811a0 = Some (OpImm ALU_SLTU 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_811a4 : bv 32 := 0xfff50513.
Lemma F_811a4 : fetch_word Asan.M.loaded_segments (0x811f4 : word) = Some W_811a4.
Proof. vm_refl. Qed.
Lemma D_811a4 : decode_any W_811a4 = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_811a8 : bv 32 := 0x008575b3.
Lemma F_811a8 : fetch_word Asan.M.loaded_segments (0x811f8 : word) = Some W_811a8.
Proof. vm_refl. Qed.
Lemma D_811a8 : decode_any W_811a8 = Some (Op ALU_AND 11 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_811ac : bv 32 := 0x00100513.
Lemma F_811ac : fetch_word Asan.M.loaded_segments (0x811fc : word) = Some W_811ac.
Proof. vm_refl. Qed.
Lemma D_811ac : decode_any W_811ac = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_811b0 : bv 32 := 0x00bb34a3.
Lemma F_811b0 : fetch_word Asan.M.loaded_segments (0x81200 : word) = Some W_811b0.
Proof. vm_refl. Qed.
Lemma D_811b0 : decode_any W_811b0 = Some (Store SZ8 22 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_811b4 : bv 32 := 0x00f56a63.
Lemma F_811b4 : fetch_word Asan.M.loaded_segments (0x81204 : word) = Some W_811b4.
Proof. vm_refl. Qed.
Lemma D_811b4 : decode_any W_811b4 = Some (Branch BC_LTU 10 15 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_811c8 : bv 32 := 0x80040513.
Lemma F_811c8 : fetch_word Asan.M.loaded_segments (0x81218 : word) = Some W_811c8.
Proof. vm_refl. Qed.
Lemma D_811c8 : decode_any W_811c8 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_811cc : bv 32 := 0xfa850513.
Lemma F_811cc : fetch_word Asan.M.loaded_segments (0x8121c : word) = Some W_811cc.
Proof. vm_refl. Qed.
Lemma D_811cc : decode_any W_811cc = Some (OpImm ALU_ADD 10 10 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_811d0 : bv 32 := 0x00098593.
Lemma F_811d0 : fetch_word Asan.M.loaded_segments (0x81220 : word) = Some W_811d0.
Proof. vm_refl. Qed.
Lemma D_811d0 : decode_any W_811d0 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_811d4 : bv 32 := 0x00040613.
Lemma F_811d4 : fetch_word Asan.M.loaded_segments (0x81224 : word) = Some W_811d4.
Proof. vm_refl. Qed.
Lemma D_811d4 : decode_any W_811d4 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_811d8 : bv 32 := 0x00000693.
Lemma F_811d8 : fetch_word Asan.M.loaded_segments (0x81228 : word) = Some W_811d8.
Proof. vm_refl. Qed.
Lemma D_811d8 : decode_any W_811d8 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_811dc : bv 32 := 0x000a0713.
Lemma F_811dc : fetch_word Asan.M.loaded_segments (0x8122c : word) = Some W_811dc.
Proof. vm_refl. Qed.
Lemma D_811dc : decode_any W_811dc = Some (OpImm ALU_ADD 14 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_811e0 : bv 32 := 0x62d070ef.
Lemma F_811e0 : fetch_word Asan.M.loaded_segments (0x81230 : word) = Some W_811e0.
Proof. vm_refl. Qed.
Lemma D_811e0 : decode_any W_811e0 = Some (Jal 1 32300, 4%Z).
Proof. vm_refl. Qed.

Definition W_811e4 : bv 32 := 0x80040613.
Lemma F_811e4 : fetch_word Asan.M.loaded_segments (0x81234 : word) = Some W_811e4.
Proof. vm_refl. Qed.
Lemma D_811e4 : decode_any W_811e4 = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_811e8 : bv 32 := 0xfa860613.
Lemma F_811e8 : fetch_word Asan.M.loaded_segments (0x81238 : word) = Some W_811e8.
Proof. vm_refl. Qed.
Lemma D_811e8 : decode_any W_811e8 = Some (OpImm ALU_ADD 12 12 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_811ec : bv 32 := 0x00090513.
Lemma F_811ec : fetch_word Asan.M.loaded_segments (0x8123c : word) = Some W_811ec.
Proof. vm_refl. Qed.
Lemma D_811ec : decode_any W_811ec = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_811f0 : bv 32 := 0x00048593.
Lemma F_811f0 : fetch_word Asan.M.loaded_segments (0x81240 : word) = Some W_811f0.
Proof. vm_refl. Qed.
Lemma D_811f0 : decode_any W_811f0 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_811f4 : bv 32 := 0xdadd80ef.
Lemma F_811f4 : fetch_word Asan.M.loaded_segments (0x81244 : word) = Some W_811f4.
Proof. vm_refl. Qed.
Lemma D_811f4 : decode_any W_811f4 = Some (Jal 1 1936812, 4%Z).
Proof. vm_refl. Qed.

Definition W_811f8 : bv 32 := 0x07010113.
Lemma F_811f8 : fetch_word Asan.M.loaded_segments (0x81248 : word) = Some W_811f8.
Proof. vm_refl. Qed.
Lemma D_811f8 : decode_any W_811f8 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_811fc : bv 32 := 0x7e813083.
Lemma F_811fc : fetch_word Asan.M.loaded_segments (0x8124c : word) = Some W_811fc.
Proof. vm_refl. Qed.
Lemma D_811fc : decode_any W_811fc = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_81200 : bv 32 := 0x7e013403.
Lemma F_81200 : fetch_word Asan.M.loaded_segments (0x81250 : word) = Some W_81200.
Proof. vm_refl. Qed.
Lemma D_81200 : decode_any W_81200 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_81204 : bv 32 := 0x7d813483.
Lemma F_81204 : fetch_word Asan.M.loaded_segments (0x81254 : word) = Some W_81204.
Proof. vm_refl. Qed.
Lemma D_81204 : decode_any W_81204 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_81208 : bv 32 := 0x7d013903.
Lemma F_81208 : fetch_word Asan.M.loaded_segments (0x81258 : word) = Some W_81208.
Proof. vm_refl. Qed.
Lemma D_81208 : decode_any W_81208 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_8120c : bv 32 := 0x7c813983.
Lemma F_8120c : fetch_word Asan.M.loaded_segments (0x8125c : word) = Some W_8120c.
Proof. vm_refl. Qed.
Lemma D_8120c : decode_any W_8120c = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_81210 : bv 32 := 0x7c013a03.
Lemma F_81210 : fetch_word Asan.M.loaded_segments (0x81260 : word) = Some W_81210.
Proof. vm_refl. Qed.
Lemma D_81210 : decode_any W_81210 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_81214 : bv 32 := 0x7b813a83.
Lemma F_81214 : fetch_word Asan.M.loaded_segments (0x81264 : word) = Some W_81214.
Proof. vm_refl. Qed.
Lemma D_81214 : decode_any W_81214 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_81218 : bv 32 := 0x7b013b03.
Lemma F_81218 : fetch_word Asan.M.loaded_segments (0x81268 : word) = Some W_81218.
Proof. vm_refl. Qed.
Lemma D_81218 : decode_any W_81218 = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_8121c : bv 32 := 0x7f010113.
Lemma F_8121c : fetch_word Asan.M.loaded_segments (0x8126c : word) = Some W_8121c.
Proof. vm_refl. Qed.
Lemma D_8121c : decode_any W_8121c = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_81220 : bv 32 := 0x00008067.
Lemma F_81220 : fetch_word Asan.M.loaded_segments (0x81270 : word) = Some W_81220.
Proof. vm_refl. Qed.
Lemma D_81220 : decode_any W_81220 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81cb4 : bv 32 := 0x000da517.
Lemma F_81cb4 : fetch_word Asan.M.loaded_segments (0x81d04 : word) = Some W_81cb4.
Proof. vm_refl. Qed.
Lemma D_81cb4 : decode_any W_81cb4 = Some (Auipc 10 218, 4%Z).
Proof. vm_refl. Qed.

Definition W_81cb8 : bv 32 := 0x51850503.
Lemma F_81cb8 : fetch_word Asan.M.loaded_segments (0x81d08 : word) = Some W_81cb8.
Proof. vm_refl. Qed.
Lemma D_81cb8 : decode_any W_81cb8 = Some (Load SZ1 true 10 10 1304, 4%Z).
Proof. vm_refl. Qed.

Definition W_81cbc : bv 32 := 0x0230000f.
Lemma F_81cbc : fetch_word Asan.M.loaded_segments (0x81d0c : word) = Some W_81cbc.
Proof. vm_refl. Qed.
Lemma D_81cbc : decode_any W_81cbc = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81cc0 : bv 32 := 0x00a03533.
Lemma F_81cc0 : fetch_word Asan.M.loaded_segments (0x81d10 : word) = Some W_81cc0.
Proof. vm_refl. Qed.
Lemma D_81cc0 : decode_any W_81cc0 = Some (Op ALU_SLTU 10 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_81cc4 : bv 32 := 0x00008067.
Lemma F_81cc4 : fetch_word Asan.M.loaded_segments (0x81d14 : word) = Some W_81cc4.
Proof. vm_refl. Qed.
Lemma D_81cc4 : decode_any W_81cc4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81cc8 : bv 32 := 0xfc010113.
Lemma F_81cc8 : fetch_word Asan.M.loaded_segments (0x81d18 : word) = Some W_81cc8.
Proof. vm_refl. Qed.
Lemma D_81cc8 : decode_any W_81cc8 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_81ccc : bv 32 := 0x02113c23.
Lemma F_81ccc : fetch_word Asan.M.loaded_segments (0x81d1c : word) = Some W_81ccc.
Proof. vm_refl. Qed.
Lemma D_81ccc : decode_any W_81ccc = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_81cd0 : bv 32 := 0x02813823.
Lemma F_81cd0 : fetch_word Asan.M.loaded_segments (0x81d20 : word) = Some W_81cd0.
Proof. vm_refl. Qed.
Lemma D_81cd0 : decode_any W_81cd0 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_81cd4 : bv 32 := 0x02913423.
Lemma F_81cd4 : fetch_word Asan.M.loaded_segments (0x81d24 : word) = Some W_81cd4.
Proof. vm_refl. Qed.
Lemma D_81cd4 : decode_any W_81cd4 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_81cd8 : bv 32 := 0x03213023.
Lemma F_81cd8 : fetch_word Asan.M.loaded_segments (0x81d28 : word) = Some W_81cd8.
Proof. vm_refl. Qed.
Lemma D_81cd8 : decode_any W_81cd8 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_81cdc : bv 32 := 0x01313c23.
Lemma F_81cdc : fetch_word Asan.M.loaded_segments (0x81d2c : word) = Some W_81cdc.
Proof. vm_refl. Qed.
Lemma D_81cdc : decode_any W_81cdc = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_81ce0 : bv 32 := 0x01413823.
Lemma F_81ce0 : fetch_word Asan.M.loaded_segments (0x81d30 : word) = Some W_81ce0.
Proof. vm_refl. Qed.
Lemma D_81ce0 : decode_any W_81ce0 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_81ce4 : bv 32 := 0x01513423.
Lemma F_81ce4 : fetch_word Asan.M.loaded_segments (0x81d34 : word) = Some W_81ce4.
Proof. vm_refl. Qed.
Lemma D_81ce4 : decode_any W_81ce4 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_81ce8 : bv 32 := 0x00060a63.
Lemma F_81ce8 : fetch_word Asan.M.loaded_segments (0x81d38 : word) = Some W_81ce8.
Proof. vm_refl. Qed.
Lemma D_81ce8 : decode_any W_81ce8 = Some (Branch BC_EQ 12 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_81cec : bv 32 := 0x000da697.
Lemma F_81cec : fetch_word Asan.M.loaded_segments (0x81d3c : word) = Some W_81cec.
Proof. vm_refl. Qed.
Lemma D_81cec : decode_any W_81cec = Some (Auipc 13 218, 4%Z).
Proof. vm_refl. Qed.

Definition W_81cf0 : bv 32 := 0x4e068683.
Lemma F_81cf0 : fetch_word Asan.M.loaded_segments (0x81d40 : word) = Some W_81cf0.
Proof. vm_refl. Qed.
Lemma D_81cf0 : decode_any W_81cf0 = Some (Load SZ1 true 13 13 1248, 4%Z).
Proof. vm_refl. Qed.

Definition W_81cf4 : bv 32 := 0x0230000f.
Lemma F_81cf4 : fetch_word Asan.M.loaded_segments (0x81d44 : word) = Some W_81cf4.
Proof. vm_refl. Qed.
Lemma D_81cf4 : decode_any W_81cf4 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81cf8 : bv 32 := 0x0a068a63.
Lemma F_81cf8 : fetch_word Asan.M.loaded_segments (0x81d48 : word) = Some W_81cf8.
Proof. vm_refl. Qed.
Lemma D_81cf8 : decode_any W_81cf8 = Some (Branch BC_EQ 13 0 180, 4%Z).
Proof. vm_refl. Qed.

Definition W_81cfc : bv 32 := 0x00757693.
Lemma F_81cfc : fetch_word Asan.M.loaded_segments (0x81d4c : word) = Some W_81cfc.
Proof. vm_refl. Qed.
Lemma D_81cfc : decode_any W_81cfc = Some (OpImm ALU_AND 13 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_81d00 : bv 32 := 0x42069863.
Lemma F_81d00 : fetch_word Asan.M.loaded_segments (0x81d50 : word) = Some W_81d00.
Proof. vm_refl. Qed.
Lemma D_81d00 : decode_any W_81d00 = Some (Branch BC_NE 13 0 1072, 4%Z).
Proof. vm_refl. Qed.

Definition W_81d04 : bv 32 := 0x000d1697.
Lemma F_81d04 : fetch_word Asan.M.loaded_segments (0x81d54 : word) = Some W_81d04.
Proof. vm_refl. Qed.
Lemma D_81d04 : decode_any W_81d04 = Some (Auipc 13 209, 4%Z).
Proof. vm_refl. Qed.

Definition W_81d08 : bv 32 := 0x3e46b683.
Lemma F_81d08 : fetch_word Asan.M.loaded_segments (0x81d58 : word) = Some W_81d08.
Proof. vm_refl. Qed.
Lemma D_81d08 : decode_any W_81d08 = Some (Load SZ8 true 13 13 996, 4%Z).
Proof. vm_refl. Qed.

Definition W_81d0c : bv 32 := 0x0006b483.
Lemma F_81d0c : fetch_word Asan.M.loaded_segments (0x81d5c : word) = Some W_81d0c.
Proof. vm_refl. Qed.
Lemma D_81d0c : decode_any W_81d0c = Some (Load SZ8 true 9 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81d10 : bv 32 := 0xfff48693.
Lemma F_81d10 : fetch_word Asan.M.loaded_segments (0x81d60 : word) = Some W_81d10.
Proof. vm_refl. Qed.
Lemma D_81d10 : decode_any W_81d10 = Some (OpImm ALU_ADD 13 9 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_81d14 : bv 32 := 0x00d4b733.
Lemma F_81d14 : fetch_word Asan.M.loaded_segments (0x81d64 : word) = Some W_81d14.
Proof. vm_refl. Qed.
Lemma D_81d14 : decode_any W_81d14 = Some (Op ALU_SLTU 14 9 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_81d18 : bv 32 := 0xfff70713.
Lemma F_81d18 : fetch_word Asan.M.loaded_segments (0x81d68 : word) = Some W_81d18.
Proof. vm_refl. Qed.
Lemma D_81d18 : decode_any W_81d18 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_81d1c : bv 32 := 0x00d77733.
Lemma F_81d1c : fetch_word Asan.M.loaded_segments (0x81d6c : word) = Some W_81d1c.
Proof. vm_refl. Qed.
Lemma D_81d1c : decode_any W_81d1c = Some (Op ALU_AND 14 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_81d20 : bv 32 := 0x1ca77c63.
Lemma F_81d20 : fetch_word Asan.M.loaded_segments (0x81d70 : word) = Some W_81d20.
Proof. vm_refl. Qed.
Lemma D_81d20 : decode_any W_81d20 = Some (Branch BC_GEU 14 10 472, 4%Z).
Proof. vm_refl. Qed.

Definition W_81d24 : bv 32 := 0x000d1797.
Lemma F_81d24 : fetch_word Asan.M.loaded_segments (0x81d74 : word) = Some W_81d24.
Proof. vm_refl. Qed.
Lemma D_81d24 : decode_any W_81d24 = Some (Auipc 15 209, 4%Z).
Proof. vm_refl. Qed.

Definition W_81d28 : bv 32 := 0x3cc7b783.
Lemma F_81d28 : fetch_word Asan.M.loaded_segments (0x81d78 : word) = Some W_81d28.
Proof. vm_refl. Qed.
Lemma D_81d28 : decode_any W_81d28 = Some (Load SZ8 true 15 15 972, 4%Z).
Proof. vm_refl. Qed.

Definition W_81d2c : bv 32 := 0x000d1817.
Lemma F_81d2c : fetch_word Asan.M.loaded_segments (0x81d7c : word) = Some W_81d2c.
Proof. vm_refl. Qed.
Lemma D_81d2c : decode_any W_81d2c = Some (Auipc 16 209, 4%Z).
Proof. vm_refl. Qed.

Definition W_81d30 : bv 32 := 0x3cc83803.
Lemma F_81d30 : fetch_word Asan.M.loaded_segments (0x81d80 : word) = Some W_81d30.
Proof. vm_refl. Qed.
Lemma D_81d30 : decode_any W_81d30 = Some (Load SZ8 true 16 16 972, 4%Z).
Proof. vm_refl. Qed.

Definition W_81d34 : bv 32 := 0x0007b883.
Lemma F_81d34 : fetch_word Asan.M.loaded_segments (0x81d84 : word) = Some W_81d34.
Proof. vm_refl. Qed.
Lemma D_81d34 : decode_any W_81d34 = Some (Load SZ8 true 17 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81d38 : bv 32 := 0x00083783.
Lemma F_81d38 : fetch_word Asan.M.loaded_segments (0x81d88 : word) = Some W_81d38.
Proof. vm_refl. Qed.
Lemma D_81d38 : decode_any W_81d38 = Some (Load SZ8 true 15 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81d3c : bv 32 := 0xfff88813.
Lemma F_81d3c : fetch_word Asan.M.loaded_segments (0x81d8c : word) = Some W_81d3c.
Proof. vm_refl. Qed.
Lemma D_81d3c : decode_any W_81d3c = Some (OpImm ALU_ADD 16 17 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_81d40 : bv 32 := 0x00a87463.
Lemma F_81d40 : fetch_word Asan.M.loaded_segments (0x81d90 : word) = Some W_81d40.
Proof. vm_refl. Qed.
Lemma D_81d40 : decode_any W_81d40 = Some (Branch BC_GEU 16 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_81d48 : bv 32 := 0x000d1297.
Lemma F_81d48 : fetch_word Asan.M.loaded_segments (0x81d98 : word) = Some W_81d48.
Proof. vm_refl. Qed.
Lemma D_81d48 : decode_any W_81d48 = Some (Auipc 5 209, 4%Z).
Proof. vm_refl. Qed.

Definition W_81d4c : bv 32 := 0x3b82b283.
Lemma F_81d4c : fetch_word Asan.M.loaded_segments (0x81d9c : word) = Some W_81d4c.
Proof. vm_refl. Qed.
Lemma D_81d4c : decode_any W_81d4c = Some (Load SZ8 true 5 5 952, 4%Z).
Proof. vm_refl. Qed.

Definition W_81d50 : bv 32 := 0x0002be03.
Lemma F_81d50 : fetch_word Asan.M.loaded_segments (0x81da0 : word) = Some W_81d50.
Proof. vm_refl. Qed.
Lemma D_81d50 : decode_any W_81d50 = Some (Load SZ8 true 28 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81d54 : bv 32 := 0x003e5313.
Lemma F_81d54 : fetch_word Asan.M.loaded_segments (0x81da4 : word) = Some W_81d54.
Proof. vm_refl. Qed.
Lemma D_81d54 : decode_any W_81d54 = Some (ShiftImm ALU_SRL 6 28 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_81d58 : bv 32 := 0x009303b3.
Lemma F_81d58 : fetch_word Asan.M.loaded_segments (0x81da8 : word) = Some W_81d58.
Proof. vm_refl. Qed.
Lemma D_81d58 : decode_any W_81d58 = Some (Op ALU_ADD 7 6 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_81d5c : bv 32 := 0x00ae6463.
Lemma F_81d5c : fetch_word Asan.M.loaded_segments (0x81dac : word) = Some W_81d5c.
Proof. vm_refl. Qed.
Lemma D_81d5c : decode_any W_81d5c = Some (Branch BC_LTU 28 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_81d60 : bv 32 := 0x0ca3e463.
Lemma F_81d60 : fetch_word Asan.M.loaded_segments (0x81db0 : word) = Some W_81d60.
Proof. vm_refl. Qed.
Lemma D_81d60 : decode_any W_81d60 = Some (Branch BC_LTU 7 10 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_81e28 : bv 32 := 0x0002b383.
Lemma F_81e28 : fetch_word Asan.M.loaded_segments (0x81e78 : word) = Some W_81e28.
Proof. vm_refl. Qed.
Lemma D_81e28 : decode_any W_81e28 = Some (Load SZ8 true 7 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81e2c : bv 32 := 0x0033d293.
Lemma F_81e2c : fetch_word Asan.M.loaded_segments (0x81e7c : word) = Some W_81e2c.
Proof. vm_refl. Qed.
Lemma D_81e2c : decode_any W_81e2c = Some (ShiftImm ALU_SRL 5 7 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_81e30 : bv 32 := 0x00928333.
Lemma F_81e30 : fetch_word Asan.M.loaded_segments (0x81e80 : word) = Some W_81e30.
Proof. vm_refl. Qed.
Lemma D_81e30 : decode_any W_81e30 = Some (Op ALU_ADD 6 5 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_81e34 : bv 32 := 0x00a3e463.
Lemma F_81e34 : fetch_word Asan.M.loaded_segments (0x81e84 : word) = Some W_81e34.
Proof. vm_refl. Qed.
Lemma D_81e34 : decode_any W_81e34 = Some (Branch BC_LTU 7 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_81e38 : bv 32 := 0x0ca36063.
Lemma F_81e38 : fetch_word Asan.M.loaded_segments (0x81e88 : word) = Some W_81e38.
Proof. vm_refl. Qed.
Lemma D_81e38 : decode_any W_81e38 = Some (Branch BC_LTU 6 10 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_81ef8 : bv 32 := 0x0075f793.
Lemma F_81ef8 : fetch_word Asan.M.loaded_segments (0x81f48 : word) = Some W_81ef8.
Proof. vm_refl. Qed.
Lemma D_81ef8 : decode_any W_81ef8 = Some (OpImm ALU_AND 15 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_81efc : bv 32 := 0x26079a63.
Lemma F_81efc : fetch_word Asan.M.loaded_segments (0x81f4c : word) = Some W_81efc.
Proof. vm_refl. Qed.
Lemma D_81efc : decode_any W_81efc = Some (Branch BC_NE 15 0 628, 4%Z).
Proof. vm_refl. Qed.

Definition W_81f00 : bv 32 := 0x00b505b3.
Lemma F_81f00 : fetch_word Asan.M.loaded_segments (0x81f50 : word) = Some W_81f00.
Proof. vm_refl. Qed.
Lemma D_81f00 : decode_any W_81f00 = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_81f04 : bv 32 := 0xff858593.
Lemma F_81f04 : fetch_word Asan.M.loaded_segments (0x81f54 : word) = Some W_81f04.
Proof. vm_refl. Qed.
Lemma D_81f04 : decode_any W_81f04 = Some (OpImm ALU_ADD 11 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_81f08 : bv 32 := 0x04b77263.
Lemma F_81f08 : fetch_word Asan.M.loaded_segments (0x81f58 : word) = Some W_81f08.
Proof. vm_refl. Qed.
Lemma D_81f08 : decode_any W_81f08 = Some (Branch BC_GEU 14 11 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_81f0c : bv 32 := 0x000d1717.
Lemma F_81f0c : fetch_word Asan.M.loaded_segments (0x81f5c : word) = Some W_81f0c.
Proof. vm_refl. Qed.
Lemma D_81f0c : decode_any W_81f0c = Some (Auipc 14 209, 4%Z).
Proof. vm_refl. Qed.

Definition W_81f10 : bv 32 := 0x1e473703.
Lemma F_81f10 : fetch_word Asan.M.loaded_segments (0x81f60 : word) = Some W_81f10.
Proof. vm_refl. Qed.
Lemma D_81f10 : decode_any W_81f10 = Some (Load SZ8 true 14 14 484, 4%Z).
Proof. vm_refl. Qed.

Definition W_81f14 : bv 32 := 0x000d1797.
Lemma F_81f14 : fetch_word Asan.M.loaded_segments (0x81f64 : word) = Some W_81f14.
Proof. vm_refl. Qed.
Lemma D_81f14 : decode_any W_81f14 = Some (Auipc 15 209, 4%Z).
Proof. vm_refl. Qed.

Definition W_81f18 : bv 32 := 0x1e47b783.
Lemma F_81f18 : fetch_word Asan.M.loaded_segments (0x81f68 : word) = Some W_81f18.
Proof. vm_refl. Qed.
Lemma D_81f18 : decode_any W_81f18 = Some (Load SZ8 true 15 15 484, 4%Z).
Proof. vm_refl. Qed.

Definition W_81f1c : bv 32 := 0x00073883.
Lemma F_81f1c : fetch_word Asan.M.loaded_segments (0x81f6c : word) = Some W_81f1c.
Proof. vm_refl. Qed.
Lemma D_81f1c : decode_any W_81f1c = Some (Load SZ8 true 17 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81f20 : bv 32 := 0x0007b703.
Lemma F_81f20 : fetch_word Asan.M.loaded_segments (0x81f70 : word) = Some W_81f20.
Proof. vm_refl. Qed.
Lemma D_81f20 : decode_any W_81f20 = Some (Load SZ8 true 14 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81f24 : bv 32 := 0xfff88813.
Lemma F_81f24 : fetch_word Asan.M.loaded_segments (0x81f74 : word) = Some W_81f24.
Proof. vm_refl. Qed.
Lemma D_81f24 : decode_any W_81f24 = Some (OpImm ALU_ADD 16 17 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_81f28 : bv 32 := 0x00b87463.
Lemma F_81f28 : fetch_word Asan.M.loaded_segments (0x81f78 : word) = Some W_81f28.
Proof. vm_refl. Qed.
Lemma D_81f28 : decode_any W_81f28 = Some (Branch BC_GEU 16 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_81f30 : bv 32 := 0x000d1797.
Lemma F_81f30 : fetch_word Asan.M.loaded_segments (0x81f80 : word) = Some W_81f30.
Proof. vm_refl. Qed.
Lemma D_81f30 : decode_any W_81f30 = Some (Auipc 15 209, 4%Z).
Proof. vm_refl. Qed.

Definition W_81f34 : bv 32 := 0x1d07b783.
Lemma F_81f34 : fetch_word Asan.M.loaded_segments (0x81f84 : word) = Some W_81f34.
Proof. vm_refl. Qed.
Lemma D_81f34 : decode_any W_81f34 = Some (Load SZ8 true 15 15 464, 4%Z).
Proof. vm_refl. Qed.

Definition W_81f38 : bv 32 := 0x0007b303.
Lemma F_81f38 : fetch_word Asan.M.loaded_segments (0x81f88 : word) = Some W_81f38.
Proof. vm_refl. Qed.
Lemma D_81f38 : decode_any W_81f38 = Some (Load SZ8 true 6 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81f3c : bv 32 := 0x00335793.
Lemma F_81f3c : fetch_word Asan.M.loaded_segments (0x81f8c : word) = Some W_81f3c.
Proof. vm_refl. Qed.
Lemma D_81f3c : decode_any W_81f3c = Some (ShiftImm ALU_SRL 15 6 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_81f40 : bv 32 := 0x009782b3.
Lemma F_81f40 : fetch_word Asan.M.loaded_segments (0x81f90 : word) = Some W_81f40.
Proof. vm_refl. Qed.
Lemma D_81f40 : decode_any W_81f40 = Some (Op ALU_ADD 5 15 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_81f44 : bv 32 := 0x12b36263.
Lemma F_81f44 : fetch_word Asan.M.loaded_segments (0x81f94 : word) = Some W_81f44.
Proof. vm_refl. Qed.
Lemma D_81f44 : decode_any W_81f44 = Some (Branch BC_LTU 6 11 292, 4%Z).
Proof. vm_refl. Qed.

Definition W_81f48 : bv 32 := 0x12b2f063.
Lemma F_81f48 : fetch_word Asan.M.loaded_segments (0x81f98 : word) = Some W_81f48.
Proof. vm_refl. Qed.
Lemma D_81f48 : decode_any W_81f48 = Some (Branch BC_GEU 5 11 288, 4%Z).
Proof. vm_refl. Qed.

Definition W_81f4c : bv 32 := 0x000d1697.
Lemma F_81f4c : fetch_word Asan.M.loaded_segments (0x81f9c : word) = Some W_81f4c.
Proof. vm_refl. Qed.
Lemma D_81f4c : decode_any W_81f4c = Some (Auipc 13 209, 4%Z).
Proof. vm_refl. Qed.

Definition W_81f50 : bv 32 := 0x1bc6b983.
Lemma F_81f50 : fetch_word Asan.M.loaded_segments (0x81fa0 : word) = Some W_81f50.
Proof. vm_refl. Qed.
Lemma D_81f50 : decode_any W_81f50 = Some (Load SZ8 true 19 13 444, 4%Z).
Proof. vm_refl. Qed.

Definition W_81f54 : bv 32 := 0x0009b303.
Lemma F_81f54 : fetch_word Asan.M.loaded_segments (0x81fa4 : word) = Some W_81f54.
Proof. vm_refl. Qed.
Lemma D_81f54 : decode_any W_81f54 = Some (Load SZ8 true 6 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81f58 : bv 32 := 0x22030c63.
Lemma F_81f58 : fetch_word Asan.M.loaded_segments (0x81fa8 : word) = Some W_81f58.
Proof. vm_refl. Qed.
Lemma D_81f58 : decode_any W_81f58 = Some (Branch BC_EQ 6 0 568, 4%Z).
Proof. vm_refl. Qed.

Definition W_81f5c : bv 32 := 0x00355693.
Lemma F_81f5c : fetch_word Asan.M.loaded_segments (0x81fac : word) = Some W_81f5c.
Proof. vm_refl. Qed.
Lemma D_81f5c : decode_any W_81f5c = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_81f60 : bv 32 := 0x0035d593.
Lemma F_81f60 : fetch_word Asan.M.loaded_segments (0x81fb0 : word) = Some W_81f60.
Proof. vm_refl. Qed.
Lemma D_81f60 : decode_any W_81f60 = Some (ShiftImm ALU_SRL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_81f64 : bv 32 := 0x00d48533.
Lemma F_81f64 : fetch_word Asan.M.loaded_segments (0x81fb4 : word) = Some W_81f64.
Proof. vm_refl. Qed.
Lemma D_81f64 : decode_any W_81f64 = Some (Op ALU_ADD 10 9 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_81f68 : bv 32 := 0x00158913.
Lemma F_81f68 : fetch_word Asan.M.loaded_segments (0x81fb8 : word) = Some W_81f68.
Proof. vm_refl. Qed.
Lemma D_81f68 : decode_any W_81f68 = Some (OpImm ALU_ADD 18 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_81f6c : bv 32 := 0x40d90433.
Lemma F_81f6c : fetch_word Asan.M.loaded_segments (0x81fbc : word) = Some W_81f6c.
Proof. vm_refl. Qed.
Lemma D_81f6c : decode_any W_81f6c = Some (Op ALU_SUB 8 18 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_81f70 : bv 32 := 0x0c061063.
Lemma F_81f70 : fetch_word Asan.M.loaded_segments (0x81fc0 : word) = Some W_81f70.
Proof. vm_refl. Qed.
Lemma D_81f70 : decode_any W_81f70 = Some (Branch BC_NE 12 0 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_81f74 : bv 32 := 0x000d1597.
Lemma F_81f74 : fetch_word Asan.M.loaded_segments (0x81fc4 : word) = Some W_81f74.
Proof. vm_refl. Qed.
Lemma D_81f74 : decode_any W_81f74 = Some (Auipc 11 209, 4%Z).
Proof. vm_refl. Qed.

Definition W_81f78 : bv 32 := 0x1645b583.
Lemma F_81f78 : fetch_word Asan.M.loaded_segments (0x81fc8 : word) = Some W_81f78.
Proof. vm_refl. Qed.
Lemma D_81f78 : decode_any W_81f78 = Some (Load SZ8 true 11 11 356, 4%Z).
Proof. vm_refl. Qed.

Definition W_81f7c : bv 32 := 0x0785b583.
Lemma F_81f7c : fetch_word Asan.M.loaded_segments (0x81fcc : word) = Some W_81f7c.
Proof. vm_refl. Qed.
Lemma D_81f7c : decode_any W_81f7c = Some (Load SZ8 true 11 11 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_81f80 : bv 32 := 0x0ab46863.
Lemma F_81f80 : fetch_word Asan.M.loaded_segments (0x81fd0 : word) = Some W_81f80.
Proof. vm_refl. Qed.
Lemma D_81f80 : decode_any W_81f80 = Some (Branch BC_LTU 8 11 176, 4%Z).
Proof. vm_refl. Qed.

