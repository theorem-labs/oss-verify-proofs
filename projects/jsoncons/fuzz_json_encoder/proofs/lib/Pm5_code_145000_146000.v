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
Definition W_145170 : bv 32 := 0xfd010113.
Lemma F_145170 : fetch_word AsanUbsan.M.loaded_segments (0x1451ac : word) = Some W_145170.
Proof. vm_refl. Qed.
Lemma D_145170 : decode_any W_145170 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_145174 : bv 32 := 0x02113423.
Lemma F_145174 : fetch_word AsanUbsan.M.loaded_segments (0x1451b0 : word) = Some W_145174.
Proof. vm_refl. Qed.
Lemma D_145174 : decode_any W_145174 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_145178 : bv 32 := 0x02813023.
Lemma F_145178 : fetch_word AsanUbsan.M.loaded_segments (0x1451b4 : word) = Some W_145178.
Proof. vm_refl. Qed.
Lemma D_145178 : decode_any W_145178 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14517c : bv 32 := 0x00913c23.
Lemma F_14517c : fetch_word AsanUbsan.M.loaded_segments (0x1451b8 : word) = Some W_14517c.
Proof. vm_refl. Qed.
Lemma D_14517c : decode_any W_14517c = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_145180 : bv 32 := 0x01213823.
Lemma F_145180 : fetch_word AsanUbsan.M.loaded_segments (0x1451bc : word) = Some W_145180.
Proof. vm_refl. Qed.
Lemma D_145180 : decode_any W_145180 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_145184 : bv 32 := 0x01313423.
Lemma F_145184 : fetch_word AsanUbsan.M.loaded_segments (0x1451c0 : word) = Some W_145184.
Proof. vm_refl. Qed.
Lemma D_145184 : decode_any W_145184 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_145188 : bv 32 := 0x01413023.
Lemma F_145188 : fetch_word AsanUbsan.M.loaded_segments (0x1451c4 : word) = Some W_145188.
Proof. vm_refl. Qed.
Lemma D_145188 : decode_any W_145188 = Some (Store SZ8 2 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14518c : bv 32 := 0x00058493.
Lemma F_14518c : fetch_word AsanUbsan.M.loaded_segments (0x1451c8 : word) = Some W_14518c.
Proof. vm_refl. Qed.
Lemma D_14518c : decode_any W_14518c = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_145190 : bv 32 := 0x00050913.
Lemma F_145190 : fetch_word AsanUbsan.M.loaded_segments (0x1451cc : word) = Some W_145190.
Proof. vm_refl. Qed.
Lemma D_145190 : decode_any W_145190 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_145194 : bv 32 := 0x0057c517.
Lemma F_145194 : fetch_word AsanUbsan.M.loaded_segments (0x1451d0 : word) = Some W_145194.
Proof. vm_refl. Qed.
Lemma D_145194 : decode_any W_145194 = Some (Auipc 10 1404, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_145198 : bv 32 := 0x71050a13.
Lemma F_145198 : fetch_word AsanUbsan.M.loaded_segments (0x1451d4 : word) = Some W_145198.
Proof. vm_refl. Qed.
Lemma D_145198 : decode_any W_145198 = Some (OpImm ALU_ADD 20 10 1808, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14519c : bv 32 := 0x004a0413.
Lemma F_14519c : fetch_word AsanUbsan.M.loaded_segments (0x1451d8 : word) = Some W_14519c.
Proof. vm_refl. Qed.
Lemma D_14519c : decode_any W_14519c = Some (OpImm ALU_ADD 8 20 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1451a0 : bv 32 := 0x00040513.
Lemma F_1451a0 : fetch_word AsanUbsan.M.loaded_segments (0x1451dc : word) = Some W_1451a0.
Proof. vm_refl. Qed.
Lemma D_1451a0 : decode_any W_1451a0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1451a4 : bv 32 := 0x799110ef.
Lemma F_1451a4 : fetch_word AsanUbsan.M.loaded_segments (0x1451e0 : word) = Some W_1451a4.
Proof. vm_refl. Qed.
Lemma D_1451a4 : decode_any W_1451a4 = Some (Jal 1 73624, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1451a8 : bv 32 := 0x000a4503.
Lemma F_1451a8 : fetch_word AsanUbsan.M.loaded_segments (0x1451e4 : word) = Some W_1451a8.
Proof. vm_refl. Qed.
Lemma D_1451a8 : decode_any W_1451a8 = Some (Load SZ1 false 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1451ac : bv 32 := 0xfff00993.
Lemma F_1451ac : fetch_word AsanUbsan.M.loaded_segments (0x1451e8 : word) = Some W_1451ac.
Proof. vm_refl. Qed.
Lemma D_1451ac : decode_any W_1451ac = Some (OpImm ALU_ADD 19 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1451b0 : bv 32 := 0x04051e63.
Lemma F_1451b0 : fetch_word AsanUbsan.M.loaded_segments (0x1451ec : word) = Some W_1451b0.
Proof. vm_refl. Qed.
Lemma D_1451b0 : decode_any W_1451b0 = Some (Branch BC_NE 10 0 92, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1451b4 : bv 32 := 0x010a3503.
Lemma F_1451b4 : fetch_word AsanUbsan.M.loaded_segments (0x1451f0 : word) = Some W_1451b4.
Proof. vm_refl. Qed.
Lemma D_1451b4 : decode_any W_1451b4 = Some (Load SZ8 true 10 20 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1451b8 : bv 32 := 0x00051663.
Lemma F_1451b8 : fetch_word AsanUbsan.M.loaded_segments (0x1451f4 : word) = Some W_1451b8.
Proof. vm_refl. Qed.
Lemma D_1451b8 : decode_any W_1451b8 = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1451c4 : bv 32 := 0x008a2583.
Lemma F_1451c4 : fetch_word AsanUbsan.M.loaded_segments (0x145200 : word) = Some W_1451c4.
Proof. vm_refl. Qed.
Lemma D_1451c4 : decode_any W_1451c4 = Some (Load SZ4 true 11 20 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1451c8 : bv 32 := 0x02000613.
Lemma F_1451c8 : fetch_word AsanUbsan.M.loaded_segments (0x145204 : word) = Some W_1451c8.
Proof. vm_refl. Qed.
Lemma D_1451c8 : decode_any W_1451c8 = Some (OpImm ALU_ADD 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1451cc : bv 32 := 0x02c59263.
Lemma F_1451cc : fetch_word AsanUbsan.M.loaded_segments (0x145208 : word) = Some W_1451cc.
Proof. vm_refl. Qed.
Lemma D_1451cc : decode_any W_1451cc = Some (Branch BC_NE 11 12 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1451f0 : bv 32 := 0x00000993.
Lemma F_1451f0 : fetch_word AsanUbsan.M.loaded_segments (0x14522c : word) = Some W_1451f0.
Proof. vm_refl. Qed.
Lemma D_1451f0 : decode_any W_1451f0 = Some (OpImm ALU_ADD 19 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1451f4 : bv 32 := 0x00359613.
Lemma F_1451f4 : fetch_word AsanUbsan.M.loaded_segments (0x145230 : word) = Some W_1451f4.
Proof. vm_refl. Qed.
Lemma D_1451f4 : decode_any W_1451f4 = Some (ShiftImm ALU_SLL 12 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1451f8 : bv 32 := 0x00c50533.
Lemma F_1451f8 : fetch_word AsanUbsan.M.loaded_segments (0x145234 : word) = Some W_1451f8.
Proof. vm_refl. Qed.
Lemma D_1451f8 : decode_any W_1451f8 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1451fc : bv 32 := 0x00158593.
Lemma F_1451fc : fetch_word AsanUbsan.M.loaded_segments (0x145238 : word) = Some W_1451fc.
Proof. vm_refl. Qed.
Lemma D_1451fc : decode_any W_1451fc = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_145200 : bv 32 := 0x01253423.
Lemma F_145200 : fetch_word AsanUbsan.M.loaded_segments (0x14523c : word) = Some W_145200.
Proof. vm_refl. Qed.
Lemma D_145200 : decode_any W_145200 = Some (Store SZ8 10 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_145204 : bv 32 := 0x10953423.
Lemma F_145204 : fetch_word AsanUbsan.M.loaded_segments (0x145240 : word) = Some W_145204.
Proof. vm_refl. Qed.
Lemma D_145204 : decode_any W_145204 = Some (Store SZ8 10 9 264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_145208 : bv 32 := 0x00ba2423.
Lemma F_145208 : fetch_word AsanUbsan.M.loaded_segments (0x145244 : word) = Some W_145208.
Proof. vm_refl. Qed.
Lemma D_145208 : decode_any W_145208 = Some (Store SZ4 20 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14520c : bv 32 := 0x00040513.
Lemma F_14520c : fetch_word AsanUbsan.M.loaded_segments (0x145248 : word) = Some W_14520c.
Proof. vm_refl. Qed.
Lemma D_14520c : decode_any W_14520c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_145210 : bv 32 := 0x1b4120ef.
Lemma F_145210 : fetch_word AsanUbsan.M.loaded_segments (0x14524c : word) = Some W_145210.
Proof. vm_refl. Qed.
Lemma D_145210 : decode_any W_145210 = Some (Jal 1 74164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_145214 : bv 32 := 0x00098513.
Lemma F_145214 : fetch_word AsanUbsan.M.loaded_segments (0x145250 : word) = Some W_145214.
Proof. vm_refl. Qed.
Lemma D_145214 : decode_any W_145214 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_145218 : bv 32 := 0x02813083.
Lemma F_145218 : fetch_word AsanUbsan.M.loaded_segments (0x145254 : word) = Some W_145218.
Proof. vm_refl. Qed.
Lemma D_145218 : decode_any W_145218 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14521c : bv 32 := 0x02013403.
Lemma F_14521c : fetch_word AsanUbsan.M.loaded_segments (0x145258 : word) = Some W_14521c.
Proof. vm_refl. Qed.
Lemma D_14521c : decode_any W_14521c = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_145220 : bv 32 := 0x01813483.
Lemma F_145220 : fetch_word AsanUbsan.M.loaded_segments (0x14525c : word) = Some W_145220.
Proof. vm_refl. Qed.
Lemma D_145220 : decode_any W_145220 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_145224 : bv 32 := 0x01013903.
Lemma F_145224 : fetch_word AsanUbsan.M.loaded_segments (0x145260 : word) = Some W_145224.
Proof. vm_refl. Qed.
Lemma D_145224 : decode_any W_145224 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_145228 : bv 32 := 0x00813983.
Lemma F_145228 : fetch_word AsanUbsan.M.loaded_segments (0x145264 : word) = Some W_145228.
Proof. vm_refl. Qed.
Lemma D_145228 : decode_any W_145228 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14522c : bv 32 := 0x00013a03.
Lemma F_14522c : fetch_word AsanUbsan.M.loaded_segments (0x145268 : word) = Some W_14522c.
Proof. vm_refl. Qed.
Lemma D_14522c : decode_any W_14522c = Some (Load SZ8 true 20 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_145230 : bv 32 := 0x03010113.
Lemma F_145230 : fetch_word AsanUbsan.M.loaded_segments (0x14526c : word) = Some W_145230.
Proof. vm_refl. Qed.
Lemma D_145230 : decode_any W_145230 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_145234 : bv 32 := 0x00008067.
Lemma F_145234 : fetch_word AsanUbsan.M.loaded_segments (0x145270 : word) = Some W_145234.
Proof. vm_refl. Qed.
Lemma D_145234 : decode_any W_145234 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1456a8 : bv 32 := 0xfffff5b7.
Lemma F_1456a8 : fetch_word AsanUbsan.M.loaded_segments (0x1456e4 : word) = Some W_1456a8.
Proof. vm_refl. Qed.
Lemma D_1456a8 : decode_any W_1456a8 = Some (Lui 11 1048575, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1456ac : bv 32 := 0x0015859b.
Lemma F_1456ac : fetch_word AsanUbsan.M.loaded_segments (0x1456e8 : word) = Some W_1456ac.
Proof. vm_refl. Qed.
Lemma D_1456ac : decode_any W_1456ac = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1456b0 : bv 32 := 0x02b56663.
Lemma F_1456b0 : fetch_word AsanUbsan.M.loaded_segments (0x1456ec : word) = Some W_1456b0.
Proof. vm_refl. Qed.
Lemma D_1456b0 : decode_any W_1456b0 = Some (Branch BC_LTU 10 11 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1456b4 : bv 32 := 0xff010113.
Lemma F_1456b4 : fetch_word AsanUbsan.M.loaded_segments (0x1456f0 : word) = Some W_1456b4.
Proof. vm_refl. Qed.
Lemma D_1456b4 : decode_any W_1456b4 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1456b8 : bv 32 := 0x00113423.
Lemma F_1456b8 : fetch_word AsanUbsan.M.loaded_segments (0x1456f4 : word) = Some W_1456b8.
Proof. vm_refl. Qed.
Lemma D_1456b8 : decode_any W_1456b8 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1456bc : bv 32 := 0x00813023.
Lemma F_1456bc : fetch_word AsanUbsan.M.loaded_segments (0x1456f8 : word) = Some W_1456bc.
Proof. vm_refl. Qed.
Lemma D_1456bc : decode_any W_1456bc = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1456c0 : bv 32 := 0x40a0043b.
Lemma F_1456c0 : fetch_word AsanUbsan.M.loaded_segments (0x1456fc : word) = Some W_1456c0.
Proof. vm_refl. Qed.
Lemma D_1456c0 : decode_any W_1456c0 = Some (Op32 ALU_SUB 8 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1456c4 : bv 32 := 0x8b9ff0ef.
Lemma F_1456c4 : fetch_word AsanUbsan.M.loaded_segments (0x145700 : word) = Some W_1456c4.
Proof. vm_refl. Qed.
Lemma D_1456c4 : decode_any W_1456c4 = Some (Jal 1 2095288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1456c8 : bv 32 := 0x00852023.
Lemma F_1456c8 : fetch_word AsanUbsan.M.loaded_segments (0x145704 : word) = Some W_1456c8.
Proof. vm_refl. Qed.
Lemma D_1456c8 : decode_any W_1456c8 = Some (Store SZ4 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1456cc : bv 32 := 0xfff00513.
Lemma F_1456cc : fetch_word AsanUbsan.M.loaded_segments (0x145708 : word) = Some W_1456cc.
Proof. vm_refl. Qed.
Lemma D_1456cc : decode_any W_1456cc = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1456d0 : bv 32 := 0x00813083.
Lemma F_1456d0 : fetch_word AsanUbsan.M.loaded_segments (0x14570c : word) = Some W_1456d0.
Proof. vm_refl. Qed.
Lemma D_1456d0 : decode_any W_1456d0 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1456d4 : bv 32 := 0x00013403.
Lemma F_1456d4 : fetch_word AsanUbsan.M.loaded_segments (0x145710 : word) = Some W_1456d4.
Proof. vm_refl. Qed.
Lemma D_1456d4 : decode_any W_1456d4 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1456d8 : bv 32 := 0x01010113.
Lemma F_1456d8 : fetch_word AsanUbsan.M.loaded_segments (0x145714 : word) = Some W_1456d8.
Proof. vm_refl. Qed.
Lemma D_1456d8 : decode_any W_1456d8 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1456dc : bv 32 := 0x00008067.
Lemma F_1456dc : fetch_word AsanUbsan.M.loaded_segments (0x145718 : word) = Some W_1456dc.
Proof. vm_refl. Qed.
Lemma D_1456dc : decode_any W_1456dc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

