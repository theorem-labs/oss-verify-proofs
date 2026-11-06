(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_135178 : bv 32 := 0xfd010113.
Lemma F_135178 : fetch_word AsanUbsan.M.loaded_segments (0x1351b4 : word) = Some W_135178.
Proof. vm_refl. Qed.
Lemma D_135178 : decode_any W_135178 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_13517c : bv 32 := 0x02113423.
Lemma F_13517c : fetch_word AsanUbsan.M.loaded_segments (0x1351b8 : word) = Some W_13517c.
Proof. vm_refl. Qed.
Lemma D_13517c : decode_any W_13517c = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_135180 : bv 32 := 0x02813023.
Lemma F_135180 : fetch_word AsanUbsan.M.loaded_segments (0x1351bc : word) = Some W_135180.
Proof. vm_refl. Qed.
Lemma D_135180 : decode_any W_135180 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_135184 : bv 32 := 0x00913c23.
Lemma F_135184 : fetch_word AsanUbsan.M.loaded_segments (0x1351c0 : word) = Some W_135184.
Proof. vm_refl. Qed.
Lemma D_135184 : decode_any W_135184 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_135188 : bv 32 := 0x01213823.
Lemma F_135188 : fetch_word AsanUbsan.M.loaded_segments (0x1351c4 : word) = Some W_135188.
Proof. vm_refl. Qed.
Lemma D_135188 : decode_any W_135188 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_13518c : bv 32 := 0x01313423.
Lemma F_13518c : fetch_word AsanUbsan.M.loaded_segments (0x1351c8 : word) = Some W_13518c.
Proof. vm_refl. Qed.
Lemma D_13518c : decode_any W_13518c = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_135190 : bv 32 := 0x01413023.
Lemma F_135190 : fetch_word AsanUbsan.M.loaded_segments (0x1351cc : word) = Some W_135190.
Proof. vm_refl. Qed.
Lemma D_135190 : decode_any W_135190 = Some (Store SZ8 2 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_135194 : bv 32 := 0x00058493.
Lemma F_135194 : fetch_word AsanUbsan.M.loaded_segments (0x1351d0 : word) = Some W_135194.
Proof. vm_refl. Qed.
Lemma D_135194 : decode_any W_135194 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_135198 : bv 32 := 0x00050913.
Lemma F_135198 : fetch_word AsanUbsan.M.loaded_segments (0x1351d4 : word) = Some W_135198.
Proof. vm_refl. Qed.
Lemma D_135198 : decode_any W_135198 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13519c : bv 32 := 0x0057d517.
Lemma F_13519c : fetch_word AsanUbsan.M.loaded_segments (0x1351d8 : word) = Some W_13519c.
Proof. vm_refl. Qed.
Lemma D_13519c : decode_any W_13519c = Some (Auipc 10 1405, 4%Z).
Proof. vm_refl. Qed.

Definition W_1351a0 : bv 32 := 0xc0850a13.
Lemma F_1351a0 : fetch_word AsanUbsan.M.loaded_segments (0x1351dc : word) = Some W_1351a0.
Proof. vm_refl. Qed.
Lemma D_1351a0 : decode_any W_1351a0 = Some (OpImm ALU_ADD 20 10 3080, 4%Z).
Proof. vm_refl. Qed.

Definition W_1351a4 : bv 32 := 0x004a0413.
Lemma F_1351a4 : fetch_word AsanUbsan.M.loaded_segments (0x1351e0 : word) = Some W_1351a4.
Proof. vm_refl. Qed.
Lemma D_1351a4 : decode_any W_1351a4 = Some (OpImm ALU_ADD 8 20 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1351a8 : bv 32 := 0x00040513.
Lemma F_1351a8 : fetch_word AsanUbsan.M.loaded_segments (0x1351e4 : word) = Some W_1351a8.
Proof. vm_refl. Qed.
Lemma D_1351a8 : decode_any W_1351a8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1351ac : bv 32 := 0x799110ef.
Lemma F_1351ac : fetch_word AsanUbsan.M.loaded_segments (0x1351e8 : word) = Some W_1351ac.
Proof. vm_refl. Qed.
Lemma D_1351ac : decode_any W_1351ac = Some (Jal 1 73624, 4%Z).
Proof. vm_refl. Qed.

Definition W_1351b0 : bv 32 := 0x000a4503.
Lemma F_1351b0 : fetch_word AsanUbsan.M.loaded_segments (0x1351ec : word) = Some W_1351b0.
Proof. vm_refl. Qed.
Lemma D_1351b0 : decode_any W_1351b0 = Some (Load SZ1 false 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1351b4 : bv 32 := 0xfff00993.
Lemma F_1351b4 : fetch_word AsanUbsan.M.loaded_segments (0x1351f0 : word) = Some W_1351b4.
Proof. vm_refl. Qed.
Lemma D_1351b4 : decode_any W_1351b4 = Some (OpImm ALU_ADD 19 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_1351b8 : bv 32 := 0x04051e63.
Lemma F_1351b8 : fetch_word AsanUbsan.M.loaded_segments (0x1351f4 : word) = Some W_1351b8.
Proof. vm_refl. Qed.
Lemma D_1351b8 : decode_any W_1351b8 = Some (Branch BC_NE 10 0 92, 4%Z).
Proof. vm_refl. Qed.

Definition W_1351bc : bv 32 := 0x010a3503.
Lemma F_1351bc : fetch_word AsanUbsan.M.loaded_segments (0x1351f8 : word) = Some W_1351bc.
Proof. vm_refl. Qed.
Lemma D_1351bc : decode_any W_1351bc = Some (Load SZ8 true 10 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1351c0 : bv 32 := 0x00051663.
Lemma F_1351c0 : fetch_word AsanUbsan.M.loaded_segments (0x1351fc : word) = Some W_1351c0.
Proof. vm_refl. Qed.
Lemma D_1351c0 : decode_any W_1351c0 = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1351cc : bv 32 := 0x008a2583.
Lemma F_1351cc : fetch_word AsanUbsan.M.loaded_segments (0x135208 : word) = Some W_1351cc.
Proof. vm_refl. Qed.
Lemma D_1351cc : decode_any W_1351cc = Some (Load SZ4 true 11 20 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1351d0 : bv 32 := 0x02000613.
Lemma F_1351d0 : fetch_word AsanUbsan.M.loaded_segments (0x13520c : word) = Some W_1351d0.
Proof. vm_refl. Qed.
Lemma D_1351d0 : decode_any W_1351d0 = Some (OpImm ALU_ADD 12 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1351d4 : bv 32 := 0x02c59263.
Lemma F_1351d4 : fetch_word AsanUbsan.M.loaded_segments (0x135210 : word) = Some W_1351d4.
Proof. vm_refl. Qed.
Lemma D_1351d4 : decode_any W_1351d4 = Some (Branch BC_NE 11 12 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_1351f8 : bv 32 := 0x00000993.
Lemma F_1351f8 : fetch_word AsanUbsan.M.loaded_segments (0x135234 : word) = Some W_1351f8.
Proof. vm_refl. Qed.
Lemma D_1351f8 : decode_any W_1351f8 = Some (OpImm ALU_ADD 19 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1351fc : bv 32 := 0x00359613.
Lemma F_1351fc : fetch_word AsanUbsan.M.loaded_segments (0x135238 : word) = Some W_1351fc.
Proof. vm_refl. Qed.
Lemma D_1351fc : decode_any W_1351fc = Some (ShiftImm ALU_SLL 12 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_135200 : bv 32 := 0x00c50533.
Lemma F_135200 : fetch_word AsanUbsan.M.loaded_segments (0x13523c : word) = Some W_135200.
Proof. vm_refl. Qed.
Lemma D_135200 : decode_any W_135200 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_135204 : bv 32 := 0x00158593.
Lemma F_135204 : fetch_word AsanUbsan.M.loaded_segments (0x135240 : word) = Some W_135204.
Proof. vm_refl. Qed.
Lemma D_135204 : decode_any W_135204 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_135208 : bv 32 := 0x01253423.
Lemma F_135208 : fetch_word AsanUbsan.M.loaded_segments (0x135244 : word) = Some W_135208.
Proof. vm_refl. Qed.
Lemma D_135208 : decode_any W_135208 = Some (Store SZ8 10 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_13520c : bv 32 := 0x10953423.
Lemma F_13520c : fetch_word AsanUbsan.M.loaded_segments (0x135248 : word) = Some W_13520c.
Proof. vm_refl. Qed.
Lemma D_13520c : decode_any W_13520c = Some (Store SZ8 10 9 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_135210 : bv 32 := 0x00ba2423.
Lemma F_135210 : fetch_word AsanUbsan.M.loaded_segments (0x13524c : word) = Some W_135210.
Proof. vm_refl. Qed.
Lemma D_135210 : decode_any W_135210 = Some (Store SZ4 20 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_135214 : bv 32 := 0x00040513.
Lemma F_135214 : fetch_word AsanUbsan.M.loaded_segments (0x135250 : word) = Some W_135214.
Proof. vm_refl. Qed.
Lemma D_135214 : decode_any W_135214 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_135218 : bv 32 := 0x1b4120ef.
Lemma F_135218 : fetch_word AsanUbsan.M.loaded_segments (0x135254 : word) = Some W_135218.
Proof. vm_refl. Qed.
Lemma D_135218 : decode_any W_135218 = Some (Jal 1 74164, 4%Z).
Proof. vm_refl. Qed.

Definition W_13521c : bv 32 := 0x00098513.
Lemma F_13521c : fetch_word AsanUbsan.M.loaded_segments (0x135258 : word) = Some W_13521c.
Proof. vm_refl. Qed.
Lemma D_13521c : decode_any W_13521c = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_135220 : bv 32 := 0x02813083.
Lemma F_135220 : fetch_word AsanUbsan.M.loaded_segments (0x13525c : word) = Some W_135220.
Proof. vm_refl. Qed.
Lemma D_135220 : decode_any W_135220 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_135224 : bv 32 := 0x02013403.
Lemma F_135224 : fetch_word AsanUbsan.M.loaded_segments (0x135260 : word) = Some W_135224.
Proof. vm_refl. Qed.
Lemma D_135224 : decode_any W_135224 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_135228 : bv 32 := 0x01813483.
Lemma F_135228 : fetch_word AsanUbsan.M.loaded_segments (0x135264 : word) = Some W_135228.
Proof. vm_refl. Qed.
Lemma D_135228 : decode_any W_135228 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_13522c : bv 32 := 0x01013903.
Lemma F_13522c : fetch_word AsanUbsan.M.loaded_segments (0x135268 : word) = Some W_13522c.
Proof. vm_refl. Qed.
Lemma D_13522c : decode_any W_13522c = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_135230 : bv 32 := 0x00813983.
Lemma F_135230 : fetch_word AsanUbsan.M.loaded_segments (0x13526c : word) = Some W_135230.
Proof. vm_refl. Qed.
Lemma D_135230 : decode_any W_135230 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_135234 : bv 32 := 0x00013a03.
Lemma F_135234 : fetch_word AsanUbsan.M.loaded_segments (0x135270 : word) = Some W_135234.
Proof. vm_refl. Qed.
Lemma D_135234 : decode_any W_135234 = Some (Load SZ8 true 20 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_135238 : bv 32 := 0x03010113.
Lemma F_135238 : fetch_word AsanUbsan.M.loaded_segments (0x135274 : word) = Some W_135238.
Proof. vm_refl. Qed.
Lemma D_135238 : decode_any W_135238 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_13523c : bv 32 := 0x00008067.
Lemma F_13523c : fetch_word AsanUbsan.M.loaded_segments (0x135278 : word) = Some W_13523c.
Proof. vm_refl. Qed.
Lemma D_13523c : decode_any W_13523c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1356b0 : bv 32 := 0xfffff5b7.
Lemma F_1356b0 : fetch_word AsanUbsan.M.loaded_segments (0x1356ec : word) = Some W_1356b0.
Proof. vm_refl. Qed.
Lemma D_1356b0 : decode_any W_1356b0 = Some (Lui 11 1048575, 4%Z).
Proof. vm_refl. Qed.

Definition W_1356b4 : bv 32 := 0x0015859b.
Lemma F_1356b4 : fetch_word AsanUbsan.M.loaded_segments (0x1356f0 : word) = Some W_1356b4.
Proof. vm_refl. Qed.
Lemma D_1356b4 : decode_any W_1356b4 = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1356b8 : bv 32 := 0x02b56663.
Lemma F_1356b8 : fetch_word AsanUbsan.M.loaded_segments (0x1356f4 : word) = Some W_1356b8.
Proof. vm_refl. Qed.
Lemma D_1356b8 : decode_any W_1356b8 = Some (Branch BC_LTU 10 11 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_1356bc : bv 32 := 0xff010113.
Lemma F_1356bc : fetch_word AsanUbsan.M.loaded_segments (0x1356f8 : word) = Some W_1356bc.
Proof. vm_refl. Qed.
Lemma D_1356bc : decode_any W_1356bc = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_1356c0 : bv 32 := 0x00113423.
Lemma F_1356c0 : fetch_word AsanUbsan.M.loaded_segments (0x1356fc : word) = Some W_1356c0.
Proof. vm_refl. Qed.
Lemma D_1356c0 : decode_any W_1356c0 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1356c4 : bv 32 := 0x00813023.
Lemma F_1356c4 : fetch_word AsanUbsan.M.loaded_segments (0x135700 : word) = Some W_1356c4.
Proof. vm_refl. Qed.
Lemma D_1356c4 : decode_any W_1356c4 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1356c8 : bv 32 := 0x40a0043b.
Lemma F_1356c8 : fetch_word AsanUbsan.M.loaded_segments (0x135704 : word) = Some W_1356c8.
Proof. vm_refl. Qed.
Lemma D_1356c8 : decode_any W_1356c8 = Some (Op32 ALU_SUB 8 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_1356cc : bv 32 := 0x8b9ff0ef.
Lemma F_1356cc : fetch_word AsanUbsan.M.loaded_segments (0x135708 : word) = Some W_1356cc.
Proof. vm_refl. Qed.
Lemma D_1356cc : decode_any W_1356cc = Some (Jal 1 2095288, 4%Z).
Proof. vm_refl. Qed.

Definition W_1356d0 : bv 32 := 0x00852023.
Lemma F_1356d0 : fetch_word AsanUbsan.M.loaded_segments (0x13570c : word) = Some W_1356d0.
Proof. vm_refl. Qed.
Lemma D_1356d0 : decode_any W_1356d0 = Some (Store SZ4 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1356d4 : bv 32 := 0xfff00513.
Lemma F_1356d4 : fetch_word AsanUbsan.M.loaded_segments (0x135710 : word) = Some W_1356d4.
Proof. vm_refl. Qed.
Lemma D_1356d4 : decode_any W_1356d4 = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_1356d8 : bv 32 := 0x00813083.
Lemma F_1356d8 : fetch_word AsanUbsan.M.loaded_segments (0x135714 : word) = Some W_1356d8.
Proof. vm_refl. Qed.
Lemma D_1356d8 : decode_any W_1356d8 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1356dc : bv 32 := 0x00013403.
Lemma F_1356dc : fetch_word AsanUbsan.M.loaded_segments (0x135718 : word) = Some W_1356dc.
Proof. vm_refl. Qed.
Lemma D_1356dc : decode_any W_1356dc = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1356e0 : bv 32 := 0x01010113.
Lemma F_1356e0 : fetch_word AsanUbsan.M.loaded_segments (0x13571c : word) = Some W_1356e0.
Proof. vm_refl. Qed.
Lemma D_1356e0 : decode_any W_1356e0 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1356e4 : bv 32 := 0x00008067.
Lemma F_1356e4 : fetch_word AsanUbsan.M.loaded_segments (0x135720 : word) = Some W_1356e4.
Proof. vm_refl. Qed.
Lemma D_1356e4 : decode_any W_1356e4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

