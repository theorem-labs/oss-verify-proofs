(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec StepTac RealizesCfg DriverCfg MuslStrlen.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import Ub_code_229d0_229e8 PHdrCalc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation PSEGS := Ubsan.M.loaded_segments.

Definition HREGS (regs : bvmap 5 word) (d0 d1 : byte) : bvmap 5 word :=
  regupd (regupd (regupd (regupd (regupd regs 21 (v_lb d1)) 10 (Z_to_bv 64 (bv_unsigned d0)))
    11 (alu64 ALU_SLL (v_lb d1) (zext 64 (57 : bv 6)))) 11 (alu64 ALU_SRL (alu64 ALU_SLL (v_lb d1) (zext 64 (57 : bv 6))) (zext 64 (49 : bv 6))))
    18 (v_or (alu64 ALU_SRL (alu64 ALU_SLL (v_lb d1) (zext 64 (57 : bv 6))) (zext 64 (49 : bv 6))) (Z_to_bv 64 (bv_unsigned d0))).

Section W.
Context {fx : FPState}.

#[using="Type"] Lemma hdr_walk : forall regs mem md T (buf : word) (d0 d1 : byte),
  m_halted md = None -> m_vm_lazy md = [] ->
  getr regs 9 = buf ->
  rdn PSEGS mem (v_addi buf 1) 1 = Some [d1] -> rdn PSEGS mem (v_addi buf 0) 1 = Some [d0] ->
  realizes PSEGS (mkCfg (mkst (HREGS regs d0 d1) (Z_to_bv 64 0x229e4) mem (seg_rom PSEGS)) md) T ->
  realizes PSEGS (mkCfg (mkst regs (Z_to_bv 64 0x229d0) mem (seg_rom PSEGS)) md) T.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs mem md T buf d0 d1 Hh Hl H9 R1 R0 K.
  replace (Z_to_bv 64 0x229d0) with (0x229d0%bv : word) by (apply bv_eq; reflexivity).
  eapply rzc_step; [exact Hh | exact Hl | reflexivity | apply (step_lb PSEGS regs _ mem _ W_229d0 21 9 1 d1 F_229d0 eq_refl D_229d0); rewrite H9; exact R1 |].
  replace (bv_eqb (21 : reg) 0) with false by reflexivity. cbv beta iota.
  replace (v_addi (0x229d0%bv : word) 4) with (0x229d4%bv : word) by (apply bv_eq; reflexivity).
  eapply rzc_step; [exact Hh | exact Hl | reflexivity | apply (step_lbu PSEGS _ _ mem _ W_229d4 10 9 0 d0 F_229d4 eq_refl D_229d4); rewrite getr_other by (intros Hc; discriminate Hc); rewrite H9; exact R0 |].
  replace (bv_eqb (10 : reg) 0) with false by reflexivity. cbv beta iota.
  replace (v_addi (0x229d4%bv : word) 4) with (0x229d8%bv : word) by (apply bv_eq; reflexivity).
  eapply rzc_step; [exact Hh | exact Hl | reflexivity | apply (step_shiftimm_gen PSEGS _ _ mem _ W_229d8 ALU_SLL 11 21 57 F_229d8 eq_refl D_229d8) |].
  replace (bv_eqb (11 : reg) 0) with false by reflexivity. cbv beta iota.
  rewrite getr_other by (intros Hc; discriminate Hc). rewrite getr_same by (intros Hc; discriminate Hc).
  replace (v_addi (0x229d8%bv : word) 4) with (0x229dc%bv : word) by (apply bv_eq; reflexivity).
  eapply rzc_step; [exact Hh | exact Hl | reflexivity | apply (step_shiftimm_gen PSEGS _ _ mem _ W_229dc ALU_SRL 11 11 49 F_229dc eq_refl D_229dc) |].
  replace (bv_eqb (11 : reg) 0) with false by reflexivity. cbv beta iota.
  rewrite getr_same by (intros Hc; discriminate Hc).
  replace (v_addi (0x229dc%bv : word) 4) with (0x229e0%bv : word) by (apply bv_eq; reflexivity).
  match goal with |- realizes _ (mkCfg (mkst ?R _ _ _) _) _ => set (R4 := R) end.
  assert (G11 : getr R4 11 = alu64 ALU_SRL (alu64 ALU_SLL (v_lb d1) (zext 64 (57 : bv 6))) (zext 64 (49 : bv 6))).
  { unfold R4. rewrite getr_same by (intros Hc; discriminate Hc). reflexivity. }
  assert (G10 : getr R4 10 = Z_to_bv 64 (bv_unsigned d0)).
  { unfold R4. rewrite getr_other by (intros Hc; discriminate Hc). rewrite getr_other by (intros Hc; discriminate Hc).
    rewrite getr_same by (intros Hc; discriminate Hc). reflexivity. }
  eapply rzc_step; [exact Hh | exact Hl | reflexivity | apply (step_or PSEGS _ _ mem _ W_229e0 18 11 10 F_229e0 eq_refl D_229e0) |].
  replace (bv_eqb (18 : reg) 0) with false by reflexivity. cbv beta iota.
  rewrite G11, G10.
  replace (v_addi (0x229e0%bv : word) 4) with (Z_to_bv 64 0x229e4) by (apply bv_eq; reflexivity).
  exact K.
Qed.
End W.
