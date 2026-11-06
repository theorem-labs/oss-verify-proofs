(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatExec SeqExec StepTac LibAtomic SymExec3Sound.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Section FX. Context {fx : FPState}.

Lemma step_amo_w : forall segs regs pc mem rom w op aq rl rd rs1 rs2 bs,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Amo op AW aq rl rd rs1 rs2, 4%Z) ->
  (bv_unsigned (getr regs rs1) mod 4 = 0)%Z ->
  rdn segs mem (getr regs rs1) 4%nat = Some bs ->
  RiscvSemantics.store_ok segs mem (getr regs rs1) 4%nat = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (SX2S.load_result SZ4 true bs))
                  (v_addi pc 4)
                  (wbytes mem (getr regs rs1)
                     (Z_to_le_bytes 4 (bv_unsigned (amo_val op (bv_extract 0 32 (le_bytes_to_word bs))
                                                           (low32 (getr regs rs2))))))
                  rom).
Proof.
  intros segs regs pc mem rom w op aq rl rd rs1 rs2 bs Hfetch Hecall Hdecode Hal Hread Hok.
  atomic_pipeline Hfetch Hecall Hdecode.
  change (if is_x0 rs1 then Z_to_bv 64 0 else reg_get regs rs1) with (getr regs rs1).
  change (if is_x0 rs2 then Z_to_bv 64 0 else reg_get regs rs2) with (getr regs rs2).
  rewrite Hal. change (negb (0 =? 0)%Z) with false. cbv beta iota.
  rewrite ov_rdn, Hread. cbv beta iota.
  rewrite Hok. cbv beta iota.
  rewrite write_to_mem_wbytes, b_npc4.
  unfold regupd, SX2S.load_result.
  destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

Lemma step_amo_d : forall segs regs pc mem rom w op aq rl rd rs1 rs2 bs,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Amo op AD aq rl rd rs1 rs2, 4%Z) ->
  (bv_unsigned (getr regs rs1) mod 8 = 0)%Z ->
  rdn segs mem (getr regs rs1) 8%nat = Some bs ->
  RiscvSemantics.store_ok segs mem (getr regs rs1) 8%nat = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (SX2S.load_result SZ8 true bs))
                  (v_addi pc 4)
                  (wbytes mem (getr regs rs1)
                     (Z_to_le_bytes 8 (bv_unsigned (amo_val op (bv_extract 0 64 (le_bytes_to_word bs))
                                                           (getr regs rs2)))))
                  rom).
Proof.
  intros segs regs pc mem rom w op aq rl rd rs1 rs2 bs Hfetch Hecall Hdecode Hal Hread Hok.
  atomic_pipeline Hfetch Hecall Hdecode.
  change (if is_x0 rs1 then Z_to_bv 64 0 else reg_get regs rs1) with (getr regs rs1).
  change (if is_x0 rs2 then Z_to_bv 64 0 else reg_get regs rs2) with (getr regs rs2).
  rewrite Hal. change (negb (0 =? 0)%Z) with false. cbv beta iota.
  rewrite ov_rdn, Hread. cbv beta iota.
  rewrite Hok. cbv beta iota.
  rewrite write_to_mem_wbytes, b_npc4.
  unfold regupd, SX2S.load_result.
  destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

End FX.

Section CAS. Context {fx : FPState}.

Lemma msteps_cas_w : forall segs regs pc mem rom w0 w1 w2 aq rl aq' rl' (rd rt rd2 rs1 rs2 : reg)
                           (imm1 : bv 13) bs,
  fetch_word segs pc = Some w0 -> is_ecall w0 = false ->
  decode_any w0 = Some (Lr AW aq rl rd rs1, 4%Z) ->
  fetch_word segs (v_addi pc 4) = Some w1 -> is_ecall w1 = false ->
  decode_any w1 = Some (Branch BC_NE rd rt imm1, 4%Z) ->
  fetch_word segs (v_addi (v_addi pc 4) 4) = Some w2 -> is_ecall w2 = false ->
  decode_any w2 = Some (Sc AW aq' rl' rd2 rs1 rs2, 4%Z) ->
  (bv_unsigned (getr regs rs1) mod 4 = 0)%Z ->
  rdn segs mem (getr regs rs1) 4%nat = Some bs ->
  RiscvSemantics.store_ok segs mem (getr regs rs1) 4%nat = true ->
  let regs1 := if bv_eqb rd 0 then regs else regupd regs rd (SX2S.load_result SZ4 true bs) in
  getr regs1 rs1 = getr regs rs1 ->
  c_eq (getr regs1 rd) (getr regs1 rt) = true ->
  CatSim.msteps segs (mkst regs pc mem rom)
    (mkst (if bv_eqb rd2 0 then regs1 else regupd regs1 rd2 (Z_to_bv 64 0))
          (v_addi (v_addi (v_addi pc 4) 4) 4)
          (wbytes mem (getr regs rs1) (word_to_le_bytes 4 (getr regs1 rs2))) rom).
Proof.
  intros segs regs pc mem rom w0 w1 w2 aq rl aq' rl' rd rt rd2 rs1 rs2 imm1 bs
         F0 E0 D0 F1 E1 D1 F2 E2 D2 Hal Hread Hok regs1 Hrs1 Heq.
  pose proof (rdn_length _ _ _ _ _ Hread) as Hlen.
  assert (Hv : bytes_le_to_Z bs = bv_unsigned (le_bytes_to_word bs)).
  { unfold le_bytes_to_word. rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small.
    pose proof (SX2S.bytes_le_to_Z_bound bs) as Hb. rewrite Hlen in Hb. cbn in Hb. unfold bv_modulus. cbn. lia. }
  assert (Hr1 : regs1 = (if bv_eqb rd 0 then regs else regupd regs rd (v_lw (le_bytes_to_word bs)))).
  { subst regs1. rewrite <- b_lw_val. reflexivity. }
  eapply CatSim.mst_step; [reflexivity | eapply (step_lr_w segs regs pc mem rom w0 aq rl rd rs1 bs); eassumption |].
  rewrite <- Hr1.
  eapply CatSim.mst_step; [reflexivity | eapply (step_bne_ft_r segs regs1); eassumption |].
  rewrite <- Hrs1.
  eapply CatSim.mst_step; [reflexivity | eapply (step_sc_w_ok segs regs1); try eassumption |].
  - rewrite Hrs1. exact Hal.
  - reflexivity.
  - rewrite Hrs1. exact Hok.
  - apply CatSim.mst_refl.
Qed.
End CAS.
