(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgB.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec MmapSim StepTac Hoare RefReadLib RefEnframeArith.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import Both_code_62000_63000 BothRegionPoisoned.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := ImgB.M.loaded_segments.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Section FPW_1. Context {fx : PropExec.FPState}.

Lemma rdn_zeros : forall k m a,
  (forall j, (0 <= j < Z.of_nat k)%Z -> m (Z_to_bv 64 (a + j)) = Some (Z_to_bv 8 0)) ->
  rdn SEGS m (Z_to_bv 64 a) k = Some (repeat (Z_to_bv 8 0) k).
Proof.
  induction k as [|k IH]; intros m a Hz; [reflexivity|].
  cbn [rdn repeat]. rewrite <- (Z.add_0_r a) at 1. rewrite (Hz 0%Z) by lia.
  rewrite zbv_add1, (IH m (a + 1)%Z); [reflexivity|].
  intros j Hj. rewrite <- Z.add_assoc. apply Hz. lia.
Qed.
Lemma bytes_le_to_Z_zeros : forall k, bytes_le_to_Z (repeat (Z_to_bv 8 0) k) = 0%Z.
Proof. induction k as [|k IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma zbv_mod : forall z, Z_to_bv 64 (z + 2 ^ 64) = Z_to_bv 64 z.
Proof.
  intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64)%Z.
  replace (z + 2 ^ 64)%Z with (z + 1 * 2 ^ 64)%Z by lia. apply Z.mod_add. lia.
Qed.

Definition RC_ENTRY : Z := 0x62cc8.
Definition RC_EXIT : Z := 0x62d20.

Section RC.
  Variables (mem rom : word -> option byte) (buf res : Z).
  Hypothesis Hres : (1 <= res <= 64)%Z.
  Hypothesis Hbuf : (0 <= buf)%Z.
  Hypothesis Hbuf64 : (buf + 64 < 2 ^ 64)%Z.
  Hypothesis C1 : cell mem 0x12a380 0x132738.
  Hypothesis C2 : cell mem 0x132738 SB.
  (* [comment removed for export] *)
  Definition h0 : Z := ((SB + buf / 8) / 8 * 8)%Z.
  Hypothesis Hz : forall j, (0 <= j < 16)%Z -> mem (Z_to_bv 64 (h0 + j)) = Some (Z_to_bv 8 0).

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  Lemma rc_arith :
    let s1 := (SB + buf / 8)%Z in
    let s2 := (SB + (buf + res - 1) / 8)%Z in
    (0 <= s1)%Z /\ (s2 + 8 < 2 ^ 64)%Z /\ (s1 <= s2 <= s1 + 8)%Z
    /\ (h0 <= s1 < h0 + 8)%Z /\ (h0 <= s2 / 8 * 8)%Z /\ (s2 / 8 * 8 + 8 <= h0 + 16)%Z /\ (0 <= h0)%Z
    /\ (0 <= buf + res - 1 < 2 ^ 64)%Z /\ (0 <= (buf + res - 1) / 8 < 2 ^ 64)%Z /\ (0 <= buf / 8 < 2 ^ 64)%Z.
  Proof. pose proof SB_val. unfold h0. cbn zeta. unfold SB. lia. Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

  Lemma rd_h : forall a, (h0 <= a)%Z -> (a + 8 <= h0 + 16)%Z ->
    rdn SEGS mem (Z_to_bv 64 a) 8 = Some (repeat (Z_to_bv 8 0) 8).
  Proof.
    intros a H1 H2. apply rdn_zeros. intros j Hj.
    replace (a + j)%Z with (h0 + (a - h0 + j))%Z by lia. apply Hz. cbn in Hj. lia.
  Qed.

  Theorem as_read_check : forall regs,
    getr regs 9 = Z_to_bv 64 buf -> getr regs 10 = Z_to_bv 64 res ->
    exists regs',
      msteps SEGS (mkst regs (0x62cc8 : word) mem rom) (mkst regs' (0x62d20 : word) mem rom)
      /\ getr regs' 11 = Z_to_bv 64 (SB + buf / 8)
      /\ getr regs' 12 = Z_to_bv 64 (SB + (buf + res - 1) / 8)
      /\ getr regs' 13 = Z_to_bv 64 (buf + res - 1)
      /\ getr regs' 14 = Z_to_bv 64 0 /\ getr regs' 15 = Z_to_bv 64 0
      /\ getr regs' 20 = v_addi (v_addi (getr regs 8) (-2048)) (-72)
      /\ (forall r, r <> 11 -> r <> 12 -> r <> 13 -> r <> 14 -> r <> 15 -> r <> 20 -> getr regs' r = getr regs r).
  Proof.
    intros regs H9 H10. pose proof SB_val as HSB.
    pose proof rc_arith as RA. cbn zeta in RA. unfold h0 in RA. destruct RA as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
    pose proof (rd_h ((SB + buf / 8) / 8 * 8)%Z ltac:(unfold h0; lia) ltac:(unfold h0; lia)) as RD1.
    pose proof (rd_h ((SB + (buf + res - 1) / 8) / 8 * 8)%Z A5 A6) as RD2.
    eexists. split.
    - (* [comment removed for export] *)
      mstep ltac:(exact (step_xori _ _ _ _ _ _ _ _ _ F_62cc8 eq_refl D_62cc8)). gr. rewrite H9, v_not_lit by lia.
      (* [comment removed for export] *)
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_62ccc eq_refl D_62ccc)). gr.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_62cd0 eq_refl D_62cd0)). gr.
      (* [comment removed for export] *)
      mstep ltac:(eapply (step_bltu_ft _ _ _ _ _ _ _ _ _ F_62cd4 eq_refl D_62cd4); gr; rewrite ?H10; br_lt).
      (* [comment removed for export] *)
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_62cd8 eq_refl D_62cd8)). gr. rewrite H10. zn.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_62cdc eq_refl D_62cdc)). gr. rewrite getr_zero. zn.
      rewrite <- (zbv_mod (res + -65)), <- (zbv_mod (0 + -64)).
      mstep ltac:(eapply (step_bltu_ft _ _ _ _ _ _ _ _ _ F_62ce0 eq_refl D_62ce0); gr; br_lt).
      (* [comment removed for export] *)
      mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0x129ce4) F_62ce4 eq_refl D_62ce4);
                   [reflexivity | apply bv_eq; vm_compute; reflexivity]).
      mld F_62ce8 D_62ce8 0x132738%Z C1 H9.
      (* [comment removed for export] *)
      mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_62cec eq_refl D_62cec)). gr. rewrite H9, H10, v_add_zbv by lia.
      (* [comment removed for export] *)
      mld F_62cf0 D_62cf0 SB C2 H9.
      (* [comment removed for export] *)
      mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_62cf4 eq_refl D_62cf4)). gr. rewrite H9, (v_srli_3 buf) by lia.
      (* [comment removed for export] *)
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_62cf8 eq_refl D_62cf8)). gr. zn.
      (* [comment removed for export] *)
      mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_62cfc eq_refl D_62cfc)). gr.
      replace (buf + res + -1)%Z with (buf + res - 1)%Z by lia. rewrite (v_srli_3 (buf + res - 1)) by lia.
      (* [comment removed for export] *)
      mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_62d00 eq_refl D_62d00)). gr. rewrite v_add_zbv by lia.
      mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_62d04 eq_refl D_62d04)). gr. rewrite v_add_zbv by lia.
      (* [comment removed for export] *)
      mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_62d08 eq_refl D_62d08)). gr. rewrite v_andi_m8 by lia.
      mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_62d0c eq_refl D_62d0c)). gr. rewrite v_andi_m8 by lia.
      (* [comment removed for export] *)
      mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 0) F_62d10 eq_refl D_62d10);
                   [ gr; zn; rewrite Z.add_0_r; exact RD1 | rewrite bytes_le_to_Z_zeros; reflexivity ]).
      mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 0) F_62d14 eq_refl D_62d14);
                   [ gr; zn; rewrite Z.add_0_r; exact RD2 | rewrite bytes_le_to_Z_zeros; reflexivity ]).
      (* [comment removed for export] *)
      mstep ltac:(exact (step_or _ _ _ _ _ _ _ _ _ F_62d18 eq_refl D_62d18)). gr. rewrite v_or_zero.
      eapply mst_step; [reflexivity | eapply (step_bne_ft _ _ _ _ _ _ _ _ _ F_62d1c eq_refl D_62d1c); gr; rewrite getr_zero; reflexivity |].
      step_simpl. imm_norm. apply mst_refl.
    - gr. repeat split; try reflexivity.
      intros r N11 N12 N13 N14 N15 N20.
      repeat (rewrite getr_other by (intros ->; first [contradiction | congruence])). reflexivity.
  Qed.
End RC.

End FPW_1.
