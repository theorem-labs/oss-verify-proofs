(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgB.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec MmapSim StepTac Hoare RefReadLib RefEnframeArith.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import  BothRegionPoisoned AsanNodesRP.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import Both_code_54000_55000.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast WalkLean.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac Lia.lia ::= lia_fast.
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := ImgB.M.loaded_segments.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
Ltac krem := lazymatch goal with |- msteps _ (mkst (regupd _ _ ?v) _ _ _) _ => let X := fresh "X" in set (X := v) | |- _ => idtac end.

Import AsanNodesRP.RPN.
(* [comment removed for export] *)

Section FPW_1. Context {fx : PropExec.FPState}.

Section MSB.
  Variables (mem rom : word -> option byte) (s1 wz : Z) (bs : list byte).
  Hypothesis Hs1 : (0 <= s1)%Z /\ (s1 + 48 + 8 < 2 ^ 64)%Z.
  Hypothesis Hrd : rdn SEGS mem (Z_to_bv 64 (s1 + 48)) 8 = Some bs.
  Hypothesis Hbs : bytes_le_to_Z bs = wz.
  Hypothesis Hwz : (0 <= wz < 2 ^ 64)%Z.

  (* [comment removed for export] *)
  #[using="bs Hs1 Hrd Hbs Hwz"] Lemma as_msb_walk : forall regs,
    getr regs 9 = Z_to_bv 64 s1 ->
    let r18_0 := getr regs 18 in
    let w := Z_to_bv 64 wz in
    let r11_1 := v_srli r18_0 1 in
    let r12_1 := v_lui 1431654400 in
    let r14_1 := v_lui 858992640 in
    let r15_1 := v_lui 252645376 in
    let r11_2 := v_or r18_0 r11_1 in
    let r12_2 := v_addiw r12_1 (1365) in
    let r14_2 := v_addiw r14_1 (819) in
    let r15_2 := v_addiw r15_1 (-241) in
    let r16_1 := v_srli r11_2 2 in
    let r11_3 := v_or r11_2 r16_1 in
    let r16_2 := v_slli r12_2 32 in
    let r12_3 := v_add r12_2 r16_2 in
    let r16_3 := v_slli r14_2 32 in
    let r14_3 := v_add r14_2 r16_3 in
    let r16_4 := v_slli r15_2 32 in
    let r15_3 := v_add r15_2 r16_4 in
    let r16_5 := v_srli r11_3 4 in
    let r11_4 := v_or r11_3 r16_5 in
    let r16_6 := v_srli r11_4 8 in
    let r11_5 := v_or r11_4 r16_6 in
    let r16_7 := v_srli r11_5 16 in
    let r11_6 := v_or r11_5 r16_7 in
    let r16_8 := v_srli r11_6 32 in
    let r11_7 := v_or r11_6 r16_8 in
    let r11_8 := v_xori r11_7 (-1) in
    let r16_9 := v_srli r11_8 1 in
    let r12_4 := v_and r16_9 r12_3 in
    let r16_10 := v_lui 16842752 in
    let r11_9 := v_sub r11_8 r12_4 in
    let r12_5 := v_srli r11_9 2 in
    let r11_10 := v_and r11_9 r14_3 in
    let r12_6 := v_and r12_5 r14_3 in
    let r14_4 := w in
    let r16_11 := v_addiw r16_10 (257) in
    let r11_11 := v_add r11_10 r12_6 in
    let r12_7 := v_srli r11_11 4 in
    let r11_12 := v_add r11_11 r12_7 in
    let r12_8 := v_slli r16_11 32 in
    let r11_13 := v_and r11_12 r15_3 in
    let r12_9 := v_add r16_11 r12_8 in
    let r11_14 := v_mul r11_13 r12_9 in
    let r19_1 := v_srli r11_14 56 in
    msteps SEGS (mkst regs (0x54a28 : word) mem rom)
                (mkst (rf_apply [(11, r11_14); (12, r12_9); (14, r14_4); (15, r15_3); (16, r16_11); (19, r19_1)] regs) (0x54ad0 : word) mem rom).
  Proof.
    intros regs H9. intros. destruct Hs1 as [Hs1a Hs1b].
    wl_begin.
    wl_step ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_54a28 eq_refl D_54a28)).   (* [comment removed for export] *)
    wl_step ltac:(exact (step_lui _ _ _ _ _ _ _ _ F_54a2c eq_refl D_54a2c)).   (* [comment removed for export] *)
    wl_step ltac:(exact (step_lui _ _ _ _ _ _ _ _ F_54a30 eq_refl D_54a30)).   (* [comment removed for export] *)
    wl_step ltac:(exact (step_lui _ _ _ _ _ _ _ _ F_54a34 eq_refl D_54a34)).   (* [comment removed for export] *)
    wl_step ltac:(exact (step_or _ _ _ _ _ _ _ _ _ F_54a38 eq_refl D_54a38)).   (* [comment removed for export] *)
    wl_step ltac:(exact (step_addiw _ _ _ _ _ _ _ _ _ F_54a3c eq_refl D_54a3c)).   (* [comment removed for export] *)
    wl_step ltac:(exact (step_addiw _ _ _ _ _ _ _ _ _ F_54a40 eq_refl D_54a40)).   (* [comment removed for export] *)
    wl_step ltac:(exact (step_addiw _ _ _ _ _ _ _ _ _ F_54a44 eq_refl D_54a44)).   (* [comment removed for export] *)
    wl_step ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_54a48 eq_refl D_54a48)).   (* [comment removed for export] *)
    wl_step ltac:(exact (step_or _ _ _ _ _ _ _ _ _ F_54a4c eq_refl D_54a4c)).   (* [comment removed for export] *)
    wl_step ltac:(exact (step_slli _ _ _ _ _ _ _ _ _ F_54a50 eq_refl D_54a50)).   (* [comment removed for export] *)
    wl_step ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_54a54 eq_refl D_54a54)).   (* [comment removed for export] *)
    wl_step ltac:(exact (step_slli _ _ _ _ _ _ _ _ _ F_54a58 eq_refl D_54a58)).   (* [comment removed for export] *)
    wl_step ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_54a5c eq_refl D_54a5c)).   (* [comment removed for export] *)
    wl_step ltac:(exact (step_slli _ _ _ _ _ _ _ _ _ F_54a60 eq_refl D_54a60)).   (* [comment removed for export] *)
    wl_step ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_54a64 eq_refl D_54a64)).   (* [comment removed for export] *)
    wl_step ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_54a68 eq_refl D_54a68)).   (* [comment removed for export] *)
    wl_step ltac:(exact (step_or _ _ _ _ _ _ _ _ _ F_54a6c eq_refl D_54a6c)).   (* [comment removed for export] *)
    wl_step ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_54a70 eq_refl D_54a70)).   (* [comment removed for export] *)
    wl_step ltac:(exact (step_or _ _ _ _ _ _ _ _ _ F_54a74 eq_refl D_54a74)).   (* [comment removed for export] *)
    wl_step ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_54a78 eq_refl D_54a78)).   (* [comment removed for export] *)
    wl_step ltac:(exact (step_or _ _ _ _ _ _ _ _ _ F_54a7c eq_refl D_54a7c)).   (* [comment removed for export] *)
    wl_step ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_54a80 eq_refl D_54a80)).   (* [comment removed for export] *)
    wl_step ltac:(exact (step_or _ _ _ _ _ _ _ _ _ F_54a84 eq_refl D_54a84)).   (* [comment removed for export] *)
    wl_step ltac:(exact (step_xori _ _ _ _ _ _ _ _ _ F_54a88 eq_refl D_54a88)).   (* [comment removed for export] *)
    wl_step ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_54a8c eq_refl D_54a8c)).   (* [comment removed for export] *)
    wl_step ltac:(exact (step_and _ _ _ _ _ _ _ _ _ F_54a90 eq_refl D_54a90)).   (* [comment removed for export] *)
    wl_step ltac:(exact (step_lui _ _ _ _ _ _ _ _ F_54a94 eq_refl D_54a94)).   (* [comment removed for export] *)
    wl_step ltac:(exact (step_sub _ _ _ _ _ _ _ _ _ F_54a98 eq_refl D_54a98)).   (* [comment removed for export] *)
    wl_step ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_54a9c eq_refl D_54a9c)).   (* [comment removed for export] *)
    wl_step ltac:(exact (step_and _ _ _ _ _ _ _ _ _ F_54aa0 eq_refl D_54aa0)).   (* [comment removed for export] *)
    wl_step ltac:(exact (step_and _ _ _ _ _ _ _ _ _ F_54aa4 eq_refl D_54aa4)).   (* [comment removed for export] *)
    wl_step ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 wz) F_54aa8 eq_refl D_54aa8);
                   [ wl_getr; rewrite H9; imm_norm; zn; exact Hrd | rewrite zbv_u by lia; exact Hbs ]).
    wl_step ltac:(exact (step_addiw _ _ _ _ _ _ _ _ _ F_54aac eq_refl D_54aac)).   (* [comment removed for export] *)
    wl_step ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_54ab0 eq_refl D_54ab0)).   (* [comment removed for export] *)
    wl_step ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_54ab4 eq_refl D_54ab4)).   (* [comment removed for export] *)
    wl_step ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_54ab8 eq_refl D_54ab8)).   (* [comment removed for export] *)
    wl_step ltac:(exact (step_slli _ _ _ _ _ _ _ _ _ F_54abc eq_refl D_54abc)).   (* [comment removed for export] *)
    wl_step ltac:(exact (step_and _ _ _ _ _ _ _ _ _ F_54ac0 eq_refl D_54ac0)).   (* [comment removed for export] *)
    wl_step ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_54ac4 eq_refl D_54ac4)).   (* [comment removed for export] *)
    wl_step ltac:(exact (step_mul _ _ _ _ _ _ _ _ _ F_54ac8 eq_refl D_54ac8)).   (* [comment removed for export] *)
    wl_step ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_54acc eq_refl D_54acc)).   (* [comment removed for export] *)
    wl_end.
  Qed.

  #[using="bs Hs1 Hrd Hbs Hwz"] Theorem as_msb_block : forall regs,
    getr regs 9 = Z_to_bv 64 s1 ->
    exists regs',
      msteps SEGS (mkst regs (0x54a28 : word) mem rom) (mkst regs' (0x54ad0 : word) mem rom)
      /\ (let '(v11, v12, v15, v16, v19) := msb_regs (getr regs 18) (Z_to_bv 64 wz) in
          getr regs' 11 = v11 /\ getr regs' 12 = v12 /\ getr regs' 15 = v15 /\ getr regs' 16 = v16 /\ getr regs' 19 = v19)
      /\ getr regs' 14 = Z_to_bv 64 wz
      /\ (forall r, r <> 11 -> r <> 12 -> r <> 14 -> r <> 15 -> r <> 16 -> r <> 19 -> getr regs' r = getr regs r).
  Proof.
    intros regs H9.
    exists (let '(v11, v12, v15, v16, v19) := msb_regs (getr regs 18) (Z_to_bv 64 wz) in
            rf_apply [(11, v11); (12, v12); (14, Z_to_bv 64 wz); (15, v15); (16, v16); (19, v19)] regs).
    split; [exact (as_msb_walk regs H9)|].
    destruct (msb_regs (getr regs 18) (Z_to_bv 64 wz)) as [[[[v11 v12] v15] v16] v19].
    split; [|split].
    - repeat split; apply rf_get_ok'; reflexivity.
    - apply rf_get_ok'; reflexivity.
    - intros r N11 N12 N14 N15 N16 N19. apply rf_frame. cbn [rf_notin]. tauto.
  Qed.
End MSB.
End FPW_1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FPW_2. Context {fx : PropExec.FPState}.


Section LS.
  Variables (mem rom : word -> option byte) (s1 idx : Z).
  Hypothesis Hs1 : (0 <= s1)%Z /\ (s1 + 616 < 2 ^ 64)%Z.
  Hypothesis Hidx : (0 <= idx <= 63)%Z.
  Hypothesis Hwr : forall j, (0 <= j < 520)%Z -> store_ok SEGS mem (Z_to_bv 64 (s1 + 96 + j)) 1 = true.
  Hypothesis Hrd8 : forall a, (s1 + 96 <= a)%Z -> (a + 8 <= s1 + 616)%Z -> exists bs, rdn SEGS mem (Z_to_bv 64 a) 8 = Some bs /\ length bs = 8%nat.

  #[using="Hs1 Hidx Hwr Hrd8"] Theorem as_ls_block : forall regs,
    getr regs 9 = Z_to_bv 64 s1 -> getr regs 11 = Z_to_bv 64 idx ->
    exists regs' mem',
      msteps SEGS (mkst regs (0x54b14 : word) mem rom) (mkst regs' (0x54b34 : word) mem' rom)
      /\ (forall r, r <> 11 -> r <> 12 -> r <> 13 -> getr regs' r = getr regs r)
      /\ (exists (v1 v2 : word), mem' = wbytes (wbytes mem (Z_to_bv 64 (s1 + 96)) (word_to_le_bytes 8 v1))
                                              (Z_to_bv 64 (s1 + 104 + 8 * idx)) (word_to_le_bytes 8 v2)).
  Proof.
    intros regs H9 H11. destruct Hs1 as [Hs1a Hs1b].
    (* [comment removed for export] *)
    assert (ST8 : forall a, (s1 + 96 <= a)%Z -> (a + 8 <= s1 + 616)%Z -> store_ok SEGS mem (Z_to_bv 64 a) 8 = true).
    { intros a Ha1 Ha2. apply store_ok8_bytes; [lia|lia|]. intros j Hj.
      replace (a + j)%Z with (s1 + 96 + (a - s1 - 96 + j))%Z by lia. apply Hwr. lia. }
    destruct (Hrd8 (s1 + 104 + 8 * idx)%Z ltac:(lia) ltac:(lia)) as (bs & Hrd & Hlen).
    pose proof (bytes_le_to_Z_bound bs) as Hbsb. rewrite Hlen in Hbsb. pose proof (bytes_le_to_Z_nonneg bs) as Hbs0.
    set (ld := bytes_le_to_Z bs) in *.
    (* [comment removed for export] *)
    assert (DIA : exists (v1 : word) regs1,
              msteps SEGS (mkst regs (0x54b14 : word) mem rom) (mkst regs1 (0x54b1c : word) mem rom)
              /\ getr regs1 12 = v1 /\ (forall r, r <> 12 -> getr regs1 r = getr regs r)).
    { destruct (c_ltu (getr regs 13) (getr regs 12)) eqn:Hc.
      - exists (getr regs 12), regs. split; [|split; [reflexivity | intros; reflexivity]].
        eapply mst_step; [reflexivity | eapply (step_bltu_tk _ _ _ _ _ _ _ _ _ F_54b14 eq_refl D_54b14); exact Hc |].
        step_simpl. imm_norm. apply mst_refl.
      - eexists _, _. split.
        + mstep ltac:(eapply (step_bltu_ft _ _ _ _ _ _ _ _ _ F_54b14 eq_refl D_54b14); exact Hc).
          mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_54b18 eq_refl D_54b18)).
          apply mst_refl.
        + split; [gr; reflexivity|]. intros r N12. rewrite getr_other by (intros ->; contradiction). reflexivity. }
    destruct DIA as (v1 & regs1 & M1 & R12 & Roth).
    assert (H9' : getr regs1 9 = Z_to_bv 64 s1) by (rewrite Roth by (intros E; discriminate E); exact H9).
    assert (H11' : getr regs1 11 = Z_to_bv 64 idx) by (rewrite Roth by (intros E; discriminate E); exact H11).
    eexists _, _. split; [|split].
    - eapply msteps_trans; [exact M1|].
      (* [comment removed for export] *)
      mstep ltac:(exact (step_slli _ _ _ _ _ _ _ _ _ F_54b1c eq_refl D_54b1c)). gr. rewrite H11', v_slli_lit by lia.
      change (2 ^ 3)%Z with 8%Z.
      mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_54b20 eq_refl D_54b20)). gr. rewrite H9', v_add_zbv by lia. replace (s1 + idx * 8)%Z with (s1 + 8 * idx)%Z by lia.
      (* [comment removed for export] *)
      mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ld) F_54b24 eq_refl D_54b24);
                   [ gr; imm_norm; zn; replace (s1 + 8 * idx + 104)%Z with (s1 + 104 + 8 * idx)%Z by lia; exact Hrd
                   | rewrite zbv_u by lia; reflexivity ]).
      (* [comment removed for export] *)
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_54b28 eq_refl D_54b28)). gr.
      (* [comment removed for export] *)
      mstep ltac:(eapply (step_sd_at _ _ _ _ _ _ _ _ _ _ _ F_54b2c eq_refl D_54b2c);
                   [ gr; rewrite H9'; imm_norm; zn; reflexivity | gr; exact R12 | apply ST8; lia ]).
      (* [comment removed for export] *)
      mstep ltac:(eapply (step_sd_at _ _ _ _ _ _ _ _ _ _ _ F_54b30 eq_refl D_54b30);
                   [ gr; imm_norm; zn; replace (s1 + 8 * idx + 104)%Z with (s1 + 104 + 8 * idx)%Z by lia; reflexivity | gr; reflexivity | ]).
      { apply store_ok8_bytes; [lia|lia|]. intros j Hj. apply store_ok1_wbytes.
        replace (s1 + 104 + 8 * idx + j)%Z with (s1 + 96 + (8 + 8 * idx + j))%Z by lia. apply Hwr. lia. }
      apply mst_refl.
    - intros r N11 N12 N13. repeat (rewrite getr_other by (intros ->; first [contradiction | congruence])).
      apply Roth. exact N12.
    - eexists _, _. reflexivity.
  Qed.
End LS.
End FPW_2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma msb_scan_spec : forall n m acc,
  (fst (msb_scan m n acc) <= fst acc)%Z /\ (snd acc <= snd (msb_scan m n acc))%Z
  /\ forall j, (0 <= j < Z.of_nat n)%Z -> (fst (msb_scan m n acc) <= msb_val (4096 * (m + j)) <= snd (msb_scan m n acc))%Z.
Proof.
  induction n as [|n IH]; intros m acc; cbn [msb_scan].
  - split; [lia|]. split; [lia|]. intros j Hj. lia.
  - destruct (IH (m + 1)%Z (Z.min (fst acc) (msb_val (4096 * m)), Z.max (snd acc) (msb_val (4096 * m)))) as (A & B & C).
    cbn [fst snd] in A, B. split; [lia|]. split; [lia|].
    intros j Hj. destruct (Z.eq_dec j 0) as [->|Hj0].
    + rewrite Z.add_0_r. lia.
    + specialize (C (j - 1)%Z ltac:(lia)). replace (m + 1 + (j - 1))%Z with (m + j)%Z in C by lia. exact C.
Qed.

Lemma msb_res_w : forall x w, msb_res x w = msb_res x (Z_to_bv 64 0).
Proof. intros. reflexivity. Qed.

Lemma msb_range_sound : forall lo hi cmin cmax (x : word),
  msb_range lo hi = Some (cmin, cmax) ->
  (lo <= bv_unsigned x <= hi)%Z -> (bv_unsigned x mod 4096 = 0)%Z ->
  forall w, (cmin <= bv_unsigned (msb_res x w) <= cmax)%Z.
Proof.
  intros lo hi cmin cmax x H Hx Hal w. unfold msb_range in H.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate H] end.
  apply andb_prop in Hc as [Hc Hcap]. apply andb_prop in Hc as [Hlo Hm]. apply Z.leb_le in Hlo. apply Z.leb_le in Hm. apply Z.leb_le in Hcap.
  set (m0 := ((lo + 4095) / 4096)%Z) in *. set (m1 := (hi / 4096)%Z) in *.
  injection H as E.
  replace cmin with (fst (msb_scan (m0 + 1) (Z.to_nat (m1 - m0)) (msb_val (4096 * m0), msb_val (4096 * m0)))) by (rewrite E; reflexivity).
  replace cmax with (snd (msb_scan (m0 + 1) (Z.to_nat (m1 - m0)) (msb_val (4096 * m0), msb_val (4096 * m0)))) by (rewrite E; reflexivity).
  clear E.
  rewrite (msb_res_w x w). pose proof (bv_unsigned_in_range _ x) as Ux. change (bv_modulus 64) with (2 ^ 64)%Z in Ux.
  assert (Hxe : x = Z_to_bv 64 (4096 * (bv_unsigned x / 4096))).
  { apply bv_eq. rewrite Z_to_bv_unsigned. pose proof (Z.div_mod (bv_unsigned x) 4096 ltac:(lia)).
    unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64)%Z. rewrite Z.mod_small; lia. }
  set (m := (bv_unsigned x / 4096)%Z) in *.
  assert (Hm01 : (m0 <= m <= m1)%Z).
  { subst m0 m1 m. split.
    - apply Z.div_le_lower_bound; [lia|]. pose proof (Z.div_mod (bv_unsigned x) 4096 ltac:(lia)).
      pose proof (Z.mul_div_le (lo + 4095) 4096 ltac:(lia)). nia.
    - apply Z.div_le_mono; lia. }
  replace (bv_unsigned (msb_res x (Z_to_bv 64 0))) with (msb_val (4096 * m)).
  2:{ unfold msb_val. rewrite <- Hxe. reflexivity. }
  destruct (msb_scan_spec (Z.to_nat (m1 - m0)) (m0 + 1)%Z (msb_val (4096 * m0), msb_val (4096 * m0))) as (A & B & C).
  cbn [fst snd] in A, B.
  destruct (Z.eq_dec m m0) as [->|Hne]; [lia|].
  specialize (C (m - m0 - 1)%Z ltac:(rewrite Z2Nat.id; lia)). replace (m0 + 1 + (m - m0 - 1))%Z with m in C by lia. exact C.
Qed.
