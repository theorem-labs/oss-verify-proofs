(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import Asan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec MmapSim StepTac Hoare RefEnframeArith.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import Asan_code_pg Asan_code_cpm AsanRegionPoisoned AsanReadCheck.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import RefReadLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastV.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastVK.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastVS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.gres ::= gres_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.vnorm ::= vnorm_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StepTac.step_simpl ::= step_simpl_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.RefMemcpyLib.not_kept ::= not_kept_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StartupTac.in_list ::= in_list_fast.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AsanWalkFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan.AsanRegionPoisoned.gr ::= gr_fast.
(* [comment removed for export] *)
#[local] Existing Instance PropExec.fx0.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := Asan.M.loaded_segments.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition PG_ENTRY : Z := 0x33e2c.
Definition PG_EXIT : Z := 0x33ec0.

(* [comment removed for export] *)
Lemma step_fence : forall segs regs pc mem rom w a b c d e,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fence a b c d e, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) = MachineOk (mkst regs (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w a b c d e Hfetch Hecall Hdecode.
  step_pipeline Hfetch Hecall Hdecode. rewrite ?b_npc4. reflexivity.
Qed.

Lemma v_subw_0_1 : v_subw (Z_to_bv 64 0) (Z_to_bv 64 1) = Z_to_bv 64 (2 ^ 64 - 1).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma v_and_m1 : forall z, (0 <= z < 2 ^ 64)%Z -> v_and (Z_to_bv 64 z) (Z_to_bv 64 (2 ^ 64 - 1)) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold v_and. rewrite !zbv_u by lia. change (2 ^ 64 - 1)%Z with (Z.ones 64).
  rewrite Z.land_ones by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma v_lb_1 : v_lb (Z_to_bv 8 1) = Z_to_bv 64 1.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma v_sltu_0_1 : v_sltu (Z_to_bv 64 0) (Z_to_bv 64 1) = Z_to_bv 64 1.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma ret_33d18 : v_jalr (v_addi (0x33e30 : word) 4) (bv_signed (0 : bv 12)) = (0x33e34 : word).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Section PG.
  Variables (mem rom : word -> option byte) (p n : Z).
  Definition q : Z := (n / 8)%Z.
  Definition r : Z := (n mod 8)%Z.
  Definition sa : Z := (SB + p / 8 + q)%Z.        (* [comment removed for export] *)
  Hypothesis Hp : (0 <= p)%Z.
  Hypothesis Hp8 : (p mod 8 = 0)%Z.
  Hypothesis Hn : (1 <= n)%Z.
  Hypothesis Hrng : (p + n <= kLowEnd)%Z \/ ((kHighBeg <= p)%Z /\ (p + n <= kHighEnd)%Z).   (* [comment removed for export] *)
  Hypothesis Hcells : cells mem.
  Hypothesis Cfl : cell mem 0xaae78 0xb0df8.
  Hypothesis Cpp : rdn SEGS mem (Z_to_bv 64 0xb0e4d) 1 = Some [Z_to_bv 8 1].    (* [comment removed for export] *)
  Hypothesis Ccp : rdn SEGS mem (Z_to_bv 64 0xb2e5c) 1 = Some [Z_to_bv 8 1].    (* [comment removed for export] *)
  Hypothesis Hst : store_ok SEGS mem (Z_to_bv 64 sa) 1 = true.

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  #[using="Hp Hp8 Hn Hrng"] Lemma pg_arith :
    (0 <= q)%Z /\ (8 * q <= n)%Z /\ (n < 8 * q + 8)%Z /\ (0 <= r < 8)%Z /\ (n = 8 * q + r)%Z
    /\ ((p + 8 * q) / 8 = p / 8 + q)%Z /\ (0 <= p / 8)%Z /\ (p + 8 * q < 2 ^ 47)%Z /\ (0 <= p / 8 + q /\ SB + (p / 8 + q) < 2 ^ 62)%Z
    /\ (0 <= 8 * q < 2 ^ 64)%Z /\ (Z.land n 7 = r)%Z.
  Proof.
    pose proof SB_val. unfold sa in *. unfold q, r, kHighBeg, kHighEnd, kLowEnd, SB in *.
    assert (HRb : (p + n <= 140737488355327)%Z) by (destruct Hrng as [HR|[HR1 HR2]]; lia).
    assert (Z.land n 7 = n mod 8)%Z by (change 7%Z with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity).
    lia.
  Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

  Definition pg_clob (x : reg) : bool :=
    (bv_eqb x 1 || bv_eqb x 10 || bv_eqb x 11 || bv_eqb x 12 || bv_eqb x 13 || bv_eqb x 14 || bv_eqb x 15
     || bv_eqb x 16 || bv_eqb x 17 || bv_eqb x 22)%bool.

  Definition pg_mem : word -> option byte :=
    if (r =? 0)%Z then mem else wbytes mem (Z_to_bv 64 sa) (word_to_le_bytes 1 (Z_to_bv 64 r)).

  #[using="Hp Hp8 Hn Hrng Hcells Cfl Cpp Ccp Hst"] Theorem partial_granule_S : forall regs,
    getr regs 9 = Z_to_bv 64 n -> getr regs 22 = Z_to_bv 64 (8 * q) -> getr regs 20 = Z_to_bv 64 p ->
    exists regs',
      msteps SEGS (mkst regs (0x33e2c : word) mem rom) (mkst regs' (0x33ec0 : word) pg_mem rom)
      /\ (forall x, pg_clob x = false -> getr regs' x = getr regs x).
  Proof.
    intros regs H9 H22 H20. pose proof SB_val as HSB.
    pose proof pg_arith as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11).
    pose proof Hcells as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8).
    unfold pg_mem. destruct (Z.eqb_spec r 0) as [R0|R1].
    - (* [comment removed for export] *)
      exists regs. split; [|intros; reflexivity].
      mstep ltac:(eapply (step_beq_tk _ _ _ _ _ _ _ _ _ F_33e2c eq_refl D_33e2c); gr; rewrite ?H9, ?H22; br_eq).
      apply mst_refl.
    - destruct Hrng as [HRL | [HR1 HR2]].
      + eexists. split.
      *
        mstep ltac:(eapply (step_beq_ft _ _ _ _ _ _ _ _ _ F_33e2c eq_refl D_33e2c); gr; rewrite ?H9, ?H22; br_eq).
        (* [comment removed for export] *)
        mstep ltac:(exact (step_jal_link _ _ _ _ _ _ _ _ F_33e30 eq_refl D_33e30)).
        mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xb3010) F_56010 eq_refl D_56010);
                     [reflexivity | apply bv_eq; vm_compute; reflexivity]).
        mstep ltac:(eapply (@step_lb _ _ _ _ _ _ _ _ _ _ (Z_to_bv 8 1) F_56014 eq_refl D_56014); gr; imm_norm; zn; exact Ccp).
        rewrite v_lb_1.
        mstep ltac:(exact (step_fence _ _ _ _ _ _ _ _ _ _ _ F_56018 eq_refl D_56018)).
        mstep ltac:(exact (step_sltu _ _ _ _ _ _ _ _ _ F_5601c eq_refl D_5601c)). gr. rewrite getr_zero, v_sltu_0_1.
        eapply mst_step; [reflexivity | eapply (step_jalr_x0 _ _ _ _ _ _ _ _ (v_addi (0x33e30 : word) 4) F_56020 eq_refl D_56020); gr; reflexivity |].
        rewrite ret_33d18.
        mstep ltac:(eapply (step_beq_ft _ _ _ _ _ _ _ _ _ F_33e34 eq_refl D_33e34); gr; rewrite ?getr_zero; br_eq).
        (* [comment removed for export] *)
        mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xaae38) F_33e38 eq_refl D_33e38);
                     [reflexivity | apply bv_eq; vm_compute; reflexivity]).
        mld F_33e3c D_33e3c 0xb35f8%Z C1 H20.
        mld F_33e40 D_33e40 SB C2 H20.
        (* [comment removed for export] *)
        mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_33e44 eq_refl D_33e44)). gr. rewrite H20, H22, v_add_zbv by lia.
        (* [comment removed for export] *)
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_33e48 eq_refl D_33e48)). gr. zn.
        mstep ltac:(exact (step_sltu _ _ _ _ _ _ _ _ _ F_33e4c eq_refl D_33e4c)). gr.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_33e50 eq_refl D_33e50)). gr.
        mstep ltac:(exact (step_and _ _ _ _ _ _ _ _ _ F_33e54 eq_refl D_33e54)). gr.
        rewrite k_low_val. unfold kLowEnd.
        (* [comment removed for export] *)
        mstep ltac:(eapply (step_bgeu_tk _ _ _ _ _ _ _ _ _ F_33e58 eq_refl D_33e58); gr; unfold kLowEnd in HRL; br_lt).
        (* [comment removed for export] *)
          mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xaae9c) F_33e9c eq_refl D_33e9c);
                       [reflexivity | apply bv_eq; vm_compute; reflexivity]).
          mld F_33ea0 D_33ea0 0xb0df8%Z Cfl H20.
          mstep ltac:(eapply (@step_lbu _ _ _ _ _ _ _ _ _ _ (Z_to_bv 8 1) F_33ea4 eq_refl D_33ea4); gr; imm_norm; zn; exact Cpp).
          change (bv_unsigned (Z_to_bv 8 1)) with 1%Z.
          (* [comment removed for export] *)
          mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_33ea8 eq_refl D_33ea8)). gr. rewrite (v_srli_3 (p + 8 * q)) by lia.
          rewrite A6.
          mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_33eac eq_refl D_33eac)). gr. rewrite v_add_zbv by lia.
          (* [comment removed for export] *)
          mstep ltac:(exact (step_subw _ _ _ _ _ _ _ _ _ F_33eb0 eq_refl D_33eb0)). gr. rewrite getr_zero, v_subw_0_1.
          mstep ltac:(exact (step_and _ _ _ _ _ _ _ _ _ F_33eb4 eq_refl D_33eb4)). gr. rewrite H9, v_and_m1 by lia.
          mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_33eb8 eq_refl D_33eb8)). gr. rewrite v_andi_lit by lia. rewrite A11.
          (* [comment removed for export] *)
          replace (SB + (p / 8 + q))%Z with sa by (unfold sa; lia).
          assert (Hsa : (0 <= sa < 2 ^ 64)%Z) by (unfold sa; lia).
          eapply mst_step; [reflexivity | eapply (step_sb _ _ _ _ _ _ _ _ _ F_33ebc eq_refl D_33ebc); gr; imm_norm; zn;
                                          rewrite ?Z.add_0_r; exact Hst |].
          step_simpl. imm_norm. gr. zn. rewrite ?Z.add_0_r. apply mst_refl.
      * intros x Hx. unfold pg_clob in Hx.
        repeat (rewrite getr_other by (intros ->; cbn in Hx; discriminate)). reflexivity.
      + eexists. split.
      *
        mstep ltac:(eapply (step_beq_ft _ _ _ _ _ _ _ _ _ F_33e2c eq_refl D_33e2c); gr; rewrite ?H9, ?H22; br_eq).
        (* [comment removed for export] *)
        mstep ltac:(exact (step_jal_link _ _ _ _ _ _ _ _ F_33e30 eq_refl D_33e30)).
        mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xb3010) F_56010 eq_refl D_56010);
                     [reflexivity | apply bv_eq; vm_compute; reflexivity]).
        mstep ltac:(eapply (@step_lb _ _ _ _ _ _ _ _ _ _ (Z_to_bv 8 1) F_56014 eq_refl D_56014); gr; imm_norm; zn; exact Ccp).
        rewrite v_lb_1.
        mstep ltac:(exact (step_fence _ _ _ _ _ _ _ _ _ _ _ F_56018 eq_refl D_56018)).
        mstep ltac:(exact (step_sltu _ _ _ _ _ _ _ _ _ F_5601c eq_refl D_5601c)). gr. rewrite getr_zero, v_sltu_0_1.
        eapply mst_step; [reflexivity | eapply (step_jalr_x0 _ _ _ _ _ _ _ _ (v_addi (0x33e30 : word) 4) F_56020 eq_refl D_56020); gr; reflexivity |].
        rewrite ret_33d18.
        mstep ltac:(eapply (step_beq_ft _ _ _ _ _ _ _ _ _ F_33e34 eq_refl D_33e34); gr; rewrite ?getr_zero; br_eq).
        (* [comment removed for export] *)
        mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xaae38) F_33e38 eq_refl D_33e38);
                     [reflexivity | apply bv_eq; vm_compute; reflexivity]).
        mld F_33e3c D_33e3c 0xb35f8%Z C1 H20.
        mld F_33e40 D_33e40 SB C2 H20.
        (* [comment removed for export] *)
        mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_33e44 eq_refl D_33e44)). gr. rewrite H20, H22, v_add_zbv by lia.
        (* [comment removed for export] *)
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_33e48 eq_refl D_33e48)). gr. zn.
        mstep ltac:(exact (step_sltu _ _ _ _ _ _ _ _ _ F_33e4c eq_refl D_33e4c)). gr.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_33e50 eq_refl D_33e50)). gr.
        mstep ltac:(exact (step_and _ _ _ _ _ _ _ _ _ F_33e54 eq_refl D_33e54)). gr.
        rewrite k_low_val. unfold kLowEnd.
        unfold kHighBeg, kHighEnd in HR1, HR2.
        mstep ltac:(eapply (step_bgeu_ft _ _ _ _ _ _ _ _ _ F_33e58 eq_refl D_33e58); gr; br_lt).
        (* [comment removed for export] *)
        mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xaae5c) F_33e5c eq_refl D_33e5c);
                     [reflexivity | apply bv_eq; vm_compute; reflexivity]).
        mld F_33e60 D_33e60 0xb42e8%Z C3 H20.
        mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xaae64) F_33e64 eq_refl D_33e64);
                     [reflexivity | apply bv_eq; vm_compute; reflexivity]).
        mld F_33e68 D_33e68 0xb42f0%Z C5 H20.
        mld F_33e6c D_33e6c 0%Z C4 H20.
        mld F_33e70 D_33e70 0%Z C6 H20.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_33e74 eq_refl D_33e74)). gr. rewrite k_m1_val.
        mstep ltac:(eapply (step_bgeu_tk _ _ _ _ _ _ _ _ _ F_33e78 eq_refl D_33e78); gr; br_lt).
        (* [comment removed for export] *)
        mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xaae80) F_33e80 eq_refl D_33e80);
                     [reflexivity | apply bv_eq; vm_compute; reflexivity]).
        mld F_33e84 D_33e84 0xb42e0%Z C7 H20.
        mld F_33e88 D_33e88 kHighEnd C8 H20.
        mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_33e8c eq_refl D_33e8c)). gr.
        mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_33e90 eq_refl D_33e90)). gr. rewrite k_hse_val. unfold kHighBeg.
        replace (17594333495296 - 1)%Z with 17594333495295%Z by reflexivity.
        mstep ltac:(eapply (step_bltu_ft _ _ _ _ _ _ _ _ _ F_33e94 eq_refl D_33e94); gr; unfold kHighEnd; br_lt).
        mstep ltac:(eapply (step_bgeu_ft _ _ _ _ _ _ _ _ _ F_33e98 eq_refl D_33e98); gr; br_lt).
        (* [comment removed for export] *)
        mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xaae9c) F_33e9c eq_refl D_33e9c);
                     [reflexivity | apply bv_eq; vm_compute; reflexivity]).
        mld F_33ea0 D_33ea0 0xb0df8%Z Cfl H20.
        mstep ltac:(eapply (@step_lbu _ _ _ _ _ _ _ _ _ _ (Z_to_bv 8 1) F_33ea4 eq_refl D_33ea4); gr; imm_norm; zn; exact Cpp).
        change (bv_unsigned (Z_to_bv 8 1)) with 1%Z.
        (* [comment removed for export] *)
        mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_33ea8 eq_refl D_33ea8)). gr. rewrite (v_srli_3 (p + 8 * q)) by lia.
        rewrite A6.
        mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_33eac eq_refl D_33eac)). gr. rewrite v_add_zbv by lia.
        (* [comment removed for export] *)
        mstep ltac:(exact (step_subw _ _ _ _ _ _ _ _ _ F_33eb0 eq_refl D_33eb0)). gr. rewrite getr_zero, v_subw_0_1.
        mstep ltac:(exact (step_and _ _ _ _ _ _ _ _ _ F_33eb4 eq_refl D_33eb4)). gr. rewrite H9, v_and_m1 by lia.
        mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_33eb8 eq_refl D_33eb8)). gr. rewrite v_andi_lit by lia. rewrite A11.
        (* [comment removed for export] *)
        replace (SB + (p / 8 + q))%Z with sa by (unfold sa; lia).
        assert (Hsa : (0 <= sa < 2 ^ 64)%Z) by (unfold sa; lia).
        eapply mst_step; [reflexivity | eapply (step_sb _ _ _ _ _ _ _ _ _ F_33ebc eq_refl D_33ebc); gr; imm_norm; zn;
                                        rewrite ?Z.add_0_r; exact Hst |].
        step_simpl. imm_norm. gr. zn. rewrite ?Z.add_0_r. apply mst_refl.
      * intros x Hx. unfold pg_clob in Hx.
        repeat (rewrite getr_other by (intros ->; cbn in Hx; discriminate)). reflexivity.
  Qed.
End PG.

(* [comment removed for export] *)
Theorem partial_granule :
  forall (mem rom : word -> option byte) (p n : Z),
  (0 <= p)%Z -> (p mod 8 = 0)%Z -> (1 <= n)%Z -> (p + n <= kLowEnd)%Z \/ ((kHighBeg <= p)%Z /\ (p + n <= kHighEnd)%Z) ->
  cells mem -> cell mem 0xaae78 0xb0df8 ->
  rdn SEGS mem (Z_to_bv 64 0xb0e4d) 1 = Some [Z_to_bv 8 1] ->
  rdn SEGS mem (Z_to_bv 64 0xb2e5c) 1 = Some [Z_to_bv 8 1] ->
  store_ok SEGS mem (Z_to_bv 64 (SB + p / 8 + n / 8)) 1 = true ->
  forall regs, getr regs 9 = Z_to_bv 64 n -> getr regs 22 = Z_to_bv 64 (8 * (n / 8)) -> getr regs 20 = Z_to_bv 64 p ->
  exists regs',
    msteps SEGS (mkst regs (0x33e2c : word) mem rom)
                (mkst regs' (0x33ec0 : word)
                      (if (n mod 8 =? 0)%Z then mem
                       else wbytes mem (Z_to_bv 64 (SB + p / 8 + n / 8)) (word_to_le_bytes 1 (Z_to_bv 64 (n mod 8)))) rom)
    /\ (forall x, x <> 1 -> x <> 10 -> x <> 11 -> x <> 12 -> x <> 13 -> x <> 14 -> x <> 15 -> x <> 16 -> x <> 17 -> x <> 22 ->
                  getr regs' x = getr regs x).
Proof.
  intros mem rom p n Hp Hp8 Hn Hrng Hcells Cfl Cpp Ccp Hst regs H9 H22 H20.
  destruct (partial_granule_S mem rom p n Hp Hp8 Hn Hrng Hcells Cfl Cpp Ccp Hst regs H9 H22 H20) as (regs' & Hms & Hoth).
  exists regs'. split; [exact Hms|].
  intros x N1 N10 N11 N12 N13 N14 N15 N16 N17 N22. apply Hoth. unfold pg_clob.
  repeat match goal with
  | |- context [bv_eqb x ?c] =>
      let E := fresh in destruct (bv_eqb x c) eqn:E;
      [exfalso; unfold bv_eqb in E; apply Z.eqb_eq in E;
       let X := fresh in assert (X : x = c) by (apply bv_eq; exact E); subst x; congruence | ]
  end.
  reflexivity.
Qed.
