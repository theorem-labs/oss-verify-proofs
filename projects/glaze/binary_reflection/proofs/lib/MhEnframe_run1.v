(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.glaze.binary_reflection.images Require Import Plain.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9z OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.RefCodeM1. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9z.ListFacts OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.RefCodeM1.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9z OSSVerify.Proofs.glaze.binary_reflection.lib.MhEnframeBase. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9z.RefEnframeArith OSSVerify.Proofs.glaze.binary_reflection.lib.MhEnframeBase.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.PuStep. Import OSSVerify.Proofs.glaze.binary_reflection.lib.PuStep.PuKeep.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import PuStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac is_Z_lit ::= ps_is_Z_lit.   (* [comment removed for export] *)
#[local] Ltac check_closed_term_fast ::= ps_check_closed.
#[local] Ltac gres ::= pu_gres.
#[local] Ltac chain_step ::= pu_chain_step.   (* [comment removed for export] *)
#[local] Ltac vnorm ::= pu_vnorm.
#[local] Ltac step_simpl ::= pu_step_simpl.
#[local] Ltac not_kept ::= not_kept_fast.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPGen1.
Context {fx : FPState}.


Section Run1.
  Variables (mem0 : word -> option byte) (c : word) (g M W idx n h3 o16 stride start off : Z).
  Variables (rom : word -> option byte).
  Hypothesis H : efH mem0 c g M W idx n h3 o16 stride start off.

  Ltac facts :=
    pose proof (stride_facts _ _ _ _ _ _ _ _ _ _ _ _ H) as (Sge & Smod & S31);
    pose proof (off_facts _ _ _ _ _ _ _ _ _ _ _ _ H) as (O1 & O2 & O3 & O4);
    pose proof (start_facts _ _ _ _ _ _ _ _ _ _ _ _ H) as (T1 & T2 & T3 & T4 & T5);
    pose proof (Hg _ _ _ _ _ _ _ _ _ _ _ _ H) as Gg;
    pose proof (HM _ _ _ _ _ _ _ _ _ _ _ _ H) as GM;
    pose proof (HW _ _ _ _ _ _ _ _ _ _ _ _ H) as GW;
    pose proof (Hidx _ _ _ _ _ _ _ _ _ _ _ _ H) as Gidx;
    pose proof (Hn _ _ _ _ _ _ _ _ _ _ _ _ H) as Gn;
    pose proof (Hh3 _ _ _ _ _ _ _ _ _ _ _ _ H) as Gh3;
    pose proof (Ho16 _ _ _ _ _ _ _ _ _ _ _ _ H) as Go16;
    pose proof (u64_range c) as Gc.

  (* [comment removed for export] *)
  Ltac gsym := rewrite !getr_other by assumption; reflexivity.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma blockA_tbl : forall regs,
    getr regs 14 = Z_to_bv 64 W -> (w_maplen W = 0 \/ w_lastidx W <> 0) ->
    exists regs',
      msteps RSEGS (mkst regs (0x63508%bv : word) mem0 rom) (mkst regs' (0x63524%bv : word) mem0 rom)
      /\ keeps_cs regs regs'
      /\ getr regs' 14 = Z_to_bv 64 stride
      /\ (forall r : reg, r <> 14%bv -> r <> 15%bv -> getr regs' r = getr regs r).
  Proof using H off start o16 h3 n idx M g c.
    intros regs R14 Hpath. facts.
    pose proof (Hsc _ _ _ _ _ _ _ _ _ _ _ _ H Hpath) as Hs48.
    assert (Hs0 : 0 <= w_sizeclass W) by (unfold w_sizeclass; apply Z.mod_pos_bound; lia).
    pose proof (TBL _ _ _ _ _ _ _ _ _ _ _ _ H) as Ht.
    destruct (sc_entry_rom (w_sizeclass W) ltac:(lia)) as [_ Hent].
    eexists. split; [|split; [|split]].
    - stepn F_634b4 D_634b4. rewrite R14, v_srli_lit by lia.
      stepn F_634b8 D_634b8.
      stepn F_634bc D_634bc.
      change (2 ^ 5) with 32.
      rewrite v_andi_lit by (first [apply div_range64 | cbn]; lia).
      rewrite fld_sizeclass2 by lia.
      change ((W / 64) mod 64) with (w_sizeclass W).
      stepn F_634c0 D_634c0.
      stepn F_634c4 D_634c4. rewrite v_add_lit by lia.
      pose proof (size_class_pos (w_sizeclass W) ltac:(lia)) as Hcp.
      ldhu F_634c8 D_634c8 (Z_to_bv 64 (size_class (w_sizeclass W)))
        ltac:(rdn_at (Z_to_bv 64 (SCT + 2 * w_sizeclass W)); apply sc_tbl_read; [exact Ht | lia])
        ltac:(rewrite Hent; symmetry; apply u64_lit; lia).
      stepn F_634cc D_634cc. rewrite v_slli_lit by lia. change (2 ^ 4) with 16.
      pu_refl.
    - solve_kcs.
    - gres. rewrite (Estride _ _ _ _ _ _ _ _ _ _ _ _ H). unfold slot_stride, UNIT. f_equal.
      destruct Hpath as [Hp|Hp].
      + rewrite (proj2 (Z.eqb_eq _ _) Hp). cbn [negb andb]. lia.
      + rewrite (proj2 (Z.eqb_neq _ _) Hp). rewrite andb_false_r. lia.
    - intros r Hr14 Hr15. rewrite !getr_other by assumption. reflexivity.
  Qed.


  Lemma blockA_run : forall regs,
    getr regs 10 = Z_to_bv 64 g ->
    exists regs',
      msteps RSEGS (mkst regs (0x634e4%bv : word) mem0 rom) (mkst regs' (0x63524%bv : word) mem0 rom)
      /\ keeps_cs regs regs'
      /\ getr regs' 14 = Z_to_bv 64 stride
      /\ (forall r : reg, r <> 14%bv -> r <> 15%bv -> getr regs' r = getr regs r).
  Proof using H off start o16 h3 n idx W M c.
    intros regs R10. facts.
    pose proof (RW _ _ _ _ _ _ _ _ _ _ _ _ H) as LW.
    assert (Hmr : 0 <= w_maplen W < 2 ^ 64) by (unfold w_maplen; apply div_range64; lia).
    assert (Hlr : 0 <= w_lastidx W < 32) by (unfold w_lastidx; apply Z.mod_pos_bound; lia).
    destruct (Z.eq_dec (w_maplen W) 0) as [Hm0|Hm0].
    { (* [comment removed for export] *)
      destruct (blockA_tbl (regupd (regupd regs 14 (Z_to_bv 64 W)) 15 (Z_to_bv 64 (w_maplen W))))
        as (regs' & RUN & K & R14 & RR); [gres; reflexivity | left; exact Hm0 |].
      exists regs'. split; [|split; [|split]].
      - ldd F_63490 D_63490 (Z_to_bv 64 W) ltac:(exact LW).
        stepn F_63494 D_63494. rewrite v_srli_lit by lia. change (2 ^ 12) with 4096.
        change (W / 4096) with (w_maplen W).
        stepb_tk F_63498 D_63498 ltac:(rewrite c_eq_lit by lia; apply Z.eqb_eq; exact Hm0).
        exact RUN.
      - eapply keeps_cs_trans; [|exact K]. solve_kcs.
      - exact R14.
      - intros r Hr14 Hr15. rewrite (RR r Hr14 Hr15). gsym. }
    destruct (Z.eq_dec (w_lastidx W) 0) as [Hl0|Hl0].
    2:{ (* [comment removed for export] *)
      destruct (blockA_tbl (regupd (regupd (regupd regs 14 (Z_to_bv 64 W)) 15 (Z_to_bv 64 (w_maplen W)))
                             15 (Z_to_bv 64 (w_lastidx W))))
        as (regs' & RUN & K & R14 & RR); [gres; reflexivity | right; exact Hl0 |].
      exists regs'. split; [|split; [|split]].
      - ldd F_63490 D_63490 (Z_to_bv 64 W) ltac:(exact LW).
        stepn F_63494 D_63494. rewrite v_srli_lit by lia. change (2 ^ 12) with 4096.
        change (W / 4096) with (w_maplen W).
        stepb_ft F_63498 D_63498 ltac:(rewrite c_eq_lit by lia; apply Z.eqb_neq; exact Hm0).
        stepn F_6349c D_6349c. rewrite v_andi_lit by lia. rewrite fld_lastidx.
        change (W mod 32) with (w_lastidx W).
        stepb_tk F_634a0 D_634a0 ltac:(rewrite c_eq_lit by lia; apply Z.eqb_neq; exact Hl0).
        exact RUN.
      - eapply keeps_cs_trans; [|exact K]. solve_kcs.
      - exact R14.
      - intros r Hr14 Hr15. rewrite (RR r Hr14 Hr15). gsym. }
    (* [comment removed for export] *)
    assert (Hmw : 4096 * w_maplen W <= W) by (unfold w_maplen; apply Z.mul_div_le; lia).
    eexists. split; [|split; [|split]].
    - ldd F_63490 D_63490 (Z_to_bv 64 W) ltac:(exact LW).
      stepn F_63494 D_63494. rewrite v_srli_lit by lia. change (2 ^ 12) with 4096.
      change (W / 4096) with (w_maplen W).
      stepb_ft F_63498 D_63498 ltac:(rewrite c_eq_lit by lia; apply Z.eqb_neq; exact Hm0).
      stepn F_6349c D_6349c. rewrite v_andi_lit by lia. rewrite fld_lastidx.
      change (W mod 32) with (w_lastidx W).
      stepb_ft F_634a0 D_634a0 ltac:(rewrite c_eq_lit by lia; apply Z.eqb_eq; exact Hl0).
      stepn F_634a4 D_634a4.
      stepn F_634a8 D_634a8. rewrite v_and_lit by lia.
      change (Z.land W 18446744073709547520) with (Z.land W (2 ^ 64 - 4096)).
      rewrite fld_hi by lia. change (W / 4096) with (w_maplen W).
      stepn F_634ac D_634ac. rewrite v_addi_lit by lia.
      stepn F_634b0 D_634b0.
      pu_refl.
    - solve_kcs.
    - gres. rewrite (Estride _ _ _ _ _ _ _ _ _ _ _ _ H). unfold slot_stride, UNIT. f_equal.
      rewrite (proj2 (Z.eqb_neq _ _) Hm0), (proj2 (Z.eqb_eq _ _) Hl0). cbn [negb andb]. lia.
    - intros r Hr14 Hr15. gsym.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition off0 : Z := (if h3 =? 0 then bv_unsigned c else o16 + 1) mod 256.

  Definition bregsB (regs regs' : bvmap 5 word) : Prop :=
    getr regs' 15 = Z_to_bv 64 start /\ getr regs' 16 = Z_to_bv 64 M
    /\ getr regs' 17 = Z_to_bv 64 off0 /\ getr regs' 5 = Z_to_bv 64 (stride - 4 - n)
    /\ getr regs' 6 = Z_to_bv 64 (slack_of stride n) /\ getr regs' 7 = Z_to_bv 64 0
    /\ (forall r : reg, r <> 5%bv -> r <> 6%bv -> r <> 7%bv -> r <> 13%bv -> r <> 15%bv ->
                        r <> 16%bv -> r <> 17%bv -> getr regs' r = getr regs r).

  Lemma blockB_run : forall regs,
    getr regs 10 = Z_to_bv 64 g -> getr regs 11 = Z_to_bv 64 idx -> getr regs 12 = Z_to_bv 64 n ->
    getr regs 13 = c -> getr regs 14 = Z_to_bv 64 stride ->
    exists regs',
      msteps RSEGS (mkst regs (0x63524%bv : word) mem0 rom) (mkst regs' (0x63560%bv : word) mem0 rom)
      /\ keeps_cs regs regs' /\ bregsB regs regs'.
  Proof using H off W.
    intros regs R10 R11 R12 R13 R14. facts.
    pose proof (RM _ _ _ _ _ _ _ _ _ _ _ _ H) as LM.
    pose proof (R4 _ _ _ _ _ _ _ _ _ _ _ _ H) as L4.
    pose proof (R3 _ _ _ _ _ _ _ _ _ _ _ _ H) as L3.
    pose proof (R2 _ _ _ _ _ _ _ _ _ _ _ _ H) as L2.
    assert (Hsl : Z_to_bv 64 ((stride - 4 - n) / 2 ^ 4) = Z_to_bv 64 (slack_of stride n))
      by (unfold slack_of, IB, UNIT; reflexivity).
    destruct (Z.eq_dec h3 0) as [Hz|Hz].
    { (* [comment removed for export] *)
      eexists. split; [|split].
      - ldd F_634d0 D_634d0 (Z_to_bv 64 M) ltac:(exact LM).
        stepn F_634d4 D_634d4. rewrite R14, R11, v_mul_lit by lia.
        stepn F_634d8 D_634d8. rewrite v_add_lit by lia.
        ldbu F_634dc D_634dc ltac:(rdn_at (Z_to_bv 64 (start - 3)); apply rdn1_of_mem; exact L3).
        rewrite (u8_lit h3) by lia.
        stepn F_634e0 D_634e0. rewrite R14, R12, v_sub_lit by lia.
        stepn F_634e4 D_634e4. rewrite v_addi_lit by lia.
        stepn F_634e8 D_634e8. rewrite v_addi_lit by lia.
        stepb_tk F_634ec D_634ec ltac:(rewrite c_eq_lit by lia; apply Z.eqb_eq; exact Hz).
        ldbu F_634f8 D_634f8 ltac:(rdn_at (Z_to_bv 64 (start - 4)); apply rdn1_of_mem; exact L4).
        change (bv_unsigned (Z_to_bv 8 0)) with 0.
        stepn F_634fc D_634fc. rewrite v_srli_lit by lia.
        replace (stride - n + -4) with (stride - 4 - n) by lia. rewrite Hsl.
        stepn F_63500 D_63500. rewrite R13, v_andi_255.
        stepb_tk F_63504 D_63504 ltac:(reflexivity).
        pu_refl.
      - solve_kcs.
      - unfold bregsB, off0. rewrite (proj2 (Z.eqb_eq _ _) Hz).
        repeat split; try (gres; first [reflexivity | f_equal; lia]).
        intros r ? ? ? ? ? ? ?. gsym. }
    (* [comment removed for export] *)
    eexists. split; [|split].
    - ldd F_634d0 D_634d0 (Z_to_bv 64 M) ltac:(exact LM).
      stepn F_634d4 D_634d4. rewrite R14, R11, v_mul_lit by lia.
      stepn F_634d8 D_634d8. rewrite v_add_lit by lia.
      ldbu F_634dc D_634dc ltac:(rdn_at (Z_to_bv 64 (start - 3)); apply rdn1_of_mem; exact L3).
      rewrite (u8_lit h3) by lia.
      stepn F_634e0 D_634e0. rewrite R14, R12, v_sub_lit by lia.
      stepn F_634e4 D_634e4. rewrite v_addi_lit by lia.
      stepn F_634e8 D_634e8. rewrite v_addi_lit by lia.
      stepb_ft F_634ec D_634ec ltac:(rewrite c_eq_lit by lia; apply Z.eqb_neq; exact Hz).
      ldhu F_634f0 D_634f0 (Z_to_bv 64 o16)
        ltac:(rdn_at (Z_to_bv 64 (start - 2)); exact (L2 Hz))
        ltac:(apply bytes_le_wle2; lia).
      stepn F_634f4 D_634f4. rewrite v_addi_lit by lia.
      ldbu F_634f8 D_634f8 ltac:(rdn_at (Z_to_bv 64 (start - 4)); apply rdn1_of_mem; exact L4).
      change (bv_unsigned (Z_to_bv 8 0)) with 0.
      stepn F_634fc D_634fc. rewrite v_srli_lit by lia.
      replace (stride - n + -4) with (stride - 4 - n) by lia. rewrite Hsl.
      stepn F_63500 D_63500. rewrite v_andi_255, u64_lit by lia.
      stepb_tk F_63504 D_63504 ltac:(reflexivity).
      pu_refl.
    - solve_kcs.
    - unfold bregsB, off0. rewrite (proj2 (Z.eqb_neq _ _) Hz).
      repeat split; try (gres; first [reflexivity | f_equal; lia]).
      intros r ? ? ? ? ? ? ?. gsym.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma blockC_run : forall regs,
    getr regs 17 = Z_to_bv 64 off0 -> getr regs 5 = Z_to_bv 64 (stride - 4 - n) ->
    getr regs 6 = Z_to_bv 64 (slack_of stride n) ->
    exists regs',
      msteps RSEGS (mkst regs (0x63560%bv : word) mem0 rom) (mkst regs' (0x6359c%bv : word) mem0 rom)
      /\ keeps_cs regs regs' /\ getr regs' 17 = Z_to_bv 64 off
      /\ (forall r : reg, r <> 5%bv -> r <> 13%bv -> r <> 17%bv -> getr regs' r = getr regs r).
  Proof using H start idx W M g.
    intros regs R17 R5 R6. facts.
    pose proof (Eoff _ _ _ _ _ _ _ _ _ _ _ _ H) as EO. change (off = enframe_off (slack_of stride n) off0) in EO.
    set (S := slack_of stride n) in *.
    assert (HS64 : S < 2 ^ 64) by (subst S; unfold slack_of, IB, UNIT; apply div_range64; lia).
    assert (Ho0 : 0 <= off0 < 256) by (unfold off0; apply Z.mod_pos_bound; lia).
    destruct (Z.le_gt_cases off0 S) as [Hle|Hgt].
    { (* [comment removed for export] *)
      assert (off = off0) by (rewrite EO; unfold enframe_off; rewrite (proj2 (Z.leb_le _ _) Hle); reflexivity).
      eexists. split; [|split; [|split]].
      - stepb_tk F_6350c D_6350c ltac:(rewrite R6, R17, c_ltu_lit by lia; apply Z.ltb_ge; lia).
        pu_refl.
      - apply keeps_cs_refl.
      - rewrite R17. f_equal. lia.
      - intros; reflexivity. }
    (* [comment removed for export] *)
    set (m1 := Z.lor S (S / 2)). set (m2 := Z.lor (m1 / 4) m1). set (m3 := Z.lor (m2 / 16) m2).
    assert (Hm3 : m3 = smear S) by (subst m1 m2 m3; apply smear_via_regs; lia).
    assert (R1 : 0 <= m1 < 2 ^ 64) by (subst m1; apply lor_range; [lia|lia|apply div_range64; lia]).
    assert (R2 : 0 <= m2 < 2 ^ 64) by (subst m2; apply lor_range; [lia|apply div_range64; lia|lia]).
    assert (R3 : 0 <= m3 < 2 ^ 64) by (subst m3; apply lor_range; [lia|apply div_range64; lia|lia]).
    set (om := Z.land off0 m3).
    assert (Rom : 0 <= om <= off0) by (subst om; apply land_range; lia).
    assert (EO' : off = if S <? om then om - S - 1 else om).
    { rewrite EO. unfold enframe_off. rewrite (proj2 (Z.leb_gt _ _) Hgt). rewrite <- Hm3. reflexivity. }
    eexists. split; [|split; [|split]].
    - stepb_ft F_6350c D_6350c ltac:(rewrite R6, R17, c_ltu_lit by lia; apply Z.ltb_lt; lia).
      stepn F_63510 D_63510. rewrite R5, v_srli_lit by lia.
      replace ((stride - 4 - n) / 2 ^ 5) with (S / 2)
        by (subst S; unfold slack_of, IB, UNIT; change (2 ^ 5) with (16 * 2); rewrite Z.div_div by lia; reflexivity).
      stepn F_63514 D_63514. rewrite R6, v_or_lit by (first [lia | apply div_range64; lia]). change (Z.lor S (S / 2)) with m1.
      stepn F_63518 D_63518. rewrite v_srli_lit by lia. change (2 ^ 2) with 4.
      stepn F_6351c D_6351c. rewrite v_or_lit by (first [lia | apply div_range64; lia]). change (Z.lor (m1 / 4) m1) with m2.
      stepn F_63520 D_63520. rewrite v_srli_lit by lia. change (2 ^ 4) with 16.
      stepn F_63524 D_63524. rewrite v_or_lit by (first [lia | apply div_range64; lia]). change (Z.lor (m2 / 16) m2) with m3.
      stepn F_63528 D_63528. rewrite R17, v_and_lit by lia. change (Z.land off0 m3) with om.
      stepn F_6352c D_6352c. rewrite R6, v_sltu_lit by lia.
      stepn F_63530 D_63530. rewrite R6, v_not_lit by lia.
      stepn F_63534 D_63534.
      stepn F_63538 D_63538. rewrite neg_mask by lia.
      stepn F_6353c D_6353c.
      rewrite addw_mask by (first [lia | intros Hb; apply Z.ltb_lt; exact Hb]).
      rewrite <- EO'.
      stepb_tk F_63540 D_63540 ltac:(rewrite R6, c_ltu_lit by lia; apply Z.ltb_ge; lia).
      pu_refl.
    - solve_kcs.
    - gres. reflexivity.
    - intros r ? ? ?. gsym.
  Qed.

End Run1.
End FPGen1.

