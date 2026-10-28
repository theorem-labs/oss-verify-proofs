(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC.
From OssFuzzTheorems.bzip2.bzip2_compress_target.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require PropExec CatExec CatSim SeqExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require StreamSim.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require StreamSim MmapSim StepTac Hoare WalkTac StoreOk Frame RefMemcpyLib AgentLib MallocDefs. (* [comment removed for export] *) From Stdlib Require Lia. From Stdlib Require List Lia. From stdpp Require list.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require RefEnframeArith U.S0EnframeBase.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec U.S0_code_20620_216f4.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require WalkHide.
Import WalkHide.OptIn.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require NatLitLia.
Local Ltac Lia.lia ::= NatLitLia.lia_natlit_goal.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
Module S7Enframe_run1.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.CatExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.CatSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SeqExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.StreamSim.StreamExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.StreamSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.MmapSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.StepTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Hoare OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.WalkTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.StoreOk OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Frame OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.RefMemcpyLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.AgentLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.MallocDefs. (* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.RefEnframeArith OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0EnframeBase.
Local Ltac Lia.lia ::= NatLitLia.lia_natlit_goal.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import ListNotations.
Local Ltac Lia.lia ::= NatLitLia.lia_natlit_goal.   (* [comment removed for export] *)
Open Scope bv_scope.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Run1.
  Variables (mem0 : word -> option byte) (c : word) (g M W idx n h3 o16 stride start off : Z).
  Variables (rom : word -> option byte).
  Hypothesis H : efH mem0 c g M W idx n h3 o16 stride start off.

  Ltac facts :=
    cps_pose (stride_facts _ _ _ _ _ _ _ _ _ _ _ _ H) as (Sge & Smod & S31);
    cps_pose (off_facts _ _ _ _ _ _ _ _ _ _ _ _ H) as (O1 & O2 & O3 & O4);
    cps_pose (start_facts _ _ _ _ _ _ _ _ _ _ _ _ H) as (T1 & T2 & T3 & T4 & T5);
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
      msteps RSEGS (mkst regs (0x2aacc%bv : word) mem0 rom) (mkst regs' (0x2aae8%bv : word) mem0 rom)
      /\ keeps_cs regs regs'
      /\ getr regs' 14 = Z_to_bv 64 stride
      /\ (forall r : reg, r <> 14%bv -> r <> 15%bv -> getr regs' r = getr regs r).
  Proof.
    intros regs R14 Hpath. facts.
    pose proof (Hsc _ _ _ _ _ _ _ _ _ _ _ _ H Hpath) as Hs48.
    assert (Hs0 : 0 <= w_sizeclass W) by (unfold w_sizeclass; apply Z.mod_pos_bound; lia).
    pose proof (TBL _ _ _ _ _ _ _ _ _ _ _ _ H) as Ht.
    destruct (sc_entry_rom (w_sizeclass W) ltac:(lia)) as [_ Hent].
    eexists. split; [|split; [|split]].
    - stepn F_20c48 D_20c48. rewrite R14, v_srli_lit by lia.
      stepn F_20c4c D_20c4c.
      stepn F_20c50 D_20c50.
      change (2 ^ 5) with 32.
      rewrite v_andi_lit by (first [apply div_range64 | cbn]; lia).
      rewrite fld_sizeclass2 by lia.
      change ((W / 64) mod 64) with (w_sizeclass W).
      stepn F_20c54 D_20c54.
      stepn F_20c58 D_20c58. rewrite v_add_lit by lia.
      pose proof (size_class_pos (w_sizeclass W) ltac:(lia)) as Hcp.
      ldhu F_20c5c D_20c5c (Z_to_bv 64 (size_class (w_sizeclass W)))
        ltac:(rdn_at (Z_to_bv 64 (SCT + 2 * w_sizeclass W)); apply sc_tbl_read; [exact Ht | lia])
        ltac:(rewrite Hent; symmetry; apply u64_lit; lia).
      stepn F_20c60 D_20c60. rewrite v_slli_lit by lia. change (2 ^ 4) with 16.
      apply mst_refl.
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
      msteps RSEGS (mkst regs (0x2aaa8%bv : word) mem0 rom) (mkst regs' (0x2aae8%bv : word) mem0 rom)
      /\ keeps_cs regs regs'
      /\ getr regs' 14 = Z_to_bv 64 stride
      /\ (forall r : reg, r <> 14%bv -> r <> 15%bv -> getr regs' r = getr regs r).
  Proof.
    intros regs R10. facts.
    pose proof (RW _ _ _ _ _ _ _ _ _ _ _ _ H) as LW.
    assert (Hmr : 0 <= w_maplen W < 2 ^ 64) by (unfold w_maplen; apply div_range64; lia).
    assert (Hlr : 0 <= w_lastidx W < 32) by (unfold w_lastidx; apply Z.mod_pos_bound; lia).
    destruct (Z.eq_dec (w_maplen W) 0) as [Hm0|Hm0].
    { (* [comment removed for export] *)
      cps_destruct (blockA_tbl (regupd (regupd regs 14 (Z_to_bv 64 W)) 15 (Z_to_bv 64 (w_maplen W))))
        as (regs' & RUN & K & R14 & RR); [gres; reflexivity | left; exact Hm0 |].
      exists regs'. split; [|split; [|split]].
      - ldd F_20c24 D_20c24 (Z_to_bv 64 W) ltac:(exact LW).
        stepn F_20c28 D_20c28. rewrite v_srli_lit by lia. change (2 ^ 12) with 4096.
        change (W / 4096) with (w_maplen W).
        stepb_tk F_20c2c D_20c2c ltac:(rewrite c_eq_lit by lia; apply Z.eqb_eq; exact Hm0).
        exact RUN.
      - eapply keeps_cs_trans; [|exact K]. solve_kcs.
      - exact R14.
      - intros r Hr14 Hr15. rewrite (RR r Hr14 Hr15). gsym. }
    destruct (Z.eq_dec (w_lastidx W) 0) as [Hl0|Hl0].
    2:{ (* [comment removed for export] *)
      cps_destruct (blockA_tbl (regupd (regupd (regupd regs 14 (Z_to_bv 64 W)) 15 (Z_to_bv 64 (w_maplen W)))
                             15 (Z_to_bv 64 (w_lastidx W))))
        as (regs' & RUN & K & R14 & RR); [gres; reflexivity | right; exact Hl0 |].
      exists regs'. split; [|split; [|split]].
      - ldd F_20c24 D_20c24 (Z_to_bv 64 W) ltac:(exact LW).
        stepn F_20c28 D_20c28. rewrite v_srli_lit by lia. change (2 ^ 12) with 4096.
        change (W / 4096) with (w_maplen W).
        stepb_ft F_20c2c D_20c2c ltac:(rewrite c_eq_lit by lia; apply Z.eqb_neq; exact Hm0).
        stepn F_20c30 D_20c30. rewrite v_andi_lit by lia. rewrite fld_lastidx.
        change (W mod 32) with (w_lastidx W).
        stepb_tk F_20c34 D_20c34 ltac:(rewrite c_eq_lit by lia; apply Z.eqb_neq; exact Hl0).
        exact RUN.
      - eapply keeps_cs_trans; [|exact K]. solve_kcs.
      - exact R14.
      - intros r Hr14 Hr15. rewrite (RR r Hr14 Hr15). gsym. }
    (* [comment removed for export] *)
    assert (Hmw : 4096 * w_maplen W <= W) by (unfold w_maplen; apply Z.mul_div_le; lia).
    eexists. split; [|split; [|split]].
    - ldd F_20c24 D_20c24 (Z_to_bv 64 W) ltac:(exact LW).
      stepn F_20c28 D_20c28. rewrite v_srli_lit by lia. change (2 ^ 12) with 4096.
      change (W / 4096) with (w_maplen W).
      stepb_ft F_20c2c D_20c2c ltac:(rewrite c_eq_lit by lia; apply Z.eqb_neq; exact Hm0).
      stepn F_20c30 D_20c30. rewrite v_andi_lit by lia. rewrite fld_lastidx.
      change (W mod 32) with (w_lastidx W).
      stepb_ft F_20c34 D_20c34 ltac:(rewrite c_eq_lit by lia; apply Z.eqb_eq; exact Hl0).
      stepn F_20c38 D_20c38.
      stepn F_20c3c D_20c3c. rewrite v_and_lit by lia.
      change (Z.land W 18446744073709547520) with (Z.land W (2 ^ 64 - 4096)).
      rewrite fld_hi by lia. change (W / 4096) with (w_maplen W).
      stepn F_20c40 D_20c40. rewrite v_addi_lit by lia.
      stepn F_20c44 D_20c44.
      apply mst_refl.
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
      msteps RSEGS (mkst regs (0x2aae8%bv : word) mem0 rom) (mkst regs' (0x2ab24%bv : word) mem0 rom)
      /\ keeps_cs regs regs' /\ bregsB regs regs'.
  Proof.
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
      - ldd F_20c64 D_20c64 (Z_to_bv 64 M) ltac:(exact LM).
        stepn F_20c68 D_20c68. rewrite R14, R11, v_mul_lit by lia.
        stepn F_20c6c D_20c6c. rewrite v_add_lit by lia.
        ldbu F_20c70 D_20c70 ltac:(rdn_at (Z_to_bv 64 (start - 3)); apply rdn1_of_mem; exact L3).
        rewrite (u8_lit h3) by lia.
        stepn F_20c74 D_20c74. rewrite R14, R12, v_sub_lit by lia.
        stepn F_20c78 D_20c78. rewrite v_addi_lit by lia.
        stepn F_20c7c D_20c7c. rewrite v_addi_lit by lia.
        stepb_tk F_20c80 D_20c80 ltac:(rewrite c_eq_lit by lia; apply Z.eqb_eq; exact Hz).
        ldbu F_20c8c D_20c8c ltac:(rdn_at (Z_to_bv 64 (start - 4)); apply rdn1_of_mem; exact L4).
        change (bv_unsigned (Z_to_bv 8 0)) with 0.
        stepn F_20c90 D_20c90. rewrite v_srli_lit by lia.
        replace (stride - n + -4) with (stride - 4 - n) by lia. rewrite Hsl.
        stepn F_20c94 D_20c94. rewrite R13, v_andi_255.
        stepb_tk F_20c98 D_20c98 ltac:(reflexivity).
        apply mst_refl.
      - solve_kcs.
      - unfold bregsB, off0. rewrite (proj2 (Z.eqb_eq _ _) Hz).
        repeat split; try (gres; first [reflexivity | f_equal; lia]).
        intros r ? ? ? ? ? ? ?. gsym. }
    (* [comment removed for export] *)
    eexists. split; [|split].
    - ldd F_20c64 D_20c64 (Z_to_bv 64 M) ltac:(exact LM).
      stepn F_20c68 D_20c68. rewrite R14, R11, v_mul_lit by lia.
      stepn F_20c6c D_20c6c. rewrite v_add_lit by lia.
      ldbu F_20c70 D_20c70 ltac:(rdn_at (Z_to_bv 64 (start - 3)); apply rdn1_of_mem; exact L3).
      rewrite (u8_lit h3) by lia.
      stepn F_20c74 D_20c74. rewrite R14, R12, v_sub_lit by lia.
      stepn F_20c78 D_20c78. rewrite v_addi_lit by lia.
      stepn F_20c7c D_20c7c. rewrite v_addi_lit by lia.
      stepb_ft F_20c80 D_20c80 ltac:(rewrite c_eq_lit by lia; apply Z.eqb_neq; exact Hz).
      ldhu F_20c84 D_20c84 (Z_to_bv 64 o16)
        ltac:(rdn_at (Z_to_bv 64 (start - 2)); exact (L2 Hz))
        ltac:(apply bytes_le_wle2; lia).
      stepn F_20c88 D_20c88. rewrite v_addi_lit by lia.
      ldbu F_20c8c D_20c8c ltac:(rdn_at (Z_to_bv 64 (start - 4)); apply rdn1_of_mem; exact L4).
      change (bv_unsigned (Z_to_bv 8 0)) with 0.
      stepn F_20c90 D_20c90. rewrite v_srli_lit by lia.
      replace (stride - n + -4) with (stride - 4 - n) by lia. rewrite Hsl.
      stepn F_20c94 D_20c94. rewrite v_andi_255, u64_lit by lia.
      stepb_tk F_20c98 D_20c98 ltac:(reflexivity).
      apply mst_refl.
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
      msteps RSEGS (mkst regs (0x2ab24%bv : word) mem0 rom) (mkst regs' (0x2ab60%bv : word) mem0 rom)
      /\ keeps_cs regs regs' /\ getr regs' 17 = Z_to_bv 64 off
      /\ (forall r : reg, r <> 5%bv -> r <> 13%bv -> r <> 17%bv -> getr regs' r = getr regs r).
  Proof.
    intros regs R17 R5 R6. facts.
    pose proof (Eoff _ _ _ _ _ _ _ _ _ _ _ _ H) as EO. change (off = enframe_off (slack_of stride n) off0) in EO.
    set (S := slack_of stride n) in *.
    assert (HS64 : S < 2 ^ 64) by (subst S; unfold slack_of, IB, UNIT; apply div_range64; lia).
    assert (Ho0 : 0 <= off0 < 256) by (unfold off0; apply Z.mod_pos_bound; lia).
    destruct (Z.le_gt_cases off0 S) as [Hle|Hgt].
    { (* [comment removed for export] *)
      assert (off = off0) by (rewrite EO; unfold enframe_off; rewrite (proj2 (Z.leb_le _ _) Hle); reflexivity).
      eexists. split; [|split; [|split]].
      - stepb_tk F_20ca0 D_20ca0 ltac:(rewrite R6, R17, c_ltu_lit by lia; apply Z.ltb_ge; lia).
        apply mst_refl.
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
    - stepb_ft F_20ca0 D_20ca0 ltac:(rewrite R6, R17, c_ltu_lit by lia; apply Z.ltb_lt; lia).
      stepn F_20ca4 D_20ca4. rewrite R5, v_srli_lit by lia.
      replace ((stride - 4 - n) / 2 ^ 5) with (S / 2)
        by (subst S; unfold slack_of, IB, UNIT; change (2 ^ 5) with (16 * 2); rewrite Z.div_div by lia; reflexivity).
      stepn F_20ca8 D_20ca8. rewrite R6, v_or_lit by (first [lia | apply div_range64; lia]). change (Z.lor S (S / 2)) with m1.
      stepn F_20cac D_20cac. rewrite v_srli_lit by lia. change (2 ^ 2) with 4.
      stepn F_20cb0 D_20cb0. rewrite v_or_lit by (first [lia | apply div_range64; lia]). change (Z.lor (m1 / 4) m1) with m2.
      stepn F_20cb4 D_20cb4. rewrite v_srli_lit by lia. change (2 ^ 4) with 16.
      stepn F_20cb8 D_20cb8. rewrite v_or_lit by (first [lia | apply div_range64; lia]). change (Z.lor (m2 / 16) m2) with m3.
      stepn F_20cbc D_20cbc. rewrite R17, v_and_lit by lia. change (Z.land off0 m3) with om.
      stepn F_20cc0 D_20cc0. rewrite R6, v_sltu_lit by lia.
      stepn F_20cc4 D_20cc4. rewrite R6, v_not_lit by lia.
      stepn F_20cc8 D_20cc8.
      stepn F_20ccc D_20ccc. rewrite neg_mask by lia.
      stepn F_20cd0 D_20cd0.
      rewrite addw_mask by (first [lia | intros Hb; apply Z.ltb_lt; exact Hb]).
      rewrite <- EO'.
      stepb_tk F_20cd4 D_20cd4 ltac:(rewrite R6, c_ltu_lit by lia; apply Z.ltb_ge; lia).
      apply mst_refl.
    - solve_kcs.
    - gres. reflexivity.
    - intros r ? ? ?. gsym.
  Qed.

End Run1.
End S7Enframe_run1.

(* [comment removed for export] *)
Module S7Enframe_run2.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.CatExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.CatSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SeqExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.StreamSim.StreamExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.StreamSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.MmapSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.StepTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Hoare OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.WalkTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.StoreOk OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Frame OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.RefMemcpyLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.AgentLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.MallocDefs. (* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.RefEnframeArith OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0EnframeBase.
Local Ltac Lia.lia ::= NatLitLia.lia_natlit_goal.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import ListNotations.
Local Ltac Lia.lia ::= NatLitLia.lia_natlit_goal.   (* [comment removed for export] *)
Open Scope bv_scope.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Run2.
  Variables (mem0 : word -> option byte) (c : word) (g M W idx n h3 o16 stride start off : Z).
  Variables (rom : word -> option byte).
  Hypothesis H : efH mem0 c g M W idx n h3 o16 stride start off.

  Ltac facts :=
    cps_pose (stride_facts _ _ _ _ _ _ _ _ _ _ _ _ H) as (Sge & Smod & S31);
    cps_pose (off_facts _ _ _ _ _ _ _ _ _ _ _ _ H) as (O1 & O2 & O3 & O4);
    cps_pose (start_facts _ _ _ _ _ _ _ _ _ _ _ _ H) as (T1 & T2 & T3 & T4 & T5);
    pose proof (Hg _ _ _ _ _ _ _ _ _ _ _ _ H) as Gg;
    pose proof (HM _ _ _ _ _ _ _ _ _ _ _ _ H) as GM;
    pose proof (HW _ _ _ _ _ _ _ _ _ _ _ _ H) as GW;
    pose proof (Hidx _ _ _ _ _ _ _ _ _ _ _ _ H) as Gidx;
    pose proof (Hn _ _ _ _ _ _ _ _ _ _ _ _ H) as Gn;
    pose proof (Hdisj _ _ _ _ _ _ _ _ _ _ _ _ H) as Gdisj;
    pose proof (OK _ _ _ _ _ _ _ _ _ _ _ _ H) as GOK.

  Ltac gsym := rewrite !getr_other by assumption; reflexivity.

  (* [comment removed for export] *)
  Ltac sok :=
    repeat (eapply store_ok_mono;
            [ first [ apply wbytes_grows | apply grows_mD | apply grows_mE | apply grows_mE1 | apply grows_mF
                    | eassumption ] | ]);
    lazymatch goal with
    | GOK : store_ok _ mem0 _ _ = true |- store_ok _ mem0 _ ?k = true =>
        eapply (store_ok_sub RSEGS mem0 (Z_to_bv 64 (start - 3)) _ (Z.to_nat (stride - 1)) k);
        [ rewrite u64_lit, Z2Nat.id by lia; lia
        | exact GOK
        | rewrite !u64_lit by lia; lia
        | rewrite !u64_lit, Z2Nat.id by lia; simpl (Z.of_nat _); lia ]
    end.

  (* [comment removed for export] *)
  Ltac sidez :=
    rewrite ?length_wle2, ?length_wle4; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ];
    rewrite ?u64_lit by lia; lia.

  (* [comment removed for export] *)
  Ltac peel := rewrite rdn_wbytes_out; [ | sidez | sidez | sidez ].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma blockD_run : forall regs,
    getr regs 15 = Z_to_bv 64 start -> getr regs 17 = Z_to_bv 64 off ->
    getr regs 10 = Z_to_bv 64 g -> getr regs 16 = Z_to_bv 64 M ->
    exists regs',
      msteps RSEGS (mkst regs (0x2ab60%bv : word) mem0 rom)
                   (mkst regs' (0x2ab84%bv : word) (mD start off mem0) rom)
      /\ keeps_cs regs regs' /\ getr regs' 13 = Z_to_bv 64 (start + 16 * off)
      /\ getr regs' 16 = Z_to_bv 64 M
      /\ (forall r : reg, r <> 13%bv -> r <> 16%bv -> getr regs' r = getr regs r).
  Proof.
    intros regs R15 R17 R10 R16. facts.
    pose proof (RM _ _ _ _ _ _ _ _ _ _ _ _ H) as LM.
    destruct (Z.eq_dec off 0) as [Hz|Hz].
    { (* [comment removed for export] *)
      eexists. split; [|split; [|split; [|split]]].
      - cbv delta [mD] beta. rewrite (proj2 (Z.eqb_eq _ _) Hz).
        stepn F_20cdc D_20cdc. rewrite R15.
        stepb_tk F_20ce0 D_20ce0 ltac:(rewrite R17, c_eq_lit by lia; apply Z.eqb_eq; exact Hz).
        apply mst_refl.
      - solve_kcs.
      - gres. f_equal; lia.
      - gres. exact R16.
      - intros r ? ?. gsym. }
    (* [comment removed for export] *)
    eexists. split; [|split; [|split; [|split]]].
    - cbv delta [mD] beta. rewrite (proj2 (Z.eqb_neq _ _) Hz).
      stepn F_20cdc D_20cdc. rewrite R15.
      stepb_ft F_20ce0 D_20ce0 ltac:(rewrite R17, c_eq_lit by lia; apply Z.eqb_neq; exact Hz).
      stepn F_20ce4 D_20ce4.
      stepn F_20ce8 D_20ce8. rewrite R17, v_slliw_lit by lia. change (2 ^ 4) with 16.
      stepn F_20cec D_20cec. rewrite R15, v_add_lit by lia.
      stb F_20cf0 D_20cf0 (Z_to_bv 64 (start - 3)) (Z_to_bv 8 224)
        ltac:(apply bv_eq; vm_compute; reflexivity) ltac:(sok).
      sth F_20cf4 D_20cf4 (Z_to_bv 64 (start - 2)) (Z_to_bv 64 off) ltac:(sok).
      stb F_20cf8 D_20cf8 (Z_to_bv 64 (start + 16 * off - 4)) (Z_to_bv 8 0)
        ltac:(reflexivity) ltac:(sok).
      ldd F_20cfc D_20cfc (Z_to_bv 64 M)
        ltac:(peel; peel; peel; exact LM).
      apply mst_refl.
    - solve_kcs.
    - gres. f_equal; lia.
    - gres. reflexivity.
    - intros r ? ?. gsym.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Notation PP := (start + 16 * off).
  Local Notation EE := (start + stride - 4).
  Local Notation RR := (stride - 4 - n - 16 * off).
  Local Notation QQ := (stride * idx / 16 + off).

  Lemma qq_eq : (PP - M - 16) / 2 ^ 4 = QQ.
  Proof.
    facts. change (2 ^ 4) with 16.
    replace (start + 16 * off - M - 16) with (stride * idx + off * 16) by lia.
    rewrite Z.div_add by lia. reflexivity.
  Qed.

  Lemma qq_range : 0 <= QQ < 65536.
  Proof.
    facts.
    pose proof (div_le_self (stride * idx) 16 ltac:(lia) ltac:(lia)).
    assert (stride * idx / 16 < 65536 - 255); [|lia].
    apply Z.div_lt_upper_bound; lia.
  Qed.

  Lemma blockE1_run : forall regs m,
    getr regs 13 = Z_to_bv 64 PP -> getr regs 15 = Z_to_bv 64 start ->
    getr regs 14 = Z_to_bv 64 stride -> getr regs 16 = Z_to_bv 64 M ->
    getr regs 12 = Z_to_bv 64 n -> getr regs 11 = Z_to_bv 64 idx ->
    mem_grows mem0 m ->
    exists regs',
      msteps RSEGS (mkst regs (0x2ab84%bv : word) m rom)
                   (mkst regs' (0x2aba8%bv : word) (mE1 idx stride start off m) rom)
      /\ keeps_cs regs regs'
      /\ getr regs' 10 = Z_to_bv 64 EE /\ getr regs' 12 = Z_to_bv 64 (n + PP)
      /\ getr regs' 14 = Z_to_bv 64 (start + stride) /\ getr regs' 16 = Z_to_bv 64 RR
      /\ (forall r : reg, r <> 10%bv -> r <> 12%bv -> r <> 14%bv -> r <> 15%bv -> r <> 16%bv ->
                          getr regs' r = getr regs r).
  Proof.
    intros regs m R13 R15 R14 R16 R12 R11 Gm. facts. pose proof qq_range as Qr.
    eexists. split; [|split; [|split; [|split; [|split; [|split]]]]].
    - cbv delta [mE1] beta.
      stepn F_20d00 D_20d00. rewrite R15, R14, v_add_lit by lia.
      stepn F_20d04 D_20d04. rewrite R13, R16, v_subw_lit by lia.
      stepn F_20d08 D_20d08. rewrite R12, R13, v_add_lit by lia.
      stepn F_20d0c D_20d0c. rewrite v_addi_lit by lia.
      stepn F_20d10 D_20d10. rewrite v_addi_lit by lia.
      stepn F_20d14 D_20d14. rewrite v_srli_lit by lia.
      replace (start + 16 * off - M + -16) with (PP - M - 16) by lia. rewrite qq_eq.
      stepn F_20d18 D_20d18. rewrite v_subw_lit by lia.
      stb F_20d1c D_20d1c (Z_to_bv 64 (start + 16 * off - 3)) (Z_to_bv 8 idx)
        ltac:(apply sb_byte_small; lia) ltac:(sok).
      sth F_20d20 D_20d20 (Z_to_bv 64 (start + 16 * off - 2)) (Z_to_bv 64 QQ) ltac:(sok).
      apply mst_refl.
    - solve_kcs.
    - gres. f_equal; lia.
    - gres. reflexivity.
    - gres. reflexivity.
    - gres. f_equal; lia.
    - intros r ? ? ? ? ?. gsym.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma blockE2_run : forall regs m,
    getr regs 16 = Z_to_bv 64 RR -> getr regs 10 = Z_to_bv 64 EE ->
    getr regs 12 = Z_to_bv 64 (n + PP) -> getr regs 14 = Z_to_bv 64 (start + stride) ->
    mem_grows mem0 m ->
    exists regs',
      msteps RSEGS (mkst regs (0x2aba8%bv : word) (mE1 idx stride start off m) rom)
                   (mkst regs' (0x2abdc%bv : word) (mE idx n stride start off m) rom)
      /\ keeps_cs regs regs'
      /\ getr regs' 10 = Z_to_bv 64 (res_code RR)
      /\ (forall r : reg, r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> getr regs' r = getr regs r).
  Proof.
    intros regs m R16 R10 R12 R14 Gm. facts.
    destruct (Z.eq_dec RR 0) as [Hr0|Hr0].
    { eexists. split; [|split; [|split]].
      - cbv delta [mE] beta zeta. rewrite (proj2 (Z.eqb_eq _ _) Hr0).
        stepb_tk F_20d24 D_20d24 ltac:(rewrite R16, c_eq_lit by lia; apply Z.eqb_eq; exact Hr0).
        stepn F_20d4c D_20d4c. stepn F_20d50 D_20d50.
        apply mst_refl.
      - solve_kcs.
      - gres. unfold res_code. rewrite Hr0. reflexivity.
      - intros r ? ? ?. gsym. }
    destruct (Z.lt_ge_cases RR 5) as [Hr5|Hr5].
    { eexists. split; [|split; [|split]].
      - cbv delta [mE] beta zeta. rewrite (proj2 (Z.eqb_neq _ _) Hr0), (proj2 (Z.ltb_lt _ _) Hr5).
        stepb_ft F_20d24 D_20d24 ltac:(rewrite R16, c_eq_lit by lia; apply Z.eqb_neq; exact Hr0).
        stepn F_20d28 D_20d28. rewrite R10, R12, v_subw_lit by lia.
        replace (EE - (n + PP)) with RR by lia.
        stepn F_20d2c D_20d2c. rewrite v_subw_lit by lia.
        stepn F_20d30 D_20d30. rewrite R10, v_add_neg by lia.
        stepn F_20d34 D_20d34.
        stb F_20d38 D_20d38 (Z_to_bv 64 (start + 16 * off + n)) (Z_to_bv 8 0) ltac:(reflexivity) ltac:(sok).
        stepb_tk F_20d3c D_20d3c ltac:(rewrite c_lts_lit by lia; apply Z.ltb_lt; exact Hr5).
        stepn F_20d54 D_20d54.
        apply mst_refl.
      - solve_kcs.
      - gres. unfold res_code. rewrite (proj2 (Z.ltb_lt _ _) Hr5). reflexivity.
      - intros r ? ? ?. gsym. }
    eexists. split; [|split; [|split]].
    - cbv delta [mE] beta zeta. rewrite (proj2 (Z.eqb_neq _ _) Hr0), (proj2 (Z.ltb_ge _ _) Hr5).
      stepb_ft F_20d24 D_20d24 ltac:(rewrite R16, c_eq_lit by lia; apply Z.eqb_neq; exact Hr0).
      stepn F_20d28 D_20d28. rewrite R10, R12, v_subw_lit by lia.
      replace (EE - (n + PP)) with RR by lia.
      stepn F_20d2c D_20d2c. rewrite v_subw_lit by lia.
      stepn F_20d30 D_20d30. rewrite R10, v_add_neg by lia.
      stepn F_20d34 D_20d34.
      stb F_20d38 D_20d38 (Z_to_bv 64 (start + 16 * off + n)) (Z_to_bv 8 0) ltac:(reflexivity) ltac:(sok).
      stepb_ft F_20d3c D_20d3c ltac:(rewrite c_lts_lit by lia; apply Z.ltb_ge; exact Hr5).
      stb F_20d40 D_20d40 (Z_to_bv 64 (start + stride - 4 - 5)) (Z_to_bv 8 0) ltac:(reflexivity) ltac:(sok).
      stw F_20d44 D_20d44 (Z_to_bv 64 (start + stride - 4 - 4)) (Z_to_bv 64 RR) ltac:(sok).
      stepn F_20d48 D_20d48.
      apply mst_refl.
    - solve_kcs.
    - gres. unfold res_code. rewrite (proj2 (Z.ltb_ge _ _) Hr5). reflexivity.
    - intros r ? ? ?. gsym.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma blockF_run : forall regs m (ret : word),
    getr regs 13 = Z_to_bv 64 PP -> getr regs 10 = Z_to_bv 64 (res_code RR) ->
    getr regs 1 = ret -> ret_ok ret ->
    rdn RSEGS m (Z_to_bv 64 (start + 16 * off - 3)) 1 = Some [Z_to_bv 8 idx] ->
    mem_grows mem0 m ->
    exists regs',
      msteps RSEGS (mkst regs (0x2abdc%bv : word) m rom)
                   (mkst regs' ret (mF idx n stride start off m) rom)
      /\ keeps_cs regs regs'
      /\ getr regs' 10 = Z_to_bv 64 PP.
  Proof.
    intros regs m ret R13 R10 R1 Hret Rd Gm. facts.
    assert (Hrc : 0 <= res_code RR <= 5) by (unfold res_code; destruct (RR <? 5) eqn:E; [apply Z.ltb_lt in E|]; lia).
    eexists. split; [|split].
    - cbv delta [mF] beta.
      ldbu F_20d58 D_20d58 ltac:(rdn_at (Z_to_bv 64 (start + 16 * off - 3)); exact Rd).
      rewrite (u8_lit idx) by lia.
      stepn F_20d5c D_20d5c. rewrite v_andi_31, u64_lit, Z.mod_small by lia.
      stepn F_20d60 D_20d60. rewrite R10, v_slli_lit by lia.
      stepn F_20d64 D_20d64. rewrite v_or_lit by lia. rewrite lor_shift5 by lia.
      stb F_20d68 D_20d68 (Z_to_bv 64 (start + 16 * off - 3)) (Z_to_bv 8 (idx + 32 * res_code RR))
        ltac:(apply sb_byte_small; lia) ltac:(sok).
      stepn F_20d6c D_20d6c. rewrite R13.
      stepret F_20d70 D_20d70 ret ltac:(exact R1).
      apply mst_refl.
    - solve_kcs.
    - gres. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma rd_idx : forall m,
    rdn RSEGS (mE idx n stride start off m) (Z_to_bv 64 (start + 16 * off - 3)) 1 = Some [Z_to_bv 8 idx].
  Proof.
    intros m. facts.
    assert (E1 : rdn RSEGS (mE1 idx stride start off m) (Z_to_bv 64 (start + 16 * off - 3)) 1
                 = Some [Z_to_bv 8 idx]).
    { cbv delta [mE1] beta. peel. apply (rdn_wbytes_hit RSEGS [Z_to_bv 8 idx]). sidez. }
    cbv delta [mE] beta zeta.
    destruct (Z.eqb_spec RR 0) as [Hr0|Hr0]; [exact E1|].
    destruct (Z.ltb_spec RR 5) as [Hr5|Hr5]; [peel; exact E1|].
    peel. peel. peel. exact E1.
  Qed.

End Run2.
End S7Enframe_run2.

(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.CatExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.CatSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SeqExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.StreamSim.StreamExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.StreamSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.MmapSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.StepTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Hoare OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.WalkTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.StoreOk OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Frame OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.RefMemcpyLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.AgentLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.MallocDefs. (* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.RefEnframeArith OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0EnframeBase S7Enframe_run1 S7Enframe_run2.
Local Ltac Lia.lia ::= NatLitLia.lia_natlit_goal.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import ListNotations.
Local Ltac Lia.lia ::= NatLitLia.lia_natlit_goal.   (* [comment removed for export] *)
Open Scope bv_scope.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Enframe.
  Variables (mem0 : word -> option byte) (c : word) (g M W idx n h3 o16 stride start off : Z).
  Hypothesis H : efH mem0 c g M W idx n h3 o16 stride start off.

  Ltac facts :=
    cps_pose (stride_facts _ _ _ _ _ _ _ _ _ _ _ _ H) as (Sge & Smod & S31);
    cps_pose (off_facts _ _ _ _ _ _ _ _ _ _ _ _ H) as (O1 & O2 & O3 & O4);
    cps_pose (start_facts _ _ _ _ _ _ _ _ _ _ _ _ H) as (T1 & T2 & T3 & T4 & T5);
    pose proof (Hidx _ _ _ _ _ _ _ _ _ _ _ _ H) as Gidx;
    pose proof (Hn _ _ _ _ _ _ _ _ _ _ _ _ H) as Gn.

  Local Notation PP := (start + 16 * off).
  Local Notation EE := (start + stride - 4).
  Local Notation RR := (stride - 4 - n - 16 * off).
  Local Notation QQ := (stride * idx / 16 + off).

  (* [comment removed for export] *)
  Definition memF : memT :=
    mF idx n stride start off (mE idx n stride start off (mD start off mem0)).

  (* [comment removed for export] *)

  Ltac sidez :=
    rewrite ?length_wle2, ?length_wle4; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ];
    rewrite ?u64_lit by lia; lia.
  Ltac peel := rewrite rdn_wbytes_out; [ | sidez | sidez | sidez ].
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma enframe_run : forall regs rom (ret : word),
    getr regs 1 = ret -> ret_ok ret ->
    getr regs 10 = Z_to_bv 64 g -> getr regs 11 = Z_to_bv 64 idx ->
    getr regs 12 = Z_to_bv 64 n -> getr regs 13 = c ->
    exists regs',
      msteps RSEGS (mkst regs (0x2aaa8%bv : word) mem0 rom) (mkst regs' ret memF rom)
      /\ keeps_cs regs regs'
      /\ getr regs' 10 = Z_to_bv 64 PP.
  Proof.
    intros regs rom ret R1 Hret R10 R11 R12 R13. facts.
    (* [comment removed for export] *)
    cps_destruct (blockA_run _ _ _ _ _ _ _ _ _ _ _ _ rom H regs R10) as (r1 & RUN1 & K1 & A14 & P1).
    assert (A10 : getr r1 10 = Z_to_bv 64 g) by (rewrite P1 by discriminate; exact R10).
    assert (A11 : getr r1 11 = Z_to_bv 64 idx) by (rewrite P1 by discriminate; exact R11).
    assert (A12 : getr r1 12 = Z_to_bv 64 n) by (rewrite P1 by discriminate; exact R12).
    assert (A13 : getr r1 13 = c) by (rewrite P1 by discriminate; exact R13).
    assert (A1 : getr r1 1 = ret) by (rewrite P1 by discriminate; exact R1).
    (* [comment removed for export] *)
    cps_destruct (blockB_run _ _ _ _ _ _ _ _ _ _ _ _ rom H r1 A10 A11 A12 A13 A14)
      as (r2 & RUN2 & K2 & (B15 & B16 & B17 & B5 & B6 & B7 & P2)).
    assert (B10 : getr r2 10 = Z_to_bv 64 g) by (rewrite P2 by discriminate; exact A10).
    assert (B11 : getr r2 11 = Z_to_bv 64 idx) by (rewrite P2 by discriminate; exact A11).
    assert (B12 : getr r2 12 = Z_to_bv 64 n) by (rewrite P2 by discriminate; exact A12).
    assert (B14 : getr r2 14 = Z_to_bv 64 stride) by (rewrite P2 by discriminate; exact A14).
    assert (B1 : getr r2 1 = ret) by (rewrite P2 by discriminate; exact A1).
    (* [comment removed for export] *)
    cps_destruct (blockC_run _ _ _ _ _ _ _ _ _ _ _ _ rom H r2 B17 B5 B6) as (r3 & RUN3 & K3 & C17 & P3).
    assert (C10 : getr r3 10 = Z_to_bv 64 g) by (rewrite P3 by discriminate; exact B10).
    assert (C11 : getr r3 11 = Z_to_bv 64 idx) by (rewrite P3 by discriminate; exact B11).
    assert (C12 : getr r3 12 = Z_to_bv 64 n) by (rewrite P3 by discriminate; exact B12).
    assert (C14 : getr r3 14 = Z_to_bv 64 stride) by (rewrite P3 by discriminate; exact B14).
    assert (C15 : getr r3 15 = Z_to_bv 64 start) by (rewrite P3 by discriminate; exact B15).
    assert (C16 : getr r3 16 = Z_to_bv 64 M) by (rewrite P3 by discriminate; exact B16).
    assert (C1 : getr r3 1 = ret) by (rewrite P3 by discriminate; exact B1).
    (* [comment removed for export] *)
    cps_destruct (blockD_run _ _ _ _ _ _ _ _ _ _ _ _ rom H r3 C15 C17 C10 C16) as (r4 & RUN4 & K4 & D13 & D16 & P4).
    assert (D11 : getr r4 11 = Z_to_bv 64 idx) by (rewrite P4 by discriminate; exact C11).
    assert (D12 : getr r4 12 = Z_to_bv 64 n) by (rewrite P4 by discriminate; exact C12).
    assert (D14 : getr r4 14 = Z_to_bv 64 stride) by (rewrite P4 by discriminate; exact C14).
    assert (D15 : getr r4 15 = Z_to_bv 64 start) by (rewrite P4 by discriminate; exact C15).
    assert (D1 : getr r4 1 = ret) by (rewrite P4 by discriminate; exact C1).
    set (m1 := mD start off mem0) in *.
    assert (G1 : mem_grows mem0 m1) by (subst m1; apply grows_mD).
    (* [comment removed for export] *)
    cps_destruct (blockE1_run _ _ _ _ _ _ _ _ _ _ _ _ rom H r4 m1 D13 D15 D14 D16 D12 D11 G1)
      as (r5 & RUN5 & K5 & E10 & E12 & E14 & E16 & P5).
    assert (E13 : getr r5 13 = Z_to_bv 64 PP) by (rewrite P5 by discriminate; exact D13).
    assert (E1' : getr r5 1 = ret) by (rewrite P5 by discriminate; exact D1).
    (* [comment removed for export] *)
    cps_destruct (blockE2_run _ _ _ _ _ _ _ _ _ _ _ _ rom H r5 m1 E16 E10 E12 E14 G1)
      as (r6 & RUN6 & K6 & F10 & P6).
    assert (F13 : getr r6 13 = Z_to_bv 64 PP) by (rewrite P6 by discriminate; exact E13).
    assert (F1 : getr r6 1 = ret) by (rewrite P6 by discriminate; exact E1').
    (* [comment removed for export] *)
    assert (G2 : mem_grows mem0 (mE idx n stride start off m1))
      by (eapply mem_grows_trans; [exact G1 | apply grows_mE]).
    cps_destruct (blockF_run _ _ _ _ _ _ _ _ _ _ _ _ rom H r6 _ ret F13 F10 F1 Hret
                (rd_idx _ _ _ _ _ _ _ _ _ _ _ _ H m1) G2)
      as (r7 & RUN7 & K7 & Z10).
    exists r7. split; [|split].
    - unfold memF. fold m1.
      eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|].
      eapply msteps_trans; [exact RUN3|]. eapply msteps_trans; [exact RUN4|].
      eapply msteps_trans; [exact RUN5|]. eapply msteps_trans; [exact RUN6|]. exact RUN7.
    - repeat (eapply keeps_cs_trans; [eassumption|]); first [assumption | apply keeps_cs_refl].
    - exact Z10.
  Qed.
End Enframe.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
