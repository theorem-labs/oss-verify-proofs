(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC.
From OSSVerify.skcms.iccprofile_info.images Require Plain.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require ListFacts PropExec CatExec CatSim SeqExec StreamExec StreamSim MmapSim StepTac Hoare WalkTac StoreOk Frame RefMemcpyLib AgentLib MallocDefs.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require RefEnframeArith RefEnframeBase.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Ref_code_17404_183b0 Ref_code_183b0_19140.
From Stdlib Require Zify.
Unset Nia Cache.  (* [comment removed for export] *)

Module RefEnframe_run1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.skcms.iccprofile_info.images.Plain.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ListFacts OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StreamExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StreamSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MmapSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StepTac OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Hoare OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.WalkTac OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefMemcpyLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AgentLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MallocDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Ref_code_17404_183b0 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Ref_code_183b0_19140.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefEnframeArith OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefEnframeBase.
Import Stdlib.micromega.Zify.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section WithFP1. Context {FP : PropExec.FPState}.
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
      msteps RSEGS (mkst regs (0x1836c%bv : word) mem0 rom) (mkst regs' (0x18388%bv : word) mem0 rom)
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
    - stepn F_1836c D_1836c. rewrite R14, v_srli_lit by lia.
      stepn F_18370 D_18370.
      stepn F_18374 D_18374.
      change (2 ^ 5) with 32.
      rewrite v_andi_lit by (first [apply div_range64 | cbn]; lia).
      rewrite fld_sizeclass2 by lia.
      change ((W / 64) mod 64) with (w_sizeclass W).
      stepn F_18378 D_18378.
      stepn F_1837c D_1837c. rewrite v_add_lit by lia.
      pose proof (size_class_pos (w_sizeclass W) ltac:(lia)) as Hcp.
      ldhu F_18380 D_18380 (Z_to_bv 64 (size_class (w_sizeclass W)))
        ltac:(rdn_at (Z_to_bv 64 (SCT + 2 * w_sizeclass W)); apply sc_tbl_read; [exact Ht | lia])
        ltac:(rewrite Hent; symmetry; apply u64_lit; lia).
      stepn F_18384 D_18384. rewrite v_slli_lit by lia. change (2 ^ 4) with 16.
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
      msteps RSEGS (mkst regs (0x18348%bv : word) mem0 rom) (mkst regs' (0x18388%bv : word) mem0 rom)
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
      destruct (blockA_tbl (regupd (regupd regs 14 (Z_to_bv 64 W)) 15 (Z_to_bv 64 (w_maplen W))))
        as (regs' & RUN & K & R14 & RR); [gres; reflexivity | left; exact Hm0 |].
      exists regs'. split; [|split; [|split]].
      - ldd F_18348 D_18348 (Z_to_bv 64 W) ltac:(exact LW).
        stepn F_1834c D_1834c. rewrite v_srli_lit by lia. change (2 ^ 12) with 4096.
        change (W / 4096) with (w_maplen W).
        stepb_tk F_18350 D_18350 ltac:(rewrite c_eq_lit by lia; apply Z.eqb_eq; exact Hm0).
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
      - ldd F_18348 D_18348 (Z_to_bv 64 W) ltac:(exact LW).
        stepn F_1834c D_1834c. rewrite v_srli_lit by lia. change (2 ^ 12) with 4096.
        change (W / 4096) with (w_maplen W).
        stepb_ft F_18350 D_18350 ltac:(rewrite c_eq_lit by lia; apply Z.eqb_neq; exact Hm0).
        stepn F_18354 D_18354. rewrite v_andi_lit by lia. rewrite fld_lastidx.
        change (W mod 32) with (w_lastidx W).
        stepb_tk F_18358 D_18358 ltac:(rewrite c_eq_lit by lia; apply Z.eqb_neq; exact Hl0).
        exact RUN.
      - eapply keeps_cs_trans; [|exact K]. solve_kcs.
      - exact R14.
      - intros r Hr14 Hr15. rewrite (RR r Hr14 Hr15). gsym. }
    (* [comment removed for export] *)
    assert (Hmw : 4096 * w_maplen W <= W) by (unfold w_maplen; apply Z.mul_div_le; lia).
    eexists. split; [|split; [|split]].
    - ldd F_18348 D_18348 (Z_to_bv 64 W) ltac:(exact LW).
      stepn F_1834c D_1834c. rewrite v_srli_lit by lia. change (2 ^ 12) with 4096.
      change (W / 4096) with (w_maplen W).
      stepb_ft F_18350 D_18350 ltac:(rewrite c_eq_lit by lia; apply Z.eqb_neq; exact Hm0).
      stepn F_18354 D_18354. rewrite v_andi_lit by lia. rewrite fld_lastidx.
      change (W mod 32) with (w_lastidx W).
      stepb_ft F_18358 D_18358 ltac:(rewrite c_eq_lit by lia; apply Z.eqb_eq; exact Hl0).
      stepn F_1835c D_1835c.
      stepn F_18360 D_18360. rewrite v_and_lit by lia.
      change (Z.land W 18446744073709547520) with (Z.land W (2 ^ 64 - 4096)).
      rewrite fld_hi by lia. change (W / 4096) with (w_maplen W).
      stepn F_18364 D_18364. rewrite v_addi_lit by lia.
      stepn F_18368 D_18368.
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
      msteps RSEGS (mkst regs (0x18388%bv : word) mem0 rom) (mkst regs' (0x183c4%bv : word) mem0 rom)
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
      - ldd F_18388 D_18388 (Z_to_bv 64 M) ltac:(exact LM).
        stepn F_1838c D_1838c. rewrite R14, R11, v_mul_lit by lia.
        stepn F_18390 D_18390. rewrite v_add_lit by lia.
        ldbu F_18394 D_18394 ltac:(rdn_at (Z_to_bv 64 (start - 3)); apply rdn1_of_mem; exact L3).
        rewrite (u8_lit h3) by lia.
        stepn F_18398 D_18398. rewrite R14, R12, v_sub_lit by lia.
        stepn F_1839c D_1839c. rewrite v_addi_lit by lia.
        stepn F_183a0 D_183a0. rewrite v_addi_lit by lia.
        stepb_tk F_183a4 D_183a4 ltac:(rewrite c_eq_lit by lia; apply Z.eqb_eq; exact Hz).
        ldbu F_183b0 D_183b0 ltac:(rdn_at (Z_to_bv 64 (start - 4)); apply rdn1_of_mem; exact L4).
        change (bv_unsigned (Z_to_bv 8 0)) with 0.
        stepn F_183b4 D_183b4. rewrite v_srli_lit by lia.
        replace (stride - n + -4) with (stride - 4 - n) by lia. rewrite Hsl.
        stepn F_183b8 D_183b8. rewrite R13, v_andi_255.
        stepb_tk F_183bc D_183bc ltac:(reflexivity).
        apply mst_refl.
      - solve_kcs.
      - unfold bregsB, off0. rewrite (proj2 (Z.eqb_eq _ _) Hz).
        repeat split; try (gres; first [reflexivity | f_equal; lia]).
        intros r ? ? ? ? ? ? ?. gsym. }
    (* [comment removed for export] *)
    eexists. split; [|split].
    - ldd F_18388 D_18388 (Z_to_bv 64 M) ltac:(exact LM).
      stepn F_1838c D_1838c. rewrite R14, R11, v_mul_lit by lia.
      stepn F_18390 D_18390. rewrite v_add_lit by lia.
      ldbu F_18394 D_18394 ltac:(rdn_at (Z_to_bv 64 (start - 3)); apply rdn1_of_mem; exact L3).
      rewrite (u8_lit h3) by lia.
      stepn F_18398 D_18398. rewrite R14, R12, v_sub_lit by lia.
      stepn F_1839c D_1839c. rewrite v_addi_lit by lia.
      stepn F_183a0 D_183a0. rewrite v_addi_lit by lia.
      stepb_ft F_183a4 D_183a4 ltac:(rewrite c_eq_lit by lia; apply Z.eqb_neq; exact Hz).
      ldhu F_183a8 D_183a8 (Z_to_bv 64 o16)
        ltac:(rdn_at (Z_to_bv 64 (start - 2)); exact (L2 Hz))
        ltac:(apply bytes_le_wle2; lia).
      stepn F_183ac D_183ac. rewrite v_addi_lit by lia.
      ldbu F_183b0 D_183b0 ltac:(rdn_at (Z_to_bv 64 (start - 4)); apply rdn1_of_mem; exact L4).
      change (bv_unsigned (Z_to_bv 8 0)) with 0.
      stepn F_183b4 D_183b4. rewrite v_srli_lit by lia.
      replace (stride - n + -4) with (stride - 4 - n) by lia. rewrite Hsl.
      stepn F_183b8 D_183b8. rewrite v_andi_255, u64_lit by lia.
      stepb_tk F_183bc D_183bc ltac:(reflexivity).
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
      msteps RSEGS (mkst regs (0x183c4%bv : word) mem0 rom) (mkst regs' (0x18400%bv : word) mem0 rom)
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
      - stepb_tk F_183c4 D_183c4 ltac:(rewrite R6, R17, c_ltu_lit by lia; apply Z.ltb_ge; lia).
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
    - stepb_ft F_183c4 D_183c4 ltac:(rewrite R6, R17, c_ltu_lit by lia; apply Z.ltb_lt; lia).
      stepn F_183c8 D_183c8. rewrite R5, v_srli_lit by lia.
      replace ((stride - 4 - n) / 2 ^ 5) with (S / 2)
        by (subst S; unfold slack_of, IB, UNIT; change (2 ^ 5) with (16 * 2); rewrite Z.div_div by lia; reflexivity).
      stepn F_183cc D_183cc. rewrite R6, v_or_lit by (first [lia | apply div_range64; lia]). change (Z.lor S (S / 2)) with m1.
      stepn F_183d0 D_183d0. rewrite v_srli_lit by lia. change (2 ^ 2) with 4.
      stepn F_183d4 D_183d4. rewrite v_or_lit by (first [lia | apply div_range64; lia]). change (Z.lor (m1 / 4) m1) with m2.
      stepn F_183d8 D_183d8. rewrite v_srli_lit by lia. change (2 ^ 4) with 16.
      stepn F_183dc D_183dc. rewrite v_or_lit by (first [lia | apply div_range64; lia]). change (Z.lor (m2 / 16) m2) with m3.
      stepn F_183e0 D_183e0. rewrite R17, v_and_lit by lia. change (Z.land off0 m3) with om.
      stepn F_183e4 D_183e4. rewrite R6, v_sltu_lit by lia.
      stepn F_183e8 D_183e8. rewrite R6, v_not_lit by lia.
      stepn F_183ec D_183ec.
      stepn F_183f0 D_183f0. rewrite neg_mask by lia.
      stepn F_183f4 D_183f4.
      rewrite addw_mask by (first [lia | intros Hb; apply Z.ltb_lt; exact Hb]).
      rewrite <- EO'.
      stepb_tk F_183f8 D_183f8 ltac:(rewrite R6, c_ltu_lit by lia; apply Z.ltb_ge; lia).
      apply mst_refl.
    - solve_kcs.
    - gres. reflexivity.
    - intros r ? ? ?. gsym.
  Qed.

End Run1.
End WithFP1.

End RefEnframe_run1.

Module RefEnframe_run2.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.skcms.iccprofile_info.images.Plain.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ListFacts OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StreamExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StreamSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MmapSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StepTac OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Hoare OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.WalkTac OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefMemcpyLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AgentLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MallocDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Ref_code_183b0_19140.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefEnframeArith OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefEnframeBase.
Import Stdlib.micromega.Zify.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section WithFP1. Context {FP : PropExec.FPState}.
Section Run2.
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
      msteps RSEGS (mkst regs (0x18400%bv : word) mem0 rom)
                   (mkst regs' (0x18424%bv : word) (mD start off mem0) rom)
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
        stepn F_18400 D_18400. rewrite R15.
        stepb_tk F_18404 D_18404 ltac:(rewrite R17, c_eq_lit by lia; apply Z.eqb_eq; exact Hz).
        apply mst_refl.
      - solve_kcs.
      - gres. f_equal; lia.
      - gres. exact R16.
      - intros r ? ?. gsym. }
    (* [comment removed for export] *)
    eexists. split; [|split; [|split; [|split]]].
    - cbv delta [mD] beta. rewrite (proj2 (Z.eqb_neq _ _) Hz).
      stepn F_18400 D_18400. rewrite R15.
      stepb_ft F_18404 D_18404 ltac:(rewrite R17, c_eq_lit by lia; apply Z.eqb_neq; exact Hz).
      stepn F_18408 D_18408.
      stepn F_1840c D_1840c. rewrite R17, v_slliw_lit by lia. change (2 ^ 4) with 16.
      stepn F_18410 D_18410. rewrite R15, v_add_lit by lia.
      stb F_18414 D_18414 (Z_to_bv 64 (start - 3)) (Z_to_bv 8 224)
        ltac:(apply bv_eq; vm_compute; reflexivity) ltac:(sok).
      sth F_18418 D_18418 (Z_to_bv 64 (start - 2)) (Z_to_bv 64 off) ltac:(sok).
      stb F_1841c D_1841c (Z_to_bv 64 (start + 16 * off - 4)) (Z_to_bv 8 0)
        ltac:(reflexivity) ltac:(sok).
      ldd F_18420 D_18420 (Z_to_bv 64 M)
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
      msteps RSEGS (mkst regs (0x18424%bv : word) m rom)
                   (mkst regs' (0x18448%bv : word) (mE1 idx stride start off m) rom)
      /\ keeps_cs regs regs'
      /\ getr regs' 10 = Z_to_bv 64 EE /\ getr regs' 12 = Z_to_bv 64 (n + PP)
      /\ getr regs' 14 = Z_to_bv 64 (start + stride) /\ getr regs' 16 = Z_to_bv 64 RR
      /\ (forall r : reg, r <> 10%bv -> r <> 12%bv -> r <> 14%bv -> r <> 15%bv -> r <> 16%bv ->
                          getr regs' r = getr regs r).
  Proof.
    intros regs m R13 R15 R14 R16 R12 R11 Gm. facts. pose proof qq_range as Qr.
    eexists. split; [|split; [|split; [|split; [|split; [|split]]]]].
    - cbv delta [mE1] beta.
      stepn F_18424 D_18424. rewrite R15, R14, v_add_lit by lia.
      stepn F_18428 D_18428. rewrite R13, R16, v_subw_lit by lia.
      stepn F_1842c D_1842c. rewrite R12, R13, v_add_lit by lia.
      stepn F_18430 D_18430. rewrite v_addi_lit by lia.
      stepn F_18434 D_18434. rewrite v_addi_lit by lia.
      stepn F_18438 D_18438. rewrite v_srli_lit by lia.
      replace (start + 16 * off - M + -16) with (PP - M - 16) by lia. rewrite qq_eq.
      stepn F_1843c D_1843c. rewrite v_subw_lit by lia.
      stb F_18440 D_18440 (Z_to_bv 64 (start + 16 * off - 3)) (Z_to_bv 8 idx)
        ltac:(apply sb_byte_small; lia) ltac:(sok).
      sth F_18444 D_18444 (Z_to_bv 64 (start + 16 * off - 2)) (Z_to_bv 64 QQ) ltac:(sok).
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
      msteps RSEGS (mkst regs (0x18448%bv : word) (mE1 idx stride start off m) rom)
                   (mkst regs' (0x1847c%bv : word) (mE idx n stride start off m) rom)
      /\ keeps_cs regs regs'
      /\ getr regs' 10 = Z_to_bv 64 (res_code RR)
      /\ (forall r : reg, r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> getr regs' r = getr regs r).
  Proof.
    intros regs m R16 R10 R12 R14 Gm. facts.
    destruct (Z.eq_dec RR 0) as [Hr0|Hr0].
    { eexists. split; [|split; [|split]].
      - cbv delta [mE] beta zeta. rewrite (proj2 (Z.eqb_eq _ _) Hr0).
        stepb_tk F_18448 D_18448 ltac:(rewrite R16, c_eq_lit by lia; apply Z.eqb_eq; exact Hr0).
        stepn F_18470 D_18470. stepn F_18474 D_18474.
        apply mst_refl.
      - solve_kcs.
      - gres. unfold res_code. rewrite Hr0. reflexivity.
      - intros r ? ? ?. gsym. }
    destruct (Z.lt_ge_cases RR 5) as [Hr5|Hr5].
    { eexists. split; [|split; [|split]].
      - cbv delta [mE] beta zeta. rewrite (proj2 (Z.eqb_neq _ _) Hr0), (proj2 (Z.ltb_lt _ _) Hr5).
        stepb_ft F_18448 D_18448 ltac:(rewrite R16, c_eq_lit by lia; apply Z.eqb_neq; exact Hr0).
        stepn F_1844c D_1844c. rewrite R10, R12, v_subw_lit by lia.
        replace (EE - (n + PP)) with RR by lia.
        stepn F_18450 D_18450. rewrite v_subw_lit by lia.
        stepn F_18454 D_18454. rewrite R10, v_add_neg by lia.
        stepn F_18458 D_18458.
        stb F_1845c D_1845c (Z_to_bv 64 (start + 16 * off + n)) (Z_to_bv 8 0) ltac:(reflexivity) ltac:(sok).
        stepb_tk F_18460 D_18460 ltac:(rewrite c_lts_lit by lia; apply Z.ltb_lt; exact Hr5).
        stepn F_18478 D_18478.
        apply mst_refl.
      - solve_kcs.
      - gres. unfold res_code. rewrite (proj2 (Z.ltb_lt _ _) Hr5). reflexivity.
      - intros r ? ? ?. gsym. }
    eexists. split; [|split; [|split]].
    - cbv delta [mE] beta zeta. rewrite (proj2 (Z.eqb_neq _ _) Hr0), (proj2 (Z.ltb_ge _ _) Hr5).
      stepb_ft F_18448 D_18448 ltac:(rewrite R16, c_eq_lit by lia; apply Z.eqb_neq; exact Hr0).
      stepn F_1844c D_1844c. rewrite R10, R12, v_subw_lit by lia.
      replace (EE - (n + PP)) with RR by lia.
      stepn F_18450 D_18450. rewrite v_subw_lit by lia.
      stepn F_18454 D_18454. rewrite R10, v_add_neg by lia.
      stepn F_18458 D_18458.
      stb F_1845c D_1845c (Z_to_bv 64 (start + 16 * off + n)) (Z_to_bv 8 0) ltac:(reflexivity) ltac:(sok).
      stepb_ft F_18460 D_18460 ltac:(rewrite c_lts_lit by lia; apply Z.ltb_ge; exact Hr5).
      stb F_18464 D_18464 (Z_to_bv 64 (start + stride - 4 - 5)) (Z_to_bv 8 0) ltac:(reflexivity) ltac:(sok).
      stw F_18468 D_18468 (Z_to_bv 64 (start + stride - 4 - 4)) (Z_to_bv 64 RR) ltac:(sok).
      stepn F_1846c D_1846c.
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
      msteps RSEGS (mkst regs (0x1847c%bv : word) m rom)
                   (mkst regs' ret (mF idx n stride start off m) rom)
      /\ keeps_cs regs regs'
      /\ getr regs' 10 = Z_to_bv 64 PP.
  Proof.
    intros regs m ret R13 R10 R1 Hret Rd Gm. facts.
    assert (Hrc : 0 <= res_code RR <= 5) by (unfold res_code; destruct (RR <? 5) eqn:E; [apply Z.ltb_lt in E|]; lia).
    eexists. split; [|split].
    - cbv delta [mF] beta.
      ldbu F_1847c D_1847c ltac:(rdn_at (Z_to_bv 64 (start + 16 * off - 3)); exact Rd).
      rewrite (u8_lit idx) by lia.
      stepn F_18480 D_18480. rewrite v_andi_31, u64_lit, Z.mod_small by lia.
      stepn F_18484 D_18484. rewrite R10, v_slli_lit by lia.
      stepn F_18488 D_18488. rewrite v_or_lit by lia. rewrite lor_shift5 by lia.
      stb F_1848c D_1848c (Z_to_bv 64 (start + 16 * off - 3)) (Z_to_bv 8 (idx + 32 * res_code RR))
        ltac:(apply sb_byte_small; lia) ltac:(sok).
      stepn F_18490 D_18490. rewrite R13.
      stepret F_18494 D_18494 ret ltac:(exact R1).
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
End WithFP1.

End RefEnframe_run2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.skcms.iccprofile_info.images Require Import Plain.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import
  ListFacts PropExec CatExec CatSim SeqExec StreamExec StreamSim MmapSim StepTac Hoare WalkTac StoreOk
  Frame RefMemcpyLib AgentLib MallocDefs.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import RefEnframeArith RefEnframeBase. Import RefEnframe_run1. Import RefEnframe_run2.
From Stdlib Require Import Zify.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section WithFP1. Context {FP : PropExec.FPState}.
Section Enframe.
  Variables (mem0 : word -> option byte) (c : word) (g M W idx n h3 o16 stride start off : Z).
  Hypothesis H : efH mem0 c g M W idx n h3 o16 stride start off.

  Ltac facts :=
    pose proof (stride_facts _ _ _ _ _ _ _ _ _ _ _ _ H) as (Sge & Smod & S31);
    pose proof (off_facts _ _ _ _ _ _ _ _ _ _ _ _ H) as (O1 & O2 & O3 & O4);
    pose proof (start_facts _ _ _ _ _ _ _ _ _ _ _ _ H) as (T1 & T2 & T3 & T4 & T5);
    pose proof (Hidx _ _ _ _ _ _ _ _ _ _ _ _ H) as Gidx;
    pose proof (Hn _ _ _ _ _ _ _ _ _ _ _ _ H) as Gn.

  Local Notation PP := (start + 16 * off).
  Local Notation EE := (start + stride - 4).
  Local Notation RR := (stride - 4 - n - 16 * off).
  Local Notation QQ := (stride * idx / 16 + off).

  (* [comment removed for export] *)
  Definition memF : memT :=
    mF idx n stride start off (mE idx n stride start off (mD start off mem0)).

  Definition RGN : list (word * Z) := [(Z_to_bv 64 (start - 3), stride - 1)].

  Ltac sidez :=
    rewrite ?length_wle2, ?length_wle4; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ];
    rewrite ?u64_lit by lia; lia.
  Ltac peel := rewrite rdn_wbytes_out; [ | sidez | sidez | sidez ].
  Ltac miss := rewrite wbytes_miss; [ | sidez | sidez ].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma fm_layer : forall m a bs,
    start - 3 <= a -> a + Z.of_nat (length bs) <= start + stride - 4 ->
    frame_mod m (wbytes m (Z_to_bv 64 a) bs) RGN.
  Proof.
    intros m a bs Ha Hb. facts.
    eapply frame_mod_weaken; [| apply frame_mod_wbytes; rewrite u64_lit by lia; lia].
    intros x [Hx _]. split; [|exact I]. intros Hin. apply Hx.
    unfold in_rng in *. rewrite !u64_lit in * by lia. lia.
  Qed.

  Lemma fm_step : forall m m' a bs,
    frame_mod mem0 m RGN ->
    m' = wbytes m (Z_to_bv 64 a) bs ->
    start - 3 <= a -> a + Z.of_nat (length bs) <= start + stride - 4 ->
    frame_mod mem0 m' RGN.
  Proof.
    intros m m' a bs Hm -> Ha Hb. eapply frame_mod_trans_same; [exact Hm | apply fm_layer; assumption].
  Qed.

  Lemma frame_memF : frame_mod mem0 memF RGN.
  Proof.
    facts. unfold memF.
    assert (FD : frame_mod mem0 (mD start off mem0) RGN).
    { cbv delta [mD] beta. destruct (Z.eqb_spec off 0) as [Hz|Hz]; [apply frame_mod_refl|].
      eapply fm_step; [| reflexivity | lia | cbn [length]; lia].
      eapply fm_step; [| reflexivity | lia | rewrite length_wle2; cbn; lia].
      eapply fm_step; [apply frame_mod_refl | reflexivity | lia | cbn [length]; lia]. }
    set (m1 := mD start off mem0) in *. clearbody m1.
    assert (FE1 : frame_mod mem0 (mE1 idx stride start off m1) RGN).
    { cbv delta [mE1] beta.
      eapply fm_step; [| reflexivity | lia | rewrite length_wle2; cbn; lia].
      eapply fm_step; [exact FD | reflexivity | lia | cbn [length]; lia]. }
    assert (FE : frame_mod mem0 (mE idx n stride start off m1) RGN).
    { cbv delta [mE] beta zeta.
      destruct (Z.eqb_spec RR 0) as [Hr0|Hr0]; [exact FE1|].
      destruct (Z.ltb_spec RR 5) as [Hr5|Hr5].
      - eapply fm_step; [exact FE1 | reflexivity | lia | cbn [length]; lia].
      - eapply fm_step; [| reflexivity | lia | rewrite length_wle4; cbn; lia].
        eapply fm_step; [| reflexivity | lia | cbn [length]; lia].
        eapply fm_step; [exact FE1 | reflexivity | lia | cbn [length]; lia]. }
    cbv delta [mF] beta.
    eapply fm_step; [exact FE | reflexivity | lia | cbn [length]; lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma post_memF : enframe_post memF idx n stride start off.
  Proof.
    facts. pose proof (qq_range _ _ _ _ _ _ _ _ _ _ _ _ H) as Qr.
    pose proof (R4 _ _ _ _ _ _ _ _ _ _ _ _ H) as L4.
    assert (Hrc : 0 <= res_code RR <= 5)
      by (unfold res_code; destruct (Z.ltb_spec RR 5); lia).
    unfold memF. set (m1 := mD start off mem0).
    (* [comment removed for export] *)
    assert (M4 : m1 (Z_to_bv 64 (PP - 4)) = Some (Z_to_bv 8 0)).
    { subst m1. cbv delta [mD] beta. destruct (Z.eqb_spec off 0) as [Hz|Hz].
      - rewrite <- L4. f_equal. f_equal. lia.
      - replace (PP - 4) with (start + 16 * off - 4) by lia. apply wbytes_hit1. }
    assert (M3 : off <> 0 -> m1 (Z_to_bv 64 (start - 3)) = Some (Z_to_bv 8 224)).
    { intros Hz. subst m1. cbv delta [mD] beta. rewrite (proj2 (Z.eqb_neq _ _) Hz).
      miss. miss. apply wbytes_hit1. }
    assert (M2 : off <> 0 -> rdn RSEGS m1 (Z_to_bv 64 (start - 2)) 2
                           = Some (word_to_le_bytes 2 (Z_to_bv 64 off))).
    { intros Hz. subst m1. cbv delta [mD] beta. rewrite (proj2 (Z.eqb_neq _ _) Hz).
      peel. apply (rdn_wbytes_hit RSEGS (word_to_le_bytes 2 (Z_to_bv 64 off))). sidez. }
    clearbody m1.
    set (m2 := mE idx n stride start off m1).
    cbv delta [mF] beta.
    split.
    - (* [comment removed for export] *) miss.
      subst m2. cbv delta [mE mE1] beta zeta.
      destruct (Z.eqb_spec RR 0) as [Hr0|Hr0]; [miss; miss; exact M4|].
      destruct (Z.ltb_spec RR 5) as [Hr5|Hr5]; [miss; miss; miss; exact M4|].
      miss. miss. miss. miss. miss. exact M4.
    - (* [comment removed for export] *) apply wbytes_hit1.
    - (* [comment removed for export] *) peel.
      subst m2. cbv delta [mE mE1] beta zeta.
      destruct (Z.eqb_spec RR 0) as [Hr0|Hr0].
      + apply (rdn_wbytes_hit RSEGS (word_to_le_bytes 2 (Z_to_bv 64 QQ))). sidez.
      + destruct (Z.ltb_spec RR 5) as [Hr5|Hr5].
        * peel. apply (rdn_wbytes_hit RSEGS (word_to_le_bytes 2 (Z_to_bv 64 QQ))). sidez.
        * peel. peel. peel. apply (rdn_wbytes_hit RSEGS (word_to_le_bytes 2 (Z_to_bv 64 QQ))). sidez.
    - (* [comment removed for export] *) intros Hr. miss.
      subst m2. cbv delta [mE] beta zeta.
      destruct (Z.eqb_spec RR 0) as [Hr0|Hr0]; [lia|].
      destruct (Z.ltb_spec RR 5) as [Hr5|Hr5]; [apply wbytes_hit1|].
      miss. destruct (Z.eq_dec RR 5) as [H5|H5].
      + replace (start + stride - 4 - 5) with (PP + n) by lia. apply wbytes_hit1.
      + miss. apply wbytes_hit1.
    - (* [comment removed for export] *) intros Hr. miss.
      subst m2. cbv delta [mE] beta zeta.
      destruct (Z.eqb_spec RR 0) as [Hr0|Hr0]; [lia|].
      destruct (Z.ltb_spec RR 5) as [Hr5|Hr5]; [lia|].
      miss. replace (EE - 5) with (start + stride - 4 - 5) by lia. apply wbytes_hit1.
    - (* [comment removed for export] *) intros Hr. peel.
      subst m2. cbv delta [mE] beta zeta.
      destruct (Z.eqb_spec RR 0) as [Hr0|Hr0]; [lia|].
      destruct (Z.ltb_spec RR 5) as [Hr5|Hr5]; [lia|].
      replace (EE - 4) with (start + stride - 4 - 4) by lia.
      apply (rdn_wbytes_hit RSEGS (word_to_le_bytes 4 (Z_to_bv 64 RR))). sidez.
    - (* [comment removed for export] *) intros Hz. miss.
      subst m2. cbv delta [mE mE1] beta zeta.
      destruct (Z.eqb_spec RR 0) as [Hr0|Hr0]; [miss; miss; exact (M3 Hz)|].
      destruct (Z.ltb_spec RR 5) as [Hr5|Hr5]; [miss; miss; miss; exact (M3 Hz)|].
      miss. miss. miss. miss. miss. exact (M3 Hz).
    - (* [comment removed for export] *) intros Hz. peel.
      subst m2. cbv delta [mE mE1] beta zeta.
      destruct (Z.eqb_spec RR 0) as [Hr0|Hr0]; [peel; peel; exact (M2 Hz)|].
      destruct (Z.ltb_spec RR 5) as [Hr5|Hr5]; [peel; peel; peel; exact (M2 Hz)|].
      peel. peel. peel. peel. peel. exact (M2 Hz).
    - lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma enframe_run : forall regs rom (ret : word),
    getr regs 1 = ret -> ret_ok ret ->
    getr regs 10 = Z_to_bv 64 g -> getr regs 11 = Z_to_bv 64 idx ->
    getr regs 12 = Z_to_bv 64 n -> getr regs 13 = c ->
    exists regs',
      msteps RSEGS (mkst regs (0x18348%bv : word) mem0 rom) (mkst regs' ret memF rom)
      /\ keeps_cs regs regs'
      /\ getr regs' 10 = Z_to_bv 64 PP.
  Proof.
    intros regs rom ret R1 Hret R10 R11 R12 R13. facts.
    (* [comment removed for export] *)
    destruct (blockA_run _ _ _ _ _ _ _ _ _ _ _ _ rom H regs R10) as (r1 & RUN1 & K1 & A14 & P1).
    assert (A10 : getr r1 10 = Z_to_bv 64 g) by (rewrite P1 by discriminate; exact R10).
    assert (A11 : getr r1 11 = Z_to_bv 64 idx) by (rewrite P1 by discriminate; exact R11).
    assert (A12 : getr r1 12 = Z_to_bv 64 n) by (rewrite P1 by discriminate; exact R12).
    assert (A13 : getr r1 13 = c) by (rewrite P1 by discriminate; exact R13).
    assert (A1 : getr r1 1 = ret) by (rewrite P1 by discriminate; exact R1).
    (* [comment removed for export] *)
    destruct (blockB_run _ _ _ _ _ _ _ _ _ _ _ _ rom H r1 A10 A11 A12 A13 A14)
      as (r2 & RUN2 & K2 & (B15 & B16 & B17 & B5 & B6 & B7 & P2)).
    assert (B10 : getr r2 10 = Z_to_bv 64 g) by (rewrite P2 by discriminate; exact A10).
    assert (B11 : getr r2 11 = Z_to_bv 64 idx) by (rewrite P2 by discriminate; exact A11).
    assert (B12 : getr r2 12 = Z_to_bv 64 n) by (rewrite P2 by discriminate; exact A12).
    assert (B14 : getr r2 14 = Z_to_bv 64 stride) by (rewrite P2 by discriminate; exact A14).
    assert (B1 : getr r2 1 = ret) by (rewrite P2 by discriminate; exact A1).
    (* [comment removed for export] *)
    destruct (blockC_run _ _ _ _ _ _ _ _ _ _ _ _ rom H r2 B17 B5 B6) as (r3 & RUN3 & K3 & C17 & P3).
    assert (C10 : getr r3 10 = Z_to_bv 64 g) by (rewrite P3 by discriminate; exact B10).
    assert (C11 : getr r3 11 = Z_to_bv 64 idx) by (rewrite P3 by discriminate; exact B11).
    assert (C12 : getr r3 12 = Z_to_bv 64 n) by (rewrite P3 by discriminate; exact B12).
    assert (C14 : getr r3 14 = Z_to_bv 64 stride) by (rewrite P3 by discriminate; exact B14).
    assert (C15 : getr r3 15 = Z_to_bv 64 start) by (rewrite P3 by discriminate; exact B15).
    assert (C16 : getr r3 16 = Z_to_bv 64 M) by (rewrite P3 by discriminate; exact B16).
    assert (C1 : getr r3 1 = ret) by (rewrite P3 by discriminate; exact B1).
    (* [comment removed for export] *)
    destruct (blockD_run _ _ _ _ _ _ _ _ _ _ _ _ rom H r3 C15 C17 C10 C16) as (r4 & RUN4 & K4 & D13 & D16 & P4).
    assert (D11 : getr r4 11 = Z_to_bv 64 idx) by (rewrite P4 by discriminate; exact C11).
    assert (D12 : getr r4 12 = Z_to_bv 64 n) by (rewrite P4 by discriminate; exact C12).
    assert (D14 : getr r4 14 = Z_to_bv 64 stride) by (rewrite P4 by discriminate; exact C14).
    assert (D15 : getr r4 15 = Z_to_bv 64 start) by (rewrite P4 by discriminate; exact C15).
    assert (D1 : getr r4 1 = ret) by (rewrite P4 by discriminate; exact C1).
    set (m1 := mD start off mem0) in *.
    assert (G1 : mem_grows mem0 m1) by (subst m1; apply grows_mD).
    (* [comment removed for export] *)
    destruct (blockE1_run _ _ _ _ _ _ _ _ _ _ _ _ rom H r4 m1 D13 D15 D14 D16 D12 D11 G1)
      as (r5 & RUN5 & K5 & E10 & E12 & E14 & E16 & P5).
    assert (E13 : getr r5 13 = Z_to_bv 64 PP) by (rewrite P5 by discriminate; exact D13).
    assert (E1' : getr r5 1 = ret) by (rewrite P5 by discriminate; exact D1).
    (* [comment removed for export] *)
    destruct (blockE2_run _ _ _ _ _ _ _ _ _ _ _ _ rom H r5 m1 E16 E10 E12 E14 G1)
      as (r6 & RUN6 & K6 & F10 & P6).
    assert (F13 : getr r6 13 = Z_to_bv 64 PP) by (rewrite P6 by discriminate; exact E13).
    assert (F1 : getr r6 1 = ret) by (rewrite P6 by discriminate; exact E1').
    (* [comment removed for export] *)
    assert (G2 : mem_grows mem0 (mE idx n stride start off m1))
      by (eapply mem_grows_trans; [exact G1 | apply grows_mE]).
    destruct (blockF_run _ _ _ _ _ _ _ _ _ _ _ _ rom H r6 _ ret F13 F10 F1 Hret
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

Theorem ref_enframe :
  forall regs mem rom (ret c : word) (g M W idx n h3 o16 stride start off : Z),
    efH mem c g M W idx n h3 o16 stride start off ->
    getr regs 1 = ret -> ret_ok ret ->
    getr regs 10 = Z_to_bv 64 g -> getr regs 11 = Z_to_bv 64 idx ->
    getr regs 12 = Z_to_bv 64 n -> getr regs 13 = c ->
    exists regs' mem',
      msteps RSEGS (mkst regs (0x18348%bv : word) mem rom) (mkst regs' ret mem' rom)
      /\ keeps_cs regs regs'
      /\ getr regs' 10 = Z_to_bv 64 (start + 16 * off)
      /\ frame_mod mem mem' [(Z_to_bv 64 (start - 3), stride - 1)]
      /\ enframe_post mem' idx n stride start off.
Proof.
  intros regs mem rom ret c g M W idx n h3 o16 stride start off EH R1 Hret R10 R11 R12 R13.
  destruct (enframe_run mem c g M W idx n h3 o16 stride start off EH regs rom ret R1 Hret R10 R11 R12 R13)
    as (regs' & RUN & K & A0).
  exists regs', (memF mem idx n stride start off). split; [|split; [|split; [|split]]].
  - exact RUN.
  - exact K.
  - exact A0.
  - exact (frame_memF mem c g M W idx n h3 o16 stride start off EH).
  - exact (post_memF mem c g M W idx n h3 o16 stride start off EH).
Qed.
End WithFP1.


