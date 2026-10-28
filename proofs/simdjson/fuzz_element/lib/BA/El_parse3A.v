(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun Stdio SjModel AtpModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_stage1_kit Atp_h_defs.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2 RT_iface3 RT_iface5 RT_anndefs. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_hkit2 Sj_new. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_num_akit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_h_alloc Sj_stage2_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_fzwA Atp_setcapA Atp_activewA Atp_activeA Atp_defsA Atp_kitA Atp_h_defsA Atp_h_vkitA Atp_hkit5A Atp_hkit6A Atp_pidwA Atp_pidiA Atp_pid0A Atp_pdtorA RT_rtf Pj_rtkA Pj_lftoi1A Pj_defsA Pj_os_defsA Pj_cpsA El_defsA El_lf1A El_lf2A El_lf2bA El_costA El_phasesA El_frontA El_parsewA El_parsekA El_parseA El_parse2A.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma outside_sjw : forall a, outside EL_LIB_FP a -> outside SJ_W a.
Proof.
  intros a H. unfold EL_LIB_FP, LIB_FP, SJ_W in *. cbn [outside app] in *.
  destruct H as (_ & _ & H2 & H3 & _ & _ & _ & H7 & H8 & _). repeat split; try exact I; lia.
Qed.

Section Parse3.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC2 : rt_contracts2 RT.
Hypothesis PID : pid_cps RT sj_lib.
Hypothesis PID0 : pid0_cps RT sj_lib.
Hypothesis AFC : forall Σ m, ART RT Σ m -> cli_got_nothrow m.
Variable PMc : Model -> Prop.

Local Ltac ul := unfold FUZZ_STACK, PID_STACK in *; unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, SHB in *; lia.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Theorem el_parse_p3 : forall (Σ0 : rts RT) (m0 : mem) (X : lfA) (d : Z) (bs : list byte) (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (K : config -> Prop),
    fdfs_only PMc -> mat_stable PMc -> lfA_ok X -> rt_sp0 RT Σ0 - STACK_WIN <= lf_lo X ->
    0 < d -> Z.of_nat (length bs) < 2^26 ->
    ((exists p n, In (p, n) (rt_live RT Σ0) /\ p <= d /\ d + Z.of_nat (length bs) <= p + n) \/ (bs = [] /\ d < SEGTOP_A)) ->
    (forall p n, In (p, n) (rt_live RT Σ0) -> 0 < n) -> Z.of_nat (length (rt_live RT Σ0)) + FUZZ_LIVE <= LIVE_MAX -> FUZZ_COST <= rt_credit RT Σ0 ->
    cutG RT PMc Σ0 m0 X d bs ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 K ->
    cutP7 RT PMc Σ0 m0 X d bs ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 K.
Proof using AF RC2 PID PID0 AFC.
  intros Σ0 m0 X d bs ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 K FDO MST LK LOW D0 BSL INLV LVPOS LVB CR0 CUTG.
  unfold cutP7. intros Σ m x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x7 t3 t4 t5 t6 F fc j0 j8 j10 j15 jr h3 t j56 j176 j224 jos j528 q1 q17 q57 idx act sel A buf doc
    BASE FRl ACT SEL N10 FS VR F56 FP F176 FE F224 FO F528 BUFC CR FRM.
  pose proof BASE as (ARTg & MIg & STg & STp & FRs & FH & BS & LIB & PRES & FRSg & SPg).
  pose proof LK as [(SPR & SPA') (SPT & SPA) (LLO & LOR) (FPOS & F64 & FSEG & FLO) (FSELF & SHB0 & SHT)].
  destruct X as [usp sp' f lo]. cbn [lf_usp lf_S1 lf_F lf_lo] in *.
  pose proof (af_sp0_range RT AF Σ m ARTg) as SP0R. rewrite SPg in SP0R.
  pose proof (rc2_rt RT RC2) as RC.
  assert (EU : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; ul).
  assert (INF : In (f, 4%nat) (rt_frames RT Σ)) by (rewrite FRSg; left; reflexivity).
  pose proof (af_frames_range RT AF Σ m f 4%nat ARTg INF) as (_ & _ & _ & FLV). change (fs_size 4) with 1024 in FLV.
  pose proof (af_fshadow_apart RT AF Σ m f 4%nat ARTg INF) as (FSL & _).
  assert (SH128 : shad (f + fs_size 4) = shad f + 128) by (change (fs_size 4) with 1024; unfold shad; clear - F64 FPOS; Z.div_mod_to_equations; lia).
  rewrite SH128 in FSL. clear SH128.
  set (n := Z.of_nat (length bs)) in *. set (len := Z.of_nat (length doc)) in *. set (cap := Z.max len 32).
  set (p0 := fst (el_s0A d bs)) in *. set (l0 := snd (el_s0A d bs)) in *.

  pose proof VR as (ELS & SZC & CAPB & A0 & AH & SV & BLK).
  assert (P2 : (2 <= el_PA bs)%nat) by (unfold el_PA, atp_P; lia). pose proof (vcap_iter_inv (el_PA bs) 0 0 ltac:(lia) ltac:(lia)) as CAPI. rewrite Z.add_0_l in CAPI.
  destruct BLK as [(C0 & _)|(CP1 & A16 & APOS & ELTS)]; [exfalso; lia|].
  destruct (el_els_two d bs) as (erest & EELS & ELEN).
  destruct INLV as [(pL & kL & HinL & PL1 & PL2)|(E0 & _)]; [| exfalso; subst bs n; cbn [length] in *; lia].

  set (Lr := vblockA A (vcap_iter (el_PA bs) 0 0) (Z.of_nat (el_PA bs)) ++ rt_live RT Σ0) in *.
  assert (LVX : (buf = 0 /\ doc = [] /\ rt_live RT Σ = Lr) \/ (0 < buf /\ rt_live RT Σ = (buf, len + 64) :: Lr)).
  { destruct BUFC as [(B0 & D0' & VL)|(BP & _ & _ & _ & _ & LV)]; [left| right]; [split; [exact B0| split; [exact D0'| exact VL]]| split; [exact BP| exact LV]]. }
  assert (INCL : forall e, In e Lr -> In e (rt_live RT Σ)) by (intros e He; destruct LVX as [(_ & _ & ->)|(_ & ->)]; [exact He| right; exact He]).
  assert (INA : In (A, 16 * Z.of_nat (el_PA bs)) (rt_live RT Σ)).
  { apply INCL. subst Lr. apply in_or_app. left. unfold vblockA. destruct (Z.eqb_spec (vcap_iter (el_PA bs) 0 0) 0); [lia|]. apply ann_block_vis. }
  assert (HinL' : In (pL, kL) (rt_live RT Σ)) by (apply INCL; subst Lr; apply in_or_app; right; exact HinL).
  pose proof (af_live_range RT AF Σ m pL kL ARTg HinL') as (_ & RL1 & RL2). rewrite SPg in RL1.
  assert (LPX : lposx Lr).
  { subst Lr. apply lposx_app; [| exact (lposx_of_pos _ LVPOS)].
    unfold vblockA. destruct (vcap_iter (el_PA bs) 0 0 =? 0); [intros p' k' []| apply lposx_ann_block; lia]. }
  assert (LRLEN : Z.of_nat (length Lr) + 13 <= LIVE_MAX).
  { subst Lr. rewrite length_app. pose proof (vblockA_length A (vcap_iter (el_PA bs) 0 0) (Z.of_nat (el_PA bs))). unfold FUZZ_LIVE in LVB. lia. }
  assert (LEN : 0 <= len <= 1048512) by (destruct BUFC as [(_ & -> & _)|(_ & _ & L & _)]; subst len; cbn [length] in *; lia).
  assert (CAPR : 32 <= cap <= 2^20 + 32) by (subst cap; lia).

  assert (NCL : forall x, (f <= x < f + 1024 \/ shad f <= x < shad f + 128 \/ sp' <= x < usp) -> client_static x \/ in_live (rt_live RT Σ) x -> False).
  { intros x Hx [H|H].
    - pose proof (client_static_range _ H) as R. clear - Hx R FSEG SHB0 SPR LOW LOR SP0R. ul.
    - destruct H as (p & k & Hin & Hr). pose proof (FLV p k Hin) as Y1. pose proof (FSL p k Hin) as Y2.
      pose proof (af_live_range RT AF Σ m p k ARTg Hin) as (_ & Y3 & _). rewrite SPg in Y3. clear - Hx Hr Y1 Y2 Y3 LOW LOR SPR. ul. }
  assert (COK : forall (Σx : rts RT) mx, rt_sp0 RT Σx = rt_sp0 RT Σ0 -> stk asegs mx lo sp' -> call_ok RT Σx mx (Z_to_bv 64 sp') lo).
  { intros Σx mx SPx STx. unfold call_ok. rewrite EU, SPx. split; [exact STx|]. split; [ul|]. split; [ul|]. split; [ul| clear - SPA'; Z.div_mod_to_equations; lia]. }

  pose proof FRl as FRl'. unfold el_locals4 in FRl'.
  lazymatch type of FRl' with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?rest) =>
    change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: rest)
      with ([c0; c1; c2; c3; c4; c5; c6; c7] ++ [c8] ++ rest) in FRl' end.
  apply Sj_stage1_kit.rw_cells_app in FRl'. destruct FRl' as [FRlo FRl'].
  apply Sj_stage1_kit.rw_cells_app in FRl'. destruct FRl' as [RESC FRhi].
  cbn [cells_size csize Nat.add app] in RESC, FRhi. replace (sp' + Z.of_nat 96) with (sp' + 96) in RESC by lia.
  replace (sp' + Z.of_nat 96 + Z.of_nat 24) with (sp' + 120) in FRhi by lia.

  assert (GOAL8 : forall (Σ2 : rts RT) (m2 : mem) (r : word) (j20 : list byte) (impl ix oc ia tape sbuf : Z)
                         (u0 u1 u2 v b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word) (F2 : bvmap 5 word) (fc2 : bv 32),
    ART RT Σ2 m2 -> mem_inv asegs m2 -> stk asegs m2 lo sp' -> frm0 fc2 ->
    rt_live RT Σ2 = (ia, 1024) :: (oc, 8192) :: (ix, sc_idx cap) :: (impl, 96) :: (tape, al_tape cap) :: (sbuf, al_sbuf cap) :: rt_live RT Σ ->
    (impl mod 16 = 0 /\ ix mod 16 = 0 /\ oc mod 16 = 0 /\ ia mod 16 = 0 /\ tape mod 16 = 0 /\ sbuf mod 16 = 0) ->
    rt_frames RT Σ2 = [(f, 4%nat)] -> rt_sp0 RT Σ2 = rt_sp0 RT Σ0 -> rt_credit RT Σ0 - el_vcostA bs - 2^28 <= rt_credit RT Σ2 ->
    (forall a : word, aclient (rt_live RT Σ) [(f, 4%nat)] sp' (bv_unsigned a) -> outside [(f + 96, f + 176); (sp' + 96, sp' + 120)] (bv_unsigned a) ->
                      outside SJ_W (bv_unsigned a) -> m2 a = m a) ->
    rw_cells asegs m2 (sp' + 96) (res_cellsA (f + 120) r j20) -> bv_unsigned r < 64 -> s2a_okres tape sbuf (roundup64 (cap + 3)) (al_sbuf cap) r m2 ->
    sj_lib m2 -> pdone RT Σ2 m2 (f + 96) (rt_live RT Σ) -> pidA_st RT Σ2 m2 (f + 96) impl ix oc ia tape sbuf cap ->
    aevt RT PMc Σ2 K (MS (mkR (wz EL_PIDRET_A) (wz sp') gp (wz TPV_A) u0 u1 u2 (wz usp) (wz sp') v b1 b2 b3 b4 b5 b6 b7
                            (wz f) (wz (shad f)) (wz (f + 32)) (wz (f + 96)) (wz (f + 208)) x7 (wz f) (wz buf) (wz len) (wz (f + 120)) u3 u4 u5 u6)
                       F2 (ret_pc (wz EL_PIDRET_A)) fc2 None m2 (seg_rom asegs))).
  { intros Σ2 m2 r j20 impl ix oc ia tape sbuf u0 u1 u2 v b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F2 fc2 ART2 MI2 ST2 FRM2 LV2 MODS FRS2 SP2 CR2 AG2 RESC2 R64 OKR LIB2 PD2 PST2.
    rewrite (ret_pc_even EL_PIDRET_A) by (unfold EL_PIDRET_A; lia).
    assert (INF2 : In (f, 4%nat) (rt_frames RT Σ2)) by (rewrite FRS2; left; reflexivity).
    assert (INCL2 : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σ2)) by (intros e He; rewrite LV2; do 6 right; exact He).
    pose proof (bv_unsigned_in_range 64 r) as RR. unfold bv_modulus in RR. change (2 ^ Z.of_N 64) with (2^64) in RR.

    assert (AGF2 : forall P : Z -> Prop,
              (forall x, P x -> (sp' <= x < usp /\ ~ (sp' + 96 <= x < sp' + 120)) \/ (f <= x < f + 1016 /\ ~ (f + 96 <= x < f + 176)) \/ shad f <= x < shad f + 128) ->
              agree_on P m m2).
    { intros P HP a Ha. apply AG2.
      - destruct (HP _ Ha) as [[H1 H2]|[[H1 H2]|H]]; [left; ul| right; right; right; left| right; right; right; right];
          [exists f, 4%nat; split; [left; reflexivity| change (fs_size 4) with 1024; lia]
          | exists f, 4%nat; split; [left; reflexivity| change (fs_size 4) with 1024; unfold shad in *; Z.div_mod_to_equations; lia]].
      - cbn [outside]. destruct (HP _ Ha) as [[H1 H2]|[[H1 H2]|H1]];
          [clear - H1 H2 FLO LOR SHT SPR FSELF| clear - H1 H2 FLO LOR SHT SPR FSELF| clear - H1 FLO LOR SHT SPR FSELF]; (split; [| split; [| exact I]]); ul.
      - unfold SJ_W. cbn [outside]. destruct (HP _ Ha) as [[H1 H2]|[[H1 H2]|H1]];
          [clear - H1 FSEG SHB0 LLO LOR SPR| clear - H1 FSEG SHB0 LLO LOR SPR| clear - H1 FSEG SHB0 LLO LOR SPR]; (repeat split; try exact I); ul. }
    assert (AGL2 : forall P : Z -> Prop, (forall x, P x -> in_live (rt_live RT Σ) x) -> agree_on P m m2).
    { intros P HP a Ha. destruct (HP _ Ha) as (p & k & Hin & Hr). pose proof (af_live_range RT AF Σ m p k ARTg Hin) as (_ & Y3 & Y4). rewrite SPg in Y3.
      apply AG2; [right; right; left; exists p, k; split; [exact Hin| exact Hr]| |].
      - cbn [outside]. pose proof (FLV p k Hin). clear - H Hr Y3 LOW LOR SPR. split; [lia|]. split; [ul| exact I].
      - unfold SJ_W. cbn [outside]. clear - Hr Y4. unfold SEGTOP_A in *. repeat split; try exact I; lia. }
    assert (LIB2' : el_libA m2).
    { apply (el_libA_pid m m2 LIB LIB2). intros a [Ha Ho]. pose proof (el_lib_rng_static _ Ha) as [CS _]. apply AG2; [right; left; exact CS| | exact Ho].
      cbn [outside]. split; [| split; [| exact I]]; intros E; exact (NCL (bv_unsigned a) ltac:(clear - E SPR; lia) (or_introl CS)). }
    assert (FS2 : rw_cells asegs m2 (shad f) (el_shadowA 0 0 0 (-8) t)).
    { eapply rw_cells_agree_nw; [exact FS|]. apply AGF2. intros x Hx. rewrite el_shadowA_size in Hx. right; right. lia. }
    assert (FE2 : rw_cells asegs m2 (f + 208) [C8 (wz 0); C8 (wz 0)]).
    { eapply rw_cells_agree_nw; [exact FE|]. apply AGF2. intros x Hx. cbn [cells_size csize Nat.add] in Hx. right; left. split; lia. }
    lazymatch type of FRlo with rw_cells _ _ _ ?cs =>
      assert (FRlo2 : rw_cells asegs m2 sp' cs) by (eapply rw_cells_agree_nw; [exact FRlo|]; apply AGF2; intros x Hx; cbn [cells_size csize Nat.add] in Hx; left; split; lia) end.

    pose proof (al_sbuf_bounds cap ltac:(lia)) as RG1. pose proof (al_tape_bounds cap ltac:(lia)) as RG2. pose proof (sc_idx_bounds cap ltac:(lia)) as RG3.
    assert (INT : In (tape, al_tape cap) (rt_live RT Σ2)) by (rewrite LV2; do 4 right; left; reflexivity).
    assert (INS : In (sbuf, al_sbuf cap) (rt_live RT Σ2)) by (rewrite LV2; do 5 right; left; reflexivity).
    assert (INM : In (impl, 96) (rt_live RT Σ2)) by (rewrite LV2; do 3 right; left; reflexivity).
    pose proof (af_frames_range RT AF Σ2 m2 f 4%nat ART2 INF2) as (_ & _ & _ & FLV2). change (fs_size 4) with 1024 in FLV2.
    assert (BUFR : 0 <= buf < 2^63) by (destruct LVX as [(-> & _)|(BP & LV)]; [lia|]; pose proof (af_live_range RT AF Σ m buf (len + 64) ARTg ltac:(rewrite LV; left; reflexivity)) as (_ & Y & _); clear - BP Y SP0R SPg; rewrite SPg in Y; ul).

    assert (FING : forall (mx : mem) (Σ' : rts RT) (m' : mem) (ra' a0' a1' : word) (t0' t1' t2' a2' a3' a4' a5' a6' a7' x9 x10 t3' t4' t5' t6' : word) (F' : bvmap 5 word),
      ART RT Σ2 mx -> mem_inv asegs mx ->
      (forall a : word, aclient (rt_live RT Σ2) [(f, 4%nat)] sp' (bv_unsigned a) -> ~ (f + 208 <= bv_unsigned a < f + 224) -> mx a = m2 a) ->
      rw_cells asegs mx (f + 208) (if bv_eqb r (wz 0) then [C8 (wz (f + 120)); C8 (wz 1)] else [C8 (wz 0); C8 (wz 0)]) ->
      ART RT Σ' m' -> mem_inv asegs m' -> stk asegs m' lo sp' ->
      rt_live RT Σ' = (ia, 1024) :: (oc, 8192) :: (ix, sc_idx cap) :: (impl, 96) :: (tape, al_tape cap) :: (sbuf, al_sbuf cap) :: Lr ->
      rt_frames RT Σ' = [(f, 4%nat)] -> rt_sp0 RT Σ' = rt_sp0 RT Σ0 -> rt_credit RT Σ' = rt_credit RT Σ2 ->
      rt_pres (rt_live RT Σ') [(f, 4%nat)] sp' mx m' -> pdone RT Σ' m' (f + 96) Lr ->
      aevt RT PMc Σ' K (MS (mkR ra' (wz sp') gp (wz TPV_A) t0' t1' t2' (wz usp) (wz sp') a0' a1' a2' a3' a4' a5' a6' a7'
                              (wz f) (wz (shad f)) (wz (f + 32)) (wz (f + 96)) (wz (f + 208)) (wz (bv_unsigned r)) (wz f) x9 x10 (wz (f + 120)) t3' t4' t5' t6')
                         F' (wz (el_gate_pcA r)) fc2 None m' (seg_rom asegs))).
    { intros mx Σ' m' ra' a0' a1' t0' t1' t2' a2' a3' a4' a5' a6' a7' x9 x10 t3' t4' t5' t6' F' ARTx MIx AGx FEx ART' MI' ST' LV' FRS' SP' CR' PRES' PD'.
      assert (INCL' : forall e, In e Lr -> In e (rt_live RT Σ')) by (intros e He; rewrite LV'; do 6 right; exact He).

      assert (AGFx : forall P : Z -> Prop,
                (forall x, P x -> (sp' <= x < usp /\ ~ (sp' + 96 <= x < sp' + 120)) \/ (f <= x < f + 1016 /\ ~ (f + 96 <= x < f + 176) /\ ~ (f + 208 <= x < f + 224))
                                  \/ shad f <= x < shad f + 128) -> agree_on P m mx).
      { intros P HP. eapply agree_trans; [apply AGF2; intros x Hx; destruct (HP _ Hx) as [H|[(H1 & H2 & H3)|H]]; [left; exact H| right; left; split; [exact H1| exact H2]| right; right; exact H]|].
        intros a Ha. destruct (HP _ Ha) as [[H1 H2]|[(H1 & H2 & H3)|H1]].
        - apply AGx; [left; ul| clear - H1 FLO LOR SPR; ul].
        - apply AGx; [right; right; right; left; exists f, 4%nat; split; [left; reflexivity| change (fs_size 4) with 1024; lia]| exact H3].
        - apply AGx; [right; right; right; right; exists f, 4%nat; split; [left; reflexivity| change (fs_size 4) with 1024; unfold shad in *; Z.div_mod_to_equations; lia]| clear - H1 FSELF; lia]. }
      assert (AGLx : forall P : Z -> Prop, (forall x, P x -> in_live (rt_live RT Σ) x) -> agree_on P m mx).
      { intros P HP. eapply agree_trans; [apply AGL2; exact HP|]. intros a Ha. destruct (HP _ Ha) as (p & k & Hin & Hr).
        apply AGx; [right; right; left; exists p, k; split; [exact (INCL2 _ Hin)| exact Hr]|]. pose proof (FLV p k Hin). clear - H Hr. lia. }
      assert (AG2x : forall P : Z -> Prop, (forall x, P x -> aclient (rt_live RT Σ2) [(f, 4%nat)] sp' x /\ ~ (f + 208 <= x < f + 224)) -> agree_on P m2 mx).
      { intros P HP a Ha. destruct (HP _ Ha) as [H1 H2]. exact (AGx a H1 H2). }

      assert (AGP : forall P : Z -> Prop,
                (forall x, P x -> (sp' <= x < USTACK_TOP) \/ (f <= x < f + 1016) \/ (shad f <= x < shad f + 128) \/ client_static x \/ in_live (rt_live RT Σ') x) -> agree_on P mx m').
      { intros P HP a Ha. apply PRES'. destruct (HP _ Ha) as [H|[H|[H|[H|H]]]].
        - left. exact H.
        - right; right; right; left. exists f, 4%nat. split; [left; reflexivity| change (fs_size 4) with 1024; lia].
        - right; right; right; right. exists f, 4%nat. split; [left; reflexivity| change (fs_size 4) with 1024; unfold shad in *; Z.div_mod_to_equations; lia].
        - right; left. exact H.
        - right; right; left. exact H. }
      assert (AGA : forall P : Z -> Prop,
                (forall x, P x -> (sp' <= x < usp /\ ~ (sp' + 96 <= x < sp' + 120)) \/ (f <= x < f + 1016 /\ ~ (f + 96 <= x < f + 176) /\ ~ (f + 208 <= x < f + 224))
                                  \/ shad f <= x < shad f + 128) -> agree_on P m m').
      { intros P HP. eapply agree_trans; [apply AGFx; exact HP|]. apply AGP. intros x Hx. destruct (HP _ Hx) as [[H _]|[(H & _)|H]]; [left; clear - H SPT SPR; ul| right; left; exact H| right; right; left; exact H]. }
      assert (AGLA : forall P : Z -> Prop, (forall x, P x -> in_live Lr x) -> agree_on P m m').
      { intros P HP. eapply agree_trans; [apply AGLx; intros x Hx; destruct (HP _ Hx) as (p & k & Hin & Hr); exists p, k; split; [exact (INCL _ Hin)| exact Hr]|].
        apply AGP. intros x Hx. do 4 right. destruct (HP _ Hx) as (p & k & Hin & Hr). exists p, k. split; [exact (INCL' _ Hin)| exact Hr]. }
      assert (SZ24 : Z.of_nat (cells_size (res_cellsA (f + 120) r j20)) = 24) by (unfold res_cellsA; destruct (bv_eqb r (Z_to_bv 64 0)); reflexivity).
      assert (RESC' : rw_cells asegs m' (sp' + 96) (res_cellsA (f + 120) r j20)).
      { eapply rw_cells_agree_nw; [exact RESC2|]. rewrite SZ24. eapply agree_trans.
        - apply AG2x. intros x Hx. split; [left; clear - Hx SPT SPR; ul| clear - Hx FLO LOR SPR; ul].
        - apply AGP. intros x Hx. left. clear - Hx SPT SPR. ul. }

      lazymatch type of FRlo with rw_cells _ _ _ ?cs =>
        assert (FRloM : rw_cells asegs m' sp' cs) by (eapply rw_cells_agree_nw; [exact FRlo|]; apply AGA; intros x Hx; cbn [cells_size csize Nat.add] in Hx; left; split; lia) end.
      lazymatch type of FRhi with rw_cells _ _ _ ?cs =>
        assert (FRhiM : rw_cells asegs m' (sp' + 120) cs) by (eapply rw_cells_agree_nw; [exact FRhi|]; apply AGA; intros x Hx; cbn [cells_size csize Nat.add] in Hx; left; split; lia) end.
      rewrite Z_to_bv_bv_unsigned.
      eapply (CUTG Σ' m' ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x9 x10 t3' t4' t5' t6' F' fc2 j0 j8 j10 j15 h3 t j56 j176 j224 jos j528 j20
                 idx act sel A impl ix oc ia tape sbuf cap r); cbn [lf_usp lf_S1 lf_F lf_lo].
      - unfold el_baseA. cbn [lf_usp lf_S1 lf_F lf_lo]. split; [exact ART'|]. split; [exact MI'|]. split; [exact ST'|].
        split; [eapply stk_agree_nw; [exact STp|]; apply AGA; intros x Hx; cbv beta in Hx; left; split; lia|].
        split; [eapply rw_cells_agree_nw; [exact FRs|]; apply AGA; intros x Hx; unfold fa_saved in Hx; cbn [cells_size csize Nat.add] in Hx; left; split; lia|].
        split; [eapply rw_cells_agree_nw; [exact FH|]; apply AGA; intros x Hx; unfold fz_hdr in Hx; cbn [cells_size csize Nat.add] in Hx; right; left; repeat split; lia|].
        split; [apply (bytes_at_agree asegs m m' _ _ BS); apply AGLA; intros x Hx; cbv beta in Hx; exists pL, kL; split; [subst Lr; apply in_or_app; right; exact HinL| subst n; lia]|].
        split; [apply (el_libA_agree m2 m' LIB2'); eapply agree_trans;
                 [apply AG2x; intros x Hx; pose proof (el_lib_rng_static x Hx) as [CS R]; split; [right; left; exact CS| clear - R FSEG; unfold SEGTOP_A in *; lia]
                 | apply AGP; intros x Hx; do 3 right; left; exact (proj1 (el_lib_rng_static x Hx))]|].
        split; [| split; [exact FRS'| exact SP']].
        intros a Ha Ho. rewrite <- (PRES a Ha Ho).
        assert (E2 : m2 a = m a).
        { apply AG2; [| | exact (outside_sjw _ Ho)].
          - apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; apply INCL; subst Lr; apply in_or_app; right; exact He| intros e []| lia].
          - cbn [outside]. destruct Ha as [H|[H|[H|[H|H]]]].
            + clear - H FLO LOR SPR. split; [ul| split; [lia| exact I]].
            + split; [| split; [| exact I]]; intros E; exact (NCL (bv_unsigned a) ltac:(clear - E SPR; lia) (or_introl H)).
            + assert (IL : in_live (rt_live RT Σ) (bv_unsigned a)) by (destruct H as (p & k & Hin & Hr); exists p, k; split; [apply INCL; subst Lr; apply in_or_app; right; exact Hin| exact Hr]).
              split; [| split; [| exact I]]; intros E; exact (NCL (bv_unsigned a) ltac:(clear - E SPR; lia) (or_intror IL)).
            + destruct H as (? & ? & [] & _).
            + destruct H as (? & ? & [] & _). }
        rewrite <- E2. transitivity (mx a).
        { apply (AGP (fun x => x = bv_unsigned a)); [| reflexivity]. intros x ->.
          destruct Ha as [H|[H|[H|[H|H]]]]; [left; clear - H SPR; ul| do 3 right; left; exact H| do 4 right| destruct H as (? & ? & [] & _)| destruct H as (? & ? & [] & _)].
          destruct H as (p & k & Hin & Hr). exists p, k. split; [apply INCL'; subst Lr; apply in_or_app; right; exact Hin| exact Hr]. }
        { apply AGx; [apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; apply INCL2, INCL; subst Lr; apply in_or_app; right; exact He| intros e []| lia]|].
          intros E. destruct Ha as [H|[H|[H|[H|H]]]]; [clear - H E FLO LOR SPR; ul| exact (NCL (bv_unsigned a) ltac:(clear - E SPR; lia) (or_introl H))| | destruct H as (? & ? & [] & _)| destruct H as (? & ? & [] & _)].
          refine (NCL (bv_unsigned a) ltac:(clear - E SPR; lia) (or_intror _)). destruct H as (p & k & Hin & Hr); exists p, k; split; [apply INCL; subst Lr; apply in_or_app; right; exact Hin| exact Hr]. }
      -
        unfold el_localsG. cbn [lf_usp lf_S1 lf_F lf_lo].
        apply Sj_stage1_kit.rw_cells_app. split; [exact FRloM|].
        cbn [cells_size csize Nat.add]. replace (sp' + Z.of_nat 96) with (sp' + 96) by lia.
        apply Sj_stage1_kit.rw_cells_app. split; [exact RESC'|].
        rewrite SZ24. replace (sp' + 96 + 24) with (sp' + 120) by lia. exact FRhiM.
      - exact ACT. - exact SEL. - exact R64.
      - eapply rw_cells_agree_nw; [exact FS|]. apply AGA. intros x Hx. rewrite el_shadowA_size in Hx. right; right. lia.
      - split; [exact ELS|]. split; [exact SZC|]. split; [exact CAPB|]. split; [exact A0|]. split; [exact AH|]. split; [| right; split; [exact CP1|]; split; [exact A16|]; split; [exact APOS|]].
        + eapply rw_cells_agree_nw; [exact SV|]. apply AGA. intros x Hx. cbn [cells_size csize Nat.add] in Hx. right; left. repeat split; lia.
        + eapply rw_cells_agree_nw; [exact ELTS|]. apply AGLA. intros x Hx. rewrite velts_size, ELEN in Hx. exists A, (16 * Z.of_nat (el_PA bs)).
          split; [subst Lr; apply in_or_app; left; unfold vblockA; destruct (Z.eqb_spec (vcap_iter (el_PA bs) 0 0) 0); [lia| apply ann_block_vis]| lia].
      - eapply rw_cells_agree_nw; [exact F56|]. apply AGA. intros x Hx. cbn [cells_size csize Nat.add] in Hx. right; left. repeat split; lia.
      - exact PD'.
      - apply (pidA_st_xfer RT Σ2 Σ' m2 m' (f + 96) impl ix oc ia tape sbuf cap PST2 ART2 ltac:(rewrite FRS', FRS2; reflexivity) ltac:(rewrite LV'; do 3 right; left; reflexivity)).
        eapply agree_trans; [apply AG2x| apply AGP]; intros x [Hx|[Hx|Hx]].
        + split; [right; right; right; left; exists f, 4%nat; split; [left; reflexivity| change (fs_size 4) with 1024; lia]| lia].
        + replace (shad (f + 96)) with (shad f + 12) in Hx by (unfold shad; clear - F64 FPOS; Z.div_mod_to_equations; lia).
          split; [right; right; right; right; exists f, 4%nat; split; [left; reflexivity| change (fs_size 4) with 1024; unfold shad in *; Z.div_mod_to_equations; lia]|].
          clear - Hx FSELF. lia.
        + split; [right; right; left; exists impl, 96; split; [exact INM| lia]|]. pose proof (FLV2 impl 96 INM) as Y. clear - Y Hx. lia.
        + right; left. lia.
        + replace (shad (f + 96)) with (shad f + 12) in Hx by (unfold shad; clear - F64 FPOS; Z.div_mod_to_equations; lia). right; right; left. lia.
        + do 4 right. exists impl, 96. split; [rewrite LV'; do 3 right; left; reflexivity| lia].
      - apply (s2a_okres_agree (fun x => (tape <= x < tape + al_tape cap) \/ (sbuf <= x < sbuf + al_sbuf cap)) m2 m'); [| intros x Hx; left; unfold al_tape in *; lia| intros x Hx; right; lia| exact OKR].
        eapply agree_trans; [apply AG2x| apply AGP]; intros x Hx.
        + destruct Hx as [Hx|Hx]; (split; [right; right; left| ]); [exists tape, (al_tape cap); split; [exact INT| lia]| pose proof (FLV2 _ _ INT) as Y; clear - Y Hx; lia
            | exists sbuf, (al_sbuf cap); split; [exact INS| lia]| pose proof (FLV2 _ _ INS) as Y; clear - Y Hx; lia].
        + do 4 right. destruct Hx as [Hx|Hx]; [exists tape, (al_tape cap)| exists sbuf, (al_sbuf cap)]; rewrite LV'.
          * split; [do 4 right; left; reflexivity| lia]. * split; [do 5 right; left; reflexivity| lia].
      - exact CAPR.
      - eapply rw_cells_agree_nw; [exact F176|]. apply AGA. intros x Hx. cbn [cells_size csize Nat.add] in Hx. right; left. repeat split; lia.
      - eapply rw_cells_agree_nw; [exact FEx|]. apply AGP. intros x Hx. right; left. destruct (bv_eqb r (wz 0)); cbn [cells_size csize Nat.add] in Hx; lia.
      - eapply rw_cells_agree_nw; [exact F224|]. apply AGA. intros x Hx. cbn [cells_size csize Nat.add] in Hx. right; left. repeat split; lia.
      - eapply rw_cells_agree_nw; [exact FO|]. apply AGA. intros x Hx. cbn [cells_size csize Nat.add] in Hx. right; left. repeat split; lia.
      - eapply rw_cells_agree_nw; [exact F528|]. apply AGA. intros x Hx. cbn [cells_size csize Nat.add] in Hx. right; left. repeat split; lia.
      - exact LV'.
      - exact MODS.
      - rewrite CR'. exact CR2.
      - exact FRM2. }

    assert (GN : forall (mx : mem) (ra' a0' a1' t0' t1' t2' a2' a3' a4' a5' a6' a7' x9 x10 t3' t4' t5' t6' : word) (F' : bvmap 5 word),
      buf = 0 -> ART RT Σ2 mx -> mem_inv asegs mx -> stk asegs mx lo sp' ->
      (forall a : word, aclient (rt_live RT Σ2) [(f, 4%nat)] sp' (bv_unsigned a) -> ~ (f + 208 <= bv_unsigned a < f + 224) -> mx a = m2 a) ->
      rw_cells asegs mx (f + 208) (if bv_eqb r (wz 0) then [C8 (wz (f + 120)); C8 (wz 1)] else [C8 (wz 0); C8 (wz 0)]) ->
      aevt RT PMc Σ2 K (MS (mkR ra' (wz sp') gp (wz TPV_A) t0' t1' t2' (wz usp) (wz sp') a0' a1' a2' a3' a4' a5' a6' a7'
                              (wz f) (wz (shad f)) (wz (f + 32)) (wz (f + 96)) (wz (f + 208)) (wz (bv_unsigned r)) (wz f) x9 x10 (wz (f + 120)) t3' t4' t5' t6')
                         F' (wz (el_gate_pcA r)) fc2 None mx (seg_rom asegs))).
    { intros mx ra' a0' a1' t0' t1' t2' a2' a3' a4' a5' a6' a7' x9 x10 t3' t4' t5' t6' F' B0 ARTx MIx STx AGx FEx.
      destruct LVX as [(_ & _ & LV)|(BP & _)]; [| exfalso; lia].
      apply (FING mx Σ2 mx ra' a0' a1' t0' t1' t2' a2' a3' a4' a5' a6' a7' x9 x10 t3' t4' t5' t6' F' ARTx MIx AGx FEx ARTx MIx STx ltac:(rewrite LV2, LV; reflexivity) FRS2 SP2 eq_refl ltac:(intros a _; reflexivity)).
      rewrite <- LV. apply (pdone_fp RT Σ2 Σ2 m2 mx (f + 96) _ PD2 eq_refl eq_refl). intros a Ha. apply AGx; destruct Ha as [Hx|[Hx|(q & k & Hin & Hx)]].
      * right; right; right; left; exists f, 4%nat; split; [left; reflexivity| change (fs_size 4) with 1024; lia].
      * replace (shad (f + 96)) with (shad f + 12) in Hx by (unfold shad; clear - F64 FPOS; Z.div_mod_to_equations; lia).
        right; right; right; right; exists f, 4%nat; split; [left; reflexivity| change (fs_size 4) with 1024; unfold shad in *; Z.div_mod_to_equations; lia].
      * right; right; left; exists q, k; split; [exact Hin| exact Hx].
      * lia.
      * replace (shad (f + 96)) with (shad f + 12) in Hx by (unfold shad; clear - F64 FPOS; Z.div_mod_to_equations; lia). clear - Hx FSELF; lia.
      * pose proof (FLV2 q k Hin) as Y. clear - Y Hx. lia. }
    assert (GD : forall (mx : mem) (a1' t0' t1' t2' a2' a3' a4' a5' a6' a7' x10 t3' t4' t5' t6' : word) (F' : bvmap 5 word),
      0 < buf -> ART RT Σ2 mx -> mem_inv asegs mx -> stk asegs mx lo sp' ->
      (forall a : word, aclient (rt_live RT Σ2) [(f, 4%nat)] sp' (bv_unsigned a) -> ~ (f + 208 <= bv_unsigned a < f + 224) -> mx a = m2 a) ->
      rw_cells asegs mx (f + 208) (if bv_eqb r (wz 0) then [C8 (wz (f + 120)); C8 (wz 1)] else [C8 (wz 0); C8 (wz 0)]) ->
      aevt RT PMc Σ2 K (MS (mkR (wz 0xb1a74) (wz sp') gp (wz TPV_A) t0' t1' t2' (wz usp) (wz sp') (wz buf) a1' a2' a3' a4' a5' a6' a7'
                              (wz f) (wz (shad f)) (wz (f + 32)) (wz (f + 96)) (wz (f + 208)) (wz (bv_unsigned r)) (wz f) (wz buf) x10 (wz (f + 120)) t3' t4' t5' t6')
                         F' (wz e_delarr) fc2 None mx (seg_rom asegs))).
    { intros mx a1' t0' t1' t2' a2' a3' a4' a5' a6' a7' x10 t3' t4' t5' t6' F' BP ARTx MIx STx AGx FEx.
      destruct LVX as [(B0 & _)|(_ & LV)]; [exfalso; lia|].
      assert (INB : In (buf, len + 64) (rt_live RT Σ2)) by (apply INCL2; rewrite LV; left; reflexivity).
      assert (UOK : unwind_ok (wz 0xb1a74) (wz usp) (wz sp')) by (unfold unwind_ok; rewrite EU, !unsigned_lit by ul; right; right; lia).
      eapply (aevt_delarr RT AF RC PMc FDO MST Σ2 K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F' fc2 mx buf (len + 64) lo
                INB eq_refl ARTx MIx (COK Σ2 mx SP2 STx) UOK).
      intros Σ4 v4 w0 w1 w2 g1 g2 g3 g4 g5 g6 g7 w3 w4 w5 w6 F4 m4 (ART4 & MI4 & ST4) PRES4 LV4 FRS4 SP4 CR4. rewrite EU in ST4, PRES4.
      rewrite (ret_pc_even 0xb1a74) by lia. rewrite SP2 in SP4.
      assert (POS3 : 0 < sc_idx cap /\ 0 < al_tape cap /\ 0 < al_sbuf cap) by (clear - RG1 RG2 RG3; lia).
      assert (PDx : pdone RT Σ2 mx (f + 96) ((buf, len + 64) :: Lr)).
      { rewrite <- LV. apply (pdone_fp RT Σ2 Σ2 m2 mx (f + 96) _ PD2 eq_refl eq_refl). intros a Ha. apply AGx; destruct Ha as [Hx|[Hx|(q & k & Hin & Hx)]].
        * right; right; right; left; exists f, 4%nat; split; [left; reflexivity| change (fs_size 4) with 1024; lia].
        * replace (shad (f + 96)) with (shad f + 12) in Hx by (unfold shad; clear - F64 FPOS; Z.div_mod_to_equations; lia).
          right; right; right; right; exists f, 4%nat; split; [left; reflexivity| change (fs_size 4) with 1024; unfold shad in *; Z.div_mod_to_equations; lia].
        * right; right; left; exists q, k; split; [exact Hin| exact Hx].
        * lia.
        * replace (shad (f + 96)) with (shad f + 12) in Hx by (unfold shad; clear - F64 FPOS; Z.div_mod_to_equations; lia). clear - Hx FSELF; lia.
        * pose proof (FLV2 q k Hin) as Y. clear - Y Hx. lia. }
      destruct (pdone_free RT AF Σ2 Σ4 mx m4 (f + 96) buf (len + 64) sp' ia oc ix impl tape sbuf 1024 8192 (sc_idx cap) 96 (al_tape cap) (al_sbuf cap) Lr
                  PDx ARTx ltac:(rewrite LV2, LV; reflexivity) eq_refl eq_refl (proj1 POS3) eq_refl (proj1 (proj2 POS3)) (proj2 (proj2 POS3)) ltac:(clear - LEN; lia)
                  LPX LV4 FRS4 PRES4) as [PD4 LV4'].

      apply (aevt_evt RT AF PMc MST).
      eapply evt_cut; [eapply (pw_walk9 usp sp' f (bv_unsigned r) (wz 0xb1a74) gp w0 w1 w2 v4 g1 g2 g3 g4 g5 g6 g7 (wz (f + 208)) (wz f) (wz buf) x10 (wz (f + 120)) w3 w4 w5 w6 F4 fc2 m4 ltac:(lia) MI4)|].
      cbv beta. intros ms9 <-. apply evt_done. unfold pw_st.
      replace (el_gate_pcA (Z_to_bv 64 (bv_unsigned r))) with (el_gate_pcA r) by (rewrite Z_to_bv_bv_unsigned; reflexivity).
      exact (FING mx Σ4 m4 (wz 0xb1a74) v4 g1 w0 w1 w2 g2 g3 g4 g5 g6 g7 (wz buf) x10 w3 w4 w5 w6 F4 ARTx MIx AGx FEx ART4 MI4 ST4 LV4' (eq_trans FRS4 FRS2) SP4 CR4 ltac:(rewrite <- FRS2; exact PRES4) PD4). }

    apply (aevt_evt RT AF PMc MST).
    assert (RESX : exists pre, cells_size pre = 16%nat /\ rw_cells asegs m2 (sp' + 96) (pre ++ C4 (wz (bv_unsigned r)) :: [CB 4 j20])).
    { unfold res_cellsA in RESC2. destruct (bv_eqb r (wz 0)) eqn:ER.
      - exists [C8 (wz (f + 120)); C8 (wz 1)]. split; [reflexivity|]. unfold bv_eqb in ER. rewrite (unsigned_lit 0) in ER by (clear; lia). apply Z.eqb_eq in ER. rewrite ER. exact RESC2.
      - exists [CB 16 (repeat z8 16)]. split; [reflexivity|]. rewrite Z_to_bv_bv_unsigned. exact RESC2. }
    destruct RESX as (rpre & RSZ & RESC2').
    lazymatch type of FRlo2 with rw_cells _ _ _ ?cs =>
      assert (FR8 : rw_cells asegs m2 sp' ((cs ++ rpre) ++ C4 (wz (bv_unsigned r)) :: [CB 4 j20]))
        by (rewrite <- app_assoc; apply Sj_stage1_kit.rw_cells_app; split; [exact FRlo2|]; cbn [cells_size csize Nat.add]; replace (sp' + Z.of_nat 96) with (sp' + 96) by lia; exact RESC2')
    end.
    lazymatch type of FR8 with rw_cells _ _ _ (?pre ++ _ :: ?mid) =>
    eapply evt_cut; [eapply (pw_walk8 usp sp' f (bv_unsigned r) buf (wz EL_PIDRET_A) gp u0 u1 u2 v b1 b2 b3 b4 b5 b6 b7 x7 (wz f) (wz len) u3 u4 u5 u6 pre mid F2 fc2 m2
                               FPOS ltac:(ul) ltac:(ul) ltac:(ul) ltac:(lia) ltac:(lia) ltac:(rewrite cells_size_app, RSZ; reflexivity) FR8 MI2)|]
    end.
    cbv beta. intros ms8 [(RZ & ->)|[(RNZ & B0 & ->)|(RNZ & BNZ & ->)]]; apply evt_done; unfold pw_st.
    -
      assert (ER : r = wz 0) by (rewrite <- (Z_to_bv_bv_unsigned r), RZ; reflexivity).
      assert (RB : bytes_at asegs m2 (sp' + 96) (cells_bytes [C8 (wz (f + 120)); C8 (wz 1)])).
      { pose proof RESC2 as X. rewrite ER in X. unfold res_cellsA in X. change (bv_eqb (wz 0) (wz 0)) with true in X. cbv iota in X.
        change ([C8 (wz (f + 120)); C8 (wz 1); C4 (wz 0); CB 4 j20]) with ([C8 (wz (f + 120)); C8 (wz 1)] ++ [C4 (wz 0); CB 4 j20]) in X.
        apply Sj_stage1_kit.rw_cells_app in X. destruct X as [[[_ X] _] _]. exact X. }
      assert (CSRC : checked_src RT Σ2 m2 (Z_to_bv 64 sp') lo (sp' + 96) 16).
      { split; [| right; rewrite EU; lia]. intros _. split.
        - apply (af_acc_stack RT AF Σ2 m2 (sp' + 96) 16 ART2); [rewrite SP2; ul| ul].
        - right; right; left. rewrite SP2. ul. }
      pose proof FE2 as [_ WRE]. cbn [cells_size csize Nat.add] in WRE. change (Z.of_nat 16) with 16 in WRE.
      pose proof (el_fobj_dst RT Σ2 m2 (Z_to_bv 64 sp') f (f + 208) 16 (f + 208) 16 (el_elem_fobj RT Σ2 m2 f 0 0 (-8) t FS2 FRS2 FPOS F64) ltac:(lia) FRS2 WRE
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as CDE.
      eapply (aevt_memcpyP RT RC PMc FDO MST Σ2 K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 m2 (f + 208) (sp' + 96)
                (cells_bytes [C8 (wz (f + 120)); C8 (wz 1)]) lo eq_refl eq_refl eq_refl
                ltac:(clear - FPOS FLO LOR SPT; ul) ltac:(clear - SPR SPT LLO LOR; ul) ltac:(cbn; clear; lia) RB CSRC CDE ltac:(cbn; clear - FLO LOR SPR; left; ul) ART2 MI2 (COK Σ2 m2 SP2 ST2)).
      intros y0 y1 y2 e1 e2 e3 e4 e5 e6 e7 y3 y4 y5 y6 F3 m3 (ART3 & MI3 & WM3 & ST3) PRES3 BY3. rewrite EU in ST3, PRES3.
      rewrite (ret_pc_even 0xb1a68) by lia. rewrite FRS2 in PRES3. change (Z.of_nat (length _)) with 16 in PRES3.
      assert (AG3 : forall a : word, aclient (rt_live RT Σ2) [(f, 4%nat)] sp' (bv_unsigned a) -> ~ (f + 208 <= bv_unsigned a < f + 224) -> m3 a = m2 a)
        by (intros a Ha Hn; apply (PRES3 a Ha); clear - Hn; lia).
      assert (FE3 : rw_cells asegs m3 (f + 208) (if bv_eqb r (wz 0) then [C8 (wz (f + 120)); C8 (wz 1)] else [C8 (wz 0); C8 (wz 0)])).
      { rewrite ER. change (bv_eqb (wz 0) (wz 0)) with true. cbv iota.
        split; [split; [cbn; tauto| exact BY3]|]. cbn [cells_size csize Nat.add]. exact (wr_at_transport asegs m2 m3 (f + 208) 16 WRE WM3). }

      apply (aevt_evt RT AF PMc MST).
      eapply evt_cut; [eapply (pw_walk8b usp sp' f buf (wz 0xb1a68) gp y0 y1 y2 (wz (f + 208)) e1 e2 e3 e4 e5 e6 e7 (wz (f + 208)) (wz f) (wz len) (wz (f + 120)) y3 y4 y5 y6 F3 fc2 m3 ltac:(lia) MI3)|].
      cbv beta. intros ms9 [(B0 & ->)|(BNZ & ->)]; apply evt_done; unfold pw_st.
      +
        replace EL_DISPATCH_A with (el_gate_pcA r) by (rewrite ER; reflexivity).
        replace (Z_to_bv 64 0) with (Z_to_bv 64 (bv_unsigned r)) by (rewrite RZ; reflexivity).
        apply (GN m3 (wz 0xb1a68) (wz (f + 208)) e1 y0 y1 y2 e2 e3 e4 e5 e6 e7 (wz buf) (wz len) y3 y4 y5 y6 F3 B0 ART3 MI3 ST3 AG3 FE3).
      +
        replace (Z_to_bv 64 0) with (Z_to_bv 64 (bv_unsigned r)) by (rewrite RZ; reflexivity).
        apply (GD m3 e1 y0 y1 y2 e2 e3 e4 e5 e6 e7 (wz len) y3 y4 y5 y6 F3 ltac:(lia) ART3 MI3 ST3 AG3 FE3).
    -
      replace EL_EXIT_A with (el_gate_pcA r).
      2: { unfold el_gate_pcA. replace (bv_eqb r (wz 0)) with false; [reflexivity|]. symmetry. unfold bv_eqb. rewrite (unsigned_lit 0) by lia. apply Z.eqb_neq. exact RNZ. }
      apply (GN m2 (wz EL_PIDRET_A) v b1 u0 u1 u2 b2 b3 b4 b5 b6 b7 (wz buf) (wz len) u3 u4 u5 u6 F2 B0 ART2 MI2 ST2 ltac:(intros a _ _; reflexivity)).
      replace (bv_eqb r (wz 0)) with false by (clear - RNZ; unfold bv_eqb; rewrite (unsigned_lit 0) by lia; destruct (Z.eqb_spec (bv_unsigned r) 0); [lia| reflexivity]). exact FE2.
    -
      apply (GD m2 b1 u0 u1 u2 b2 b3 b4 b5 b6 b7 (wz len) u3 u4 u5 u6 F2 ltac:(lia) ART2 MI2 ST2 ltac:(intros a _ _; reflexivity)).
      replace (bv_eqb r (wz 0)) with false by (clear - RNZ; unfold bv_eqb; rewrite (unsigned_lit 0) by lia; destruct (Z.eqb_spec (bv_unsigned r) 0); [lia| reflexivity]). exact FE2. }

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (pw_walk7 usp sp' f buf len x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (wz (f + 208)) x7 (wz f) t3 t4 t5 t6 F fc m FPOS ltac:(ul) ltac:(ul) ltac:(ul) MIg)|].
  cbv beta. intros ms7 <-. apply evt_done. unfold pw_st.
  pose proof (el_parser_fobj RT Σ m f 0 0 (-8) t FS FRSg FPOS F64) as FOBJ.
  assert (CRP : pid_costA len <= rt_credit RT Σ) by (pose proof (pid_costA_bound len LEN); pose proof (el_vcost_bound bs BSL); unfold FUZZ_COST in CR0; lia).
  destruct LVX as [(B0 & D0' & LV)|(BP & LV)].
  -
    assert (EL0 : len = 0) by (subst len; rewrite D0'; reflexivity).
    eapply (aevt_rt RT PMc Σ K _ _
             (PID0 Σ PMc (wz EL_PIDRET_A) (wz sp') gp (wz TPV_A) t0 t1 t2 (wz usp) (wz sp') (wz (sp' + 96)) (wz (f + 96)) (wz (f + 120)) (wz buf) (wz len) (wz 0) a6 a7
                (wz f) (wz (shad f)) (wz (f + 32)) (wz (f + 96)) (wz (f + 208)) x7 (wz f) (wz buf) (wz len) (wz (f + 120)) t3 t4 t5 t6 F fc m (f + 96) (sp' + 96) q1 q17 q57 jr lo
                FDO MST eq_refl eq_refl ltac:(f_equal; lia) ltac:(rewrite B0; reflexivity) ltac:(rewrite EL0; reflexivity) eq_refl eq_refl FOBJ FP ltac:(rewrite EU; lia) ltac:(ul) RESC
                ltac:(rewrite LV; exact LPX) ltac:(rewrite LV; lia) ltac:(rewrite EL0 in CRP; exact CRP) (proj1 (proj1 LIB)) ARTg MIg
                ltac:(rewrite EU; exact STg) ltac:(rewrite SPg; exact LOW) ltac:(rewrite EU; ul) ltac:(rewrite EU; ul) ltac:(rewrite EU; clear - SPA'; Z.div_mod_to_equations; lia) FRM));
      [exact FRM|].
    intros c (Σ2 & impl & ix & oc & ia & tape & sbuf & HA & LV2 & MODS & FRS2 & SP2 & CR2). eexists Σ2, _. split; [exact HA|].
    intros ms' (v & m2 & RS & (ART2 & MI2 & ST2) & PRES2 & (r & j20 & RESC2 & R64 & OKR) & LIB2 & PD2 & PST2) FRM2.
    destruct RS as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->). cbn [ms_fcsr] in FRM2.
    rewrite EU in ST2, PRES2. rewrite FRSg in FRS2, PRES2. rewrite SPg in SP2. replace (f + 96 + 24) with (f + 120) in RESC2 by lia.
    assert (EC : cap = 32) by (subst cap; rewrite EL0; reflexivity).
    apply (GOAL8 Σ2 m2 r j20 impl ix oc ia tape sbuf u0 u1 u2 v b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F2 fc2 ART2 MI2 ST2 FRM2); rewrite ?EC;
      [exact LV2| exact MODS| exact FRS2| exact SP2| pose proof (pid_costA_bound 0 ltac:(lia)); clear - H CR CR2; lia| | exact RESC2| exact R64| exact OKR| exact LIB2| exact PD2| exact PST2].
    intros a Ha Ho Hs. apply PRES2; [exact Ha|]. cbn [outside app] in Ho |- *. destruct Ho as (H1 & H2 & _). split; [lia|]. split; [lia| exact Hs].
  -
    destruct BUFC as [(B0 & _)|(_ & B16 & _ & _ & BYP & _)]; [exfalso; lia|].
    eapply (aevt_rt RT PMc Σ K _ _
             (PID Σ PMc (wz EL_PIDRET_A) (wz sp') gp (wz TPV_A) t0 t1 t2 (wz usp) (wz sp') (wz (sp' + 96)) (wz (f + 96)) (wz (f + 120)) (wz buf) (wz len) (wz 0) a6 a7
                (wz f) (wz (shad f)) (wz (f + 32)) (wz (f + 96)) (wz (f + 208)) x7 (wz f) (wz buf) (wz len) (wz (f + 120)) t3 t4 t5 t6 F fc m (f + 96) (sp' + 96) buf doc q1 q17 q57 jr lo
                FDO MST eq_refl eq_refl ltac:(f_equal; lia) eq_refl eq_refl eq_refl eq_refl (proj2 LEN) BYP ltac:(rewrite LV; left; reflexivity) B16 FOBJ FP
                ltac:(rewrite EU; lia) ltac:(ul) RESC ltac:(rewrite LV; apply lposx_cons; [lia| exact LPX]) ltac:(rewrite LV; cbn [length]; lia)
                ltac:(rewrite FRSg; cbn; unfold PID_FRAMES, FRAMES_MAX; lia) CRP (proj1 (proj1 LIB)) ARTg MIg
                ltac:(rewrite EU; exact STg) ltac:(rewrite SPg; exact LOW) ltac:(rewrite EU; ul) ltac:(rewrite EU; ul) ltac:(rewrite EU; clear - SPA'; Z.div_mod_to_equations; lia) FRM));
      [exact FRM|].
    intros c (Σ2 & impl & ix & oc & ia & tape & sbuf & HA & LV2 & MODS & FRS2 & SP2 & CR2). eexists Σ2, _. split; [exact HA|].
    intros ms' (v & m2 & RS & (ART2 & MI2 & ST2) & PRES2 & (r & j20 & RESC2 & R64 & OKR) & LIB2 & PD2 & PST2) FRM2.
    destruct RS as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->). cbn [ms_fcsr] in FRM2.
    rewrite EU in ST2, PRES2. rewrite FRSg in FRS2, PRES2. rewrite SPg in SP2. replace (f + 96 + 24) with (f + 120) in RESC2 by lia.
    fold len in LV2, OKR, PST2, CR2. fold cap in LV2, OKR, PST2.
    apply (GOAL8 Σ2 m2 r j20 impl ix oc ia tape sbuf u0 u1 u2 v b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F2 fc2 ART2 MI2 ST2 FRM2 LV2 MODS FRS2 SP2);
      [pose proof (pid_costA_bound len LEN); clear - H CR CR2; lia| | exact RESC2| exact R64| exact OKR| exact LIB2| exact PD2| exact PST2].
    intros a Ha Ho Hs. apply PRES2; [exact Ha|]. cbn [outside app] in Ho |- *. destruct Ho as (H1 & H2 & _). split; [lia|]. split; [lia| exact Hs].
Qed.
End Parse3.

Section ParseOk.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC2 : rt_contracts2 RT.
Hypothesis PID : pid_cps RT sj_lib.
Hypothesis PID0 : pid0_cps RT sj_lib.
Hypothesis AFC : forall Σ m, ART RT Σ m -> cli_got_nothrow m.

Theorem el_parse_ok : forall PMc, el_parse_cps RT PMc.
Proof using AF RC2 PID PID0 AFC.
  intros PMc Σ0 m0 X d bs ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 K FDO MST LK LOW D0 BSL INLV LVPOS LVB CR0 CUTG CUTX CUTX2.
  apply (el_parse_p1 RT AF RC2 PMc Σ0 m0 X d bs ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 K FDO MST LK LOW D0 BSL INLV LVPOS LVB CR0); [| exact CUTX2].
  apply (el_parse_p2 RT AF RC2 AFC PMc Σ0 m0 X d bs ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 K FDO MST LK LOW D0 BSL INLV LVPOS LVB CR0).
  exact (el_parse_p3 RT AF RC2 PID PID0 AFC PMc Σ0 m0 X d bs ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 K FDO MST LK LOW D0 BSL INLV LVPOS LVB CR0 CUTG).
Qed.
End ParseOk.
