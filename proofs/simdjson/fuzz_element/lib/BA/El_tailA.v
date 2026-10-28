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
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2 RT_iface3 RT_iface5. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_hkit2 Sj_new Sj_h_dtor Sj_h_deldtor. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_num_akit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_h_alloc Sj_stage2_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_fzwA Atp_setcapA Atp_activewA Atp_defsA Atp_h_defsA Atp_h_vkitA Atp_h_destroyA Atp_pidiA Atp_pdtorA RT_rtf Pj_rtkA Pj_lftoi1A Pj_defsA Pj_os_defsA Pj_cpsA El_defsA El_lf1A El_lf2A El_lf2bA El_phasesA El_frontA El_costA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition tl_st (usp sp' f : Z) (pc : Z) (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state :=
  MS (mkR ra (Z_to_bv 64 sp') gp (Z_to_bv 64 TPV_A) t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 sp') a0 a1 a2 a3 a4 a5 a6 a7
          (Z_to_bv 64 f) (Z_to_bv 64 (shad f)) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f + 96)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
     F (Z_to_bv 64 pc) fc None m (seg_rom asegs).

Lemma tl_walkD : forall (usp sp' f : Z) (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (ja jc jd : list byte) F fc (m : mem),
  0 < f -> f + 1024 < 2^63 -> SEGTOP_A <= sp' -> sp' + 152 < 2^63 ->
  rw_cells asegs m sp' [CB 96 ja; CB 8 jc; CB 48 jd] -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem),
      ms = tl_st usp sp' f ATPA_DESTROY (Z_to_bv 64 0xb1ac0) gp t0 t1 t2 (Z_to_bv 64 (sp' + 96)) a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1
      /\ munch [(sp' + 96, sp' + 104)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ rw_cells asegs m1 sp' [CB 96 ja; C8 (Z_to_bv 64 (f + 32)); CB 48 jd])
    (tl_st usp sp' f EL_EXIT2_A ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros F0 FH GLO SPH FRl MI.
  unfold tl_st, EL_EXIT2_A, ATPA_DESTROY, SEGTOP_A in *.
  pose proof (munch_refl [(sp' + 96, sp' + 104)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (ES : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; lia).
  ls. zstep. zstep.
  apply evt_done. eexists. split; [atp_st_eq_goal|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|]. eassumption.
Qed.

Lemma tl_walkX1 : forall (usp sp' f : Z) (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) (p e : Z) (h3 t : list byte) F fc (m : mem),
  0 < f -> f + 1024 < 2^63 -> 0 <= shad f -> shad f + 128 < 2^63 -> (f + 1024 <= shad f \/ shad f + 128 <= f) -> SEGTOP_A <= sp' -> sp' + 152 < 2^63 ->
  f + 1024 <= sp' -> shad f + 128 <= sp' ->
  rw_cells asegs m f (fz_hdr (C8 (Z_to_bv 64 0x41b58ab3)) (C8 (Z_to_bv 64 0x126fb)) (C8 (Z_to_bv 64 0xb1608)) h3) ->
  rw_cells asegs m (shad f) (el_shadowA 0 p e (-8) t) ->
  mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem),
      ms = tl_st usp sp' f (e_set_shadow 245) (Z_to_bv 64 0xb1aec) gp t0 t1 t2 (Z_to_bv 64 (shad f)) (Z_to_bv 64 128) a2 a3 a4 a5 a6 a7 s6 s7 (Z_to_bv 64 f) s9 s10 s11 t3 t4 t5 t6 F fc m1
      /\ munch [(f, f + 8); (shad f + 4, shad f + 7)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ rw_cells asegs m1 f (fz_hdr (C8 (Z_to_bv 64 0x45e0360e)) (C8 (Z_to_bv 64 0x126fb)) (C8 (Z_to_bv 64 0xb1608)) h3)
      /\ rw_cells asegs m1 (shad f) (el_shadowA (-8) p e (-8) t))
    (tl_st usp sp' f 0xb1ac0 ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 (Z_to_bv 64 f) s9 s10 s11 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros F0 FHI SH0 SHH SEP GLO SPH FSP SSP FH FS MI.
  unfold tl_st, fz_hdr, el_shadowA, el_shbytesA, e_set_shadow, shad, SHB, SEGTOP_A in *. cbn [map app repeat] in *.
  pose proof (munch_refl [(f, f + 8); (f / 8 + 2147450880 + 4, f / 8 + 2147450880 + 7)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (ESH : bv_unsigned (Z_to_bv 64 (f / 8 + 2147450880)) = f / 8 + 2147450880) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; lia).

  zstep. ls. ls. ls. zstep. zstep. ls.
  zstep. if_cases K; zify_cond K; [exfalso; lia|].
  zstep. zstep. zstep.
  apply evt_done. eexists. split; [atp_st_eq_goal|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|].
  split; eassumption.
Qed.

Lemma tl_walkX2 : forall (usp sp' f fl lo : Z) (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word)
    (xra xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 : word) (LC : list cell) F fc (m : mem),
  0 < f -> f + 1024 <= lo -> 0 < fl -> fl + 1 <= lo ->
  SEGTOP_A <= lo -> lo <= sp' -> cells_size LC = 152%nat -> sp' + 152 <= usp - 104 -> usp < 2^63 ->
  stk asegs m lo sp' -> rw_cells asegs m sp' LC -> stk asegs m (sp' + 152) (usp - 104) ->
  rw_cells asegs m (usp - 104) (fa_saved xra xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11) ->
  ro_cells asegs m (f + 1016) [C8 (Z_to_bv 64 fl)] -> rw_cells asegs m fl [C1 (Z_to_bv 8 1)] ->
  mem_inv asegs m ->
  evt asegs (fun ms => exists (m' : mem), ret_st xra (Z_to_bv 64 usp) gp (Z_to_bv 64 TPV_A) xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 0) m' ms
      /\ ms_fcsr ms = fc /\ munch [(fl, fl + 1)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo usp /\ rw_cells asegs m' fl [C1 (Z_to_bv 8 0)])
    (tl_st usp sp' f 0xb1aec ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 (Z_to_bv 64 f) s9 s10 s11 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros F0 FLO FL0 FLLO GLO LSP SZ LUSP SPH ST FRl STp FRs FW FLC MI.
  unfold tl_st, fa_saved, SEGTOP_A in *.
  pose proof (munch_refl [(fl, fl + 1)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (EFL : bv_unsigned (Z_to_bv 64 fl) = fl) by (apply unsigned_lit; lia).
  assert (EUS : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).

  zstep. ls. zstep. zstep. zstep.
  replace (usp - 104) with (usp + -104) in FRs by lia.
  do 13 zstep. zstep.
  replace (usp + -104) with (usp - 104) in FRs by lia.
  pose proof (stk_release asegs _ _ _ _ ST FRl ltac:(lia)) as ST1. rewrite SZ in ST1. change (Z.of_nat 152%nat) with 152 in ST1.
  pose proof (stk_merge asegs _ _ _ _ ST1 STp ltac:(lia)) as ST2.
  pose proof (stk_release asegs _ _ _ _ ST2 FRs ltac:(lia)) as ST3. cbn [cells_size csize Nat.add] in ST3.
  replace (usp - 104 + Z.of_nat 104) with usp in ST3 by lia.
  zstep.
  apply evt_done. eexists. split; [unfold ret_st; do 16 eexists; cbv delta [mkR]; reflexivity|]. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST3| eassumption].
Qed.

Lemma el_PA_ge2 : forall bs, (2 <= el_PA bs)%nat.
Proof. intros bs. unfold el_PA, atp_P. lia. Qed.

Section Tail2.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Hypothesis RC2 : rt_contracts2 RT.
Variable PMc : Model -> Prop.

Local Ltac ul := unfold FUZZ_STACK, ATPA_DESTROY_STACK in *; unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Theorem el_tail2_ok : el_tail2_cps RT PMc.
Proof using AF RC RC2.
  intros Σ0 m0 X d bs ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 crd K FDO MST LK LOW LVPOS KR.
  unfold cutX2. intros Σ m x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x6 x7 x9 x10 x11 t3 t4 t5 t6 F fc LC h3 t p e A
    ARTx MIx STx STp FRs FH LIB PRES FRSx SPx SZ FRl FS VR VL CR FRM.
  destruct LK as [(SPR & SPA') (SPT & SPA) (LLO & LOR) (FPOS & F64 & FSEG & FLO) (FSELF & SHB0 & SHT)].
  destruct X as [usp sp' f lo]. cbn [lf_usp lf_S1 lf_F lf_lo] in *.
  pose proof (af_sp0_range RT AF Σ m ARTx) as SP0R. rewrite SPx in SP0R.
  assert (EU : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; ul).
  assert (INF : In (f, 4%nat) (rt_frames RT Σ)) by (rewrite FRSx; left; reflexivity).
  assert (SHF0 : shad f = f / 8 + SHB) by reflexivity.

  pose proof VR as (ELS & SZC & CAPB & A0 & AH & SV & BLK).
  pose proof (vcap_iter_inv (el_PA bs) 0 0 ltac:(lia) ltac:(lia)) as CAPI. pose proof (el_PA_ge2 bs) as P2.

  destruct (rw_cells_forget asegs m sp' LC FRl) as [jl FRl']. rewrite SZ in FRl'. clear FRl.
  apply (rw_cells_split_CB asegs _ _ [] 152 _ [] [96; 8; 48]%nat) in FRl'; [| reflexivity]. cbn [mk_CB_cells app] in FRl'.
  lazymatch type of FRl' with rw_cells _ _ _ [CB 96 ?xa; CB 8 ?xc; CB 48 ?xd] =>
    pose proof (tl_walkD usp sp' f x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x6 x7 (wz f) x9 x10 x11 t3 t4 t5 t6 xa xc xd F fc m FPOS ltac:(ul) ltac:(ul) ltac:(ul) FRl' MIx) as WD;
    set (JL := xa) in *; set (JH := xd) in *; clearbody JL JH
  end.
  apply (aevt_evt RT AF PMc MST). eapply evt_cut; [exact WD|]. cbv beta. clear WD.
  intros ms1 (m1 & -> & MU1 & WM1 & MI1 & FRl1). apply evt_done. unfold tl_st.
  assert (AG1 : forall (P : Z -> Prop), (forall x, P x -> ~ (sp' + 96 <= x < sp' + 104)) -> agree_on P m m1).
  { intros P HP a Ha. apply MU1. cbn [outside]. split; [exact (HP _ Ha)| exact I]. }
  assert (ART1 : ART RT Σ m1).
  { apply (art_client_write RT AF Σ m m1 sp' ARTx ltac:(rewrite SPx; ul)); [| exact WM1]. apply AG1. intros x Hx E. apply Hx. left. ul. }
  assert (ST1 : stk asegs m1 lo sp') by (apply (stk_agree asegs m m1 _ _ STx); [| exact WM1]; apply AG1; intros x Hx; cbv beta in Hx; lia).

  pose proof FRl1 as FC1.
  lazymatch type of FC1 with rw_cells _ _ _ (?c0 :: ?c1 :: ?rest) => change (c0 :: c1 :: rest) with ([c0] ++ [c1] ++ rest) in FC1 end.
  apply rw_cells_app in FC1. destruct FC1 as [_ FC1]. apply rw_cells_app in FC1. destruct FC1 as [FC1 _]. cbn [cells_size csize Nat.add] in FC1.
  replace (sp' + Z.of_nat 96) with (sp' + 96) in FC1 by lia.
  assert (FOBJV : fobj RT Σ m1 (f + 32) 24).
  { split; [Z.div_mod_to_equations; lia|]. split; [lia|]. change ((24 + 7) / 8) with 3.
    split; [exists f, 4%nat; change (fs_size 4) with 1024; split; [exact INF| lia]|].
    replace (shad (f + 32)) with (shad f + 4) by (unfold shad, SHB; Z.div_mod_to_equations; lia).
    assert (FS1 : rw_cells asegs m1 (shad f) (el_shadowA 0 p e (-8) t)).
    { eapply rw_cells_agree_nw; [exact FS|]. apply AG1. intros x Hx E. rewrite el_shadowA_size in Hx. unfold shad, SHB in *. ul. }
    pose proof FS1 as XS. unfold el_shadowA, el_shbytesA in XS. cbn [map app repeat] in XS.
    lazymatch type of XS with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?d0 :: ?d1 :: ?d2 :: ?rest) =>
      change (c0 :: c1 :: c2 :: c3 :: d0 :: d1 :: d2 :: rest) with ([c0; c1; c2; c3] ++ [d0; d1; d2] ++ rest) in XS end.
    apply Sj_stage1_kit.rw_cells_app in XS. destruct XS as [_ XS]. apply Sj_stage1_kit.rw_cells_app in XS. destruct XS as [XS _].
    cbn [cells_size csize Nat.add] in XS. destruct XS as [[_ HB] _]. replace (shad f + Z.of_nat 4) with (shad f + 4) in HB by lia. exact HB. }
  assert (VR1 : vrepA m1 (f + 32) A (vcap_iter (el_PA bs) 0 0) (Z.of_nat (el_PA bs)) (el_elsA d bs)).
  { split; [exact ELS|]. split; [exact SZC|]. split; [exact CAPB|]. split; [exact A0|]. split; [exact AH|]. split.
    - eapply rw_cells_agree_nw; [exact SV|]. apply AG1. intros x Hx E. cbn [cells_size csize Nat.add] in Hx. ul.
    - destruct BLK as [B|(B1 & B2 & B3 & B4)]; [left; exact B| right]. split; [exact B1|]. split; [exact B2|]. split; [exact B3|].
      eapply rw_cells_agree_nw; [exact B4|]. apply AG1. intros x Hx E.
      assert (INA : In (A, 16 * Z.of_nat (el_PA bs)) (rt_live RT Σ)).
      { unfold vliveA, vblockA in VL. rewrite VL. apply in_or_app. left. destruct (Z.eqb_spec (vcap_iter (el_PA bs) 0 0) 0); [lia|]. apply ann_block_vis. }
      pose proof (af_live_range RT AF Σ m A _ ARTx INA) as (_ & Y & _). rewrite SPx in Y. rewrite velts_size in Hx.
      unfold el_elsA in Hx. rewrite atp_elsA_length in Hx. fold (el_PA bs) in Hx. clear - Hx E Y LOW LOR SPR. ul. }
  eapply (aevt_rt RT PMc Σ K _ _
           (vdestroy_ok RT AF (rtf_of_rt RT RC) (rc2_annotate RT RC2) Σ PMc (wz 0xb1ac0) (wz sp') gp (wz TPV_A) t0 t1 t2 (wz usp) (wz sp')
                (wz (sp' + 96)) a1 a2 a3 a4 a5 a6 a7 (wz f) (wz (shad f)) (wz (f + 32)) (wz (f + 96)) x6 x7 (wz f) x9 x10 x11 t3 t4 t5 t6 F fc m1
                (sp' + 96) (f + 32) A (vcap_iter (el_PA bs) 0 0) (Z.of_nat (el_PA bs)) (el_elsA d bs) (rt_live RT Σ0) lo
                FDO MST eq_refl eq_refl ltac:(rewrite EU; lia) ltac:(ul) ltac:(clear - SPA'; Z.div_mod_to_equations; lia) FC1
                VR1 VL LVPOS ltac:(lia) FOBJV ART1 MI1 ltac:(rewrite EU; exact ST1) ltac:(rewrite SPx; exact LOW) ltac:(rewrite EU; ul)
                ltac:(rewrite EU; ul) ltac:(rewrite EU; clear - SPA'; Z.div_mod_to_equations; lia)
                ltac:(unfold unwind_ok; rewrite EU, !unsigned_lit by ul; right; right; lia) FRM)); [exact FRM|].
  intros c (Σ2 & HA & LV2 & FRS2 & SP2 & CR2). eexists Σ2, _. split; [exact HA|].
  intros ms' (v & m2 & RS & (ART2 & MI2 & ST2) & PRES2) FRM2.
  destruct RS as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->). cbn [ms_fcsr] in FRM2.
  rewrite EU in ST2, PRES2. rewrite (ret_pc_even 0xb1ac0) by lia. rewrite FRSx in PRES2, FRS2. rewrite SPx in SP2.

  pose proof (af_frames_range RT AF Σ m f 4%nat ARTx INF) as (_ & _ & _ & FLV). change (fs_size 4) with 1024 in FLV.
  pose proof (af_fshadow_apart RT AF Σ m f 4%nat ARTx INF) as (FSL & _). change (fs_size 4) with 1024 in FSL.
  assert (NCL : forall x, (f <= x < f + 1024 \/ shad f <= x < shad f + 128 \/ sp' <= x < usp) -> client_static x \/ in_live (rt_live RT Σ0) x -> False).
  { intros x Hx [H|H].
    - pose proof (client_static_range _ H) as R. clear - Hx R FSEG SHB0 SPR LOW LOR SP0R. unfold shad, SEGTOP_A, SHB in *. ul.
    - destruct H as (q & k & Hin & Hr). assert (Hin' : In (q, k) (rt_live RT Σ)) by (unfold vliveA in VL; rewrite VL; apply in_or_app; right; exact Hin).
      pose proof (FLV q k Hin') as Y1. pose proof (FSL q k Hin') as Y2.
      pose proof (af_live_range RT AF Σ m q k ARTx Hin') as (_ & Y3 & _). rewrite SPx in Y3. rewrite SHF0 in Hx. unfold shad, SHB in Y2. clear - Hx Hr Y1 Y2 Y3 LOW LOR SPR.
      replace ((f + 1024) / 8 + 2147450880) with (f / 8 + 2147450880 + 128) in Y2 by (Z.div_mod_to_equations; lia). unfold SHB in *. ul. }

  assert (AG2 : forall (P : Z -> Prop), (forall x, P x -> aclient (rt_live RT Σ0) [(f, 4%nat)] sp' x /\ ~ (sp' + 96 <= x < sp' + 104) /\ ~ (f + 32 <= x < f + 56)) ->
                 agree_on P m m2).
  { intros P HP a Ha. destruct (HP _ Ha) as (H1 & H2 & H3). rewrite (PRES2 a), (MU1 a); [reflexivity| | |].
    - cbn [outside]. split; [exact H2| exact I]. - exact H1. - cbn [outside]. split; [lia| exact I]. }
  assert (INF' : forall lo' hi', f <= lo' -> hi' <= f + 1016 -> forall x, lo' <= x < hi' -> aclient (rt_live RT Σ0) [(f, 4%nat)] sp' x).
  { intros lo' hi' H1 H2 x Hx. right; right; right; left. exists f, 4%nat. split; [left; reflexivity| change (fs_size 4) with 1024; lia]. }
  assert (INS' : forall x, shad f <= x < shad f + 128 -> aclient (rt_live RT Σ0) [(f, 4%nat)] sp' x).
  { intros x Hx. right; right; right; right. exists f, 4%nat. split; [left; reflexivity| rewrite SHF0 in Hx |- *; unfold shad, SHB in *; change (fs_size 4) with 1024; Z.div_mod_to_equations; lia]. }
  assert (FRl2 : rw_cells asegs m2 sp' [CB 96 JL; C8 (wz (f + 32)); CB 48 JH]).
  { eapply rw_cells_agree_nw; [exact FRl1|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply PRES2; [left; ul| cbn [outside]; split; [ul| exact I]]. }
  assert (STp2 : stk asegs m2 (sp' + 152) (usp - 104)).
  { eapply stk_agree_nw; [exact STp|]. apply AG2. intros x Hx. cbv beta in Hx. split; [left; ul| split; [lia| ul]]. }
  assert (FRs2 : rw_cells asegs m2 (usp - 104) (fa_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
  { eapply rw_cells_agree_nw; [exact FRs|]. apply AG2. intros x Hx. unfold fa_saved in Hx. cbn [cells_size csize Nat.add] in Hx. split; [left; ul| split; [lia| ul]]. }
  assert (FH2 : rw_cells asegs m2 f (fz_hdr (C8 (wz 0x41b58ab3)) (C8 (wz 0x126fb)) (C8 (wz 0xb1608)) h3)).
  { eapply rw_cells_agree_nw; [exact FH|]. apply AG2. intros x Hx. unfold fz_hdr in Hx. cbn [cells_size csize Nat.add] in Hx. split; [apply (INF' f (f + 32)); lia| split; [ul| lia]]. }
  assert (FS2 : rw_cells asegs m2 (shad f) (el_shadowA 0 p e (-8) t)).
  { eapply rw_cells_agree_nw; [exact FS|]. apply AG2. intros x Hx. rewrite el_shadowA_size in Hx. split; [apply INS'; lia| unfold shad, SHB in *; split; [ul| lia]]. }
  assert (LIB2 : el_libA m2).
  { eapply el_libA_agree; [exact LIB|]. apply AG2. intros x Hx. pose proof (el_lib_rng_static _ Hx) as [CS R]. pose proof (client_static_range _ CS).
    split; [right; left; exact CS| unfold SEGTOP_A in *; split; [ul| lia]]. }
  assert (PRES2' : forall a : word, aclient (rt_live RT Σ0) [] usp (bv_unsigned a) -> outside EL_LIB_FP (bv_unsigned a) -> m2 a = m0 a).
  { intros a Ha Ho. rewrite <- (PRES a Ha Ho). apply (AG2 (fun x => x = bv_unsigned a)); [| reflexivity]. intros x ->.
    split; [apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros q Hq; exact Hq| intros q []| lia]|].
    destruct Ha as [H|[H|[H|[H|H]]]]; [clear - H FLV SPR LOW LOR FLO; split; ul| | | destruct H as (? & ? & [] & _)| destruct H as (? & ? & [] & _)].
    - pose proof (client_static_range _ H). unfold SEGTOP_A in *. split; [ul| lia].
    - destruct H as (q & k & Hin & Hr). assert (Hin' : In (q, k) (rt_live RT Σ)) by (unfold vliveA in VL; rewrite VL; apply in_or_app; right; exact Hin).
      pose proof (af_live_range RT AF Σ m q k ARTx Hin') as (_ & Y3 & _). rewrite SPx in Y3. pose proof (FLV q k Hin') as Y1. clear - Hr Y3 Y1 LOW LOR SPR. split; ul. }
  clear AG2 PRES2 MU1 WM1 FRl1 ART1 ST1 MI1 FRl' STp FRs FH FS LIB.

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (tl_walkX1 usp sp' f (wz 0xb1ac0) gp u0 u1 u2 v b1 b2 b3 b4 b5 b6 b7 x6 x7 x9 x10 x11 u3 u4 u5 u6 p e h3 t F2 fc2 m2);
                   [lia| ul| unfold shad, SHB; lia| unfold shad, SHB; ul| exact FSELF| ul| ul| ul| unfold shad, SHB in *; ul| exact FH2| exact FS2| exact MI2]|].
  cbv beta. intros ms3 (m3 & -> & MU3 & WM3 & MI3 & FH3 & FS3). apply evt_done. unfold tl_st.
  assert (ART3 : ART RT Σ2 m3).
  { apply (art_client_write RT AF Σ2 m2 m3 sp' ART2 ltac:(rewrite SP2; ul)); [| exact WM3].
    intros a Ha. apply MU3. cbn [outside]. split; [| split; [| exact I]]; intros Hin; apply Ha; rewrite FRS2.
    - right; right; right; left. exists f, 4%nat. split; [left; reflexivity| change (fs_size 4) with 1024; lia].
    - right; right; right; right. exists f, 4%nat. split; [left; reflexivity| rewrite SHF0 in Hin |- *; unfold shad, SHB in *; change (fs_size 4) with 1024; Z.div_mod_to_equations; lia]. }
  assert (ST3 : stk asegs m3 lo sp').
  { apply (stk_agree asegs m2 m3 _ _ ST2); [| exact WM3]. apply (agree_of_munch _ _ _ _ MU3). intros x Hx. cbn [outside]. unfold shad, SHB in *. repeat split; ul. }

  eapply (aevt_setshadow RT RC PMc FDO MST Σ2 K 245 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 m3 (shad f) 128 lo);
    [cbn; tauto| reflexivity| reflexivity| lia| | | exact ART3| exact MI3| |].
  { intros i Hi. exists f, 4%nat. rewrite FRS2. split; [left; reflexivity|]. rewrite SHF0. unfold shad, SHB. change (fs_size 4) with 1024. Z.div_mod_to_equations; lia. }
  { eapply (rw_cells_wr_at asegs m3 _ _ 128 FS3). rewrite el_shadowA_size. reflexivity. }
  { unfold call_ok. rewrite EU. split; [exact ST3|]. split; [rewrite SP2; lia|]. split; [ul|]. split; [ul| Z.div_mod_to_equations; lia]. }
  intros v0 w0 w1 w2 e1 e2 e3 e4 e5 e6 e7 w3 w4 w5 w6 F4 m4 (ART4 & MI4 & WM4 & ST4) PR4 BY4. rewrite EU in ST4, PR4.
  rewrite (ret_pc_even 0xb1aec) by lia.

  destruct (af_frame_release RT AF Σ2 m4 f 4%nat [] ART4 FRS2) as (Σ5 & fl & FLC & NAC & FL0 & FLW & FW & REL).
  change (fs_size 4) with 1024 in FW. replace (f + 1024 - 8) with (f + 1016) in FW by lia. rewrite SP2 in FLW.
  assert (AG4 : forall (P : Z -> Prop), (forall x, P x -> sp' <= x < usp) -> agree_on P m2 m4).
  { intros P HP a Ha. pose proof (HP _ Ha) as H1. rewrite (PR4 a), (MU3 a); [reflexivity| | |].
    - cbn [outside]. split; [ul|]. split; [unfold shad, SHB in *; ul| exact I].
    - left. ul.
    - unfold shad, SHB in *. ul. }
  assert (FRl4 : rw_cells asegs m4 sp' [CB 96 JL; C8 (wz (f + 32)); CB 48 JH]) by (eapply rw_cells_agree_nw; [exact FRl2|]; apply AG4; intros x Hx; cbn [cells_size csize Nat.add] in Hx; lia).
  assert (STp4 : stk asegs m4 (sp' + 152) (usp - 104)) by (eapply stk_agree_nw; [exact STp2|]; apply AG4; intros x Hx; cbv beta in Hx; lia).
  assert (FRs4 : rw_cells asegs m4 (usp - 104) (fa_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11))
    by (eapply rw_cells_agree_nw; [exact FRs2|]; apply AG4; intros x Hx; unfold fa_saved in Hx; cbn [cells_size csize Nat.add] in Hx; lia).

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (tl_walkX2 usp sp' f fl lo (wz 0xb1aec) gp w0 w1 w2 v0 e1 e2 e3 e4 e5 e6 e7 x6 x7 x9 x10 x11 w3 w4 w5 w6
                             ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 [CB 96 JL; C8 (wz (f + 32)); CB 48 JH] F4 fc2 m4);
                   [lia| ul| exact FL0| ul| ul| ul| reflexivity| lia| ul| exact ST4| exact FRl4| exact STp4| exact FRs4| exact FW| exact FLC| exact MI4]|].
  cbv beta. intros ms5 (m5 & RS5 & FC5 & MU5 & WM5 & MI5 & ST5 & FLC5).
  destruct (REL m5 MU5 WM5 FLC5) as (ART5 & FRS5 & LV5 & SP5 & CR5 & AL5 & AM5).
  apply evt_done. apply (aevt_switch RT PMc Σ2 Σ5 K ms5 AL5 AM5).
  revert FC5. apply (ret_st_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 ms5 (fun ms => ms_fcsr ms = fc2 -> aevt RT PMc Σ5 K ms) RS5).
  intros q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F5 fc5 FC5. change (fc5 = fc2) in FC5. subst fc5.
  apply (KR Σ5 m5 fc2 F5 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 ART5 MI5 ST5 FRM2); [| | rewrite LV5; exact LV2| exact FRS5| rewrite SP5; exact SP2| rewrite CR5, CR2; exact CR].
  - eapply el_libA_agree; [exact LIB2|]. intros a Ha. pose proof (el_lib_rng_static _ Ha) as [CS R].
    rewrite (MU5 a), (PR4 a), (MU3 a); [reflexivity| | | |].
    + cbn [outside]. unfold SEGTOP_A, shad, SHB in *. split; [lia|]. split; [lia| exact I].
    + right; left. exact CS.
    + unfold SEGTOP_A, shad, SHB in *. lia.
    + cbn [outside]. split; [| exact I]. intros E. apply NAC. right; left. replace fl with (bv_unsigned a) by lia. exact CS.
  - intros a Ha Ho. rewrite <- (PRES2' a Ha Ho). rewrite (MU5 a), (PR4 a), (MU3 a); [reflexivity| | | |].
    + cbn [outside]. destruct Ha as [H|[H|[H|[H|H]]]]; [| | | destruct H as (? & ? & [] & _)| destruct H as (? & ? & [] & _)].
      * clear - H FLV SHT LOW LOR SPR SHB0 FSELF FLO. unfold shad, SHB in *. split; [ul|]. split; [ul| exact I].
      * pose proof (client_static_range _ H). unfold SEGTOP_A, shad, SHB in *. split; [lia|]. split; [lia| exact I].
      * split; [intros E; apply (NCL (bv_unsigned a)); [left; lia| right; exact H]|]. split; [intros E; apply (NCL (bv_unsigned a)); [right; left; rewrite SHF0 in E |- *; unfold shad, SHB in *; lia| right; exact H]| exact I].
    + apply (aclient_mono _ _ _ _ _ _ _ Ha); [rewrite LV2; intros q Hq; exact Hq| intros q []| lia].
    + destruct Ha as [H|[H|[H|[H|H]]]]; [clear - H FLV SHT LOW LOR SPR; ul| pose proof (client_static_range _ H); unfold SEGTOP_A, shad, SHB in *; lia
                                         | intros E; apply (NCL (bv_unsigned a)); [right; left; exact E| right; exact H]| destruct H as (? & ? & [] & _)| destruct H as (? & ? & [] & _)].
    + cbn [outside]. split; [| exact I]. intros E. apply NAC. rewrite LV2, FRS2. replace fl with (bv_unsigned a) by lia.
      destruct Ha as [H|[H|[H|[H|H]]]]; [exfalso; clear - H E FLW LOW LOR; ul| right; left; exact H
                                        | right; right; left; exact H| destruct H as (? & ? & [] & _)| destruct H as (? & ? & [] & _)].
Qed.
End Tail2.

Lemma tl_walkP1 : forall (usp sp' f : Z) (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (t : list byte) F fc (m : mem),
  0 < f -> f + 1024 < 2^63 -> 0 <= shad f -> shad f + 128 < 2^63 ->
  rw_cells asegs m (shad f) (el_shadowA 0 0 0 (-8) t) -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem),
      ms = tl_st usp sp' f e_pdtor (Z_to_bv 64 0xb1a8c) gp t0 t1 t2 (Z_to_bv 64 (f + 96)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-8)) s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1
      /\ munch [(shad f + 26, shad f + 28)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ rw_cells asegs m1 (shad f) (el_shadowA 0 0 (-8) (-8) t))
    (tl_st usp sp' f EL_EXIT_A ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros F0 FH SH0 SHH FS MI.
  unfold tl_st, el_shadowA, el_shbytesA, EL_EXIT_A, e_pdtor, shad, SHB in *. cbn [map app repeat] in *.
  pose proof (munch_refl [(f / 8 + 2147450880 + 26, f / 8 + 2147450880 + 28)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (ESH : bv_unsigned (Z_to_bv 64 (f / 8 + 2147450880)) = f / 8 + 2147450880) by (apply unsigned_lit; lia).
  zstep. ls. ls. zstep. zstep.
  apply evt_done. eexists. split; [atp_st_eq_goal|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|]. eassumption.
Qed.

Lemma tl_walkP2 : forall (usp sp' f : Z) (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (t : list byte) F fc (m : mem),
  0 < f -> f + 1024 < 2^63 -> 0 <= shad f -> shad f + 128 < 2^63 ->
  rw_cells asegs m (shad f) (el_shadowA 0 0 (-8) (-8) t) -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem),
      ms = tl_st usp sp' f EL_EXIT2_A ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-8)) s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1
      /\ munch [(shad f + 12, shad f + 22)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ rw_cells asegs m1 (shad f) (el_shadowA 0 (-8) (-8) (-8) t))
    (tl_st usp sp' f 0xb1a8c ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-8)) s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros F0 FH SH0 SHH FS MI.
  unfold tl_st, el_shadowA, el_shbytesA, EL_EXIT2_A, shad, SHB in *. cbn [map app repeat] in *.
  pose proof (munch_refl [(f / 8 + 2147450880 + 12, f / 8 + 2147450880 + 22)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (ESH : bv_unsigned (Z_to_bv 64 (f / 8 + 2147450880)) = f / 8 + 2147450880) by (apply unsigned_lit; lia).
  do 10 ls.
  apply evt_done. eexists. split; [atp_st_eq_goal|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|]. eassumption.
Qed.

Section TailP.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis PDT : pdtor_cps RT (pdone RT).
Variable PMc : Model -> Prop.

Local Ltac ul := unfold FUZZ_STACK, PID_STACK in *; unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Theorem el_tailP_ok : el_tailP_cps RT PMc.
Proof using AF PDT.
  intros Σ0 m0 X d bs ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 crd K FDO MST LK LOW LVPOS CUT2.
  unfold cutX. intros Σ m x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x6 x7 x9 x10 x11 t3 t4 t5 t6 F fc LC h3 t A L0 j56 j176 ce jq
    ARTx MIx STx STp FRs FH LIB PRES FRSx SPx SZ FRl FS VR FQ EL0 PD INCL LEN F176 SZE FE F224 CR FRM.
  destruct LK as [(SPR & SPA') (SPT & SPA) (LLO & LOR) (FPOS & F64 & FSEG & FLO) (FSELF & SHB0 & SHT)].
  destruct X as [usp sp' f lo]. cbn [lf_usp lf_S1 lf_F lf_lo] in *.
  pose proof (af_sp0_range RT AF Σ m ARTx) as SP0R. rewrite SPx in SP0R.
  assert (EU : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; ul).
  assert (INF : In (f, 4%nat) (rt_frames RT Σ)) by (rewrite FRSx; left; reflexivity).
  assert (SHF0 : shad f = f / 8 + SHB) by reflexivity.
  pose proof (af_frames_range RT AF Σ m f 4%nat ARTx INF) as (_ & _ & _ & FLV). change (fs_size 4) with 1024 in FLV.
  pose proof (af_fshadow_apart RT AF Σ m f 4%nat ARTx INF) as (FSL & _). change (fs_size 4) with 1024 in FSL.

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (tl_walkP1 usp sp' f x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x6 x7 (wz f) x9 x10 x11 t3 t4 t5 t6 t F fc m);
                   [lia| ul| unfold shad, SHB; lia| unfold shad, SHB; ul| exact FS| exact MIx]|].
  cbv beta. intros ms1 (m1 & -> & MU1 & WM1 & MI1 & FS1). apply evt_done. unfold tl_st.
  assert (AG1 : forall (P : Z -> Prop), (forall x, P x -> ~ (shad f + 26 <= x < shad f + 28)) -> agree_on P m m1).
  { intros P HP a Ha. apply MU1. cbn [outside]. split; [exact (HP _ Ha)| exact I]. }
  assert (ART1 : ART RT Σ m1).
  { apply (art_client_write RT AF Σ m m1 sp' ARTx ltac:(rewrite SPx; ul)); [| exact WM1]. apply AG1. intros x Hx E. apply Hx.
    right; right; right; right. exists f, 4%nat. split; [exact INF| rewrite SHF0 in E |- *; unfold shad, SHB in *; change (fs_size 4) with 1024; Z.div_mod_to_equations; lia]. }
  assert (ST1 : stk asegs m1 lo sp') by (apply (stk_agree asegs m m1 _ _ STx); [| exact WM1]; apply AG1; intros x Hx; cbv beta in Hx; unfold shad, SHB in *; ul).
  assert (PD1 : pdone RT Σ m1 (f + 96) L0).
  { destruct PD as (impl & tape & sbuf & idx & oc & ia & nt & ns & nidx & noc & nia & dcap & pre8 & mid & mid2 & rest & ipre8 & imid & irest
                    & FOBJ & PC & INM & I8 & IC & INS & INT & INA & INO & INX & REST).
    exists impl, tape, sbuf, idx, oc, ia, nt, ns, nidx, noc, nia, dcap, pre8, mid, mid2, rest, ipre8, imid, irest.
    split; [| split; [| split; [exact INM| split; [exact I8| split; [| exact (conj INS (conj INT (conj INA (conj INO (conj INX REST)))))]]]]].
    - destruct FOBJ as (B1 & B2 & B3 & B4). split; [exact B1|]. split; [exact B2|]. split; [exact B3|].
      eapply bytes_at_agree; [exact B4|]. apply AG1. intros x Hx E. rewrite repeat_length in Hx. change (Z.to_nat ((80 + 7) / 8)) with 10%nat in Hx.
      replace (shad (f + 96)) with (shad f + 12) in Hx by (unfold shad, SHB; Z.div_mod_to_equations; lia). lia.
    - eapply rw_cells_agree_nw; [exact PC|]. apply AG1. intros x Hx E. unfold pd_cells in Hx. cbn [cells_size csize Nat.add] in Hx. unfold shad, SHB in *. ul.
    - eapply rw_cells_agree_nw; [exact IC|]. apply AG1. intros x Hx E. unfold dl_cells in Hx. cbn [cells_size csize Nat.add] in Hx.
      pose proof (FSL impl 96 INM) as Y. rewrite SHF0 in E. unfold shad, SHB in Y, E.
      replace ((f + 1024) / 8 + 2147450880) with (f / 8 + 2147450880 + 128) in Y by (Z.div_mod_to_equations; lia). lia. }

  eapply (aevt_rt RT PMc Σ K _ _
           (PDT Σ PMc (wz 0xb1a8c) (wz sp') gp (wz TPV_A) t0 t1 t2 (wz usp) (wz sp') (wz (f + 96)) a1 a2 a3 a4 a5 a6 a7
                (wz f) (wz (shad f)) (wz (f + 32)) (wz (f + 96)) (wz (-8)) x7 (wz f) x9 x10 x11 t3 t4 t5 t6 F fc m1 (f + 96) L0 lo
                FDO MST eq_refl eq_refl PD1 ART1 MI1 ltac:(rewrite EU; exact ST1) ltac:(rewrite SPx; exact LOW) ltac:(rewrite EU; ul) ltac:(rewrite EU; ul)
                ltac:(rewrite EU; clear - SPA'; Z.div_mod_to_equations; lia) ltac:(unfold unwind_ok; rewrite EU, !unsigned_lit by ul; right; right; lia) FRM)); [exact FRM|].
  intros c (Σ2 & HA & LV2 & FRS2 & SP2 & CR2). eexists Σ2, _. split; [exact HA|].
  intros ms' (v & m2 & RS & (ART2 & MI2 & ST2) & PRES2) FRM2.
  destruct RS as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->). cbn [ms_fcsr] in FRM2.
  rewrite EU in ST2, PRES2. rewrite (ret_pc_even 0xb1a8c) by lia. rewrite FRSx in PRES2, FRS2. rewrite SPx in SP2.

  assert (AG2 : forall (P : Z -> Prop), (forall x, P x -> aclient L0 [(f, 4%nat)] sp' x /\ ~ (shad f + 26 <= x < shad f + 28) /\ ~ (f + 96 <= x < f + 176)) ->
                 agree_on P m m2).
  { intros P HP a Ha. destruct (HP _ Ha) as (H1 & H2 & H3). rewrite (PRES2 a), (MU1 a); [reflexivity| | |].
    - cbn [outside]. split; [exact H2| exact I]. - exact H1. - cbn [outside]. split; [lia| exact I]. }
  assert (INF' : forall lo' hi', f <= lo' -> hi' <= f + 1016 -> forall x, lo' <= x < hi' -> aclient L0 [(f, 4%nat)] sp' x).
  { intros lo' hi' H1 H2 x Hx. right; right; right; left. exists f, 4%nat. split; [left; reflexivity| change (fs_size 4) with 1024; lia]. }
  assert (INS' : forall x, shad f <= x < shad f + 128 -> aclient L0 [(f, 4%nat)] sp' x).
  { intros x Hx. right; right; right; right. exists f, 4%nat. split; [left; reflexivity| rewrite SHF0 in Hx |- *; unfold shad, SHB in *; change (fs_size 4) with 1024; Z.div_mod_to_equations; lia]. }
  Ltac tpx H AG2 tac := eapply rw_cells_agree_nw; [exact H|]; apply AG2; intros x Hx; cbn [cells_size csize Nat.add] in Hx; tac.
  assert (FRl2 : rw_cells asegs m2 sp' LC).
  { eapply rw_cells_agree_nw; [exact FRl|]. apply AG2. intros x Hx. rewrite SZ in Hx. unfold shad, SHB in *. split; [left; ul| split; [ul| ul]]. }
  assert (STp2 : stk asegs m2 (sp' + 152) (usp - 104)).
  { eapply stk_agree_nw; [exact STp|]. apply AG2. intros x Hx. cbv beta in Hx. unfold shad, SHB in *. split; [left; ul| split; [ul| ul]]. }
  assert (FRs2 : rw_cells asegs m2 (usp - 104) (fa_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
  { eapply rw_cells_agree_nw; [exact FRs|]. apply AG2. intros x Hx. unfold fa_saved in Hx. cbn [cells_size csize Nat.add] in Hx. unfold shad, SHB in *. split; [left; ul| split; [ul| ul]]. }
  assert (FH2 : rw_cells asegs m2 f (fz_hdr (C8 (wz 0x41b58ab3)) (C8 (wz 0x126fb)) (C8 (wz 0xb1608)) h3)).
  { eapply rw_cells_agree_nw; [exact FH|]. apply AG2. intros x Hx. unfold fz_hdr in Hx. cbn [cells_size csize Nat.add] in Hx. unfold shad, SHB in *.
    split; [apply (INF' f (f + 32)); lia| split; [ul| lia]]. }
  assert (FS2 : rw_cells asegs m2 (shad f) (el_shadowA 0 0 (-8) (-8) t)).
  { eapply rw_cells_agree_nw; [exact FS1|]. intros a Ha. rewrite el_shadowA_size in Ha. apply PRES2; [apply INS'; lia| cbn [outside]; unfold shad, SHB in *; split; [ul| exact I]]. }
  assert (F56_2 : rw_cells asegs m2 (f + 56) [CB 40 j56]) by (tpx FQ AG2 ltac:(unfold shad, SHB in *; split; [apply (INF' (f + 56) (f + 96)); lia| split; [ul| lia]])).
  assert (F176_2 : rw_cells asegs m2 (f + 176) [CB 32 j176]) by (tpx F176 AG2 ltac:(unfold shad, SHB in *; split; [apply (INF' (f + 176) (f + 208)); lia| split; [ul| lia]])).
  assert (FE2 : rw_cells asegs m2 (f + 208) ce) by (tpx FE AG2 ltac:(rewrite SZE in Hx; unfold shad, SHB in *; split; [apply (INF' (f + 208) (f + 224)); lia| split; [ul| lia]])).
  assert (F224_2 : rw_cells asegs m2 (f + 224) [CB 792 jq]) by (tpx F224 AG2 ltac:(unfold shad, SHB in *; split; [apply (INF' (f + 224) (f + 1016)); lia| split; [ul| lia]])).
  assert (VR2 : vrepA m2 (f + 32) A (vcap_iter (el_PA bs) 0 0) (Z.of_nat (el_PA bs)) (el_elsA d bs)).
  { pose proof VR as (ELS & SZC & CAPB & A0 & AH & SV & BLK).
    split; [exact ELS|]. split; [exact SZC|]. split; [exact CAPB|]. split; [exact A0|]. split; [exact AH|]. split.
    - tpx SV AG2 ltac:(unfold shad, SHB in *; split; [apply (INF' (f + 32) (f + 56)); lia| split; [ul| lia]]).
    - destruct BLK as [B|(B1 & B2 & B3 & B4)]; [left; exact B| right]. split; [exact B1|]. split; [exact B2|]. split; [exact B3|].
      eapply rw_cells_agree_nw; [exact B4|]. apply AG2. intros x Hx.
      assert (INA : In (A, 16 * Z.of_nat (el_PA bs)) L0).
      { rewrite EL0. apply in_or_app. left. unfold vblockA. destruct (Z.eqb_spec (vcap_iter (el_PA bs) 0 0) 0); [pose proof (el_PA_ge2 bs); pose proof (vcap_iter_inv (el_PA bs) 0 0 ltac:(lia) ltac:(lia)); lia|]. apply ann_block_vis. }
      rewrite velts_size in Hx. unfold el_elsA in Hx. rewrite atp_elsA_length in Hx. fold (el_PA bs) in Hx.
      pose proof (af_live_range RT AF Σ m A _ ARTx (INCL _ INA)) as (_ & Y & _). rewrite SPx in Y. pose proof (FLV A _ (INCL _ INA)) as Y1. pose proof (FSL A _ (INCL _ INA)) as Y2.
      rewrite SHF0 in Y2 |- *. unfold shad, SHB in *. replace ((f + 1024) / 8 + 2147450880) with (f / 8 + 2147450880 + 128) in Y2 by (Z.div_mod_to_equations; lia).
      split; [right; right; left; exists A, (16 * Z.of_nat (el_PA bs)); split; [exact INA| lia]| clear - Hx Y Y1 Y2 LOW LOR SPR; split; ul]. }
  assert (LIB2 : el_libA m2).
  { eapply el_libA_agree; [exact LIB|]. apply AG2. intros x Hx. pose proof (el_lib_rng_static _ Hx) as [CS R]. pose proof (client_static_range _ CS).
    unfold SEGTOP_A, shad, SHB in *. split; [right; left; exact CS| split; [lia| lia]]. }
  assert (PRES2' : forall a : word, aclient (rt_live RT Σ0) [] usp (bv_unsigned a) -> outside EL_LIB_FP (bv_unsigned a) -> m2 a = m0 a).
  { intros a Ha Ho. rewrite <- (PRES a Ha Ho). apply (AG2 (fun x => x = bv_unsigned a)); [| reflexivity]. intros x ->.
    split; [apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros q Hq; rewrite EL0; apply in_or_app; right; exact Hq| intros q []| lia]|].
    destruct Ha as [H|[H|[H|[H|H]]]]; [clear - H FLV SPR LOW LOR FLO SHT; unfold shad, SHB in *; split; ul| | | destruct H as (? & ? & [] & _)| destruct H as (? & ? & [] & _)].
    - pose proof (client_static_range _ H). unfold SEGTOP_A, shad, SHB in *. split; [lia| lia].
    - destruct H as (q & k & Hin & Hr). assert (Hin' : In (q, k) (rt_live RT Σ)) by (apply INCL; rewrite EL0; apply in_or_app; right; exact Hin).
      pose proof (af_live_range RT AF Σ m q k ARTx Hin') as (_ & Y3 & _). rewrite SPx in Y3. pose proof (FLV q k Hin') as Y1. pose proof (FSL q k Hin') as Y2.
      rewrite SHF0 in Y2. unfold shad, SHB in *. replace ((f + 1024) / 8 + 2147450880) with (f / 8 + 2147450880 + 128) in Y2 by (Z.div_mod_to_equations; lia).
      clear - Hr Y3 Y1 Y2 LOW LOR SPR. split; ul. }
  clear AG2 PRES2 MU1 WM1 ART1 ST1 MI1 FRl STp FRs FH FS FS1 LIB PD PD1.

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (tl_walkP2 usp sp' f (wz 0xb1a8c) gp u0 u1 u2 v b1 b2 b3 b4 b5 b6 b7 x7 (wz f) x9 x10 x11 u3 u4 u5 u6 t F2 fc2 m2);
                   [lia| ul| unfold shad, SHB; lia| unfold shad, SHB; ul| exact FS2| exact MI2]|].
  cbv beta. intros ms3 (m3 & -> & MU3 & WM3 & MI3 & FS3). apply evt_done. unfold tl_st.
  assert (AG3 : forall (P : Z -> Prop), (forall x, P x -> ~ (shad f + 12 <= x < shad f + 22)) -> agree_on P m2 m3).
  { intros P HP a Ha. apply MU3. cbn [outside]. split; [exact (HP _ Ha)| exact I]. }
  assert (ART3 : ART RT Σ2 m3).
  { apply (art_client_write RT AF Σ2 m2 m3 sp' ART2 ltac:(rewrite SP2; ul)); [| exact WM3]. apply AG3. intros x Hx E. apply Hx. rewrite FRS2.
    right; right; right; right. exists f, 4%nat. split; [left; reflexivity| rewrite SHF0 in E |- *; unfold shad, SHB in *; change (fs_size 4) with 1024; Z.div_mod_to_equations; lia]. }
  assert (ST3 : stk asegs m3 lo sp') by (apply (stk_agree asegs m2 m3 _ _ ST2); [| exact WM3]; apply AG3; intros x Hx; cbv beta in Hx; unfold shad, SHB in *; ul).
  Ltac tp3 H AG3 := eapply rw_cells_agree_nw; [exact H|]; apply AG3; intros x Hx; cbn [cells_size csize Nat.add] in Hx; unfold shad, SHB in *; ul.
  unfold EL_EXIT2_A.
  eapply (CUT2 Σ2 m3 (wz 0xb1a8c) u0 u1 u2 v b1 b2 b3 b4 b5 b6 b7 (wz (-8)) x7 x9 x10 x11 u3 u4 u5 u6 F2 fc2 LC h3 t (-8) (-8) A);
    [exact ART3| exact MI3| exact ST3| | | | | | exact FRS2| exact SP2| exact SZ| | exact FS3| | rewrite LV2, EL0; reflexivity| rewrite CR2; exact CR| exact FRM2].
  all: cbn [lf_usp lf_S1 lf_F lf_lo].
  - eapply stk_agree_nw; [exact STp2|]. apply AG3. intros x Hx. cbv beta in Hx. unfold shad, SHB in *. ul.
  - tp3 FRs2 AG3.
  - eapply rw_cells_agree_nw; [exact FH2|]. apply AG3. intros x Hx. unfold fz_hdr in Hx. cbn [cells_size csize Nat.add] in Hx. unfold shad, SHB in *. lia.
  - eapply el_libA_agree; [exact LIB2|]. apply AG3. intros x Hx. pose proof (el_lib_rng_static _ Hx) as [CS R]. pose proof (client_static_range _ CS). unfold SEGTOP_A, shad, SHB in *. lia.
  - intros a Ha Ho. rewrite <- (PRES2' a Ha Ho). apply MU3. cbn [outside]. split; [| exact I].
    destruct Ha as [H|[H|[H|[H|H]]]]; [clear - H SHT SPR LOW LOR; unfold shad, SHB in *; ul| pose proof (client_static_range _ H); unfold SEGTOP_A, shad, SHB in *; lia
                                      | | destruct H as (? & ? & [] & _)| destruct H as (? & ? & [] & _)].
    destruct H as (q & k & Hin & Hr). assert (Hin' : In (q, k) (rt_live RT Σ)) by (apply INCL; rewrite EL0; apply in_or_app; right; exact Hin).
    pose proof (FSL q k Hin') as Y2. rewrite SHF0 in Y2. unfold shad, SHB in *.
    replace ((f + 1024) / 8 + 2147450880) with (f / 8 + 2147450880 + 128) in Y2 by (Z.div_mod_to_equations; lia). clear - Hr Y2. lia.
  - eapply rw_cells_agree_nw; [exact FRl2|]. apply AG3. intros x Hx. rewrite SZ in Hx. unfold shad, SHB in *. ul.
  - pose proof VR2 as (ELS & SZC & CAPB & A0 & AH & SV & BLK).
    split; [exact ELS|]. split; [exact SZC|]. split; [exact CAPB|]. split; [exact A0|]. split; [exact AH|]. split; [tp3 SV AG3|].
    destruct BLK as [B|(B1 & B2 & B3 & B4)]; [left; exact B| right]. split; [exact B1|]. split; [exact B2|]. split; [exact B3|].
    eapply rw_cells_agree_nw; [exact B4|]. apply AG3. intros x Hx.
    assert (INA : In (A, 16 * Z.of_nat (el_PA bs)) L0).
    { rewrite EL0. apply in_or_app. left. unfold vblockA. destruct (Z.eqb_spec (vcap_iter (el_PA bs) 0 0) 0); [pose proof (el_PA_ge2 bs); pose proof (vcap_iter_inv (el_PA bs) 0 0 ltac:(lia) ltac:(lia)); lia|]. apply ann_block_vis. }
    rewrite velts_size in Hx. unfold el_elsA in Hx. rewrite atp_elsA_length in Hx. fold (el_PA bs) in Hx.
    pose proof (FSL A _ (INCL _ INA)) as Y2. rewrite SHF0 in Y2. unfold shad, SHB in *.
    replace ((f + 1024) / 8 + 2147450880) with (f / 8 + 2147450880 + 128) in Y2 by (Z.div_mod_to_equations; lia). clear - Hx Y2. lia.
Qed.
End TailP.
