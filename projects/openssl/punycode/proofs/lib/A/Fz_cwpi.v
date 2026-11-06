(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require StoreOk.
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep.
From OSSVerify.Proofs.openssl.punycode.lib.A Require Import Layout Shadow RT_iface D_defs D_kit D_clx D_libiface I_lkit
  Fz_defs Fz_voc Fz_regions Fz_regw Fz_iface Fz_ckit Fz_w1 Fz_w2 Fz_w3 Fz_w4 Fz_w5 Fz_w6 Fz_w7.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require WpEngine LibKit StrKit AShadow ARt ACode ARtIc AIface AFakeStack AInit ABridge KBridge.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Abbreviation W z := (Z_to_bv 64 z) (only parsing).

Section WPI.
Variable RT : rt_sig.
Hypothesis RC : rt_contracts RT.
Hypothesis R0 : ring0_facts RT.
Let AF : art_facts RT := rc_facts RT RC.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, LIVE_MAX, FRAMES_MAX in *; lia.

Ltac to_cps W c Hc Σ MST :=
  lazymatch type of W with evt asegs _ ?X =>
    let W' := fresh "W'" in
    assert (W' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W);
    clear W; apply (cps_realizes asegs _ _ _ c (asta_evt' RT AF Σ _ _ _ MST W') Hc); clear W' end.

Lemma wpinit_cps : forall (Σ : rts RT) PMc
    (gp tp t0 t1 t2 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem)
    (L lo spa FB6 out : Z) (j2 j3 j5 j7 : list byte) (eb lv : byte),
  fdfs_only PMc -> mat_stable PMc -> tp = W 0xba7ed0 ->
  ART RT Σ m -> mem_inv asegs m -> stk asegs m lo L ->
  rt_sp0 RT Σ - STACK_WIN <= lo -> lo + 0x20000 <= L -> L mod 32 = 0 -> L + 32 <= spa -> spa + 16 <= USTACK_TOP ->
  no_cls0 (rt_frames RT Σ) -> In (FB6, 6%nat) (rt_frames RT Σ) -> (length (rt_frames RT Σ) + 1 < FRAMES_MAX)%nat ->
  Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> 0 <= rt_credit RT Σ ->
  uw_chain m (W L) (W spa) [0x1f32a0; 0x1f2f94] ->
  rw_cells asegs m (FB6 + 2208) (pkt_cells0 out j2 j3 j5 j7 eb) -> acc asegs m (FB6 + 2224) 16 ->
  ro_cells asegs m (shad FB6 + 281) [C1 z8] ->
  ro_cells asegs m G_MALLOC_IMPL [C8 (W e_cmalloc)] -> rw_cells asegs m G_LATCH [C1 lv] -> bv_unsigned lv <> 0 ->
  cps asegs (ASTA RT Σ PMc (eq (MS (mkR (W 0x4081c0) (W L) gp tp t0 t1 t2 (W spa) s1 (W (FB6 + 2208)) (W 0) a2 a3 a4 a5 a6 a7
                                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (W 0x26d794) fc None m (seg_rom asegs))))
    (fun c => exists (Σ' : rts RT) (p : Z),
       ASTA RT Σ' PMc (fun ms => exists (m' : mem) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) F' fc',
           ms = MS (mkR (W 0x4081c0) (W L) gp tp t0' t1' t2' (W spa) s1 (W 1) a1' a2' a3' a4' a5' a6' a7'
                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (W 0x4081c0) fc' None m' (seg_rom asegs)
           /\ ART RT Σ' m' /\ mem_inv asegs m' /\ stk asegs m' lo L /\ wmono asegs m m'
           /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) L [(FB6 + 2224, FB6 + 2240); (FB6 + 2248, FB6 + 2256)] m m'
           /\ rw_cells asegs m' (FB6 + 2224) [C8 (W 0); C8 (W 0)] /\ rw_cells asegs m' (FB6 + 2248) [C8 (W p)]
           /\ bytes_at asegs m' p (repeat z8 40)) c
       /\ rt_live RT Σ' = (p, 40) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ /\ 0 < p /\ p mod 16 = 0).
Proof using RC R0.
  intros Σ PMc gp tp t0 t1 t2 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L lo spa FB6 out j2 j3 j5 j7 eb lv
    FDO MST -> ART0 MI0 ST0 LOW LOR L32 LSPA SPAT NC0 IN6 FRB LVB CRB UW PKT ACP SHP MIM LAT LVNZ T c Hc Hk.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  destruct (r0_view RT R0 Σ m ART0 MI0 NC0) as (fs & Tt & ctx & thr & h & (RTOK & ICOK & FSRT & FSWF & UAR & FSW) & GEO & Hh & HINT & ZF & RWR & RAP & CL_IDLE & CL_PUSH).
  destruct GEO as (G1 & G2 & G3 & GD1 & GD2 & GD3).
  pose proof (af_frames_range RT AF Σ m FB6 6 ART0 IN6) as (F6a & F6b & F6c & F6d). change (fs_size 6) with 4096 in *.
  destruct (G3 FB6 6%nat IN6 ltac:(lia)) as (F6e & F6f). change (fs_size 6) with 4096 in *.
  set (k := h mod 16384). set (FB0 := fs + 36864 + 64 * k).
  assert (Hkr : 0 <= k < 16384) by (unfold k; apply Z.mod_pos_bound; lia).
  destruct FSW as ((FSW1 & FSW2) & FSW3 & FSW4).
  destruct GD1 as (GD1b & GD1c & GD1d). destruct GD2 as (GD2b & GD2c & GD2d).
  destruct GD3 as (GD3b & GD3c & GD3d).
  assert (LOB : 0x7fff7f800000 <= lo) by (clear - LOW SP0W; ul).
  assert (EL : bv_unsigned (W L) = L) by (apply unsigned_lit; clear - LOB LOR LSPA SPAT; ul).
  pose proof (wpinit_r1_evt (W 0x4081c0) (W L) gp (W 0xba7ed0) t0 t1 t2 (W spa) s1 (W (FB6 + 2208)) (W 0) a2 a3 a4 a5 a6 a7
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m fs Tt ctx thr h (FB6 + 2208) 0 L
                eq_refl eq_refl eq_refl eq_refl RTOK ICOK FSRT FSWF UAR (conj (conj FSW1 FSW2) (conj FSW3 FSW4)) Hh HINT ZF RWR) as W1.
  assert (ST1 : stk asegs m lo (L - 336) /\ stk asegs m (L - 336) L) by (apply stk_split; [exact ST0| clear - LOR; lia]).
  specialize (W1 ltac:(unfold ARt.A_IMG_END; clear - LOB LOR; lia) ltac:(clear - LSPA SPAT; ul) L32
                 (KBridge.wr_ok_stk asegs m lo L (L - 336) 336 ST0 ltac:(clear - LOR; lia) ltac:(lia))
                 ltac:(right; unfold AIface.FS_SIZE in *; clear - G1 LOW LOR; lia)
                 ltac:(right; unfold AShadow.HIMEM_BEG; clear - LOB LOR; lia)
                 ltac:(unfold AFakeStack.fsrt_sep; clear - GD1b GD2b GD3b G1 LOW LOR; unfold AIface.FS_SIZE in *; lia)).
  cbv zeta in W1. fold k in W1. fold FB0 in W1.
  to_cps W1 c Hc Σ MST. intros c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (ra1 & x0 & x1 & x2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & m1 & -> & SLOTS & HINT1 & FLG1 & ZA1 & ZB1 & C56 & HU1 & HG1) & Hc1').
  clear Hc1.
  destruct (CL_PUSH m1 (L - 336) ltac:(clear - LOW LOR; lia) ltac:(clear - FRB; lia)) as (Σ1 & ART1 & FRS1 & LV1 & SP1 & CR1 & AL1 & AM1).
  { intros a NA NR. apply HU1. intros [HS|HR]; [| exact (NR HR)]. apply NA. left. unfold LibKit.inr in HS. clear - HS LSPA SPAT. ul. }
  { exact HG1. }
  { exact HINT1. } { exact FLG1. } { exact ZA1. } { exact ZB1. } { exact C56. }
  fold k in FRS1. fold FB0 in FRS1.
  pose proof (KBridge.wmono_of_grows asegs m m1 HG1) as WM1.
  assert (MI1 : mem_inv asegs m1).
  { apply (KBridge.mem_inv_unch asegs m m1 _ MI0 HU1). intros x [HS|HR].
    - unfold LibKit.inr in HS. apply (stk_wview m lo L); [exact ST0| clear - HS LOR; lia].
    - destruct RWR as (RW1 & RW2 & RW3 & RW4). destruct HR as [HR|[HR|[HR|HR]]]; unfold LibKit.inr in HR;
        [exact (wview_of_wr_ok m _ _ x RW1 HR)| exact (wview_of_wr_ok m _ _ x RW2 HR)| exact (wview_of_wr_ok m _ _ x RW3 HR)
        | exact (wview_of_wr_ok m _ _ x RW4 HR)]. }
  (* [comment removed for export] *)
  pose proof (af_frames_align RT AF Σ m FB6 6 ART0 IN6) as (F64 & F6g).
  assert (SH6 : shad (FB6 + 4096) = shad FB6 + 512) by (unfold shad; clear - F64; Z.div_mod_to_equations; lia).
  set (Wm := [(FB6 + 2224, FB6 + 2240); (FB6 + 2248, FB6 + 2256)]).
  assert (AG01 : agree_on (fun x => aclient (rt_live RT Σ) (rt_frames RT Σ) L x) m m1).
  { apply (agree_of_unch m m1 _ _ HU1). intros x Hx [HS|HR].
    - unfold LibKit.inr in HS. destruct (aclient_split RT AF Σ m L _ ART0 Hx); clear - H HS LOW LOR; lia.
    - apply (RAP x HR). apply (aclient_mono _ _ _ _ _ _ _ Hx); [auto| auto| clear - LOW LOR; lia]. }
  assert (PR1 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) L Wm m m1) by (intros a Ha _; exact (AG01 a Ha)).
  assert (STK1 : stk asegs m1 lo L) by exact (KBridge.stk_grows asegs m m1 lo L ST0 HG1).
  assert (PKT1 : rw_cells asegs m1 (FB6 + 2208) (pkt_cells0 out j2 j3 j5 j7 eb)).
  { apply (rw_cells_agree_nw asegs m m1 _ _ PKT). eapply agree_sub; [exact AG01|]. intros y Hy. cbn [pkt_cells0 cells_size csize Nat.add] in Hy.
    apply (acl_frame _ _ _ FB6 6%nat); [exact IN6| change (fs_size 6) with 4096; clear - Hy; lia]. }
  assert (ACP1 : acc asegs m1 (FB6 + 2224) 16).
  { apply (acc_agree m m1 _ _ ACP ltac:(clear - F6a; lia)). eapply agree_sub; [exact AG01|]. intros y Hy. cbv beta in Hy.
    apply (acl_fshadow _ _ _ FB6 6%nat); [exact IN6| change (fs_size 6) with 4096; rewrite SH6]. unfold shad in *. clear - Hy F64.
    Z.div_mod_to_equations. lia. }
  replace (L - 128) with (L + -128) in Hc1' by lia.
  (* [comment removed for export] *)
  pose proof (wi_w0 ra1 (W (L + -128)) gp (W 0xba7ed0) x0 x1 x2 (W L) (W (L + -128)) (W (FB6 + 2208 + 16)) (W 0) (W 16) y3 y4 y5 y6 y7
                (W FB0) (W 0) (W (FB6 + 2208)) s5 s6 (W (FB6 + 2208 + 16)) (W (AShadow.sha FB0)) (W FB0) (W AShadow.SB) s11 x3 x4 x5 x6 F fc m1) as W2.
  to_cps W2 c1 Hc1' Σ MST. intros c2 Hc2.
  assert (Hc2' : ASTA RT Σ1 PMc (eq (entry_st (W 0x26d8a4) (W (L + -128)) gp (W 0xba7ed0) x0 x1 x2 (W L) (W (L + -128)) (W (FB6 + 2208 + 16)) (W 0) (W 16) y3 y4 y5 y6 y7
                (W FB0) (W 0) (W (FB6 + 2208)) s5 s6 (W (FB6 + 2208 + 16)) (W (AShadow.sha FB0)) (W FB0) (W AShadow.SB) s11 x3 x4 x5 x6 F fc e_asan_memset m1)) c2).
  { eapply ASTA_conseq; [exact (ASTA_switch RT Σ Σ1 PMc _ c2 Hc2 AL1 AM1)|]. intros ms E. exact (eq_sym E). }
  clear Hc2.
  assert (EL1 : bv_unsigned (W (L + -128)) = L - 128) by (apply unsigned_lit; clear - LOB LOR LSPA SPAT; ul).
  assert (IN61 : In (FB6, 6%nat) (rt_frames RT Σ1)) by (rewrite FRS1; right; exact IN6).
  assert (STK1a : stk asegs m1 lo (L + -128)) by (apply (stk_split asegs m1 lo (L + -128) L STK1); clear - LOR; lia).
  eapply (cps_realizes asegs _ _ T c2).
  { eapply (rc_asan_memset RT RC Σ1 PMc (W 0x26d8a4) (W (L + -128)) gp (W 0xba7ed0) x0 x1 x2 (W L) (W (L + -128)) (W (FB6 + 2208 + 16)) (W 0) (W 16) y3 y4 y5 y6 y7
                (W FB0) (W 0) (W (FB6 + 2208)) s5 s6 (W (FB6 + 2208 + 16)) (W (AShadow.sha FB0)) (W FB0) (W AShadow.SB) s11 x3 x4 x5 x6 F fc m1
                (FB6 + 2224) 16 z8 lo FDO MST); try reflexivity.
    - f_equal. lia.
    - clear - F6a F6b SP0R. ul.
    - lia.
    - split; [intros _; split; [exact ACP1|]| split].
      + right; left. exists FB6, 6%nat. split; [exact IN61| change (fs_size 6) with 4096; lia].
      + intros i Hi. apply (acl_frame _ _ _ FB6 6%nat); [exact IN61| change (fs_size 6) with 4096; lia].
      + apply (rw_cells_wr_at asegs m1 (FB6 + 2208) _ 56) in PKT1; [| reflexivity].
        apply (wr_at_sub m1 (FB6 + 2208) 56); [exact PKT1| lia| lia| lia].
    - exact ART1.
    - exact MI1.
    - unfold call_ok. rewrite EL1, SP1. split; [exact STK1a|]. split; [exact LOW|]. split; [clear - LOR; ul|].
      split; [clear - LSPA SPAT; ul| clear - L32; Z.div_mod_to_equations; lia]. }
  { exact Hc2'. }
  clear Hc2'. intros c3 Hc3.
  destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & (m3 & RS3 & (ART3 & MI3 & WM3 & ST3) & PR3 & B3) & Hc3'). clear Hc3.
  destruct RS3 as (w0 & w1 & w2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & F3 & fc3 & ->).
  rewrite EL1 in ST3, PR3. rewrite (ret_pc_even 0x26d8a4 ltac:(lia) eq_refl) in Hc3'. change (Z.to_nat 16) with 16%nat in B3.
  (* [comment removed for export] *)
  assert (SUB1 : forall x, aclient (rt_live RT Σ) (rt_frames RT Σ) L x -> aclient (rt_live RT Σ1) (rt_frames RT Σ1) (L + -128) x).
  { intros x Hx. apply (aclient_mono _ _ _ _ _ _ _ Hx); [rewrite LV1; auto| rewrite FRS1; intros e He; right; exact He| lia]. }
  assert (PRm3 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) L Wm m m3).
  { apply (pres_fp_trans _ _ _ _ m m1 m3 PR1). intros a Ha Ho. apply PR3; [exact (SUB1 _ Ha)|]. unfold Wm in Ho. cbn [outside] in Ho. clear - Ho. lia. }
  assert (WMm3 : wmono asegs m m3) by exact (wmono_trans _ _ _ _ WM1 WM3).
  assert (AGS3 : agree_on (fun x => L + -128 <= x < L) m1 m3).
  { apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PR3). intros x Hx. split; [apply acl_stack; clear - Hx LSPA SPAT; ul| clear - Hx F6b LOW LOR; lia]. }
  assert (STAT3 : forall lo' hi', (forall y, lo' <= y < hi' -> client_static y) -> agree_on (fun y => lo' <= y < hi') m m3).
  { intros lo' hi' H a Ha. apply PRm3; [apply acl_static; exact (H _ Ha)|]. pose proof (client_static_range _ (H _ Ha)) as CR.
    unfold Wm. cbn [outside]. clear - CR F6g. unfold SEGTOP_A in *. lia. }
  pose proof (ro_cells_agree asegs m m3 _ _ MIM ltac:(apply STAT3; intros y Hy; apply client_static_intro; unfold G_MALLOC_IMPL in *; cbn in Hy; lia)) as MIM3.
  pose proof (rw_cells_agree asegs m m3 _ _ LAT ltac:(apply STAT3; intros y Hy; apply client_static_intro; unfold G_LATCH in *; cbn in Hy; lia) WMm3) as LAT3.
  destruct (lib_ro_cells m3 (af_lib_ro RT AF Σ1 m3 ART3)) as (_ & _ & GOTM3 & _).
  (* [comment removed for export] *)
  pose proof (wi_wA L lo gp (W 0xba7ed0) w0 w1 w2 (W L) (W (L + -128)) (W (FB6 + 2224)) e1 e2 e3 e4 e5 e6 e7
                (W FB0) (W 0) (W (FB6 + 2208)) s5 s6 (W (FB6 + 2208 + 16)) (W (AShadow.sha FB0)) (W FB0) (W AShadow.SB) s11 w3 w4 w5 w6 F3 fc3 m3 lv
                ST3 LOB ltac:(clear - LOR; lia) ltac:(clear - LSPA SPAT; ul) MI3 MIM3 GOTM3 LAT3 LVNZ) as W4.
  to_cps W4 c3 Hc3' Σ1 MST. intros c4 Hc4.
  destruct (ASTA_unpack RT Σ1 _ _ c4 Hc4) as (ms4 & (m4 & jf & -> & MU4 & WM4 & MI4 & ST4 & CZF4 & CMF4) & Hc4'). clear Hc4.
  assert (EL2 : bv_unsigned (W (L + -208)) = L + -208) by (apply unsigned_lit; clear - LOB LOR LSPA SPAT; ul).
  assert (EL3 : bv_unsigned (W (L + -160)) = L + -160) by (apply unsigned_lit; clear - LOB LOR LSPA SPAT; ul).
  assert (ESPA : bv_unsigned (W spa) = spa) by (apply unsigned_lit; clear - LOB LOR LSPA SPAT; ul).
  assert (ART4 : ART RT Σ1 m4).
  { apply (af_frame RT AF Σ1 m3 m4 (L + -208) ART3 ltac:(rewrite SP1; clear - LOW LOR; lia)); [| exact WM4].
    intros a Ha. apply MU4. cbn [outside]. split; [| exact I]. intros Hin. apply Ha. apply acl_stack. clear - Hin LSPA SPAT. ul. }
  assert (AGS4 : agree_on (fun x => L + -128 <= x < L) m1 m4).
  { apply (agree_trans _ m1 m3 m4 AGS3). apply (agree_of_munch _ _ _ _ MU4). intros x Hx. cbn [outside]. clear - Hx. lia. }
  assert (WIR4 : rw_cells asegs m4 (L + -16) [C8 (W spa); C8 (W 0x4081c0)]).
  { assert (WR : wr_at asegs m4 (L + -16) 16).
    { apply (wr_at_transport asegs m1 m4); [| exact (wmono_trans _ _ _ _ WM3 WM4)].
      apply (stk_wr_at m1 lo L); [exact STK1| clear - LOR; lia| lia| lia]. }
    apply rw_cells_join2.
    - apply rw_C8_of_cell; [clear - LOB LOR; lia| clear - LSPA SPAT; ul| | apply (wr_at_sub m4 (L + -16) 16); [exact WR| lia| lia| lia]].
      pose proof (SLOTS 112 8%nat ltac:(unfold AInit.WI_SLOTS; in_slot)) as C. cbn [wi_sv] in C.
      replace (L - 128 + 112) with (L + -16) in C by lia.
      eapply (LibKit.cell_agree asegs m1 m4); [| | | exact C]; [clear - LOB LOR; lia| clear - LSPA SPAT; ul|].
      intros x Hx. apply AGS4. unfold LibKit.inr in Hx. cbv beta. clear - Hx. lia.
    - cbn [csize]. apply rw_C8_of_cell; [clear - LOB LOR; lia| clear - LSPA SPAT; ul| | apply (wr_at_sub m4 (L + -16) 16); [exact WR| lia| lia| lia]].
      pose proof (SLOTS 120 1%nat ltac:(unfold AInit.WI_SLOTS; in_slot)) as C. cbn [wi_sv] in C.
      replace (L - 128 + 120) with (L + -16 + Z.of_nat 8) in C by lia.
      eapply (LibKit.cell_agree asegs m1 m4); [| | | exact C]; [clear - LOB LOR; lia| clear - LSPA SPAT; ul|].
      intros x Hx. apply AGS4. unfold LibKit.inr in Hx. cbv beta. clear - Hx. lia. }
  assert (PRm4 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) L Wm m m4).
  { apply (pres_fp_trans _ _ _ _ m m3 m4 PRm3). apply (pres_fp_of_munch _ _ _ _ _ m3 m4 MU4). intros x Hx _. cbn [outside]. split; [| exact I].
    destruct (aclient_split RT AF Σ m L _ ART0 Hx); clear - H LOW LOR; lia. }
  assert (UW4 : uw_chain m4 (W L) (W spa) [0x1f32a0; 0x1f2f94]).
  { apply (uw_chain_agree _ m m4 _ _ UW). intros a Ha. rewrite EL in Ha. apply PRm4; [apply acl_stack; exact Ha|].
    unfold Wm. cbn [outside]. clear - Ha F6b LOW LOR. lia. }
  assert (UWM : unwind_ok m4 (W 0x1f34d0) (W (L + -160)) (W (L + -208))).
  { split; [rewrite (unsigned_lit 0x1f34d0) by lia; unfold ALLOC_RAS; do 6 right; left; reflexivity|]. right.
    exists [0x1f3544; 0x26d8b8; 0x4081c0; 0x1f32a0; 0x1f2f94]. split; [rewrite (unsigned_lit 0x1f34d0) by lia; unfold ALLOC_CHAINS; right; left; reflexivity|].
    cbn [uw_chain]. rewrite EL2, EL3. split; [lia|]. split; [clear - LSPA SPAT; ul|]. exists (W (L + -128)). split.
    { unfold cm_frame in CMF4.
      pose proof (rw_cells_skip m4 (L + -208) [CB 8 jf; C8 (W 0); C8 (W FB0); C8 (W 40)] [C8 (W (L + -128)); C8 (W 0x1f3544)] CMF4) as H.
      cbn [cells_size csize Nat.add] in H. replace (L + -208 + Z.of_nat 32) with (L + -160 - 16) in H by lia. exact H. }
    rewrite EL1. split; [lia|]. split; [clear - LSPA SPAT; ul|]. exists (W L). split.
    { unfold cz_frame in CZF4.
      pose proof (rw_cells_skip m4 (L + -160) [C8 (W FB0); C8 (W (L + -128))] [C8 (W L); C8 (W 0x26d8b8)] CZF4) as H.
      cbn [cells_size csize Nat.add] in H. replace (L + -160 + Z.of_nat 16) with (L + -128 - 16) in H by lia. exact H. }
    rewrite EL. split; [lia|]. split; [clear - LSPA SPAT; ul|]. exists (W spa). split.
    { replace (L - 16) with (L + -16) by lia. exact WIR4. }
    cbn [uw_chain] in UW4. rewrite EL in UW4. exact UW4. }
  eapply (cps_realizes asegs _ _ T c4).
  { eapply (rc_malloc RT RC Σ1 PMc (W 0x1f34d0) (W (L + -208)) gp (W 0xba7ed0) w0 w1 w2 (W (L + -160))
              (W 110) (W 40) (W (bv_unsigned lv)) (W 5936256) (W 2045016) e4 e5 e6 e7 (W 519360) (W 40)
              (W (FB6 + 2208)) s5 s6 (W (FB6 + 2208 + 16)) (W (AShadow.sha FB0)) (W FB0) (W AShadow.SB) s11 w3 w4 w5 w6 F3 fc3 m4
              40 lo FDO MST); try reflexivity.
    - lia.
    - rewrite LV1. exact LVB.
    - rewrite CR1. change (mcost 40) with 0. exact CRB.
    - exact ART4.
    - exact MI4.
    - unfold call_ok. rewrite EL2, SP1. split; [exact ST4|]. split; [exact LOW|]. split; [clear - LOR; ul|].
      split; [clear - LSPA SPAT; ul| clear - L32; Z.div_mod_to_equations; lia].
    - exact UWM. }
  { exact Hc4'. }
  clear Hc4'. intros c5 Hc5. destruct Hc5 as (Σ2 & p & Hc5 & LV2 & FRS2 & SP2 & CR2 & P0 & P16 & PT).
  destruct (ASTA_unpack RT Σ2 _ _ c5 Hc5) as (ms5 & (m5 & RS5 & (ART5 & MI5 & WM5 & ST5) & PR5 & WRP & ACCP) & Hc5'). clear Hc5.
  destruct RS5 as (v0 & v1 & v2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & v3 & v4 & v5 & v6 & F5 & fc5 & ->).
  rewrite EL2 in ST5, PR5. rewrite (ret_pc_even 0x1f34d0 ltac:(lia) eq_refl) in Hc5'.
  assert (SUB2 : forall x, aclient (rt_live RT Σ) (rt_frames RT Σ) L x -> aclient (rt_live RT Σ1) (rt_frames RT Σ1) (L + -208) x).
  { intros x Hx. apply (aclient_mono _ _ _ _ _ _ _ Hx); [rewrite LV1; auto| rewrite FRS1; intros e He; right; exact He| lia]. }
  assert (PRm5 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) L Wm m m5).
  { apply (pres_fp_trans _ _ _ _ m m4 m5 PRm4). intros a Ha _. exact (PR5 a (SUB2 _ Ha)). }
  assert (AGS5 : agree_on (fun x => L + -208 <= x < L) m4 m5).
  { apply (agree_of_pres _ _ _ _ _ _ PR5). intros x Hx. apply acl_stack. clear - Hx LSPA SPAT. ul. }
  pose proof (rw_cells_agree_nw asegs m4 m5 _ _ CMF4 ltac:(eapply agree_sub; [exact AGS5|]; intros y Hy; cbn [cm_frame cells_size csize Nat.add] in Hy; cbv beta; clear - Hy; lia)) as CMF5.
  pose proof (rw_cells_agree_nw asegs m4 m5 _ _ CZF4 ltac:(eapply agree_sub; [exact AGS5|]; intros y Hy; cbn [cz_frame cells_size csize Nat.add] in Hy; cbv beta; clear - Hy; lia)) as CZF5.
  (* [comment removed for export] *)
  pose proof (wi_wB L lo p gp (W 0xba7ed0) v0 v1 v2 g1 g2 g3 g4 g5 g6 g7 (W 0) (W FB0) (W (FB6 + 2208)) s5 s6 (W (FB6 + 2208 + 16))
                (W (AShadow.sha FB0)) (W FB0) (W AShadow.SB) s11 v3 v4 v5 v6 F5 fc5 m5 jf
                ST5 LOB ltac:(clear - LOR; lia) ltac:(clear - LSPA SPAT; ul) MI5 ltac:(clear - P0 PT; ul) CMF5) as W6.
  to_cps W6 c5 Hc5' Σ2 MST. intros c6 Hc6.
  destruct (ASTA_unpack RT Σ2 _ _ c6 Hc6) as (ms6 & (-> & ST6) & Hc6'). clear Hc6.
  assert (INP : In (p, 40) (rt_live RT Σ2)) by (rewrite LV2; left; reflexivity).
  eapply (cps_realizes asegs _ _ T c6).
  { eapply (rc_asan_memset RT RC Σ2 PMc (W 0x1f355c) (W (L + -160)) gp (W 0xba7ed0) v0 v1 v2 (W (L + -128)) (W 40) (W p) (W 0) (W 40)
              g3 g4 g5 g6 g7 (W p) (W 0) (W (FB6 + 2208)) s5 s6 (W (FB6 + 2208 + 16)) (W (AShadow.sha FB0)) (W FB0) (W AShadow.SB) s11
              v3 v4 v5 v6 F5 fc5 m5 p 40 z8 lo FDO MST); try reflexivity.
    - clear - P0 PT. ul.
    - lia.
    - split; [intros _; split; [exact ACCP|]| split].
      + left. exists p, 40. split; [exact INP| lia].
      + intros i Hi. apply (acl_live _ _ _ p 40); [exact INP| lia].
      + exact WRP.
    - exact ART5.
    - exact MI5.
    - unfold call_ok. rewrite EL3, SP2, SP1. split; [exact ST6|]. split; [exact LOW|]. split; [clear - LOR; ul|].
      split; [clear - LSPA SPAT; ul| clear - L32; Z.div_mod_to_equations; lia]. }
  { exact Hc6'. }
  clear Hc6'. intros c7 Hc7.
  destruct (ASTA_unpack RT Σ2 _ _ c7 Hc7) as (ms7 & (m7 & RS7 & (ART7 & MI7 & WM7 & ST7) & PR7 & B7) & Hc7'). clear Hc7.
  destruct RS7 as (q0 & q1 & q2 & k1 & k2 & k3 & k4 & k5 & k6 & k7 & q3 & q4 & q5 & q6 & F7 & fc7 & ->).
  rewrite EL3 in ST7, PR7. rewrite (ret_pc_even 0x1f355c ltac:(lia) eq_refl) in Hc7'. change (Z.to_nat 40) with 40%nat in B7.
  pose proof (af_live_range RT AF Σ2 m5 p 40 ART5 INP) as (_ & PR & _). rewrite SP2, SP1 in PR.
  assert (AGS7 : agree_on (fun x => L + -160 <= x < L) m5 m7).
  { apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PR7). intros x Hx. split; [apply acl_stack; clear - Hx LSPA SPAT; ul| clear - Hx PR LOW LOR; lia]. }
  pose proof (rw_cells_agree_nw asegs m5 m7 _ _ CZF5 ltac:(eapply agree_sub; [exact AGS7|]; intros y Hy; cbn [cz_frame cells_size csize Nat.add] in Hy; cbv beta; clear - Hy; lia)) as CZF7.
  (* [comment removed for export] *)
  pose proof (wi_wC L lo p gp (W 0xba7ed0) q0 q1 q2 (W p) k1 k2 k3 k4 k5 k6 k7 (W FB0) (W (L + -128)) (W L) (W 0) (W (FB6 + 2208)) s5 s6
                (W (FB6 + 2208 + 16)) (W (AShadow.sha FB0)) (W FB0) (W AShadow.SB) s11 q3 q4 q5 q6 F7 fc7 m7
                ST7 LOB ltac:(clear - LOR; lia) ltac:(clear - LSPA SPAT; ul) MI7 CZF7) as W8.
  to_cps W8 c7 Hc7' Σ2 MST. intros c8 Hc8.
  destruct (ASTA_unpack RT Σ2 _ _ c8 Hc8) as (ms8 & (-> & ST8) & Hc8'). clear Hc8.
  (* [comment removed for export] *)
  assert (FRS2' : rt_frames RT Σ2 = (FB0, 0%nat) :: rt_frames RT Σ) by (rewrite FRS2; exact FRS1).
  destruct (r0_view1 RT R0 Σ2 m7 FB0 (rt_frames RT Σ) ART7 FRS2' NC0)
    as (fs' & k' & FSW' & Hk' & EFB & G1' & G3' & G2' & C56' & ZA' & ZB' & WFB' & WSH' & WFL' & NAF' & CL_REL).
  rewrite SP2, SP1 in G1', NAF'.
  pose proof (af_frames_align RT AF Σ2 m7 FB0 0 ART7 ltac:(rewrite FRS2'; left; reflexivity)) as (FB064 & FB0g).
  pose proof (af_frames_hi RT AF Σ m FB6 6 ART0 IN6) as F6h. change (fs_size 6) with 4096 in F6h.
  destruct (G3' FB6 6%nat IN6) as (F6e' & F6f'). change (fs_size 6) with 4096 in F6f'.
  assert (AGSm7 : agree_on (fun x => L + -128 <= x < L) m1 m7).
  { apply (agree_trans _ m1 m4 m7 AGS4). apply (agree_trans _ m4 m5 m7).
    - eapply agree_sub; [exact AGS5|]. intros y Hy. cbv beta in *. clear - Hy. lia.
    - eapply agree_sub; [exact AGS7|]. intros y Hy. cbv beta in *. clear - Hy. lia. }
  assert (SUB7 : forall x, aclient (rt_live RT Σ) (rt_frames RT Σ) L x -> aclient (rt_live RT Σ2) (rt_frames RT Σ2) (L + -160) x).
  { intros x Hx. apply (aclient_mono _ _ _ _ _ _ _ Hx); [rewrite LV2, LV1; intros e He; right; exact He| rewrite FRS2'; intros e He; right; exact He| lia]. }
  assert (NP0 : forall x, aclient (rt_live RT Σ) (rt_frames RT Σ) L x -> ~ (p <= x < p + 40)).
  { intros x Hx. apply (newchunk_apart RT AF Σ1 Σ2 m5 p 40 (L + -208) x ART5 LV2 FRS2 SP2 ltac:(rewrite SP1; clear - LOW LOR; lia) ltac:(lia)).
    exact (SUB2 _ Hx). }
  assert (PRm7 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) L Wm m m7).
  { apply (pres_fp_trans _ _ _ _ m m5 m7 PRm5). intros a Ha _. apply PR7; [exact (SUB7 _ Ha)| exact (NP0 _ Ha)]. }
  assert (WMm7 : wmono asegs m m7).
  { apply (wmono_trans _ m m3 m7 WMm3). apply (wmono_trans _ m3 m4 m7 WM4). exact (wmono_trans _ m4 m5 m7 WM5 WM7). }
  assert (PKTW7 : wr_at asegs m7 (FB6 + 2208) 56).
  { apply (wr_at_transport asegs m m7); [| exact WMm7]. apply (rw_cells_wr_at asegs m (FB6 + 2208) _ 56 PKT). cbn. lia. }
  assert (SHP7 : ro_cells asegs m7 (shad FB6 + 281) [C1 z8]).
  { apply (ro_cells_agree asegs m m7 _ _ SHP). intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply PRm7.
    - apply (acl_fshadow _ _ _ FB6 6%nat); [exact IN6| change (fs_size 6) with 4096; rewrite SH6; clear - Ha; lia].
    - unfold Wm. cbn [outside]. unfold shad, SHB in Ha. clear - Ha F6h F6a F6b SP0R. unfold USTACK_TOP, STACK_WIN in *. Z.div_mod_to_equations. lia. }
  assert (SLOTS7 : forall off r, In (off, r) AInit.WI_SLOTS ->
            LibKit.cell ACode.ASEGS m7 (L - 128 + off) 8 (wi_sv (W 0x4081c0) (W spa) s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 r)).
  { intros off r Hin. pose proof (SLOTS off r Hin) as C.
    assert (OFF : 0 <= off /\ off + 8 <= 128).
    { unfold AInit.WI_SLOTS in Hin. cbn [In] in Hin. clear - Hin.
      repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin. }
    eapply (LibKit.cell_agree ACode.ASEGS m1 m7); [| | | exact C]; [clear - LOB LOR OFF; lia| clear - LSPA SPAT OFF; ul|].
    intros x Hx. apply AGSm7. unfold LibKit.inr in Hx. cbv beta. clear - Hx OFF. lia. }
  (* [comment removed for export] *)
  pose proof (wpinit_r2_evt (W 0x26d8b8) (W (L + -128)) gp (W 0xba7ed0) q0 q1 q2 (W L) (W (L + -128)) (W p) k1 k2 k3 k4 k5 k6 k7
                (W FB0) (W 0) (W (FB6 + 2208)) s5 s6 (W (FB6 + 2208 + 16)) (W (AShadow.sha FB0)) (W FB0) (W AShadow.SB) s11 q3 q4 q5 q6
                F7 fc7 m7 fs' (FB6 + 2208) L k' (W 0x4081c0) (W spa) s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) as W9.
  cbv zeta in W9. rewrite <- EFB in W9.
  specialize (W9 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl FSW' Hk' SLOTS7 C56' ZA' ZB').
  assert (ESHP : AShadow.sha (FB6 + 2208 + 40) = shad FB6 + 281) by (unfold AShadow.sha, shad, AShadow.SB, SHB; clear - F64; Z.div_mod_to_equations; lia).
  specialize (W9 ltac:(rewrite ESHP; apply (zeros_of_bytes m7 (shad FB6 + 281) 1); [exact (proj2 SHP7)| right; unfold shad, SHB; clear - F6a; Z.div_mod_to_equations; lia])
                 ltac:(unfold ARt.A_IMG_END; clear - F6g; unfold SEGTOP_A in *; lia)
                 ltac:(unfold AShadow.memrange, AShadow.LOMEM_END, AShadow.HIMEM_BEG, AShadow.HIMEM_END; clear - F6h F6a F6b SP0R; ul)
                 ltac:(clear - F64; Z.div_mod_to_equations; lia)
                 (KBridge.wr_ok_wr_at asegs m7 (FB6 + 2208) 56 (FB6 + 2208 + 40) 8 PKTW7 ltac:(lia) ltac:(lia))
                 WFB' WSH' WFL'
                 ltac:(unfold ARt.A_IMG_END; clear - LOB LOR; lia) ltac:(clear - LSPA SPAT; ul)
                 ltac:(right; clear - G1' LOW LOR; lia) ltac:(right; unfold AShadow.HIMEM_BEG; clear - LOB LOR; lia)
                 ltac:(right; clear - F6b LOW LOR; lia) ltac:(right; clear - F6e'; lia)).
  to_cps W9 c8 Hc8' Σ2 MST. intros c9 Hc9.
  destruct (ASTA_unpack RT Σ2 _ _ c9 Hc9) as (ms9 & (a1' & m9 & a0v & -> & A0Z & A0N & CSUB & ZF9 & HU9 & HG9) & Hc9'). clear Hc9.
  assert (EP : bv_unsigned (W p) = p) by (apply unsigned_lit; clear - P0 PT; ul).
  assert (A01 : a0v = 1) by (apply A0N; rewrite EP; clear - P0; lia). subst a0v.
  assert (IN62 : In (FB6, 6%nat) (rt_frames RT Σ2)) by (rewrite FRS2'; right; exact IN6).
  assert (IN02 : In (FB0, 0%nat) (rt_frames RT Σ2)) by (rewrite FRS2'; left; reflexivity).
  assert (SH0 : shad (FB0 + 64) = shad FB0 + 8) by (unfold shad; clear - FB064; Z.div_mod_to_equations; lia).
  destruct (CL_REL m9 (L + -128) ltac:(rewrite SP2, SP1; clear - LOW LOR; lia)) as (Σ3 & ART9 & FRS3 & LV3 & SP3 & CR3 & AL3 & AM3).
  { intros a NA NX. apply HU9. unfold AInit.FP_r2. rewrite <- EFB. intros [H|[H|[H|H]]]; unfold LibKit.inr in H.
    - apply NA. apply (acl_frame _ _ _ FB6 6%nat); [exact IN62| change (fs_size 6) with 4096; clear - H; lia].
    - apply NA. apply (acl_frame _ _ _ FB0 0%nat); [exact IN02| change (fs_size 0) with 64; clear - H; lia].
    - apply NA. apply (acl_fshadow _ _ _ FB0 0%nat); [exact IN02| change (fs_size 0) with 64; rewrite SH0; exact H].
    - exact (NX H). }
  { exact HG9. } { exact ZF9. }
  pose proof (KBridge.wmono_of_grows asegs m7 m9 HG9) as WM9.
  assert (WV9 : forall x : word, AInit.FP_r2 fs' (FB6 + 2208) k' x -> wview asegs m7 x <> None).
  { unfold AInit.FP_r2. rewrite <- EFB. intros x [H|[H|[H|H]]]; unfold LibKit.inr in H.
    - apply (wr_at_wview m7 (FB6 + 2208) 56); [exact PKTW7| clear - H; lia].
    - exact (wview_of_wr_ok m7 _ _ x WFB' H).
    - exact (wview_of_wr_ok m7 _ _ x WSH' H).
    - exact (wview_of_wr_ok m7 _ _ x WFL' H). }
  pose proof (KBridge.mem_inv_unch asegs m7 m9 _ MI7 HU9 WV9) as MI9.
  pose proof (af_frames_range RT AF Σ2 m5 FB6 6 ART5 ltac:(rewrite FRS2, FRS1; right; exact IN6)) as (_ & _ & _ & F6p).
  specialize (F6p p 40 INP). change (fs_size 6) with 4096 in F6p.
  destruct (r0_live_mem RT R0 Σ2 m7 p 40 ART7 INP) as (MRP & _).
  unfold AShadow.memrange, AShadow.LOMEM_END, AShadow.HIMEM_BEG, AShadow.HIMEM_END in MRP.
  assert (SHB0 : AShadow.SB <= AShadow.sha FB0 /\ AShadow.sha FB0 + 8 <= AShadow.HIMEM_BEG).
  { unfold AShadow.sha, AShadow.SB, AShadow.HIMEM_BEG. unfold SEGTOP_A in FB0g. unfold AIface.FS_SIZE in G1'. clear - FB0g EFB Hk' G1' SP0R.
    unfold USTACK_TOP, STACK_WIN in *. Z.div_mod_to_equations. lia. }
  unfold AShadow.SB, AShadow.HIMEM_BEG in SHB0.
  (* [comment removed for export] *)
  assert (AG79 : forall (Q : Z -> Prop),
            (forall y, Q y -> (y < FB6 + 2248 \/ FB6 + 2256 <= y) /\ (y < fs' \/ fs' + 1085440 <= y) /\ (y < 0x7fff8000 \/ 0x10007fff8000 <= y)) ->
            agree_on Q m7 m9).
  { intros Q HQ. apply (agree_of_unch m7 m9 _ _ HU9). intros x Hx. destruct (HQ _ Hx) as (H1 & H2 & H3).
    unfold AInit.FP_r2. rewrite <- EFB. intros [H|[H|[H|H]]]; unfold LibKit.inr in H.
    - clear - H H1. lia.
    - clear - H H2 EFB Hk'. lia.
    - clear - H H3 SHB0. lia.
    - clear - H H2 Hk'. lia. }
  apply Hk. exists Σ3, p.
  split; [| split; [rewrite LV3, LV2, LV1; reflexivity| split; [exact FRS3| split; [rewrite SP3, SP2, SP1; reflexivity|
            split; [rewrite CR3, CR2, CR1; change (mcost 40) with 0; lia| split; [exact P0| exact P16]]]]]].
  eapply ASTA_conseq; [exact (ASTA_switch RT Σ2 Σ3 PMc _ c9 Hc9' AL3 AM3)|]. intros ms <-.
  exists m9, q0, q1, q2, a1', k2, k3, k4, k5, k6, k7, q3, q4, q5, q6, F7, fc7.
  split; [reflexivity|]. split; [exact ART9|]. split; [exact MI9|].
  split.
  { apply (stk_merge asegs m9 lo (L + -128) L); [exact (KBridge.stk_grows asegs m7 m9 _ _ ST8 HG9)| | clear - LOR; lia].
    apply (KBridge.stk_grows asegs m7 m9 _ _); [| exact HG9]. apply (stk_agree_nw asegs m1 m7); [| exact AGSm7].
    apply (stk_split asegs m1 lo (L + -128) L STK1). clear - LOR. lia. }
  split; [exact (wmono_trans _ _ _ _ WMm7 WM9)|].
  split.
  { apply (pres_fp_trans _ _ _ _ m m7 m9 PRm7). apply (pres_fp_of_unch _ _ _ _ m7 m9 _ HU9).
    unfold AInit.FP_r2. rewrite <- EFB. intros x [H|[H|[H|H]]] Hc'; unfold LibKit.inr in H.
    - unfold Wm. cbn [outside]. clear - H. lia.
    - exfalso. apply (RAP x); [right; right; left; unfold LibKit.inr; unfold FB0 in H; clear - H Hkr; lia|].
      apply (aclient_mono _ _ _ _ _ _ _ Hc'); [auto| auto| clear - LOW LOR; lia].
    - exfalso. apply (RAP x); [right; right; right; unfold LibKit.inr; unfold FB0 in H; rewrite AIface.sha_frame in H; clear - H Hkr; lia|].
      apply (aclient_mono _ _ _ _ _ _ _ Hc'); [auto| auto| clear - LOW LOR; lia].
    - exfalso. apply NAF'. replace (fs' + 4096 + k') with (bv_unsigned x) by (clear - H; lia).
      apply (aclient_mono _ _ _ _ _ _ _ Hc'); [rewrite LV2, LV1; intros e He; right; exact He| rewrite FRS2'; intros e He; right; exact He|
        clear - LOW LOR; lia]. }
  assert (PKTW9 : wr_at asegs m9 (FB6 + 2208) 56) by exact (wr_at_transport asegs m7 m9 _ _ PKTW7 WM9).
  split.
  { assert (B9 : bytes_at asegs m9 (FB6 + 2224) (repeat z8 16)).
    { apply (bytes_at_agree asegs m3 m9 _ _ B3). cbn [length repeat].
      apply (agree_trans _ m3 m4 m9); [apply (agree_of_munch _ _ _ _ MU4); intros y Hy; cbn [outside]; clear - Hy F6b LOW LOR; lia|].
      apply (agree_trans _ m4 m5 m9).
      { apply (agree_of_pres _ _ _ _ _ _ PR5). intros y Hy. apply (acl_frame _ _ _ FB6 6%nat); [exact IN61| change (fs_size 6) with 4096; clear - Hy; lia]. }
      apply (agree_trans _ m5 m7 m9).
      { apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PR7). intros y Hy.
        split; [apply (acl_frame _ _ _ FB6 6%nat); [exact IN62| change (fs_size 6) with 4096; clear - Hy; lia]| clear - Hy F6p; lia]. }
      apply AG79. intros y Hy. clear - Hy F6e' F6h. lia. }
    split; [split; [exact (conj I (conj I I))| exact B9]|].
    apply (wr_at_sub m9 (FB6 + 2208) 56); [exact PKTW9| lia| cbn; lia| cbn; lia]. }
  split.
  { replace (FB6 + 2208 + 40) with (FB6 + 2248) in CSUB by lia.
    apply rw_C8_of_cell; [clear - F6a; lia| clear - F6b SP0R; ul| exact CSUB| apply (wr_at_sub m9 (FB6 + 2208) 56); [exact PKTW9| lia| lia| lia]]. }
  apply (bytes_at_agree asegs m7 m9 _ _ B7). cbn [length repeat]. apply AG79. intros y Hy.
  specialize (G2' p 40 INP). unfold AIface.FS_SIZE in G2'. clear - Hy F6p G2' MRP. lia.
Qed.

End WPI.
