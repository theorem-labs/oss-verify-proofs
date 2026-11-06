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
  Fz_defs Fz_voc Fz_regions Fz_regw Fz_iface Fz_ckit Fz_w1 Fz_w2 Fz_w3 Fz_w4 Fz_w5 Fz_w6 Fz_w7 Fz_cwpi.
From OSSVerify.Proofs.openssl.punycode.lib.A Require I_consts.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require WpEngine LibKit StrKit AShadow ARt ACode ARtIc AIface AFakeStack AInit AA2u ASpecs2 ABridge KBridge.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Abbreviation W z := (Z_to_bv 64 z) (only parsing).

Section A2U.
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

Lemma a2u_cps : forall (Σ : rts RT) PMc (gp tp u0 u1 u2 a0 a3 a4 a5 a6 a7 s6 s9 s10 s11 u3 u4 u5 u6 c0 : word) F fc (m : mem)
    (usp spa lo n d b FB : Z) (lv : byte),
  fdfs_only PMc -> mat_stable PMc -> tp = W 0xba7ed0 ->
  ART RT Σ m -> mem_inv asegs m -> stk asegs m lo spa ->
  rt_sp0 RT Σ - STACK_WIN <= lo -> lo + 0x30000 <= spa -> spa mod 32 = 0 -> spa + 32 <= usp -> usp + 16 <= USTACK_TOP ->
  rt_frames RT Σ = [(FB, 2%nat)] -> In (b, n + 1) (rt_live RT Σ) -> (forall p k, In (p, k) (rt_live RT Σ) -> 0 < k) ->
  b mod 16 = 0 -> 0 <= n < 2^26 ->
  Z.of_nat (length (rt_live RT Σ)) + 1 < LIVE_MAX -> 1 <= rt_credit RT Σ ->
  rw_cells asegs m (usp - 16) [C8 c0; C8 (W RA_FUZZ)] -> fp_invalid c0 (W usp) ->
  bytes_at asegs m (b + n) [z8] ->
  wr_at asegs m (FB + 144) 16 -> acc asegs m (FB + 144) 16 -> stk asegs m (shad FB + 16) (shad FB + 24) ->
  ro_cells asegs m G_MALLOC_IMPL [C8 (W e_cmalloc)] -> ro_cells asegs m G_FREE_IMPL [C8 (W e_cfree)] ->
  rw_cells asegs m G_LATCH [C1 lv] -> bv_unsigned lv <> 0 ->
  cps asegs (ASTA RT Σ PMc (eq (MS (mkR (W 0x1f3274) (W spa) gp tp u0 u1 u2 (W usp) (W spa) a0 (W (FB + 144)) (W 16) a3 a4 a5 a6 a7
                                         (W FB) (W n) (W d) (W b) s6 (W FB) (W SHB) s9 s10 s11 u3 u4 u5 u6)
                                    F (W 0x1f3294) fc None m (seg_rom asegs))))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists (m' : mem) (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) F' fc',
           ms = MS (mkR (W 0x1f32a0) (W spa) gp tp t0' t1' t2' (W usp) (W spa) a0' a1' a2' a3' a4' a5' a6' a7'
                        (W FB) (W n) (W d) (W b) s6 (W FB) (W SHB) s9 s10 s11 t3' t4' t5' t6') F' (W 0x1f32a0) fc' None m' (seg_rom asegs)
           /\ ART RT Σ' m' /\ mem_inv asegs m' /\ stk asegs m' lo spa
           /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) spa [(FB + 144, FB + 160)] m m') c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - 1).
Proof using RC R0.
  intros Σ PMc gp tp u0 u1 u2 a0 a3 a4 a5 a6 a7 s6 s9 s10 s11 u3 u4 u5 u6 c0 F fc m usp spa lo n d b FB lv
    FDO MST -> ART0 MI0 ST0 LOW LOR S32 SPU UT FRS0 INB POS B16 Hn LVB CRB UREC FPI NUL WOUT AOUT SHOUT MIM FIM LAT LVNZ T c Hc Hk.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  assert (LOB : 0x7fff7f800000 <= lo) by (clear - LOW SP0W; ul).
  assert (INF : In (FB, 2%nat) (rt_frames RT Σ)) by (rewrite FRS0; left; reflexivity).
  pose proof (af_frames_range RT AF Σ m FB 2 ART0 INF) as (FBa & FBb & FBc & FBd). change (fs_size 2) with 256 in *.
  pose proof (af_frames_align RT AF Σ m FB 2 ART0 INF) as (FB64 & FBg).
  pose proof (af_frames_hi RT AF Σ m FB 2 ART0 INF) as FBh. change (fs_size 2) with 256 in FBh.
  pose proof (af_live_range RT AF Σ m b (n + 1) ART0 INB) as (B0 & BR & Bimg).
  set (L := spa + -224).
  (* [comment removed for export] *)
  pose proof (fz_wE usp spa lo n d b FB gp (W 0xba7ed0) u0 u1 u2 a0 a3 a4 a5 a6 a7 s6 s9 s10 s11 u3 u4 u5 u6 F fc m
                ST0 LOB ltac:(clear - LOR; lia) ltac:(clear - SPU UT; ul) S32 ltac:(clear - LOB LOR SPU UT; ul)
                (af_client_consts RT AF Σ m ART0) MI0 ltac:(clear - FBa; lia) ltac:(clear - FBb SP0R; ul) ltac:(clear - B0 BR SP0R Hn; ul)) as W1.
  to_cps W1 c Hc Σ MST. intros c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & jl & -> & MU1 & WM1 & MI1 & ST1 & A2F1) & Hc1'). clear Hc1.
  fold L in Hc1', ST1, A2F1, MU1.
  assert (EL : bv_unsigned (W L) = L) by (apply unsigned_lit; unfold L; clear - LOB LOR SPU UT; ul).
  assert (ESPA : bv_unsigned (W spa) = spa) by (apply unsigned_lit; clear - LOB LOR SPU UT; ul).
  assert (EUSP : bv_unsigned (W usp) = usp) by (apply unsigned_lit; clear - LOB LOR SPU UT; ul).
  assert (ART1 : ART RT Σ m1).
  { apply (af_frame RT AF Σ m m1 L ART0 ltac:(unfold L; clear - LOW LOR; lia)); [| exact WM1].
    intros a Ha. apply MU1. cbn [outside]. split; [| exact I]. intros Hin. apply Ha. apply acl_stack. unfold L. clear - Hin SPU UT. ul. }
  eapply (cps_realizes asegs _ _ T c1).
  { eapply (rc_stack_malloc_6 RT RC Σ PMc (W 0x408044) (W L) gp (W 0xba7ed0) u0 u1 u2 (W spa) (W L) (W 2368) (W 6753080) (W 1) a3 a4 a5 a6 a7
              (W SHB) (W n) (W d) (W b) (W 16) (W (FB + 144)) (W SHB) (W b) s10 s11 u3 u4 u5 u6 F fc m1 lo FDO MST); try reflexivity.
    - right. reflexivity.
    - rewrite FRS0. cbn. unfold FRAMES_MAX. lia.
    - exact CRB.
    - exact ART1.
    - exact MI1.
    - unfold call_ok. rewrite EL. split; [exact ST1|]. split; [exact LOW|]. split; [unfold L; clear - LOR; ul|].
      split; [unfold L; clear - SPU UT; ul| unfold L; clear - S32; Z.div_mod_to_equations; lia]. }
  { exact Hc1'. }
  clear Hc1'. intros c2 Hc2. destruct Hc2 as (Σ1 & FB6 & Hc2 & FRS1 & LV1 & SP1 & CR1 & F60 & F664 & F6T).
  destruct (ASTA_unpack RT Σ1 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PR2 & WF2 & WS2) & Hc2'). clear Hc2.
  destruct RS2 as (w0 & w1 & w2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & F2 & fc2 & ->).
  rewrite EL in ST2, PR2. rewrite FRS0 in FRS1. rewrite (ret_pc_even 0x408044 ltac:(lia) eq_refl) in Hc2'.
  change (fs_size 6) with 4096 in WF2, WS2, F6T. change (4096 - 8) with 4088 in WF2. change (4096 / 8) with 512 in WS2.
  assert (IN6 : In (FB6, 6%nat) (rt_frames RT Σ1)) by (rewrite FRS1; left; reflexivity).
  assert (INF1 : In (FB, 2%nat) (rt_frames RT Σ1)) by (rewrite FRS1; right; left; reflexivity).
  pose proof (af_frames_range RT AF Σ1 m2 FB6 6 ART2 IN6) as (_ & F6b & F6c & F6d). change (fs_size 6) with 4096 in *. rewrite SP1 in F6b.
  pose proof (af_frames_align RT AF Σ1 m2 FB6 6 ART2 IN6) as (_ & F6g). unfold SEGTOP_A in F6g.
  pose proof (af_frames_hi RT AF Σ1 m2 FB6 6 ART2 IN6) as F6h. change (fs_size 6) with 4096 in F6h.
  assert (SH6 : shad (FB6 + 4096) = shad FB6 + 512) by (unfold shad; clear - F664; Z.div_mod_to_equations; lia).
  assert (F6lo : FB6 + 4096 <= lo) by (clear - F6b LOW; lia).
  (* [comment removed for export] *)
  set (W1 := [(L, L + 120); (FB6, FB6 + 4096); (shad FB6, shad FB6 + 512); (FB + 144, FB + 160)]).
  assert (AGST2 : agree_on (fun x => L <= x < USTACK_TOP) m1 m2).
  { apply (agree_of_pres _ _ _ _ _ _ PR2). intros x Hx. apply acl_stack. exact Hx. }
  pose proof (rw_cells_agree_nw asegs m1 m2 _ _ A2F1 ltac:(eapply agree_sub; [exact AGST2|]; intros y Hy; cbn [a2u_frame cells_size csize Nat.add] in Hy; cbv beta; unfold L in *; clear - Hy SPU UT; ul)) as A2F2.
  destruct (wr_at_rw_CB m2 FB6 24 (wr_at_sub m2 FB6 4088 FB6 24 WF2 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (jh & HDR2).
  destruct (wr_at_rw_CB m2 (shad FB6) 4 (wr_at_sub m2 (shad FB6) 512 (shad FB6) 4 WS2 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (js & SHA2).
  change (Z.to_nat 24) with 24%nat in HDR2. change (Z.to_nat 4) with 4%nat in SHA2.
  destruct (lib_ro_cells m2 (af_lib_ro RT AF Σ1 m2 ART2)) as (_ & _ & _ & _ & GOTA2 & _).
  pose proof (a2_wA spa lo n d b FB FB6 gp (W 0xba7ed0) w0 w1 w2 e1 e2 e3 e4 e5 e6 e7 s10 s11 w3 w4 w5 w6 F2 fc2 m2 jl jh js
                s11 s10 s9 (W SHB) (W FB) s6 (W b) (W d) (W n) (W FB) (W spa) (W usp) (W 0x1f32a0)
                LOB ltac:(clear - LOR; lia) ltac:(clear - SPU UT; ul) MI2 F664 F6g F6lo F6h A2F2 HDR2 SHA2 GOTA2) as W3.
  to_cps W3 c2 Hc2' Σ1 MST. intros c3 Hc3.
  destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & (m3 & jl' & -> & MU3 & WM3 & MI3 & A2F3 & HDR3 & SHA3) & Hc3'). clear Hc3.
  fold L in Hc3', MU3, A2F3.
  assert (ART3 : ART RT Σ1 m3).
  { apply (af_frame RT AF Σ1 m2 m3 L ART2 ltac:(rewrite SP1; unfold L; clear - LOW LOR; lia)); [| exact WM3].
    intros a Ha. apply MU3. cbn [outside]. split; [| split; [| split; [| exact I]]]; intros Hin; apply Ha.
    - apply acl_stack. unfold L in *. clear - Hin SPU UT. ul.
    - apply (acl_frame _ _ _ FB6 6%nat); [exact IN6| change (fs_size 6) with 4096; clear - Hin; lia].
    - apply (acl_fshadow _ _ _ FB6 6%nat); [exact IN6| change (fs_size 6) with 4096; rewrite SH6; clear - Hin; lia]. }
  assert (PRES3 : rt_pres_fp (rt_live RT Σ1) (rt_frames RT Σ1) L W1 m2 m3).
  { apply (pres_fp_of_munch _ _ _ _ _ m2 m3 MU3). intros x _ Ho. unfold W1 in Ho. cbn [outside] in *. clear - Ho. lia. }
  assert (STK3 : stk asegs m3 lo L).
  { apply (stk_munch _ m2 m3 lo L ST2 MU3 WM3). intros x Hx. cbn [outside]. unfold shad, SHB. clear - Hx F6lo F6g LOB. Z.div_mod_to_equations. lia. }
  pose proof (wr_at_transport asegs m2 m3 _ _ WF2 WM3) as WF3. pose proof (wr_at_transport asegs m2 m3 _ _ WS2 WM3) as WS3.
  unfold a2u_frame2 in A2F3.
  change [C8 (W 0); CB 104 jl'; C8 (W FB6); C8 s11; C8 s10; C8 s9; C8 (W SHB); C8 (W FB); C8 s6; C8 (W b); C8 (W d); C8 (W n); C8 (W FB);
          C8 (W spa); C8 (W usp); C8 (W 0x1f32a0)]
    with ([C8 (W 0); CB 104 jl'; C8 (W FB6)] ++ [C8 s11; C8 s10; C8 s9; C8 (W SHB); C8 (W FB); C8 s6; C8 (W b); C8 (W d); C8 (W n); C8 (W FB);
          C8 (W spa); C8 (W usp); C8 (W 0x1f32a0)]) in A2F3.
  apply rw_cells_app in A2F3. destruct A2F3 as (A2H3 & A2T3). cbn [cells_size csize Nat.add] in A2T3.
  pose proof (stk_of_rw_cells asegs m3 L _ A2H3) as STA3. cbn [cells_size csize Nat.add] in STA3.
  (* [comment removed for export] *)
  eapply (cps_realizes asegs _ _ T c3).
  { eapply (rc_set_shadow RT RC 0xf8 ltac:(unfold set_shadow_vals; do 12 right; left; reflexivity) Σ1 PMc
              (W 0x4080d0) (W L) gp (W 0xba7ed0) w0 w1 w2 (W spa) (W L) (W (shad FB6 + 4)) (W 256) (W 4227012) e3 e4 e5 e6 e7
              (W SHB) (W (shad FB6)) (W FB6) (W b) (W 16) (W (FB + 144)) (W SHB) (W b) (W FB6) (W (shad FB6 + 4)) w3 w4 w5 w6 F2 fc2 m3
              (shad FB6 + 4) 256 lo FDO MST); try reflexivity.
    - unfold set_shadow_vals. do 12 right. left. reflexivity.
    - lia.
    - intros i Hi. exists FB6, 6%nat. split; [exact IN6| change (fs_size 6) with 4096; rewrite SH6; clear - Hi; lia].
    - apply (wr_at_sub m3 (shad FB6) 512); [exact WS3| lia| lia| lia].
    - exact ART3.
    - exact MI3.
    - unfold call_ok. rewrite EL, SP1. split; [exact STK3|]. split; [exact LOW|]. split; [unfold L; clear - LOR; ul|].
      split; [unfold L; clear - SPU UT; ul| unfold L; clear - S32; Z.div_mod_to_equations; lia]. }
  { exact Hc3'. }
  clear Hc3'. intros c4 Hc4. destruct Hc4 as (v4 & Hc4).
  destruct (ASTA_unpack RT Σ1 _ _ c4 Hc4) as (ms4 & (m4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PR4 & B4) & Hc4'). clear Hc4.
  destruct RS4 as (x0 & x1 & x2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & x3 & x4 & x5 & x6 & F4 & fc4 & ->).
  rewrite EL in ST4, PR4. rewrite (ret_pc_even 0x4080d0 ltac:(lia) eq_refl) in Hc4'.
  assert (SH6lo : shad FB6 + 512 <= lo /\ 0xbca000 <= shad FB6) by (unfold shad, SHB; clear - F6lo F6g LOB; Z.div_mod_to_equations; lia).
  assert (LOT : lo <= 2^47) by (clear - LOR SPU UT; ul).
  assert (PRES4 : rt_pres_fp (rt_live RT Σ1) (rt_frames RT Σ1) L W1 m2 m4).
  { apply (pres_fp_trans _ _ _ _ m2 m3 m4 PRES3). apply (pres_fp_of_ex _ _ _ _ _ _ m3 m4 PR4). intros x Hx Ho. unfold W1 in Ho. cbn [outside] in Ho. clear - Hx Ho. lia. }
  pose proof (wr_at_transport asegs m3 m4 _ _ WF3 WM4) as WF4. pose proof (wr_at_transport asegs m3 m4 _ _ WS3 WM4) as WS4.
  assert (AGST4 : agree_on (fun x => L <= x < USTACK_TOP) m3 m4).
  { apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PR4). intros x Hx. split; [apply acl_stack; exact Hx| clear - Hx SH6lo LOR; unfold L in *; lia]. }
  pose proof (stk_agree_nw asegs m3 m4 _ _ STA3 ltac:(eapply agree_sub; [exact AGST4|]; intros y Hy; cbv beta; unfold L in *; clear - Hy SPU UT; ul)) as STA4.
  (* [comment removed for export] *)
  destruct (wr_at_rw_CB m4 (shad FB6 + 260) 36 (wr_at_sub m4 (shad FB6) 512 (shad FB6 + 260) 36 WS4 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (js5 & SHJ4).
  change (Z.to_nat 36) with 36%nat in SHJ4.
  pose proof (a2_wB spa lo FB6 gp (W 0xba7ed0) x0 x1 x2 (W spa) (W L) v4 g1 g2 g3 g4 g5 g6 g7 (W SHB) (W FB6) (W b) (W 16) (W (FB + 144)) (W SHB)
                (W b) (W FB6) x3 x4 x5 x6 F4 fc4 m4 js5 (conj LOB LOT) MI4 F664 F6g F6lo F6h SHJ4) as W5.
  to_cps W5 c4 Hc4' Σ1 MST. intros c5 Hc5.
  destruct (ASTA_unpack RT Σ1 _ _ c5 Hc5) as (ms5 & (m5 & -> & MU5 & WM5 & MI5 & SHM5) & Hc5'). clear Hc5. fold L in Hc5'.
  assert (ART5 : ART RT Σ1 m5).
  { apply (af_frame RT AF Σ1 m4 m5 L ART4 ltac:(rewrite SP1; unfold L; clear - LOW LOR; lia)); [| exact WM5].
    intros a Ha. apply MU5. cbn [outside]. split; [| exact I]. intros Hin. apply Ha.
    apply (acl_fshadow _ _ _ FB6 6%nat); [exact IN6| change (fs_size 6) with 4096; rewrite SH6; clear - Hin; lia]. }
  assert (PRES5 : rt_pres_fp (rt_live RT Σ1) (rt_frames RT Σ1) L W1 m2 m5).
  { apply (pres_fp_trans _ _ _ _ m2 m4 m5 PRES4). apply (pres_fp_of_munch _ _ _ _ _ m4 m5 MU5). intros x _ Ho. unfold W1 in Ho. cbn [outside] in *. clear - Ho. lia. }
  assert (STK5 : stk asegs m5 lo L) by (apply (stk_munch _ m4 m5 lo L ST4 MU5 WM5); intros x Hx; cbn [outside]; clear - Hx SH6lo; lia).
  assert (STA5 : stk asegs m5 L (L + 120)) by (apply (stk_munch _ m4 m5 _ _ STA4 MU5 WM5); intros x Hx; cbn [outside]; clear - Hx SH6lo LOR; unfold L in *; lia).
  pose proof (wr_at_transport asegs m4 m5 _ _ WF4 WM5) as WF5. pose proof (wr_at_transport asegs m4 m5 _ _ WS4 WM5) as WS5.
  eapply (cps_realizes asegs _ _ T c5).
  { eapply (rc_set_shadow RT RC 0 ltac:(unfold set_shadow_vals; left; reflexivity) Σ1 PMc
              (W 0x40817c) (W L) gp (W 0xba7ed0) x0 x1 x2 (W spa) (W L) (W (shad FB6 + 4)) (W 256) (W (-8)) g3 g4 g5 g6 g7
              (W SHB) (W (shad FB6)) (W FB6) (W b) (W 16) (W (FB + 144)) (W SHB) (W b) (W FB6) (W (shad FB6 + 4)) x3 x4 x5 x6 F4 fc4 m5
              (shad FB6 + 4) 256 lo FDO MST); try reflexivity.
    - unfold set_shadow_vals. left. reflexivity.
    - lia.
    - intros i Hi. exists FB6, 6%nat. split; [exact IN6| change (fs_size 6) with 4096; rewrite SH6; clear - Hi; lia].
    - apply (wr_at_sub m5 (shad FB6) 512); [exact WS5| lia| lia| lia].
    - exact ART5.
    - exact MI5.
    - unfold call_ok. rewrite EL, SP1. split; [exact STK5|]. split; [exact LOW|]. split; [unfold L; clear - LOR; ul|].
      split; [unfold L; clear - SPU UT; ul| unfold L; clear - S32; Z.div_mod_to_equations; lia]. }
  { exact Hc5'. }
  clear Hc5'. intros c6 Hc6. destruct Hc6 as (v6 & Hc6).
  destruct (ASTA_unpack RT Σ1 _ _ c6 Hc6) as (ms6 & (m6 & RS6 & (ART6 & MI6 & WM6 & ST6) & PR6 & B6) & Hc6'). clear Hc6.
  destruct RS6 as (y0 & y1 & y2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & y3 & y4 & y5 & y6 & F6 & fc6 & ->).
  rewrite EL in ST6, PR6. rewrite (ret_pc_even 0x40817c ltac:(lia) eq_refl) in Hc6'. change (Z.to_nat 256) with 256%nat in B6.
  (* [comment removed for export] *)
  assert (AG02 : agree_on (fun x => aclient (rt_live RT Σ) (rt_frames RT Σ) spa x) m m2).
  { apply (agree_trans _ m m1 m2).
    - apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbn [outside]. split; [| exact I].
      destruct (aclient_split RT AF Σ m spa _ ART0 Hx); unfold L; clear - H LOW LOR; lia.
    - apply (agree_of_pres _ _ _ _ _ _ PR2). intros x Hx. apply (aclient_mono _ _ _ _ _ _ _ Hx); [auto| auto| unfold L; lia]. }
  assert (STAT02 : forall lo' hi', (forall y, lo' <= y < hi' -> client_static y) -> agree_on (fun y => lo' <= y < hi') m m2).
  { intros lo' hi' H. eapply agree_sub; [exact AG02|]. intros y Hy. apply acl_static. exact (H y Hy). }
  pose proof (ro_cells_agree asegs m m2 _ _ MIM ltac:(apply STAT02; intros y Hy; apply client_static_intro; unfold G_MALLOC_IMPL in *; cbn in Hy; lia)) as MIM2.
  pose proof (ro_cells_agree asegs m m2 _ _ FIM ltac:(apply STAT02; intros y Hy; apply client_static_intro; unfold G_FREE_IMPL in *; cbn in Hy; lia)) as FIM2.
  pose proof (rw_cells_agree_nw asegs m m2 _ _ LAT ltac:(apply STAT02; intros y Hy; apply client_static_intro; unfold G_LATCH in *; cbn in Hy; lia)) as LAT2.
  pose proof (rw_cells_agree_nw asegs m m2 _ _ UREC ltac:(eapply agree_sub; [exact AG02|]; intros y Hy; cbn [cells_size csize Nat.add] in Hy; apply acl_stack; clear - Hy SPU UT; ul)) as UREC2.
  assert (INB1 : In (b, n + 1) (rt_live RT Σ1)) by (rewrite LV1; exact INB).
  pose proof (bytes_at_agree asegs m m2 _ _ NUL ltac:(eapply agree_sub; [exact AG02|]; intros y Hy; cbn [length] in Hy; apply (acl_live _ _ _ b (n + 1)); [exact INB| clear - Hy Hn; lia])) as NUL2.
  assert (AOUT2 : acc asegs m2 (FB + 144) 16).
  { apply (acc_agree m m2 _ _ AOUT ltac:(clear - FBa; lia)). eapply agree_sub; [exact AG02|]. intros y Hy. cbv beta in Hy.
    apply (acl_fshadow _ _ _ FB 2%nat); [exact INF| change (fs_size 2) with 256]. unfold shad in *. clear - Hy FB64. Z.div_mod_to_equations. lia. }
  assert (SHOUT2 : stk asegs m2 (shad FB + 16) (shad FB + 24)).
  { apply (stk_agree_nw asegs m m2 _ _ SHOUT). eapply agree_sub; [exact AG02|]. intros y Hy. cbv beta in Hy.
    apply (acl_fshadow _ _ _ FB 2%nat); [exact INF| change (fs_size 2) with 256]. unfold shad in *. clear - Hy FB64. Z.div_mod_to_equations. lia. }
  assert (WOUT2 : wr_at asegs m2 (FB + 144) 16).
  { apply (wr_at_agree_nw asegs m m2 _ _ WOUT). eapply agree_sub; [exact AG02|]. intros y Hy. cbv beta in Hy.
    apply (acl_frame _ _ _ FB 2%nat); [exact INF| change (fs_size 2) with 256; clear - Hy; lia]. }
  (* [comment removed for export] *)
  assert (A2T2 : rw_cells asegs m2 (L + 120) [C8 s11; C8 s10; C8 s9; C8 (W SHB); C8 (W FB); C8 s6; C8 (W b); C8 (W d); C8 (W n); C8 (W FB);
                                             C8 (W spa); C8 (W usp); C8 (W 0x1f32a0)]).
  { unfold a2u_frame in A2F2.
    pose proof (rw_cells_skip m2 L [C8 (W 0); CB 112 jl] _ A2F2) as H. cbn [cells_size csize Nat.add] in H. exact H. }
  assert (PRES6 : rt_pres_fp (rt_live RT Σ1) (rt_frames RT Σ1) L W1 m2 m6).
  { apply (pres_fp_trans _ _ _ _ m2 m5 m6 PRES5). apply (pres_fp_of_ex _ _ _ _ _ _ m5 m6 PR6). intros x Hx Ho. unfold W1 in Ho. cbn [outside] in Ho. clear - Hx Ho. lia. }
  pose proof (wr_at_transport asegs m5 m6 _ _ WF5 WM6) as WF6. pose proof (wr_at_transport asegs m5 m6 _ _ WS5 WM6) as WS6.
  assert (AGST6 : agree_on (fun x => L <= x < USTACK_TOP) m5 m6).
  { apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PR6). intros x Hx. split; [apply acl_stack; exact Hx| clear - Hx SH6lo LOR; unfold L in *; lia]. }
  pose proof (stk_agree_nw asegs m5 m6 _ _ STA5 ltac:(eapply agree_sub; [exact AGST6|]; intros y Hy; cbv beta; unfold L in *; clear - Hy SPU UT; ul)) as STA6.
  assert (SHM6 : rw_cells asegs m6 (shad FB6 + 260) (a2_sh2 (Z_to_bv 8 (-8)))).
  { apply (rw_cells_agree_nw asegs m5 m6 _ _ SHM5). apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PR6). intros y Hy.
    change (Z.of_nat (cells_size (a2_sh2 (Z_to_bv 8 (-8))))) with 36 in Hy.
    split; [apply (acl_fshadow _ _ _ FB6 6%nat); [exact IN6| change (fs_size 6) with 4096; rewrite SH6; clear - Hy; lia]| clear - Hy; lia]. }
  destruct (wr_at_rw_CB m6 (FB6 + 2208) 56 (wr_at_sub m6 FB6 4088 (FB6 + 2208) 56 WF6 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (jp & PKJ6).
  change (Z.to_nat 56) with 56%nat in PKJ6.
  (* [comment removed for export] *)
  pose proof (a2_wC spa lo FB FB6 b gp (W 0xba7ed0) y0 y1 y2 v6 h1 h2 h3 h4 h5 h6 h7 y3 y4 y5 y6 F6 fc6 m6 jp
                ST6 (conj LOB LOT) ltac:(clear - LOR; lia) ltac:(clear - SPU UT; ul) (af_client_consts RT AF Σ1 m6 ART6) MI6
                F664 F6g F6lo F6h ltac:(clear - FBa; lia) ltac:(clear - FBb SP0R; ul) SHM6 PKJ6) as W7.
  to_cps W7 c6 Hc6' Σ1 MST. intros c7 Hc7.
  destruct (ASTA_unpack RT Σ1 _ _ c7 Hc7) as (ms7 & (m7 & a2' & a6' & j2 & j3 & j5 & j7 & eb & -> & MU7 & WM7 & MI7 & ST7 & SHM7 & PKT7 & EBE) & Hc7').
  clear Hc7. fold L in Hc7', ST7. replace (spa + -240) with (L + -16) in MU7 by (unfold L; lia). replace (spa + -224) with L in MU7 by reflexivity.
  assert (ART7 : ART RT Σ1 m7).
  { apply (af_frame RT AF Σ1 m6 m7 (L + -16) ART6 ltac:(rewrite SP1; unfold L; clear - LOW LOR; lia)); [| exact WM7].
    intros a Ha. apply MU7. cbn [outside]. split; [| split; [| split; [| exact I]]]; intros Hin; apply Ha.
    - apply acl_stack. unfold L in *. clear - Hin SPU UT. ul.
    - apply (acl_fshadow _ _ _ FB6 6%nat); [exact IN6| change (fs_size 6) with 4096; rewrite SH6; clear - Hin; lia].
    - apply (acl_frame _ _ _ FB6 6%nat); [exact IN6| change (fs_size 6) with 4096; clear - Hin; lia]. }
  assert (PRES7 : rt_pres_fp (rt_live RT Σ1) (rt_frames RT Σ1) L W1 m2 m7).
  { apply (pres_fp_trans _ _ _ _ m2 m6 m7 PRES6). apply (pres_fp_of_munch _ _ _ _ _ m6 m7 MU7). intros x Hx Ho. unfold W1 in Ho. cbn [outside] in *.
    destruct (aclient_split RT AF Σ1 m2 L _ ART2 Hx) as [H|H]; rewrite ?SP1 in H; clear - Ho H LOW LOR; unfold L in *; lia. }
  pose proof (wr_at_transport asegs m6 m7 _ _ WF6 WM7) as WF7. pose proof (wr_at_transport asegs m6 m7 _ _ WS6 WM7) as WS7.
  assert (STA7 : stk asegs m7 L (L + 120)) by (apply (stk_munch _ m6 m7 _ _ STA6 MU7 WM7); intros x Hx; cbn [outside]; clear - Hx SH6lo F6lo LOR; unfold L in *; lia).
  assert (AGP7 : forall (Q : Z -> Prop), (forall y, Q y -> aclient (rt_live RT Σ1) (rt_frames RT Σ1) L y /\ outside W1 y) -> agree_on Q m2 m7).
  { intros Q HQ. exact (agree_of_pres_fp _ _ _ _ _ _ _ PRES7 HQ). }
  assert (STKOUT : forall y, L + 120 <= y < USTACK_TOP -> aclient (rt_live RT Σ1) (rt_frames RT Σ1) L y /\ outside W1 y).
  { intros y Hy. split; [apply acl_stack; clear - Hy; lia|]. unfold W1. cbn [outside]. clear - Hy F6lo SH6lo FBb LOW LOR. unfold L in *. lia. }
  assert (STATOUT : forall y, client_static y -> aclient (rt_live RT Σ1) (rt_frames RT Σ1) L y /\ outside W1 y).
  { intros y Hy. split; [apply acl_static; exact Hy|]. pose proof (client_static_range y Hy) as CR. unfold W1. cbn [outside].
    unfold SEGTOP_A in *. clear - CR F6g SH6lo FBg LOB LOR. unfold L in *. lia. }
  assert (UW2 : uw_chain m2 (W L) (W spa) [0x1f32a0; 0x1f2f94]).
  { cbn [uw_chain]. rewrite EL, ESPA. split; [unfold L; lia|]. split; [clear - SPU UT; ul|]. exists (W usp). split.
    { pose proof (rw_cells_skip m2 (L + 120) [C8 s11; C8 s10; C8 s9; C8 (W SHB); C8 (W FB); C8 s6; C8 (W b); C8 (W d); C8 (W n); C8 (W FB); C8 (W spa)] _ A2T2) as H.
      cbn [cells_size csize Nat.add] in H. replace (L + 120 + Z.of_nat 88) with (spa - 16) in H by (unfold L; lia). exact H. }
    rewrite EUSP. split; [exact SPU|]. split; [exact UT|]. exists c0. split; [exact UREC2| exact FPI]. }
  assert (UW7 : uw_chain m7 (W L) (W spa) [0x1f32a0; 0x1f2f94]).
  { apply (uw_chain_agree_fp _ m2 m7 _ _ UW2). rewrite ESPA. apply AGP7. intros y Hy. apply STKOUT. unfold L. clear - Hy. lia. }
  pose proof (ro_cells_agree asegs m2 m7 _ _ MIM2 ltac:(apply AGP7; intros y Hy; apply STATOUT; apply client_static_intro; unfold G_MALLOC_IMPL in *; cbn in Hy; lia)) as MIM7.
  pose proof (rw_cells_agree_nw asegs m2 m7 _ _ LAT2 ltac:(apply AGP7; intros y Hy; apply STATOUT; apply client_static_intro; unfold G_LATCH in *; cbn in Hy; lia)) as LAT7.
  (* [comment removed for export] *)
  assert (Z7 : bytes_at asegs m7 (shad FB6 + 276) (repeat z8 7)).
  { unfold a2_sh2 in SHM7. apply rw_cells_skip in SHM7. apply rw_cells_app in SHM7. destruct SHM7 as (H & _).
    change (Z.of_nat (cells_size (repeat (C1 (Z_to_bv 8 (-14))) 16))) with 16 in H. replace (shad FB6 + 260 + 16) with (shad FB6 + 276) in H by lia.
    exact (proj2 (proj1 H)). }
  assert (ESHP : shad (FB6 + 2208) = shad FB6 + 276) by (unfold shad; clear - F664; Z.div_mod_to_equations; lia).
  assert (ACP7 : acc asegs m7 (FB6 + 2224) 16).
  { apply (acc_sub asegs m7 (FB6 + 2208) 56); [| lia| lia].
    apply (acc_zero_run asegs m7 (FB6 + 2208) 7); [clear - F664; Z.div_mod_to_equations; lia| clear - F60; lia| rewrite ESHP; exact Z7]. }
  assert (SHP7 : ro_cells asegs m7 (shad FB6 + 281) [C1 z8]).
  { split; [exact (conj I I)|]. pose proof (bytes_at_sub m7 (shad FB6 + 276) (repeat z8 7) 5 1 Z7 ltac:(cbn; lia)) as H.
    replace (shad FB6 + 276 + Z.of_nat 5) with (shad FB6 + 281) in H by lia. exact H. }
  (* [comment removed for export] *)
  eapply (cps_realizes asegs _ _ T c7).
  { eapply (wpinit_cps RT RC R0 Σ1 PMc gp (W 0xba7ed0) y0 y1 y2 (W L) a2' (W 0) (W 0) (W SHB) a6' h7 (W SHB) (W (shad FB6)) (W FB6)
              (W (FB6 + 2208)) (W 16) (W (FB + 144)) (W (-1)) (W b) (W FB6) (W (shad FB6 + 4)) y3 y4 y5 y6 F6 fc6 m7
              L lo spa FB6 (FB + 144) j2 j3 j5 j7 eb lv FDO MST eq_refl ART7 MI7 ST7).
    - rewrite SP1. exact LOW.
    - unfold L. clear - LOR. lia.
    - unfold L. clear - S32. Z.div_mod_to_equations. lia.
    - unfold L. lia.
    - clear - SPU UT. ul.
    - rewrite FRS1. intros f k [E|[E|[]]]; injection E as <- <-; lia.
    - exact IN6.
    - rewrite FRS1. cbn. unfold FRAMES_MAX. lia.
    - rewrite LV1. clear - LVB. lia.
    - rewrite CR1. clear - CRB. lia.
    - exact UW7.
    - exact PKT7.
    - exact ACP7.
    - exact SHP7.
    - exact MIM7.
    - exact LAT7.
    - exact LVNZ. }
  { exact Hc7'. }
  clear Hc7'. intros c8 Hc8. destruct Hc8 as (Σ2 & p & Hc8 & LV2 & FRS2 & SP2 & CR2 & P0 & P16).
  destruct (ASTA_unpack RT Σ2 _ _ c8 Hc8) as (ms8 & (m8 & z0 & z1 & z2 & i1 & i2 & i3 & i4 & i5 & i6 & i7 & z3 & z4 & z5 & z6 & F8 & fc8 & -> & ART8 & MI8 & ST8 & WM8 & PR8 & PKC8 & PKS8 & PZ8) & Hc8').
  clear Hc8.
  (* [comment removed for export] *)
  assert (WMIN : forall y, outside W1 y -> outside [(FB6 + 2224, FB6 + 2240); (FB6 + 2248, FB6 + 2256)] y).
  { intros y Ho. unfold W1 in Ho. cbn [outside] in *. clear - Ho. lia. }
  assert (PRES8 : rt_pres_fp (rt_live RT Σ1) (rt_frames RT Σ1) L W1 m2 m8).
  { apply (pres_fp_trans _ _ _ _ m2 m7 m8 PRES7). intros a Ha Ho. exact (PR8 a Ha (WMIN _ Ho)). }
  pose proof (wr_at_transport asegs m7 m8 _ _ WF7 WM8) as WF8. pose proof (wr_at_transport asegs m7 m8 _ _ WS7 WM8) as WS8.
  assert (AGST8 : agree_on (fun x => L <= x < USTACK_TOP) m7 m8).
  { apply (agree_of_pres_fp _ _ _ _ _ _ _ PR8). intros x Hx. split; [apply acl_stack; exact Hx|]. cbn [outside]. clear - Hx F6lo LOR. unfold L in *. lia. }
  pose proof (stk_agree_nw asegs m7 m8 _ _ STA7 ltac:(eapply agree_sub; [exact AGST8|]; intros y Hy; cbv beta; unfold L in *; clear - Hy SPU UT; ul)) as STA8.
  assert (AG78 : forall (Q : Z -> Prop), (forall y, Q y -> (FB6 <= y < FB6 + 4088 \/ shad FB6 <= y < shad FB6 + 512)
                                             /\ (y < FB6 + 2224 \/ FB6 + 2240 <= y) /\ (y < FB6 + 2248 \/ FB6 + 2256 <= y)) -> agree_on Q m7 m8).
  { intros Q HQ. apply (agree_of_pres_fp _ _ _ _ _ _ _ PR8). intros y Hy. destruct (HQ y Hy) as (H1 & H2 & H3). split.
    - destruct H1 as [H1|H1]; [apply (acl_frame _ _ _ FB6 6%nat); [exact IN6| change (fs_size 6) with 4096; clear - H1; lia]|
                               apply (acl_fshadow _ _ _ FB6 6%nat); [exact IN6| change (fs_size 6) with 4096; rewrite SH6; exact H1]].
    - cbn [outside]. clear - H2 H3. lia. }
  assert (IN62 : In (FB6, 6%nat) (rt_frames RT Σ2)) by (rewrite FRS2; exact IN6).
  assert (INF2 : In (FB, 2%nat) (rt_frames RT Σ2)) by (rewrite FRS2; exact INF1).
  assert (INB2 : In (b, n + 1) (rt_live RT Σ2)) by (rewrite LV2; right; exact INB1).
  assert (INP2 : In (p, 40) (rt_live RT Σ2)) by (rewrite LV2; left; reflexivity).
  assert (SHAPP : (FB6 + 4096 <= shad FB6 \/ shad FB6 + 512 <= FB6) /\ (FB + 256 <= shad FB6 \/ shad FB6 + 512 <= FB)
                  /\ 2147450880 <= shad FB6 /\ shad FB6 + 512 <= 17594333495296).
  { unfold shad, SHB. clear - F6h FBh F60 F6b FBa FBb SP0R. unfold USTACK_TOP, STACK_WIN in *. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  unfold pkt_cells0 in PKT7.
  assert (PKA8 : rw_cells asegs m8 (FB6 + 2208) [C8 (W 0); C8 (W (FB + 144))]).
  { pose proof (proj1 (proj1 (rw_cells_app m7 (FB6 + 2208) [C8 (W 0); C8 (W (FB + 144))] _) PKT7)) as H.
    apply (rw_cells_agree_nw asegs m7 m8 _ _ H). apply AG78. intros y Hy. cbn [cells_size csize Nat.add] in Hy. clear - Hy SHAPP. lia. }
  assert (PKM8 : rw_cells asegs m8 (FB6 + 2240) [C8 (W 16)]).
  { pose proof (rw_cells_skip m7 (FB6 + 2208) [C8 (W 0); C8 (W (FB + 144)); CB 8 j2; CB 8 j3] _ PKT7) as H. cbn [cells_size csize Nat.add] in H.
    apply rw_cells_head in H. replace (FB6 + 2208 + Z.of_nat 32) with (FB6 + 2240) in H by lia.
    apply (rw_cells_agree_nw asegs m7 m8 _ _ H). apply AG78. intros y Hy. cbn [cells_size csize Nat.add] in Hy. clear - Hy SHAPP. lia. }
  assert (PKE8 : rw_cells asegs m8 (FB6 + 2256) [C1 eb]).
  { pose proof (rw_cells_skip m7 (FB6 + 2208) [C8 (W 0); C8 (W (FB + 144)); CB 8 j2; CB 8 j3; C8 (W 16); CB 8 j5] _ PKT7) as H. cbn [cells_size csize Nat.add] in H.
    apply rw_cells_head in H. replace (FB6 + 2208 + Z.of_nat 48) with (FB6 + 2256) in H by lia.
    apply (rw_cells_agree_nw asegs m7 m8 _ _ H). apply AG78. intros y Hy. cbn [cells_size csize Nat.add] in Hy. clear - Hy SHAPP. lia. }
  assert (Z8 : bytes_at asegs m8 (shad FB6 + 276) (repeat z8 7)).
  { apply (bytes_at_agree asegs m7 m8 _ _ Z7). apply AG78. intros y Hy. cbn [length repeat] in Hy. clear - Hy SHAPP. lia. }
  assert (ZL8 : bytes_at asegs m8 (shad FB6 + 4) (repeat z8 256)).
  { apply (bytes_at_agree asegs m6 m8 _ _ B6). rewrite repeat_length. apply (agree_trans _ m6 m7 m8).
    - apply (agree_of_munch _ _ _ _ MU7). intros y Hy. cbn [outside]. clear - Hy SHAPP SH6lo LOR. unfold L in *. lia.
    - apply AG78. intros y Hy. clear - Hy SHAPP. lia. }
  (* [comment removed for export] *)
  destruct (r0_view RT R0 Σ2 m8 ART8 MI8 ltac:(rewrite FRS2, FRS1; intros f k [E|[E|[]]]; injection E as <- <-; lia))
    as (fs & Tt & ctx & thr & h & (RTOK & ICOK & FSRT & FSWF & UAR & FSW) & GEO & Hh & HINT & ZF & RWR & RAP & CL_IDLE & _).
  destruct GEO as (G1 & G2 & G3 & GD1 & GD2 & GD3). rewrite SP2, SP1 in G1.
  destruct (G3 FB6 6%nat IN62 ltac:(lia)) as (G6a & G6b). change (fs_size 6) with 4096 in G6b.
  destruct (G3 FB 2%nat INF2 ltac:(lia)) as (GFa & GFb). change (fs_size 2) with 256 in GFb.
  pose proof (G2 b (n + 1) INB2) as GB.
  destruct GD1 as (GD1b & GD1c & GD1d). destruct GD2 as (GD2b & GD2c & GD2d). destruct GD3 as (GD3b & GD3c & GD3d).
  rewrite SP2, SP1 in GD1b, GD2b, GD3b.
  pose proof FSW as ((FSW1 & FSW2) & FSW3 & FSW4).
  unfold AIface.FS_SIZE, ARt.A_IMG_END, AShadow.SB, AShadow.HIMEM_BEG, AShadow.HIMEM_END in *.
  set (N := n / 8 * 8 + 8).
  assert (HN : n + 1 <= N <= n + 8) by (unfold N; clear - Hn; Z.div_mod_to_equations; lia).
  destruct (af_acc_live RT AF Σ2 m8 b (n + 1) ART8 INB2) as (WRB8 & ACB8).
  destruct (af_live_slack RT AF Σ2 m8 b (n + 1) ART8 INB2) as (slack & SLK & SLEN & _).
  destruct (r0_live_mem RT R0 Σ2 m8 b (n + 1) ART8 INB2) as (MRB & SHWB).
  assert (BN8 : (b + N) mod 8 = 0) by (unfold N; clear - B16; Z.div_mod_to_equations; lia).
  assert (BOFF : b + N <= 0x10000 \/ 0xbca000 <= b).
  { destruct Bimg as [H|H]; [left| right; unfold SEGTOP_A in H; exact H]. unfold N. clear - H B16 Hn. Z.div_mod_to_equations. lia. }
  assert (RDB : LibKit.rd_ok m8 b N).
  { destruct (wr_at_rw_CB m8 b (n + 1) WRB8 ltac:(lia)) as (jb & JB). pose proof (proj2 (proj1 JB)) as BJ. cbn [cells_bytes cbytes] in BJ. rewrite app_nil_r in BJ.
    pose proof (proj1 (proj1 (proj1 JB))) as LJ. cbn [cell_wf] in LJ.
    pose proof (rd_ok_bytesA m8 b jb BJ ltac:(rewrite LJ, Z2Nat.id by lia; clear - BOFF HN; lia)) as R1. rewrite LJ, Z2Nat.id in R1 by lia.
    pose proof (bytes_at_sub m8 (b + (n + 1)) slack 0 (Z.to_nat (N - (n + 1))) SLK ltac:(apply Nat2Z.inj_le; rewrite Nat2Z.inj_add, Z2Nat.id by lia; cbn; unfold N in *; clear - SLEN B16 Hn HN; Z.div_mod_to_equations; lia)) as S2.
    rewrite Z.add_0_r in S2.
    pose proof (rd_ok_bytesA m8 (b + (n + 1)) _ S2) as R2. rewrite firstn_length, skipn_length in R2. cbn [skipn] in R2.
    assert (LS : Z.of_nat (Nat.min (Z.to_nat (N - (n + 1))) (length slack - 0)) = N - (n + 1)).
    { rewrite Nat.sub_0_r. rewrite Nat.min_l; [apply Z2Nat.id; lia|]. apply Nat2Z.inj_le. rewrite Z2Nat.id by lia. unfold N in *. clear - SLEN B16 Hn HN. Z.div_mod_to_equations. lia. }
    rewrite LS in R2. specialize (R2 ltac:(clear - BOFF HN Hn; lia)).
    intros i Hi. destruct (Z_lt_le_dec i (n + 1)) as [LT|GE]; [apply R1; lia|].
    replace (b + i) with (b + (n + 1) + (i - (n + 1))) by lia. apply R2. lia. }
  assert (NUL8 : bytes_at asegs m8 (b + n) [z8]).
  { pose proof (F6d b (n + 1) INB1) as D6. pose proof (FBd b (n + 1) INB) as DF.
    destruct (af_fshadow_apart RT AF Σ1 m2 FB6 6 ART2 IN6) as (SA6 & _). specialize (SA6 b (n + 1) INB1). change (fs_size 6) with 4096 in SA6. rewrite SH6 in SA6.
    apply (bytes_at_agree asegs m2 m8 _ _ NUL2). apply (agree_of_pres_fp _ _ _ _ _ _ _ PRES8). intros y Hy. cbn [length] in Hy.
    split; [apply (acl_live _ _ _ b (n + 1)); [exact INB1| clear - Hy Hn; lia]|]. unfold W1. cbn [outside].
    clear - Hy Hn D6 DF SA6 BR LOW LOR. unfold L in *. lia. }
  assert (NULM : m8 (W (b + n)) = Some (Z_to_bv 8 0)).
  { pose proof (bytes_offA m8 (b + n) [z8] 0 NUL8 ltac:(cbn [length]; clear - BOFF HN Hn; lia) ltac:(cbn; lia)) as H. rewrite Z.add_0_r in H. exact H. }
  assert (EB8 : (bv_unsigned (zxb eb) mod 2 ^ 8) mod 2 = 0).
  { unfold zxb. pose proof (bv_unsigned_in_range _ eb) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R.
    change (2 ^ 8) with 256. rewrite unsigned_lit by (clear - R; lia). rewrite (Z.mod_small (bv_unsigned eb) 256) by (clear - R; lia). exact EBE. }
  destruct (lib_ro_cells m8 (af_lib_ro RT AF Σ2 m8 ART8)) as (_ & _ & _ & _ & _ & GOTP8 & GOTW8).
  pose proof (af_lib_shadow RT AF Σ2 m8 ART8) as LSH. unfold LIB_SHADOW in LSH. apply Forall_cons_iff in LSH. destruct LSH as (XNS & _). cbn [fst snd map] in XNS.
  pose proof (r0_xn_shadow RT R0 Σ2 m8 ART8) as XNW.
  assert (AGP8 : forall (Q : Z -> Prop), (forall y, Q y -> aclient (rt_live RT Σ1) (rt_frames RT Σ1) L y /\ outside W1 y) -> agree_on Q m2 m8).
  { intros Q HQ. exact (agree_of_pres_fp _ _ _ _ _ _ _ PRES8 HQ). }
  assert (FBSH : forall y, shad FB <= y < shad FB + 32 -> aclient (rt_live RT Σ1) (rt_frames RT Σ1) L y /\ outside W1 y).
  { intros y Hy. split; [apply (acl_fshadow _ _ _ FB 2%nat); [exact INF1| change (fs_size 2) with 256; unfold shad in *; clear - Hy FB64; Z.div_mod_to_equations; lia]|].
    destruct (af_fshadow_apart RT AF Σ1 m2 FB6 6 ART2 IN6) as (_ & SA). specialize (SA FB 2%nat INF1). change (fs_size 6) with 4096 in SA. change (fs_size 2) with 256 in SA. rewrite SH6 in SA.
    destruct (af_fshadow_apart RT AF Σ1 m2 FB 2 ART2 INF1) as (_ & SB'). specialize (SB' FB6 6%nat IN6). change (fs_size 6) with 4096 in SB'. change (fs_size 2) with 256 in SB'.
    pose proof (af_frames_disj RT AF Σ1 m2 FB6 6 FB 2 [] [(FB, 2%nat)] ART2 FRS1 ltac:(left; reflexivity)) as DJ. change (fs_size 6) with 4096 in DJ. change (fs_size 2) with 256 in DJ.
    unfold W1. cbn [outside]. unfold shad, SHB in *. clear - Hy SA SB' DJ FBh F6h FB64 F664 FBa F60 LOB LOR FBb SP0R. unfold L, USTACK_TOP, STACK_WIN in *. Z.div_mod_to_equations. lia. }
  assert (AOUT8 : acc asegs m8 (FB + 144) 16).
  { apply (acc_agree m2 m8 _ _ AOUT2 ltac:(clear - FBa; lia)). apply AGP8. intros y Hy. apply FBSH. unfold shad in *. clear - Hy FB64. Z.div_mod_to_equations. lia. }
  assert (SHOUT8 : stk asegs m8 (shad FB + 16) (shad FB + 24)).
  { apply (stk_agree_nw asegs m2 m8 _ _ SHOUT2). apply AGP8. intros y Hy. apply FBSH. clear - Hy. lia. }
  assert (WOUT8 : wr_at asegs m8 (FB + 144) 16).
  { apply (wr_at_transport asegs m2 m8 _ _ WOUT2). apply (wmono_trans _ m2 m3 m8 WM3). apply (wmono_trans _ m3 m4 m8 WM4). apply (wmono_trans _ m4 m5 m8 WM5).
    apply (wmono_trans _ m5 m6 m8 WM6). exact (wmono_trans _ m6 m7 m8 WM7 WM8). }
  assert (STKW8 : stk asegs m8 lo (L + 120)) by (apply (stk_merge asegs m8 lo L (L + 120) ST8 STA8); unfold L; clear - LOR; lia).
  assert (ESH6 : forall k, AShadow.sha FB6 + k = shad FB6 + k) by (intros; reflexivity).
  assert (ESHO : AShadow.sha (FB + 144) = shad FB + 18 /\ AShadow.sha (FB + 144 + 16 - 1) = shad FB + 19 /\ (shad FB) mod 8 = 0).
  { unfold AShadow.sha, shad, AShadow.SB, SHB. clear - FB64. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  assert (K0 : LibKit.cell ACode.ASEGS m8 (FB6 + 2208) 8 (W 0)) by exact (KBridge.cell_C8 asegs m8 _ _ (proj1 (rw_cells_head m8 _ _ _ PKA8))).
  assert (K8 : LibKit.cell ACode.ASEGS m8 (FB6 + 2208 + 8) 8 (W (FB + 144))).
  { pose proof (rw_cells_tail m8 _ _ _ PKA8) as H. cbn [csize] in H. exact (KBridge.cell_C8 asegs m8 _ _ (proj1 H)). }
  assert (K16 : LibKit.cell ACode.ASEGS m8 (FB6 + 2208 + 16) 8 (W 0)).
  { replace (FB6 + 2208 + 16) with (FB6 + 2224) by lia. exact (KBridge.cell_C8 asegs m8 _ _ (proj1 (rw_cells_head m8 _ _ _ PKC8))). }
  assert (K24 : LibKit.cell ACode.ASEGS m8 (FB6 + 2208 + 24) 8 (W 0)).
  { pose proof (rw_cells_tail m8 _ _ _ PKC8) as H. cbn [csize] in H. replace (FB6 + 2224 + Z.of_nat 8) with (FB6 + 2208 + 24) in H by lia.
    exact (KBridge.cell_C8 asegs m8 _ _ (proj1 H)). }
  assert (K32 : LibKit.cell ACode.ASEGS m8 (FB6 + 2208 + 32) 8 (W 16)).
  { replace (FB6 + 2208 + 32) with (FB6 + 2240) by lia. exact (KBridge.cell_C8 asegs m8 _ _ (proj1 PKM8)). }
  assert (K40 : LibKit.cell ACode.ASEGS m8 (FB6 + 2208 + 40) 8 (W p)).
  { replace (FB6 + 2208 + 40) with (FB6 + 2248) by lia. exact (KBridge.cell_C8 asegs m8 _ _ (proj1 PKS8)). }
  assert (K48 : LibKit.cell ACode.ASEGS m8 (FB6 + 2208 + 48) 1 (zxb eb)).
  { replace (FB6 + 2208 + 48) with (FB6 + 2256) by lia. exact (KBridge.cell_C1 asegs m8 _ _ (proj1 PKE8)). }
  (* [comment removed for export] *)
  pose proof (a2_w0 (W 0x4081c0) (W L) gp (W 0xba7ed0) z0 z1 z2 (W spa) (W L) i1 i2 i3 i4 i5 i6 i7 (W SHB) (W (shad FB6)) (W FB6) (W (FB6 + 2208))
                (W 16) (W (FB + 144)) (W (-1)) (W b) (W FB6) (W (shad FB6 + 4)) z3 z4 z5 z6 F8 fc8 m8) as W8.
  to_cps W8 c8 Hc8' Σ2 MST. intros c8b Hc8b.
  destruct (ASTA_unpack RT Σ2 _ _ c8b Hc8b) as (ms8b & -> & Hc8b'). clear Hc8b.
  (* [comment removed for export] *)
  pose proof (a2u_evt (W 0x4081c0) (W L) gp (W 0xba7ed0) z0 z1 z2 (W spa) (W L) (W 1) i1 i2 i3 i4 i5 i6 i7 (W SHB) (W (shad FB6)) (W FB6) (W (FB6 + 2208))
                (W 16) (W (FB + 144)) (W (-1)) (W b) (W FB6) (W (shad FB6 + 4)) z3 z4 z5 z6 F8 fc8 m8
                fs Tt ctx thr h L FB6 b n N (FB + 144) p (zxb eb)
                eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl) as W9.
  specialize (W9 ltac:(clear - Hn; lia) ltac:(clear - HN; lia) B0 ltac:(clear - HN BR SP0R; ul) RDB NULM
                 ltac:(unfold N; clear - B16 Hn; Z.div_mod_to_equations; lia)).
  pose proof (af_live_range RT AF Σ2 m8 p 40 ART8 INP2) as (_ & PRg & Pimg). rewrite SP2, SP1 in PRg.
  specialize (W9 ltac:(unfold AShadow.memrange, AShadow.LOMEM_END, AShadow.HIMEM_BEG, AShadow.HIMEM_END in *; clear - MRB HN Hn; lia)
                 (addr_ok_of_acc m8 b (n + 1) ltac:(clear - B0; lia) ltac:(clear - BR SP0R; ul) ACB8)
                 (SHWB ltac:(clear - Hn; lia)) K0 K8 K16 K24 K32 K40 K48 EB8 ltac:(clear - P0 PRg SP0R; ul)).
  unfold ARt.A_IMG_END, AShadow.HIMEM_BEG, AShadow.HIMEM_END in W9. change AShadow.SB with 2147450880 in W9.
  specialize (W9 RTOK ICOK FSRT FSWF UAR (conj (KBridge.cell_C8 asegs m8 _ _ GOTP8) (KBridge.cell_C8 asegs m8 _ _ GOTW8))
                 (img_ok_ro m8 0xc7860 0xc7865 MI8 ltac:(lia) ltac:(lia))
                 (KBridge.cell_of_bytes asegs m8 (AShadow.sha AA2u.XNA) 1 (W 5) XNS)
                 (shw_ok_of_stk m8 0x80010f08 0x80010f10 AA2u.XNA 4 XNW ltac:(lia) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate))
                 FSW Hh HINT ZF RWR F664 ltac:(clear - F6g; lia) ltac:(clear - F6h; lia) ltac:(clear - F6b SP0R; ul)).
  specialize (W9 (zeros_of_bytes m8 (shad FB6 + 276) 7 Z8 ltac:(right; clear - SH6lo; lia))
                 (zeros_of_bytes m8 (shad FB6 + 4) 256 ZL8 ltac:(right; clear - SH6lo; lia))).
  assert (WS8o : LibKit.wr_ok asegs m8 (shad FB6) 512) by exact (KBridge.wr_ok_wr_at asegs m8 (shad FB6) 512 (shad FB6) 512 WS8 ltac:(lia) ltac:(lia)).
  specialize (W9 ltac:(apply (AImg.wr_ok_rd_ok m8 (AShadow.sha FB6) 296); [apply (LibKit.wr_ok_sub asegs m8 (shad FB6) 512); [exact WS8o| change (AShadow.sha FB6) with (shad FB6); lia| change (AShadow.sha FB6) with (shad FB6); lia]| unfold ARt.A_IMG_END; change (AShadow.sha FB6) with (shad FB6); clear - SH6lo; lia| change (AShadow.sha FB6) with (shad FB6); clear - SHAPP; lia])
                 (KBridge.wr_ok_wr_at asegs m8 (shad FB6) 512 (AShadow.sha FB6 + 288) 3 WS8 ltac:(change (AShadow.sha FB6) with (shad FB6); lia) ltac:(change (AShadow.sha FB6) with (shad FB6); lia))
                 (KBridge.wr_ok_wr_at asegs m8 FB6 4088 (FB6 + 32) 2048 WF8 ltac:(lia) ltac:(lia))
                 (KBridge.wr_ok_wr_at asegs m8 FB6 4088 (FB6 + 2224) 16 WF8 ltac:(lia) ltac:(lia))
                 (KBridge.wr_ok_wr_at asegs m8 FB6 4088 (FB6 + 2304) 4 WF8 ltac:(lia) ltac:(lia))
                 (KBridge.wr_ok_wr_at asegs m8 FB6 4088 (FB6 + 2320) 6 WF8 ltac:(lia) ltac:(lia))).
  destruct ESHO as (ESO1 & ESO2 & ESO3).
  specialize (W9 ltac:(clear - FBg; unfold SEGTOP_A in *; lia)
                 ltac:(unfold AShadow.memrange, AShadow.LOMEM_END, AShadow.HIMEM_BEG, AShadow.HIMEM_END; clear - FBh FBa FBb SP0R; ul)
                 (addr_ok_of_acc m8 (FB + 144) 16 ltac:(clear - FBa; lia) ltac:(clear - FBb SP0R; ul) AOUT8)
                 (shw_ok_of_stk m8 (shad FB + 16) (shad FB + 24) (FB + 144) 16 SHOUT8
                    ltac:(unfold shad, SHB; clear - FBa; Z.div_mod_to_equations; lia)
                    ltac:(rewrite ESO1; clear - ESO3; Z.div_mod_to_equations; lia) ltac:(rewrite ESO2; clear - ESO3; Z.div_mod_to_equations; lia))
                 (KBridge.wr_ok_wr_at asegs m8 (FB + 144) 16 (FB + 144) 16 WOUT8 ltac:(lia) ltac:(lia))
                 ltac:(unfold L; clear - LOB LOR; lia) ltac:(unfold L; clear - SPU UT; ul) ltac:(unfold L; clear - S32; Z.div_mod_to_equations; lia)
                 (KBridge.wr_ok_stk asegs m8 lo (L + 120) (L - 2400) 2496 STKW8 ltac:(unfold L; clear - LOR; lia) ltac:(lia))).
  pose proof (F6d b (n + 1) INB1) as D6. pose proof (FBd b (n + 1) INB) as DF.
  pose proof (af_frames_disj RT AF Σ1 m2 FB6 6 FB 2 [] [(FB, 2%nat)] ART2 FRS1 ltac:(left; reflexivity)) as DJ. change (fs_size 6) with 4096 in DJ. change (fs_size 2) with 256 in DJ.
  assert (SEP : AA2u.a2u_sep fs L FB6 (FB + 144) b N).
  { unfold AA2u.a2u_sep, AIface.FS_SIZE, AShadow.SB, AShadow.HIMEM_BEG.
    split; [right; clear - G1 LOW LOR; unfold L; lia|]. split; [right; clear - F6lo LOR; unfold L; lia|]. split; [right; clear - FBb LOW LOR; unfold L; lia|].
    split; [right; clear - BR HN LOW LOR; unfold L; lia|]. split; [clear - DJ; lia|]. split; [right; clear - GFa; lia|]. split; [right; clear - G6a; lia|].
    split; [clear - GB HN BN8 FSW4 Hn; Z.div_mod_to_equations; lia|]. split; [clear - DF HN BN8 FB64 Hn; Z.div_mod_to_equations; lia|].
    split; [clear - D6 HN BN8 F664 Hn; Z.div_mod_to_equations; lia|]. right. clear - LOB LOR. unfold L. lia. }
  specialize (W9 SEP
                 ltac:(unfold AFakeStack.fsrt_sep; clear - GD1b GD2b GD3b G1 LOW LOR; unfold L; lia)
                 ltac:(unfold ASpecs2.dom3_sep; clear - GD1c GD2c GD3c G6a G6b; lia)
                 ltac:(unfold ASpecs2.dom3_sep; clear - GD1c GD2c GD3c GFa GFb; lia)
                 ltac:(unfold ASpecs2.dom3_sep; clear - GD1c GD2c GD3c; lia)
                 ltac:(unfold ASpecs2.dom3_sep; clear - GD1d GD2d GD3d; lia)).
  to_cps W9 c8b Hc8b' Σ2 MST. intros c9 Hc9.
  destruct (ASTA_unpack RT Σ2 _ _ c9 Hc9) as (ms9 & (ra9 & r0 & r1 & r2 & o0 & o1 & o2 & o3 & o4 & o5 & o6 & o7 & s4' & s6' & s7' & s8' & s9' & s10' & s11' & r3 & r4 & r5 & r6
                                                   & m9 & h' & -> & CL16 & CL24 & CL32 & Hh' & HINT9 & ZF9 & HU9 & HG9) & Hc9'). clear Hc9.
  pose proof (KBridge.wmono_of_grows asegs m8 m9 HG9) as WM9.
  (* [comment removed for export] *)
  assert (ART9 : ART RT Σ2 m9).
  { apply (CL_IDLE m9 (L - 2400) ltac:(rewrite SP2, SP1; unfold L; clear - LOW LOR; lia)); [| exact HG9| exists h'; split; [exact Hh'| exact HINT9]| exact ZF9].
    intros a NA NR. apply HU9. unfold AA2u.a2u_FP. intros [H|[H|[H|[H|[H|[H|[H|H]]]]]]]; unfold LibKit.inr in H; try (exact (NR H)); apply NA.
    - apply acl_stack. unfold L in *. clear - H SPU UT. ul.
    - apply (acl_frame _ _ _ FB6 6%nat); [exact IN62| change (fs_size 6) with 4096; clear - H; lia].
    - apply (acl_frame _ _ _ FB6 6%nat); [exact IN62| change (fs_size 6) with 4096; clear - H; lia].
    - apply (acl_frame _ _ _ FB6 6%nat); [exact IN62| change (fs_size 6) with 4096; clear - H; lia].
    - apply (acl_frame _ _ _ FB6 6%nat); [exact IN62| change (fs_size 6) with 4096; clear - H; lia].
    - apply (acl_fshadow _ _ _ FB6 6%nat); [exact IN62| change (fs_size 6) with 4096; rewrite SH6; change (AShadow.sha FB6) with (shad FB6) in H; clear - H; lia].
    - apply (acl_frame _ _ _ FB 2%nat); [exact INF2| change (fs_size 2) with 256; clear - H; lia]. }
  assert (WV9 : forall x : word, AA2u.a2u_FP fs L FB6 (FB + 144) x -> wview asegs m8 x <> None).
  { unfold AA2u.a2u_FP. intros x [H|[H|[H|[H|[H|[H|[H|H]]]]]]]; unfold LibKit.inr in H.
    - apply (stk_wview m8 lo (L + 120)); [exact STKW8| unfold L in *; clear - H LOR; lia].
    - apply (wr_at_wview m8 FB6 4088); [exact WF8| clear - H; lia].
    - apply (wr_at_wview m8 FB6 4088); [exact WF8| clear - H; lia].
    - apply (wr_at_wview m8 FB6 4088); [exact WF8| clear - H; lia].
    - apply (wr_at_wview m8 FB6 4088); [exact WF8| clear - H; lia].
    - apply (wr_at_wview m8 (shad FB6) 512); [exact WS8| change (AShadow.sha FB6) with (shad FB6) in H; clear - H; lia].
    - apply (wr_at_wview m8 (FB + 144) 16); [exact WOUT8| clear - H; lia].
    - destruct RWR as (RW1 & RW2 & RW3 & RW4). destruct H as [H|[H|[H|H]]]; unfold LibKit.inr in H;
        [exact (wview_of_wr_ok m8 _ _ x RW1 H)| exact (wview_of_wr_ok m8 _ _ x RW2 H)| exact (wview_of_wr_ok m8 _ _ x RW3 H)| exact (wview_of_wr_ok m8 _ _ x RW4 H)]. }
  pose proof (KBridge.mem_inv_unch asegs m8 m9 _ MI8 HU9 WV9) as MI9.
  assert (SUB12 : forall x sp', sp' <= L -> aclient (rt_live RT Σ1) (rt_frames RT Σ1) L x -> aclient (rt_live RT Σ2) (rt_frames RT Σ2) sp' x).
  { intros x sp' Hs Hx. apply (aclient_mono _ _ _ _ _ _ _ Hx); [rewrite LV2; intros e He; right; exact He| rewrite FRS2; auto| exact Hs]. }
  assert (PRES9 : rt_pres_fp (rt_live RT Σ1) (rt_frames RT Σ1) L W1 m2 m9).
  { apply (pres_fp_trans _ _ _ _ m2 m8 m9 PRES8). apply (pres_fp_of_unch _ _ _ _ m8 m9 _ HU9).
    unfold AA2u.a2u_FP. intros x [H|[H|[H|[H|[H|[H|[H|H]]]]]]] Hc' Ho; unfold LibKit.inr in H; unfold W1 in Ho; cbn [outside] in Ho.
    - destruct (aclient_split RT AF Σ1 m2 L _ ART2 Hc') as [H'|H']; rewrite ?SP1 in H'; clear - H H' Ho LOW LOR; unfold L in *; lia.
    - clear - H Ho. lia.
    - clear - H Ho. lia.
    - clear - H Ho. lia.
    - clear - H Ho. lia.
    - change (AShadow.sha FB6) with (shad FB6) in H. clear - H Ho. lia.
    - clear - H Ho. lia.
    - apply (RAP x H). rewrite SP2, SP1. apply (SUB12 _ (rt_sp0 RT Σ - STACK_WIN)); [unfold L; clear - LOW LOR; lia| exact Hc']. }
  pose proof (wr_at_transport asegs m8 m9 _ _ WF8 WM9) as WF9. pose proof (wr_at_transport asegs m8 m9 _ _ WS8 WM9) as WS9.
  pose proof (KBridge.stk_grows asegs m8 m9 _ _ ST8 HG9) as ST9. pose proof (KBridge.stk_grows asegs m8 m9 _ _ STA8 HG9) as STA9.
  (* [comment removed for export] *)
  assert (AG89 : forall (Q : Z -> Prop),
            (forall y, Q y -> (y < L - 2400 \/ L + 96 <= y) /\ (y < FB6 + 32 \/ FB6 + 2240 <= y) /\ (y < FB6 + 2304 \/ FB6 + 2326 <= y)
                              /\ (y < shad FB6 + 288 \/ shad FB6 + 291 <= y) /\ (y < FB + 144 \/ FB + 160 <= y)
                              /\ (y < fs \/ fs + 1085440 <= y) /\ (y < AShadow.sha (fs + 36864) \/ AShadow.sha (fs + 36864) + 131072 <= y)) ->
            agree_on Q m8 m9).
  { intros Q HQ. apply (agree_of_unch m8 m9 _ _ HU9). intros x Hx. destruct (HQ _ Hx) as (H1 & H2 & H3 & H4 & H5 & H6 & H7).
    unfold AA2u.a2u_FP, AIface.ring_FP. change (AShadow.sha FB6) with (shad FB6).
    intros [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]; unfold LibKit.inr in H; clear - H H1 H2 H3 H4 H5 H6 H7; lia. }
  assert (RSH : 2147450880 <= AShadow.sha (fs + 36864) /\ AShadow.sha (fs + 36864) + 131072 <= 17594333495296).
  { unfold AShadow.sha, AShadow.SB. clear - FSW1 G1 SP0R. unfold USTACK_TOP, STACK_WIN in *. Z.div_mod_to_equations. lia. }
  pose proof (af_frames_range RT AF Σ2 m8 FB6 6 ART8 IN62) as (_ & _ & _ & F6p). specialize (F6p p 40 INP2). change (fs_size 6) with 4096 in F6p.
  pose proof (af_frames_range RT AF Σ2 m8 FB 2 ART8 INF2) as (_ & _ & _ & FBp). specialize (FBp p 40 INP2). change (fs_size 2) with 256 in FBp.
  destruct (r0_live_mem RT R0 Σ2 m8 p 40 ART8 INP2) as (MRP & _).
  unfold AShadow.memrange, AShadow.LOMEM_END, AShadow.HIMEM_BEG, AShadow.HIMEM_END in MRP.
  pose proof (G2 p 40 INP2) as GP.
  assert (SHQ : forall y, shad FB6 <= y < shad FB6 + 512 ->
            y < L - 2400 /\ (y < FB6 \/ FB6 + 4096 <= y) /\ (y < FB + 144 \/ FB + 160 <= y) /\ (y < fs \/ fs + 1085440 <= y)
            /\ AShadow.sha (fs + 36864) + 131072 <= y).
  { intros y Hy. split; [clear - Hy SH6lo LOR; unfold L; lia|]. split; [clear - Hy SHAPP; lia|]. split; [clear - Hy SHAPP; lia|].
    split; [clear - Hy SHAPP FSW2; lia|]. unfold AShadow.sha, AShadow.SB, shad, SHB in *. clear - Hy G6a FSW4 F664. Z.div_mod_to_equations. lia. }
  assert (FQ : forall y, FB6 <= y < FB6 + 4096 ->
            y < L - 2400 /\ (y < FB + 144 \/ FB + 160 <= y) /\ fs + 1085440 <= y /\ (y < shad FB6 \/ shad FB6 + 512 <= y)
            /\ (y < AShadow.sha (fs + 36864) \/ AShadow.sha (fs + 36864) + 131072 <= y)).
  { intros y Hy. split; [clear - Hy F6lo LOR; unfold L; lia|]. split; [clear - Hy DJ; lia|]. split; [clear - Hy G6a; lia|].
    split; [clear - Hy SHAPP; lia|]. clear - Hy RSH F6h. lia. }
  assert (PQ : forall y, p <= y < p + 40 ->
            y < L - 2400 /\ (y < FB6 \/ FB6 + 4096 <= y) /\ (y < FB + 144 \/ FB + 160 <= y) /\ (y < fs \/ fs + 1085440 <= y)
            /\ (y < shad FB6 \/ shad FB6 + 512 <= y) /\ (y < AShadow.sha (fs + 36864) \/ AShadow.sha (fs + 36864) + 131072 <= y)).
  { intros y Hy. split; [clear - Hy PRg LOW LOR; unfold L; lia|]. split; [clear - Hy F6p; lia|]. split; [clear - Hy FBp; lia|].
    split; [clear - Hy GP; lia|]. split; [clear - Hy MRP SHAPP; lia|]. clear - Hy MRP RSH. lia. }
  assert (SHP9 : ro_cells asegs m9 (shad FB6 + 281) [C1 z8]).
  { split; [exact (conj I I)|]. pose proof (bytes_at_sub m8 (shad FB6 + 276) (repeat z8 7) 5 1 Z8 ltac:(cbn; lia)) as H.
    replace (shad FB6 + 276 + Z.of_nat 5) with (shad FB6 + 281) in H by lia.
    apply (bytes_at_agree asegs m8 m9 _ _ H). apply AG89. intros y Hy. cbn [length firstn skipn repeat] in Hy.
    destruct (SHQ y ltac:(clear - Hy; lia)) as (Q1 & Q2 & Q3 & Q4 & Q5). clear - Hy Q1 Q2 Q3 Q4 Q5. lia. }
  assert (PKS9 : rw_cells asegs m9 (FB6 + 2248) [C8 (W p)]).
  { apply (rw_cells_agree_nw asegs m8 m9 _ _ PKS8). apply AG89. intros y Hy. cbn [cells_size csize Nat.add] in Hy.
    destruct (FQ y ltac:(clear - Hy; lia)) as (Q1 & Q2 & Q3 & Q4 & Q5). clear - Hy Q1 Q2 Q3 Q4 Q5. lia. }
  assert (PZ9 : bytes_at asegs m9 p (repeat z8 40)).
  { apply (bytes_at_agree asegs m8 m9 _ _ PZ8). apply AG89. intros y Hy. cbn [length repeat] in Hy.
    destruct (PQ y ltac:(clear - Hy; lia)) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6). clear - Hy Q1 Q2 Q3 Q4 Q5 Q6. lia. }
  assert (P09 : ro_cells asegs m9 p [C8 (W 0)]).
  { split; [exact (conj I I)|]. pose proof (bytes_at_sub m9 p (repeat z8 40) 0 8 PZ9 ltac:(cbn; lia)) as H. rewrite Z.add_0_r in H. exact H. }
  destruct (af_acc_live RT AF Σ2 m9 p 40 ART9 INP2) as (WRP9 & ACP9).
  assert (SHP0 : ro_cells asegs m9 (shad p) [C1 z8]).
  { split; [exact (conj I I)|]. apply (I_consts.acc_granule_zero m9 p); [clear - P16; Z.div_mod_to_equations; lia|].
    apply (acc_sub asegs m9 p 40); [exact ACP9| lia| lia]. }
  assert (AGP9 : forall (Q : Z -> Prop), (forall y, Q y -> aclient (rt_live RT Σ1) (rt_frames RT Σ1) L y /\ outside W1 y) -> agree_on Q m2 m9).
  { intros Q HQ. exact (agree_of_pres_fp _ _ _ _ _ _ _ PRES9 HQ). }
  pose proof (ro_cells_agree asegs m2 m9 _ _ FIM2 ltac:(apply AGP9; intros y Hy; apply STATOUT; apply client_static_intro; unfold G_FREE_IMPL in *; cbn in Hy; lia)) as FIM9.
  destruct (lib_ro_cells m9 (af_lib_ro RT AF Σ2 m9 ART9)) as (_ & _ & _ & GOTF9 & _).
  (* [comment removed for export] *)
  pose proof (a2_wD L lo FB6 p ra9 gp (W 0xba7ed0) r0 r1 r2 (W spa) o0 o1 o2 o3 o4 o5 o6 o7 (W SHB) (W (shad FB6)) s4' s6' s7' s8' s9' s10' s11' r3 r4 r5 r6
                F8 fc8 m9 ST9 (conj LOB LOT) ltac:(unfold L; clear - LOR; lia) ltac:(unfold L; clear - SPU UT; ul)
                (af_client_consts RT AF Σ2 m9 ART9) MI9 F664 F6g F6lo F6h P0 P16 ltac:(clear - PRg LOW; lia)
                SHP9 (proj1 PKS9) SHP0 P09 FIM9 GOTF9) as W10.
  to_cps W10 c9 Hc9' Σ2 MST. intros c10 Hc10.
  destruct (ASTA_unpack RT Σ2 _ _ c10 Hc10) as (ms10 & (m10 & jf & -> & MU10 & WM10 & MI10 & ST10 & WCF10) & Hc10'). clear Hc10.
  assert (EL10 : bv_unsigned (W (L + -64)) = L + -64) by (apply unsigned_lit; unfold L; clear - LOB LOR SPU UT; ul).
  assert (ART10 : ART RT Σ2 m10).
  { apply (af_frame RT AF Σ2 m9 m10 (L + -80) ART9 ltac:(rewrite SP2, SP1; unfold L; clear - LOW LOR; lia)); [| exact WM10].
    intros a Ha. apply MU10. cbn [outside]. split; [| exact I]. intros Hin. apply Ha. apply acl_stack. unfold L in *. clear - Hin SPU UT. ul. }
  assert (PRES10 : rt_pres_fp (rt_live RT Σ1) (rt_frames RT Σ1) L W1 m2 m10).
  { apply (pres_fp_trans _ _ _ _ m2 m9 m10 PRES9). apply (pres_fp_of_munch _ _ _ _ _ m9 m10 MU10). intros x Hx _. cbn [outside]. split; [| exact I].
    destruct (aclient_split RT AF Σ1 m2 L _ ART2 Hx) as [H|H]; rewrite ?SP1 in H; clear - H LOW LOR; unfold L in *; lia. }
  pose proof (wr_at_transport asegs m9 m10 _ _ WF9 WM10) as WF10. pose proof (wr_at_transport asegs m9 m10 _ _ WS9 WM10) as WS10.
  assert (STA10 : stk asegs m10 L (L + 120)) by (apply (stk_munch _ m9 m10 _ _ STA9 MU10 WM10); intros x Hx; cbn [outside]; clear - Hx; lia).
  assert (UW10 : uw_chain m10 (W L) (W spa) [0x1f32a0; 0x1f2f94]).
  { apply (uw_chain_agree_fp _ m2 m10 _ _ UW2). rewrite ESPA. apply (agree_of_pres_fp _ _ _ _ _ _ _ PRES10). intros y Hy. apply STKOUT. unfold L. clear - Hy. lia. }
  assert (UWF : unwind_ok m10 (W 0x26efac) (W L) (W (L + -64))).
  { split; [rewrite (unsigned_lit 0x26efac) by lia; unfold ALLOC_RAS; do 8 right; left; reflexivity|]. right.
    exists [0x408484; 0x1f32a0; 0x1f2f94]. split; [rewrite (unsigned_lit 0x26efac) by lia; unfold ALLOC_CHAINS; do 3 right; left; reflexivity|].
    cbn [uw_chain]. rewrite EL10, EL. split; [lia|]. split; [unfold L; clear - SPU UT; ul|]. exists (W spa). split.
    { unfold wc_frame in WCF10.
      pose proof (rw_cells_skip m10 (L + -64) [CB 8 jf; C8 (W (FB6 + 2208)); C8 s4'; C8 (W (shad FB6)); C8 (W SHB); C8 (W L)] _ WCF10) as H.
      cbn [cells_size csize Nat.add] in H. replace (L + -64 + Z.of_nat 48) with (L - 16) in H by lia. exact H. }
    cbn [uw_chain] in UW10. rewrite EL in UW10. exact UW10. }
  eapply (cps_realizes asegs _ _ T c10).
  { eapply (rc_free RT RC Σ2 PMc (W 0x26efac) (W (L + -64)) gp (W 0xba7ed0) r0 (W 2046316) r2 (W L) (W (FB6 + 2248)) (W p) (W 519360) (W 540)
              (W 2046316) (W 5937536) o5 o6 o7 (W 519360) (W SHB) (W (shad FB6 + 281)) (W 0) s6' s7' s8' s9' s10' s11' r3 r4 r5 r6 F8 fc8 m10
              p 40 lo FDO MST INP2); try reflexivity.
    - exact ART10.
    - exact MI10.
    - unfold call_ok. rewrite EL10, SP2, SP1. split; [exact ST10|]. split; [exact LOW|]. split; [unfold L; clear - LOR; ul|].
      split; [unfold L; clear - SPU UT; ul| unfold L; clear - S32; Z.div_mod_to_equations; lia].
    - exact UWF. }
  { exact Hc10'. }
  clear Hc10'. intros c11 Hc11. destruct Hc11 as (Σ3 & v11 & Hc11 & LV3 & FRS3 & SP3 & CR3).
  destruct (ASTA_unpack RT Σ3 _ _ c11 Hc11) as (ms11 & (m11 & RS11 & (ART11 & MI11 & ST11) & PR11) & Hc11'). clear Hc11.
  destruct RS11 as (q0 & q1 & q2 & k1 & k2 & k3 & k4 & k5 & k6 & k7 & q3 & q4 & q5 & q6 & F11 & fc11 & ->).
  rewrite EL10 in ST11, PR11. rewrite (ret_pc_even 0x26efac ltac:(lia) eq_refl) in Hc11'.
  assert (LV3' : rt_live RT Σ3 = rt_live RT Σ1).
  { rewrite LV3, LV2. apply live_remove_head. apply (live_fresh RT AF Σ2 m8 [] p 40 (rt_live RT Σ1) ART8 LV2 ltac:(lia)).
    intros e He. cbn [app] in He. rewrite LV1 in He. destruct e as (pe, ke). exact (POS pe ke He). }
  rewrite FRS2 in FRS3. rewrite LV3', FRS2 in PR11.
  assert (PRES11 : rt_pres_fp (rt_live RT Σ1) (rt_frames RT Σ1) L W1 m2 m11).
  { apply (pres_fp_trans _ _ _ _ m2 m10 m11 PRES10). intros a Ha _. apply PR11. apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto| auto| lia]. }
  assert (AGC11 : forall (Q : Z -> Prop), (forall y, Q y -> (L + -64 <= y < USTACK_TOP) \/ (FB6 <= y < FB6 + 4088) \/ (shad FB6 <= y < shad FB6 + 512)) -> agree_on Q m10 m11).
  { intros Q HQ. apply (agree_of_pres _ _ _ _ _ _ PR11). intros y Hy. destruct (HQ y Hy) as [H|[H|H]].
    - apply acl_stack. exact H.
    - apply (acl_frame _ _ _ FB6 6%nat); [exact IN6| change (fs_size 6) with 4096; clear - H; lia].
    - apply (acl_fshadow _ _ _ FB6 6%nat); [exact IN6| change (fs_size 6) with 4096; rewrite SH6; exact H]. }
  pose proof (wr_at_agree_nw asegs m10 m11 _ _ WF10 ltac:(apply AGC11; intros y Hy; cbv beta in Hy; right; left; exact Hy)) as WF11.
  pose proof (wr_at_agree_nw asegs m10 m11 _ _ WS10 ltac:(apply AGC11; intros y Hy; cbv beta in Hy; right; right; exact Hy)) as WS11.
  pose proof (stk_agree_nw asegs m10 m11 _ _ STA10 ltac:(apply AGC11; intros y Hy; cbv beta in Hy; left; unfold L in *; clear - Hy SPU UT; ul)) as STA11.
  pose proof (rw_cells_agree_nw asegs m10 m11 _ _ WCF10 ltac:(apply AGC11; intros y Hy; cbn [wc_frame cells_size csize Nat.add] in Hy; left; unfold L in *; clear - Hy SPU UT; ul)) as WCF11.
  assert (AG910 : forall (Q : Z -> Prop), (forall y, Q y -> y < L + -80 \/ L <= y) -> agree_on Q m9 m10).
  { intros Q HQ. apply (agree_of_munch _ _ _ _ MU10). intros y Hy. cbn [outside]. split; [| exact I]. specialize (HQ y Hy). clear - HQ. lia. }
  assert (SHP11 : ro_cells asegs m11 (shad FB6 + 281) [C1 z8]).
  { apply (ro_cells_agree asegs m10 m11); [apply (ro_cells_agree asegs m9 m10 _ _ SHP9)|].
    - apply AG910. intros y Hy. cbn [cells_size csize Nat.add] in Hy. left. clear - Hy SH6lo LOR. unfold L. lia.
    - apply AGC11. intros y Hy. cbn [cells_size csize Nat.add] in Hy. right; right. clear - Hy. lia. }
  assert (PKS11 : rw_cells asegs m11 (FB6 + 2248) [C8 (W p)]).
  { apply (rw_cells_agree_nw asegs m10 m11); [apply (rw_cells_agree_nw asegs m9 m10 _ _ PKS9)|].
    - apply AG910. intros y Hy. cbn [cells_size csize Nat.add] in Hy. left. clear - Hy F6lo LOR. unfold L. lia.
    - apply AGC11. intros y Hy. cbn [cells_size csize Nat.add] in Hy. right; left. clear - Hy. lia. }
  (* [comment removed for export] *)
  pose proof (a2_wE L lo FB6 gp (W 0xba7ed0) q0 q1 q2 v11 k1 k2 k3 k4 k5 k6 k7 (W (FB6 + 2208)) s4' (W (shad FB6)) (W SHB) (W L) (W spa)
                s6' s7' s8' s9' s10' s11' q3 q4 q5 q6 F11 fc11 m11 jf (W p)
                ST11 (conj LOB LOT) ltac:(unfold L; clear - LOR; lia) ltac:(unfold L; clear - SPU UT; ul) MI11 F664 F6g F6lo F6h SHP11 PKS11 WCF11) as W12.
  to_cps W12 c11 Hc11' Σ3 MST. intros c12 Hc12.
  destruct (ASTA_unpack RT Σ3 _ _ c12 Hc12) as (ms12 & (m12 & -> & MU12 & WM12 & MI12 & ST12 & PKZ12) & Hc12'). clear Hc12.
  assert (IN63 : In (FB6, 6%nat) (rt_frames RT Σ3)) by (rewrite FRS3; exact IN6).
  assert (ART12 : ART RT Σ3 m12).
  { apply (af_frame RT AF Σ3 m11 m12 L ART11 ltac:(rewrite SP3, SP2, SP1; unfold L; clear - LOW LOR; lia)); [| exact WM12].
    intros a Ha. apply MU12. cbn [outside]. split; [| exact I]. intros Hin. apply Ha.
    apply (acl_frame _ _ _ FB6 6%nat); [exact IN63| change (fs_size 6) with 4096; clear - Hin; lia]. }
  assert (PRES12 : rt_pres_fp (rt_live RT Σ1) (rt_frames RT Σ1) L W1 m2 m12).
  { apply (pres_fp_trans _ _ _ _ m2 m11 m12 PRES11). apply (pres_fp_of_munch _ _ _ _ _ m11 m12 MU12). intros x _ Ho. unfold W1 in Ho. cbn [outside] in *. clear - Ho. lia. }
  pose proof (wr_at_transport asegs m11 m12 _ _ WF11 WM12) as WF12. pose proof (wr_at_transport asegs m11 m12 _ _ WS11 WM12) as WS12.
  assert (STA12 : stk asegs m12 L (L + 120)) by (apply (stk_munch _ m11 m12 _ _ STA11 MU12 WM12); intros x Hx; cbn [outside]; clear - Hx F6lo LOR; unfold L in *; lia).
  (* [comment removed for export] *)
  assert (SPL9 : rw_cells asegs m9 (L + 16) [C8 (W (shad FB6 + 4)); C8 (W FB6); C8 (W FB6)]).
  { assert (WR : wr_at asegs m9 (L + 16) 24) by (apply (stk_wr_at m9 L (L + 120)); [exact STA9| lia| lia| lia]).
    apply (proj2 (rw_cells_app m9 (L + 16) [C8 (W (shad FB6 + 4))] [C8 (W FB6); C8 (W FB6)])). split.
    - apply rw_C8_of_cell; [unfold L; clear - LOB LOR; lia| unfold L; clear - SPU UT; ul| exact CL16| apply (wr_at_sub m9 (L + 16) 24); [exact WR| lia| lia| lia]].
    - cbn [cells_size csize Nat.add]. apply rw_cells_join2.
      + apply rw_C8_of_cell; [unfold L; clear - LOB LOR; lia| unfold L; clear - SPU UT; ul| replace (L + 16 + Z.of_nat 8) with (L + 24) by lia; exact CL24|
                               apply (wr_at_sub m9 (L + 16) 24); [exact WR| lia| lia| lia]].
      + cbn [csize]. apply rw_C8_of_cell; [unfold L; clear - LOB LOR; lia| unfold L; clear - SPU UT; ul| replace (L + 16 + Z.of_nat 8 + Z.of_nat 8) with (L + 32) by lia; exact CL32|
                               apply (wr_at_sub m9 (L + 16) 24); [exact WR| lia| lia| lia]]. }
  assert (SPL12 : ro_cells asegs m12 (L + 16) [C8 (W (shad FB6 + 4)); C8 (W FB6); C8 (W FB6)]).
  { apply (ro_cells_agree asegs m11 m12); [apply (ro_cells_agree asegs m10 m11); [apply (ro_cells_agree asegs m9 m10 _ _ (proj1 SPL9))| ]|].
    - apply AG910. intros y Hy. cbn [cells_size csize Nat.add] in Hy. right. clear - Hy. lia.
    - apply AGC11. intros y Hy. cbn [cells_size csize Nat.add] in Hy. left. unfold L in *. clear - Hy SPU UT. ul.
    - apply (agree_of_munch _ _ _ _ MU12). intros y Hy. cbn [cells_size csize Nat.add] in Hy. cbn [outside]. clear - Hy F6lo LOR. unfold L in *. lia. }
  destruct (wr_at_rw_CB m12 (shad FB6 + 276) 7 (wr_at_sub m12 (shad FB6) 512 (shad FB6 + 276) 7 WS12 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (js12 & SHJ12).
  change (Z.to_nat 7) with 7%nat in SHJ12.
  (* [comment removed for export] *)
  pose proof (a2_wF L lo FB6 gp (W 0xba7ed0) q0 q1 q2 (W spa) (W 0) k1 k2 k3 k4 k5 k6 k7 (W SHB) s4' (W (FB6 + 2208)) s6' s7' s8' s9' s10' s11' q3 q4 q5 q6
                F11 fc11 m12 js12 (conj LOB LOT) ltac:(unfold L; clear - SPU UT; ul) ltac:(unfold L; clear - LOR; lia) MI12 F664 F6g F6lo F6h SPL12 SHJ12) as W13.
  to_cps W13 c12 Hc12' Σ3 MST. intros c13 Hc13.
  destruct (ASTA_unpack RT Σ3 _ _ c13 Hc13) as (ms13 & (m13 & -> & MU13 & WM13 & MI13 & SHF13) & Hc13'). clear Hc13.
  assert (ART13 : ART RT Σ3 m13).
  { apply (af_frame RT AF Σ3 m12 m13 L ART12 ltac:(rewrite SP3, SP2, SP1; unfold L; clear - LOW LOR; lia)); [| exact WM13].
    intros a Ha. apply MU13. cbn [outside]. split; [| exact I]. intros Hin. apply Ha.
    apply (acl_fshadow _ _ _ FB6 6%nat); [exact IN63| change (fs_size 6) with 4096; rewrite SH6; clear - Hin; lia]. }
  assert (PRES13 : rt_pres_fp (rt_live RT Σ1) (rt_frames RT Σ1) L W1 m2 m13).
  { apply (pres_fp_trans _ _ _ _ m2 m12 m13 PRES12). apply (pres_fp_of_munch _ _ _ _ _ m12 m13 MU13). intros x _ Ho. unfold W1 in Ho. cbn [outside] in *. clear - Ho. lia. }
  pose proof (wr_at_transport asegs m12 m13 _ _ WF12 WM13) as WF13. pose proof (wr_at_transport asegs m12 m13 _ _ WS12 WM13) as WS13.
  assert (STA13 : stk asegs m13 L (L + 120)) by (apply (stk_munch _ m12 m13 _ _ STA12 MU13 WM13); intros x Hx; cbn [outside]; clear - Hx SH6lo LOR; unfold L in *; lia).
  assert (STK13 : stk asegs m13 lo L) by (apply (stk_munch _ m12 m13 _ _ ST12 MU13 WM13); intros x Hx; cbn [outside]; clear - Hx SH6lo; lia).
  eapply (cps_realizes asegs _ _ T c13).
  { eapply (rc_set_shadow RT RC 0xf8 ltac:(unfold set_shadow_vals; do 12 right; left; reflexivity) Σ3 PMc
              (W 0x4084c0) (W L) gp (W 0xba7ed0) q0 q1 q2 (W spa) (W L) (W (shad FB6 + 4)) (W 256) k2 k3 k4 k5 k6 k7
              (W SHB) (W (shad FB6)) (W FB6) (W (FB6 + 2208)) s6' s7' s8' s9' (W FB6) (W (shad FB6 + 4)) q3 q4 q5 q6 F11 fc11 m13
              (shad FB6 + 4) 256 lo FDO MST); try reflexivity.
    - unfold set_shadow_vals. do 12 right. left. reflexivity.
    - lia.
    - intros i Hi. exists FB6, 6%nat. split; [exact IN63| change (fs_size 6) with 4096; rewrite SH6; clear - Hi; lia].
    - apply (wr_at_sub m13 (shad FB6) 512); [exact WS13| lia| lia| lia].
    - exact ART13.
    - exact MI13.
    - unfold call_ok. rewrite EL, SP3, SP2, SP1. split; [exact STK13|]. split; [exact LOW|]. split; [unfold L; clear - LOR; ul|].
      split; [unfold L; clear - SPU UT; ul| unfold L; clear - S32; Z.div_mod_to_equations; lia]. }
  { exact Hc13'. }
  clear Hc13'. intros c14 Hc14. destruct Hc14 as (v14 & Hc14).
  destruct (ASTA_unpack RT Σ3 _ _ c14 Hc14) as (ms14 & (m14 & RS14 & (ART14 & MI14 & WM14 & ST14) & PR14 & B14) & Hc14'). clear Hc14.
  destruct RS14 as (n0 & n1 & n2 & l1 & l2 & l3 & l4 & l5 & l6 & l7 & n3 & n4 & n5 & n6 & F14 & fc14 & ->).
  rewrite EL in ST14, PR14. rewrite (ret_pc_even 0x4084c0 ltac:(lia) eq_refl) in Hc14'. rewrite LV3', FRS3 in PR14.
  assert (PRES14 : rt_pres_fp (rt_live RT Σ1) (rt_frames RT Σ1) L W1 m2 m14).
  { apply (pres_fp_trans _ _ _ _ m2 m13 m14 PRES13). apply (pres_fp_of_ex _ _ _ _ _ _ m13 m14 PR14). intros x Hx Ho. unfold W1 in Ho. cbn [outside] in Ho. clear - Hx Ho. lia. }
  pose proof (wr_at_transport asegs m13 m14 _ _ WF13 WM14) as WF14.
  assert (AGST14 : agree_on (fun x => L <= x < USTACK_TOP) m13 m14).
  { apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PR14). intros x Hx. split; [apply acl_stack; exact Hx| clear - Hx SH6lo LOR; unfold L in *; lia]. }
  pose proof (stk_agree_nw asegs m13 m14 _ _ STA13 ltac:(eapply agree_sub; [exact AGST14|]; intros y Hy; cbv beta; unfold L in *; clear - Hy SPU UT; ul)) as STA14.
  (* [comment removed for export] *)
  destruct (wr_at_rw_CB m14 FB6 8 (wr_at_sub m14 FB6 4088 FB6 8 WF14 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (jh14 & HDJ14).
  change (Z.to_nat 8) with 8%nat in HDJ14.
  pose proof (a2_wG L lo FB6 gp (W 0xba7ed0) n0 n1 n2 (W spa) v14 l1 l2 l3 l4 l5 l6 l7 (W SHB) (W (shad FB6)) (W (FB6 + 2208)) s6' s7' s8' s9'
                (W (shad FB6 + 4)) n3 n4 n5 n6 F14 fc14 m14 jh14 (conj LOB LOT) ltac:(unfold L; clear - SPU UT; ul) ltac:(unfold L; clear - LOR; lia) MI14
                F664 F6g F6lo HDJ14) as W15.
  to_cps W15 c14 Hc14' Σ3 MST. intros c15 Hc15.
  destruct (ASTA_unpack RT Σ3 _ _ c15 Hc15) as (ms15 & (m15 & -> & MU15 & WM15 & MI15 & HDM15) & Hc15'). clear Hc15.
  assert (ART15 : ART RT Σ3 m15).
  { apply (af_frame RT AF Σ3 m14 m15 L ART14 ltac:(rewrite SP3, SP2, SP1; unfold L; clear - LOW LOR; lia)); [| exact WM15].
    intros a Ha. apply MU15. cbn [outside]. split; [| exact I]. intros Hin. apply Ha.
    apply (acl_frame _ _ _ FB6 6%nat); [exact IN63| change (fs_size 6) with 4096; clear - Hin; lia]. }
  assert (PRES15 : rt_pres_fp (rt_live RT Σ1) (rt_frames RT Σ1) L W1 m2 m15).
  { apply (pres_fp_trans _ _ _ _ m2 m14 m15 PRES14). apply (pres_fp_of_munch _ _ _ _ _ m14 m15 MU15). intros x _ Ho. unfold W1 in Ho. cbn [outside] in *. clear - Ho. lia. }
  assert (STA15 : stk asegs m15 L (L + 120)) by (apply (stk_munch _ m14 m15 _ _ STA14 MU15 WM15); intros x Hx; cbn [outside]; clear - Hx F6lo LOR; unfold L in *; lia).
  assert (STK15 : stk asegs m15 lo L) by (apply (stk_munch _ m14 m15 _ _ ST14 MU15 WM15); intros x Hx; cbn [outside]; clear - Hx F6lo; lia).
  eapply (cps_realizes asegs _ _ T c15).
  { eapply (rc_stack_free_6 RT RC Σ3 PMc (W 0x4084e4) (W L) gp (W 0xba7ed0) n0 n1 n2 (W spa) (W L) (W FB6) (W 2368) l2 l3 l4 l5 l6 l7
              (W SHB) (W (shad FB6)) (W FB6) (W (FB6 + 2208)) s6' s7' s8' s9' (W FB6) (W (shad FB6 + 4)) n3 n4 n5 n6 F14 fc14 m15
              FB6 [(FB, 2%nat)] lo FDO MST eq_refl eq_refl); try reflexivity.
    - rewrite FRS3. exact FRS1.
    - exact ART15.
    - exact MI15.
    - unfold call_ok. rewrite EL, SP3, SP2, SP1. split; [exact STK15|]. split; [exact LOW|]. split; [unfold L; clear - LOR; ul|].
      split; [unfold L; clear - SPU UT; ul| unfold L; clear - S32; Z.div_mod_to_equations; lia]. }
  { exact Hc15'. }
  clear Hc15'. intros c16 Hc16. destruct Hc16 as (Σ4 & v16 & Hc16 & FRS4 & LV4 & SP4 & CR4).
  destruct (ASTA_unpack RT Σ4 _ _ c16 Hc16) as (ms16 & (m16 & RS16 & (ART16 & MI16 & WM16 & ST16) & PR16) & Hc16'). clear Hc16.
  destruct RS16 as (d0 & d1 & d2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & d3 & d4 & d5 & d6 & F16 & fc16 & ->).
  rewrite EL in ST16, PR16. rewrite (ret_pc_even 0x4084e4 ltac:(lia) eq_refl) in Hc16'. rewrite LV4, LV3', FRS4 in PR16.
  assert (PRES16 : rt_pres_fp (rt_live RT Σ1) (rt_frames RT Σ1) L W1 m2 m16).
  { apply (pres_fp_trans _ _ _ _ m2 m15 m16 PRES15). intros a Ha Ho. apply PR16. unfold W1 in Ho. cbn [outside] in Ho.
    destruct Ha as [H|[H|[H|[H|H]]]]; [left; exact H| right; left; exact H| right; right; left; exact H| |].
    - destruct H as (f & k & Hin & Hf). rewrite FRS1 in Hin. destruct Hin as [E|[E|[]]]; injection E as <- <-.
      + exfalso. change (fs_size 6) with 4096 in Hf. clear - Hf Ho. lia.
      + right; right; right; left. exists FB, 2%nat. split; [left; reflexivity| exact Hf].
    - destruct H as (f & k & Hin & Hf). rewrite FRS1 in Hin. destruct Hin as [E|[E|[]]]; injection E as <- <-.
      + exfalso. change (fs_size 6) with 4096 in Hf. rewrite SH6 in Hf. clear - Hf Ho. lia.
      + right; right; right; right. exists FB, 2%nat. split; [left; reflexivity| exact Hf]. }
  assert (AGST16 : agree_on (fun x => L <= x < USTACK_TOP) m15 m16).
  { apply (agree_of_pres _ _ _ _ _ _ PR16). intros x Hx. apply acl_stack. exact Hx. }
  pose proof (stk_agree_nw asegs m15 m16 _ _ STA15 ltac:(eapply agree_sub; [exact AGST16|]; intros y Hy; cbv beta; unfold L in *; clear - Hy SPU UT; ul)) as STA16.
  pose proof (rw_cells_agree_nw asegs m2 m16 _ _ A2T2 ltac:(apply (agree_of_pres_fp _ _ _ _ _ _ _ PRES16); intros y Hy; cbn [cells_size csize Nat.add] in Hy; apply STKOUT; unfold L in *; clear - Hy SPU UT; ul)) as A2T16.
  (* [comment removed for export] *)
  pose proof (a2_wH L lo gp (W 0xba7ed0) d0 d1 d2 v16 b1 b2 b3 b4 b5 b6 b7 (W L) (W SHB) (W (shad FB6)) (W FB6) (W (FB6 + 2208)) s6' s7' s8' s9' (W FB6)
                (W (shad FB6 + 4)) d3 d4 d5 d6 F16 fc16 m16 s11 s10 s9 (W SHB) (W FB) s6 (W b) (W d) (W n) (W FB) (W spa) (W usp)
                ST16 (conj LOB LOT) ltac:(unfold L; clear - SPU UT; ul) ltac:(unfold L; clear - LOR; lia) MI16 A2T16) as W17.
  replace (L + 224) with spa in W17 by (unfold L; lia).
  to_cps W17 c16 Hc16' Σ4 MST. intros c17 Hc17.
  apply Hk. exists Σ4.
  split; [| split; [rewrite LV4, LV3', LV1; reflexivity| split; [rewrite FRS4, FRS0; reflexivity| split; [rewrite SP4, SP3, SP2, SP1; reflexivity|
            rewrite CR4, CR3, CR2, CR1; reflexivity]]]].
  eapply ASTA_conseq; [exact Hc17|]. intros ms E.
  exists m16, d0, d1, d2, s8', b1, b2, b3, b4, b5, b6, b7, d3, d4, d5, d6, F16, fc16.
  split; [exact E|]. split; [exact ART16|]. split; [exact MI16|].
  split.
  { apply (stk_merge asegs m16 lo L spa ST16); [| unfold L; clear - LOR; lia].
    apply (stk_merge asegs m16 L (L + 120) spa STA16); [| unfold L; lia].
    pose proof (stk_of_rw_cells asegs m16 (L + 120) _ A2T16) as H. cbn [cells_size csize Nat.add] in H.
    replace (L + 120 + Z.of_nat 104) with spa in H by (unfold L; lia). exact H. }
  intros a Ha Ho. cbn [outside] in Ho.
  assert (FRS1' : rt_frames RT Σ1 = (FB6, 6%nat) :: rt_frames RT Σ) by (rewrite FRS1, FRS0; reflexivity).
  destruct (newframe_apart RT AF Σ Σ1 m2 FB6 6 spa _ ART2 FRS1' LV1 SP1 ltac:(clear - LOW LOR; lia) Ha) as (NF1 & NF2).
  change (fs_size 6) with 4096 in NF1, NF2. rewrite SH6 in NF2.
  rewrite (PRES16 a).
  - exact (AG02 a Ha).
  - apply (aclient_mono _ _ _ _ _ _ _ Ha); [rewrite LV1; auto| rewrite FRS1'; intros e He; right; exact He| unfold L; lia].
  - unfold W1. cbn [outside]. destruct (aclient_split RT AF Σ m spa _ ART0 Ha) as [H|H]; clear - H Ho NF1 NF2 LOW LOR; unfold L in *; lia.
Qed.

End A2U.
