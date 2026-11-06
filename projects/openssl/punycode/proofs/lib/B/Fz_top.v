(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require StoreOk.
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep.
From OSSVerify.Proofs.openssl.punycode.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.punycode.lib.B Require Import Layout RT_iface D_defs D_kit D_clx D_libiface I_lkit Fz_defs Fz_voc Fz_regions Fz_regw Fz_iface Fz_ckit Fz_w1 Fz_w2 Fz_w3 Fz_w4 Fz_w5 Fz_w6 Fz_w7 Fz_cwpi Fz_ca2u.
From OSSVerify.Proofs.openssl.punycode.lib.B Require I_consts.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require WpEngine LibKit StrKit AShadow ABridge KBridge.
From OSSVerify.Proofs.openssl.punycode.lib.LibB Require BRt BCode BRtIc BIface BFakeStack BInit BA2u BSpecs2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Abbreviation W z := (Z_to_bv 64 z) (only parsing).

Section TOP.
Variable RT : rt_sig.
Hypothesis RC : rt_contracts RT.
Hypothesis R0 : ring0_facts RT.
Let AF : art_facts RT := rc_facts RT RC.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, LIVE_MAX, FRAMES_MAX, FUZZ_STACK, FUZZ_COST, FUZZ_LIVE in *; lia.

Ltac to_cps W c Hc Σ MST :=
  lazymatch type of W with evt bsegs _ ?X =>
    let W' := fresh "W'" in
    assert (W' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W);
    clear W; apply (cps_realizes bsegs _ _ _ c (asta_evt' RT AF Σ _ _ _ MST W') Hc); clear W' end.

(* [comment removed for export] *)
Definition FZQ (Σ : rts RT) PMc (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (usp lo : Z) (m : mem) : config -> Prop :=
  fun c => exists (Σ' : rts RT),
    ASTA RT Σ' PMc (fun ms => exists m', ret_st ra (W usp) gp (W 0xbdae10) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (W 0) m' ms
         /\ rt_after_f RT Σ' usp lo m m'
         /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp LIB_FP m m' /\ LIB_A m') c
    /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = [] /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
    /\ rt_credit RT Σ - FUZZ_COST <= rt_credit RT Σ'.

Lemma fz_mid_cps : forall (Σ : rts RT) PMc (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (usp lo : Z) (m : mem) (d : Z) (bs : list byte)
    (spa : Z) (m1 : mem) (u0 u1 u2 a1' a2' a3' a4' a5' a6' a7' u3 u4 u5 u6 : word) F fc,
  fdfs_only PMc -> mat_stable PMc -> ra = W RA_FUZZ ->
  0 < d -> Z.of_nat (length bs) < 2^26 -> bytes_at bsegs m d bs ->
  ((exists p n, In (p, n) (rt_live RT Σ) /\ p <= d /\ d + Z.of_nat (length bs) <= p + n) \/ (bs = [] /\ d = FZ_EMPTY)) ->
  rt_frames RT Σ = [] -> (forall p n, In (p, n) (rt_live RT Σ) -> 0 < n) ->
  Z.of_nat (length (rt_live RT Σ)) + FUZZ_LIVE <= LIVE_MAX -> FUZZ_COST <= rt_credit RT Σ ->
  fp_invalid s0 (W usp) ->
  LIB_A m -> ART RT Σ m -> mem_inv bsegs m ->
  rt_sp0 RT Σ - STACK_WIN <= lo -> lo + FUZZ_STACK <= usp -> usp + 16 <= USTACK_TOP -> usp <= rt_sp0 RT Σ ->
  usp + -112 <= spa <= usp + -96 -> spa mod 32 = 0 ->
  munch [(spa, usp)] m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 -> stk bsegs m1 lo spa ->
  stk bsegs m1 spa (usp + -88) ->
  rw_cells bsegs m1 (usp + -88) [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  cps bsegs (ASTA RT Σ PMc (eq (entry_st (W 0x1ee05c) (W spa) gp (W 0xbdae10) u0 u1 u2 (W usp) (W spa) (W 192) a1' a2' a3' a4' a5' a6' a7'
                                   s2 (W (Z.of_nat (length bs))) (W d) s5 s6 s7 (W SHB) s9 s10 s11 u3 u4 u5 u6 F fc (e_stack_malloc 2) m1)))
    (FZQ Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m).
Proof using RC R0.
  intros Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m d bs spa m1 u0 u1 u2 a1' a2' a3' a4' a5' a6' a7' u3 u4 u5 u6 F fc
    FDO MST -> D0 BSL INB INPC FRS0 POS LVB CRB FPI LIB0 ART0 MI0 LOW LOR SPT SPS SPA1 SPA2 MU1 WM1 MI1 ST1 SLOT1 FZF1 T c Hc Hk.
  set (n := Z.of_nat (length bs)) in *.
  assert (Hn : 0 <= n) by (unfold n; lia).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  assert (LOB : 0x7fff7f800000 <= lo) by (clear - LOW SP0W; ul).
  assert (LOT : lo <= 2^47) by (clear - LOR SPT; ul).
  assert (ESPA : bv_unsigned (W spa) = spa) by (apply unsigned_lit; clear - LOB LOR SPA1 SPT; ul).
  assert (EUSP : bv_unsigned (W usp) = usp) by (apply unsigned_lit; clear - LOB LOR SPT; ul).
  assert (ART1 : ART RT Σ m1).
  { apply (af_frame RT AF Σ m m1 spa ART0 ltac:(clear - SPA1 LOR LOW; ul)); [| exact WM1].
    intros a Ha. apply MU1. cbn [outside]. split; [| exact I]. intros Hin. apply Ha. apply acl_stack. clear - Hin SPT. ul. }
  (* [comment removed for export] *)
  eapply (cps_realizes bsegs _ _ T c).
  { eapply (rc_stack_malloc_2 RT RC Σ PMc (W 0x1ee05c) (W spa) gp (W 0xbdae10) u0 u1 u2 (W usp) (W spa) (W 192) a1' a2' a3' a4' a5' a6' a7'
              s2 (W n) (W d) s5 s6 s7 (W SHB) s9 s10 s11 u3 u4 u5 u6 F fc m1 lo FDO MST); try reflexivity.
    - left. reflexivity.
    - rewrite FRS0. cbn. unfold FRAMES_MAX. lia.
    - clear - CRB. unfold FUZZ_COST in *. lia.
    - exact ART1.
    - exact MI1.
    - unfold call_ok. rewrite ESPA. split; [exact ST1|]. split; [exact LOW|]. split; [clear - SPA1 LOR; ul|].
      split; [clear - SPA1 SPT; ul| clear - SPA2; Z.div_mod_to_equations; lia]. }
  { exact Hc. }
  clear Hc. intros c2 Hc2. destruct Hc2 as (Σ1 & FB & Hc2 & FRS1 & LV1 & SP1 & CR1 & FB0 & FB64 & FBT).
  destruct (ASTA_unpack RT Σ1 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PR2 & WF2 & WS2) & Hc2'). clear Hc2.
  destruct RS2 as (w0 & w1 & w2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & F2 & fc2 & ->).
  rewrite ESPA in ST2, PR2. rewrite FRS0 in FRS1, PR2. rewrite (ret_pc_even 0x1ee05c ltac:(lia) eq_refl) in Hc2'.
  change (fs_size 2) with 256 in WF2, WS2, FBT. change (256 - 8) with 248 in WF2. change (256 / 8) with 32 in WS2.
  assert (INF : In (FB, 2%nat) (rt_frames RT Σ1)) by (rewrite FRS1; left; reflexivity).
  pose proof (af_frames_range RT AF Σ1 m2 FB 2 ART2 INF) as (_ & FBb & FBc & FBd). change (fs_size 2) with 256 in *. rewrite SP1 in FBb.
  pose proof (af_frames_align RT AF Σ1 m2 FB 2 ART2 INF) as (_ & FBg). unfold SEGTOP_A in FBg.
  pose proof (af_frames_hi RT AF Σ1 m2 FB 2 ART2 INF) as FBh. change (fs_size 2) with 256 in FBh.
  assert (SHF : shad (FB + 256) = shad FB + 32) by (unfold shad; clear - FB64; Z.div_mod_to_equations; lia).
  assert (FBlo : FB + 256 <= lo) by (clear - FBb LOW; lia).
  assert (SHFlo : shad FB + 32 <= lo /\ 0xbfd000 <= shad FB) by (unfold shad, SHB; clear - FBlo FBg LOB; Z.div_mod_to_equations; lia).
  (* [comment removed for export] *)
  assert (AG02 : agree_on (fun x => aclient (rt_live RT Σ) [] spa x /\ ~ (spa <= x < usp)) m m2).
  { apply (agree_trans _ m m1 m2).
    - apply (agree_of_munch _ _ _ _ MU1). intros x (_ & Hx). cbn [outside]. split; [exact Hx| exact I].
    - apply (agree_of_pres _ _ _ _ _ _ PR2). intros x (Hx & _). exact Hx. }
  assert (STAT02 : forall lo' hi', (forall y, lo' <= y < hi' -> client_static y) -> agree_on (fun y => lo' <= y < hi') m m2).
  { intros lo' hi' H. eapply agree_sub; [exact AG02|]. intros y Hy. pose proof (client_static_range y (H y Hy)) as CR.
    split; [apply acl_static; exact (H y Hy)| unfold SEGTOP_A in CR; clear - CR LOB LOR SPA1; ul]. }
  destruct LIB0 as (MIM & FIM & (lv & LAT)).
  pose proof (ro_cells_agree bsegs m m2 _ _ MIM ltac:(apply STAT02; intros y Hy; apply client_static_intro; unfold G_MALLOC_IMPL in *; cbn in Hy; lia)) as MIM2.
  pose proof (ro_cells_agree bsegs m m2 _ _ FIM ltac:(apply STAT02; intros y Hy; apply client_static_intro; unfold G_FREE_IMPL in *; cbn in Hy; lia)) as FIM2.
  pose proof (rw_cells_agree_nw bsegs m m2 _ _ LAT ltac:(apply STAT02; intros y Hy; apply client_static_intro; unfold G_LATCH in *; cbn in Hy; lia)) as LAT2.
  assert (AGST2 : agree_on (fun x => spa <= x < USTACK_TOP) m1 m2).
  { apply (agree_of_pres _ _ _ _ _ _ PR2). intros x Hx. apply acl_stack. exact Hx. }
  pose proof (stk_agree_nw bsegs m1 m2 _ _ SLOT1 ltac:(eapply agree_sub; [exact AGST2|]; intros y Hy; cbv beta; clear - Hy SPT; ul)) as SLOT2.
  pose proof (rw_cells_agree_nw bsegs m1 m2 _ _ FZF1 ltac:(eapply agree_sub; [exact AGST2|]; intros y Hy; cbn [cells_size csize Nat.add] in Hy; cbv beta; clear - Hy SPA1 SPT; ul)) as FZF2.
  destruct (stk_split bsegs m2 spa (spa + 8) (usp + -88) SLOT2 ltac:(clear - SPA1; lia)) as (SL2a & SL2b).
  destruct (stk_carve bsegs m2 spa (spa + 8) 8 SL2a ltac:(lia)) as (_ & j0 & J02). replace (spa + 8 - Z.of_nat 8) with spa in J02 by lia.
  destruct (wr_at_rw_CB m2 FB 24 (wr_at_sub m2 FB 248 FB 24 WF2 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (jh & HDR2).
  destruct (wr_at_rw_CB m2 (FB + 128) 4 (wr_at_sub m2 FB 248 (FB + 128) 4 WF2 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (jl & LEN2).
  destruct (wr_at_rw_CB m2 (shad FB) 24 (wr_at_sub m2 (shad FB) 32 (shad FB) 24 WS2 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (jsh & SHA2).
  change (Z.to_nat 24) with 24%nat in HDR2, SHA2. change (Z.to_nat 4) with 4%nat in LEN2.
  destruct (lib_ro_cells m2 (af_lib_ro RT AF Σ1 m2 ART2)) as (_ & _ & GOTM2 & _).
  (* [comment removed for export] *)
  pose proof (fz_wB usp spa lo n d FB gp (W 0xbdae10) w0 w1 w2 e1 e2 e3 e4 e5 e6 e7 s2 s5 s6 s7 s9 s10 s11 w3 w4 w5 w6 F2 fc2 m2 j0 jh jl jsh lv
                ST2 ltac:(clear - SPA1 LOR; ul) LOB ltac:(clear - SPT; ul) SPA2 ltac:(clear - SPA1; lia) MI2 ltac:(clear - Hn BSL; lia)
                FB64 FBg FBlo FBh J02 HDR2 LEN2 SHA2 MIM2 GOTM2 LAT2) as W3.
  to_cps W3 c2 Hc2' Σ1 MST. intros c3 Hc3.
  destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & (m3 & a1'' & jf & lv' & -> & MU3 & WM3 & MI3 & ST3 & CMF3 & SPL3 & HDR3 & LEN3 & SH3 & LAT3 & LVNZ) & Hc3'). clear Hc3.
  assert (FRS1' : rt_frames RT Σ1 = (FB, 2%nat) :: rt_frames RT Σ) by (rewrite FRS1, FRS0; reflexivity).
  assert (NFB : forall x, aclient (rt_live RT Σ) [] usp x -> ~ (FB <= x < FB + 256) /\ ~ (shad FB <= x < shad FB + 32) /\ (usp <= x \/ x < lo)).
  { intros x Hx. rewrite <- FRS0 in Hx.
    destruct (newframe_apart RT AF Σ Σ1 m2 FB 2 usp x ART2 FRS1' LV1 SP1 ltac:(clear - LOW LOR; ul) Hx) as (N1 & N2).
    change (fs_size 2) with 256 in N1, N2. rewrite SHF in N2. split; [exact N1|]. split; [exact N2|].
    destruct (aclient_split RT AF Σ m usp x ART0 Hx) as [H|H]; [left; exact H| right; clear - H LOW; lia]. }
  assert (ART3 : ART RT Σ1 m3).
  { apply (af_frame RT AF Σ1 m2 m3 (spa + -48) ART2 ltac:(rewrite SP1; clear - SPA1 LOR LOW; ul)); [| exact WM3].
    intros a Ha. apply MU3. unfold fz_WB. cbn [outside]. split; [| split; [| split; [| split; [| split; [| exact I]]]]]; intros Hin; apply Ha.
    - apply acl_stack. clear - Hin SPA1 SPT. ul.
    - apply (acl_frame _ _ _ FB 2%nat); [exact INF| change (fs_size 2) with 256; clear - Hin; lia].
    - apply (acl_frame _ _ _ FB 2%nat); [exact INF| change (fs_size 2) with 256; clear - Hin; lia].
    - apply (acl_fshadow _ _ _ FB 2%nat); [exact INF| change (fs_size 2) with 256; rewrite SHF; clear - Hin; lia].
    - apply acl_static. apply client_static_intro. unfold G_LATCH in *. clear - Hin. lia. }
  set (W0 := [(G_LATCH, G_LATCH + 1)]).
  assert (PRES0_3 : rt_pres_fp (rt_live RT Σ) [] usp W0 m m3).
  { intros a Ha Ho. destruct (NFB _ Ha) as (N1 & N2 & N3). rewrite (MU3 a).
    - apply AG02. split; [apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto| auto| clear - SPA1; lia]| clear - N3 LOR SPA1; ul].
    - unfold fz_WB. unfold W0 in Ho. cbn [outside] in *. clear - N1 N2 N3 Ho LOR SPA1. unfold FUZZ_STACK in *. lia. }
  pose proof (wr_at_transport bsegs m2 m3 _ _ WF2 WM3) as WF3. pose proof (wr_at_transport bsegs m2 m3 _ _ WS2 WM3) as WS3.
  assert (AG23 : forall (Q : Z -> Prop), (forall y, Q y -> spa + 8 <= y < USTACK_TOP) -> agree_on Q m2 m3).
  { intros Q HQ. apply (agree_of_munch _ _ _ _ MU3). intros y Hy. specialize (HQ y Hy). unfold fz_WB. cbn [outside]. unfold shad, SHB, G_LATCH.
    clear - HQ FBlo LOR SHFlo LOB SPA1. unfold shad, SHB, FUZZ_STACK in *. lia. }
  pose proof (rw_cells_agree_nw bsegs m2 m3 _ _ FZF2 ltac:(apply AG23; intros y Hy; cbn [cells_size csize Nat.add] in Hy; clear - Hy SPA1 SPT; ul)) as FZF3.
  pose proof (stk_agree_nw bsegs m2 m3 _ _ SL2b ltac:(apply AG23; intros y Hy; cbv beta in Hy; clear - Hy SPT; ul)) as SL3b.
  assert (SLOT3 : stk bsegs m3 spa (usp + -88)).
  { apply (stk_merge bsegs m3 spa (spa + 8) (usp + -88)); [| exact SL3b| clear - SPA1; lia].
    pose proof (stk_of_rw_cells bsegs m3 spa _ SPL3) as H. cbn [cells_size csize Nat.add] in H. exact H. }
  (* [comment removed for export] *)
  assert (EL3 : bv_unsigned (W (spa + -48)) = spa + -48) by (apply unsigned_lit; clear - LOB LOR SPA1 SPT; ul).
  assert (UREC3 : rw_cells bsegs m3 (usp - 16) [C8 s0; C8 (W RA_FUZZ)]).
  { pose proof (rw_cells_skip m3 (usp + -88) [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] _ FZF3) as H.
    cbn [cells_size csize Nat.add] in H. replace (usp + -88 + Z.of_nat 72) with (usp - 16) in H by lia. exact H. }
  assert (UWM : unwind_ok m3 (W 0x1ee3bc) (W spa) (W (spa + -48))).
  { split; [rewrite (unsigned_lit 0x1ee3bc) by lia; unfold ALLOC_RAS; do 6 right; left; reflexivity|]. right.
    exists [0x1ee154; 0x1edea4]. split; [rewrite (unsigned_lit 0x1ee3bc) by lia; unfold ALLOC_CHAINS; left; reflexivity|].
    cbn [uw_chain]. rewrite EL3, ESPA. split; [lia|]. split; [clear - SPA1 SPT; ul|]. exists (W usp). split.
    { unfold cm_frame in CMF3. pose proof (rw_cells_skip m3 (spa + -48) [CB 8 jf; C8 (W n); C8 (W FB); C8 (W spa)] _ CMF3) as H.
      cbn [cells_size csize Nat.add] in H. replace (spa + -48 + Z.of_nat 32) with (spa - 16) in H by lia. exact H. }
    rewrite EUSP. split; [clear - SPA1; lia|]. split; [exact SPT|]. exists s0. split; [exact UREC3| exact FPI]. }
  assert (DR : d + n < 2^47 /\ (bs = [] \/ d + n <= 0x10000 \/ 0xbfd000 <= d)).
  { destruct INPC as [(p0 & n0 & IN0 & P1 & P2)|(E1 & E2)].
    - pose proof (af_live_range RT AF Σ m p0 n0 ART0 IN0) as (Q0 & Q1 & Q2). fold n in P2. unfold SEGTOP_A in Q2.
      split; [clear - P2 Q1 SP0R; ul| right; clear - P1 P2 Q2; lia].
    - split; [subst bs d; unfold n, FZ_EMPTY; cbn; lia| left; exact E1]. }
  destruct DR as (DT & DOFF).
  eapply (cps_realizes bsegs _ _ T c3).
  { eapply (rc_malloc RT RC Σ1 PMc (W 0x1ee3bc) (W (spa + -48)) gp (W 0xbdae10) w0 w1 w2 (W spa) (W 29) (W (n + 1)) a1'' (W 6169452) (W 2024260)
              (W (-14)) (W (-13)) e6 e7 (W 229042) (W (n + 1)) (W d) s5 (W (shad FB)) (W FB) (W SHB) (W (-8)) s10 s11 w3 w4 w5 w6 F2 fc2 m3
              (n + 1) lo FDO MST); try reflexivity.
    - clear - Hn BSL. lia.
    - rewrite LV1. clear - LVB. ul.
    - rewrite CR1. unfold mcost. destruct (n + 1 <=? 64512); clear - CRB BSL Hn; unfold FUZZ_COST in *; lia.
    - exact ART3.
    - exact MI3.
    - unfold call_ok. rewrite EL3, SP1. split; [exact ST3|]. split; [exact LOW|]. split; [clear - SPA1 LOR; ul|].
      split; [clear - SPA1 SPT; ul| clear - SPA2; Z.div_mod_to_equations; lia].
    - exact UWM. }
  { exact Hc3'. }
  clear Hc3'. intros c4 Hc4. destruct Hc4 as (Σ2 & b & Hc4 & LV2 & FRS2 & SP2 & CR2 & B0 & B16 & BT).
  destruct (ASTA_unpack RT Σ2 _ _ c4 Hc4) as (ms4 & (m4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PR4 & WRB4 & ACB4) & Hc4'). clear Hc4.
  destruct RS4 as (x0 & x1 & x2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & x3 & x4 & x5 & x6 & F4 & fc4 & ->).
  rewrite EL3 in ST4, PR4. rewrite (ret_pc_even 0x1ee3bc ltac:(lia) eq_refl) in Hc4'.
  assert (INF2 : In (FB, 2%nat) (rt_frames RT Σ2)) by (rewrite FRS2; exact INF).
  assert (INB2 : In (b, n + 1) (rt_live RT Σ2)) by (rewrite LV2; left; reflexivity).
  assert (PRES0_4 : rt_pres_fp (rt_live RT Σ) [] usp W0 m m4).
  { apply (pres_fp_trans _ _ _ _ m m3 m4 PRES0_3). intros a Ha _. apply PR4.
    apply (aclient_mono _ _ _ _ _ _ _ Ha); [rewrite LV1; auto| intros e []| clear - SPA1; lia]. }
  set (W3 := [(FB, FB + 256)]).
  assert (PRES3_4 : rt_pres_fp (rt_live RT Σ1) (rt_frames RT Σ1) spa W3 m3 m4).
  { intros a Ha _. apply PR4. apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto| auto| lia]. }
  pose proof (wr_at_transport bsegs m3 m4 _ _ WF3 WM4) as WF4. pose proof (wr_at_transport bsegs m3 m4 _ _ WS3 WM4) as WS4.
  assert (AGC4 : forall (Q : Z -> Prop), (forall y, Q y -> (spa + -48 <= y < USTACK_TOP) \/ (FB <= y < FB + 248) \/ (shad FB <= y < shad FB + 32)) -> agree_on Q m3 m4).
  { intros Q HQ. apply (agree_of_pres _ _ _ _ _ _ PR4). intros y Hy. destruct (HQ y Hy) as [H|[H|H]].
    - apply acl_stack. exact H.
    - apply (acl_frame _ _ _ FB 2%nat); [exact INF| change (fs_size 2) with 256; clear - H; lia].
    - apply (acl_fshadow _ _ _ FB 2%nat); [exact INF| change (fs_size 2) with 256; rewrite SHF; exact H]. }
  pose proof (rw_cells_agree_nw bsegs m3 m4 _ _ CMF3 ltac:(apply AGC4; intros y Hy; cbn [cm_frame cells_size csize Nat.add] in Hy; left; clear - Hy SPA1 SPT; ul)) as CMF4.
  pose proof (rw_cells_agree_nw bsegs m3 m4 _ _ LEN3 ltac:(apply AGC4; intros y Hy; cbn [cells_size csize Nat.add] in Hy; right; left; clear - Hy; lia)) as LEN4.
  pose proof (rw_cells_agree_nw bsegs m3 m4 _ _ SH3 ltac:(apply AGC4; intros y Hy; change (Z.of_nat (cells_size fz_sh1)) with 24 in Hy; right; right; clear - Hy; lia)) as SH4.
  (* [comment removed for export] *)
  pose proof (fz_wC usp spa lo n d FB b gp (W 0xbdae10) x0 x1 x2 g1 g2 g3 g4 g5 g6 g7 s5 s10 s11 x3 x4 x5 x6 F4 fc4 m4 jf
                ST4 LOB ltac:(clear - SPA1 LOR; ul) ltac:(clear - SPA1 SPT; ul) ltac:(clear - LOB LOR SPT; ul) MI4
                ltac:(clear - B0 BT Hn; ul) ltac:(clear - Hn BSL; lia) ltac:(clear - D0 DT Hn; lia) ltac:(clear - FB0; lia) ltac:(clear - FBlo LOT; lia) CMF4) as W5.
  to_cps W5 c4 Hc4' Σ2 MST. intros c5 Hc5.
  destruct (ASTA_unpack RT Σ2 _ _ c5 Hc5) as (ms5 & (-> & ST5) & Hc5'). clear Hc5.
  (* [comment removed for export] *)
  destruct (r0_view RT R0 Σ2 m4 ART4 MI4 ltac:(rewrite FRS2, FRS1; intros f k [E|[]]; injection E as <- <-; lia))
    as (fs & Tt & ctx & thr & h & (RTOK & _) & _).
  assert (INL2 : forall p k, In (p, k) (rt_live RT Σ) -> In (p, k) (rt_live RT Σ2)) by (intros p k H; rewrite LV2, LV1; right; exact H).
  assert (PAY4 : bytes_at bsegs m4 d bs /\ acc bsegs m4 d n /\ AShadow.memrange d n).
  { destruct INPC as [(p0 & n0 & IN0 & P1 & P2)|(E1 & E2)].
    - fold n in P2. pose proof (af_live_range RT AF Σ m p0 n0 ART0 IN0) as (Q0 & Q1 & Q2). unfold SEGTOP_A in Q2.
      destruct (af_acc_live RT AF Σ2 m4 p0 n0 ART4 (INL2 _ _ IN0)) as (_ & AC0).
      destruct (r0_live_mem RT R0 Σ2 m4 p0 n0 ART4 (INL2 _ _ IN0)) as (MR0 & _).
      split; [| split].
      + apply (bytes_at_agree bsegs m m4 _ _ INB). intros a Ha. fold n in Ha. apply PRES0_4.
        * apply (acl_live _ _ _ p0 n0); [exact IN0| clear - Ha P1 P2; lia].
        * unfold W0, G_LATCH. cbn [outside]. clear - Ha P1 P2 Q2. lia.
      + apply (acc_sub bsegs m4 p0 n0); [exact AC0| exact P1| exact P2].
      + unfold AShadow.memrange, AShadow.LOMEM_END, AShadow.HIMEM_BEG, AShadow.HIMEM_END in *. clear - MR0 P1 P2 Hn. lia.
    - subst bs d. split; [apply bytes_at_nil; unfold FZ_EMPTY; lia| split; [intros i Hi; unfold n in Hi; cbn in Hi; lia|]].
      unfold AShadow.memrange, AShadow.LOMEM_END, FZ_EMPTY, n. cbn. lia. }
  destruct PAY4 as (INB4 & ACD4 & MRD).
  assert (SHO4 : bytes_at bsegs m4 (shad FB + 4) (repeat z8 8)).
  { pose proof (bytes_at_sub m4 (shad FB) (cells_bytes fz_sh1) 4 8 (proj2 (proj1 SH4)) ltac:(cbn; lia)) as H. exact H. }
  assert (SHL4 : bytes_at bsegs m4 (shad FB + 16) [Z_to_bv 8 4]).
  { pose proof (bytes_at_sub m4 (shad FB) (cells_bytes fz_sh1) 16 1 (proj2 (proj1 SH4)) ltac:(cbn; lia)) as H. exact H. }
  pose proof (stk_of_rw_cells bsegs m4 (shad FB) _ SH4) as SHW4. change (Z.of_nat (cells_size fz_sh1)) with 24 in SHW4.
  pose proof (decode_w usp spa lo d FB bs gp (W 0xbdae10) x0 x1 x2 g4 g5 g6 g7 (W FB) (W n) (W d) (W b) (W (shad FB)) (W FB) (W SHB) (W (-8)) s10 s11
                x3 x4 x5 x6 F4 fc4 m4 RTOK MI4 BSL INB4 ACD4 MRD DOFF ltac:(clear - D0; lia) ST5 ltac:(clear - LOB; lia) ltac:(clear - SPA1 LOR; ul)
                ltac:(clear - SPA1 SPT; ul) FB64 FBg FBlo FBh
                (wr_at_sub m4 FB 248 (FB + 32) 64 WF4 ltac:(lia) ltac:(lia) ltac:(lia)) LEN4 SHO4 SHL4 SHW4) as W6.
  to_cps W6 c5 Hc5' Σ2 MST. intros c6 Hc6.
  destruct (ASTA_unpack RT Σ2 _ _ c6 Hc6) as (ms6 & (y0 & y1 & y2 & h0 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & y3 & y4 & y5 & y6 & m6 & -> & MU6 & WM6 & MI6 & HG6) & Hc6').
  clear Hc6.
  assert (ART6 : ART RT Σ2 m6).
  { apply (af_frame RT AF Σ2 m4 m6 (spa - 2400) ART4 ltac:(rewrite SP2, SP1; clear - SPA1 LOR LOW; ul)); [| exact WM6].
    intros a Ha. apply MU6. cbn [outside]. split; [| split; [| split; [| exact I]]]; intros Hin; apply Ha.
    - apply acl_stack. clear - Hin SPA1 SPT. ul.
    - apply (acl_frame _ _ _ FB 2%nat); [exact INF2| change (fs_size 2) with 256; clear - Hin; lia].
    - apply (acl_frame _ _ _ FB 2%nat); [exact INF2| change (fs_size 2) with 256; clear - Hin; lia]. }
  assert (PRES0_6 : rt_pres_fp (rt_live RT Σ) [] usp W0 m m6).
  { apply (pres_fp_trans _ _ _ _ m m4 m6 PRES0_4). apply (pres_fp_of_munch _ _ _ _ _ m4 m6 MU6). intros x Hx _. destruct (NFB _ Hx) as (N1 & N2 & N3).
    cbn [outside]. clear - N1 N3 SPA1 LOR. unfold FUZZ_STACK in *. lia. }
  assert (PRES3_6 : rt_pres_fp (rt_live RT Σ1) (rt_frames RT Σ1) spa W3 m3 m6).
  { apply (pres_fp_trans _ _ _ _ m3 m4 m6 PRES3_4). apply (pres_fp_of_munch _ _ _ _ _ m4 m6 MU6). intros x Hx Ho. unfold W3 in Ho. cbn [outside] in *.
    destruct (aclient_split RT AF Σ1 m2 spa _ ART2 Hx) as [H|H]; rewrite ?SP1 in H; clear - H Ho LOW LOR SPA1; unfold FUZZ_STACK in *; lia. }
  pose proof (wr_at_transport bsegs m4 m6 _ _ WF4 WM6) as WF6. pose proof (wr_at_transport bsegs m4 m6 _ _ WS4 WM6) as WS6.
  pose proof (KBridge.stk_grows bsegs m4 m6 _ _ ST5 HG6) as ST6.
  (* [comment removed for export] *)
  pose proof (fz_wD spa n d b gp (W 0xbdae10) y0 y1 y2 (W usp) h0 h1 h2 h3 h4 h5 h6 h7 (W FB) (W (shad FB)) (W FB) (W SHB) (W (-8)) s10 s11 y3 y4 y5 y6 F4 fc4 m6) as W7.
  to_cps W7 c6 Hc6' Σ2 MST. intros c7 Hc7.
  destruct (ASTA_unpack RT Σ2 _ _ c7 Hc7) as (ms7 & -> & Hc7'). clear Hc7.
  destruct (af_acc_live RT AF Σ2 m6 b (n + 1) ART6 INB2) as (WRB6 & ACB6).
  pose proof (af_live_range RT AF Σ2 m6 b (n + 1) ART6 INB2) as (_ & BR & Bimg). rewrite SP2, SP1 in BR.
  assert (SRC6 : bytes_at bsegs m6 d bs /\ checked_src RT Σ2 m6 (W spa) lo d n /\ (b + n <= d \/ d + n <= b)).
  { destruct INPC as [(p0 & n0 & IN0 & P1 & P2)|(E1 & E2)].
    - fold n in P2. pose proof (af_live_range RT AF Σ m p0 n0 ART0 IN0) as (Q0 & Q1 & Q2). unfold SEGTOP_A in Q2.
      destruct (af_acc_live RT AF Σ2 m6 p0 n0 ART6 (INL2 _ _ IN0)) as (_ & AC0).
      pose proof (af_live_disj RT AF Σ2 m6 b (n + 1) p0 n0 [] (rt_live RT Σ1) ART6 LV2 ltac:(cbn [app]; rewrite LV1; exact IN0)) as DJ.
      split; [| split].
      + apply (bytes_at_agree bsegs m m6 _ _ INB). intros a Ha. fold n in Ha. apply PRES0_6.
        * apply (acl_live _ _ _ p0 n0); [exact IN0| clear - Ha P1 P2; lia].
        * unfold W0, G_LATCH. cbn [outside]. clear - Ha P1 P2 Q2. lia.
      + split; [intros _; split; [apply (acc_sub bsegs m6 p0 n0); [exact AC0| exact P1| exact P2]|]|].
        * left. exists p0, n0. split; [exact (INL2 _ _ IN0)| split; [exact P1| exact P2]].
        * left. clear - P2 Q1 LOW. lia.
      + clear - DJ P1 P2 Hn. lia.
    - subst bs d. split; [apply bytes_at_nil; unfold FZ_EMPTY; lia| split].
      + split; [intros Hc'; unfold n in Hc'; cbn in Hc'; lia| left; unfold FZ_EMPTY, n; cbn; clear - LOB; lia].
      + unfold n. cbn. lia. }
  destruct SRC6 as (INB6 & CSRC & DISJ).
  eapply (cps_realizes bsegs _ _ T c7).
  { eapply (rc_asan_memcpy RT RC Σ2 PMc (W 0x1ee184) (W spa) gp (W 0xbdae10) y0 y1 y2 (W usp) (W spa) (W b) (W d) (W n) h3 h4 h5 h6 h7
              (W FB) (W n) (W d) (W b) (W (shad FB)) (W FB) (W SHB) (W (-8)) s10 s11 y3 y4 y5 y6 F4 fc4 m6 b d bs lo FDO MST); try reflexivity.
    - clear - B0 BT Hn. ul.
    - clear - D0 DT Hn. lia.
    - fold n. clear - BSL. lia.
    - exact INB6.
    - exact CSRC.
    - fold n. split; [intros _; split; [apply (acc_sub bsegs m6 b (n + 1)); [exact ACB6| lia| lia]|]| split].
      + left. exists b, (n + 1). split; [exact INB2| lia].
      + intros i Hi. apply (acl_live _ _ _ b (n + 1)); [exact INB2| lia].
      + apply (wr_at_sub m6 b (n + 1)); [exact WRB6| lia| lia| lia].
    - exact DISJ.
    - exact ART6.
    - exact MI6.
    - unfold call_ok. rewrite ESPA, SP2, SP1. split; [exact ST6|]. split; [exact LOW|]. split; [clear - SPA1 LOR; ul|].
      split; [clear - SPA1 SPT; ul| clear - SPA2; Z.div_mod_to_equations; lia]. }
  { exact Hc7'. }
  clear Hc7'. intros c8 Hc8.
  destruct (ASTA_unpack RT Σ2 _ _ c8 Hc8) as (ms8 & (m8 & RS8 & (ART8 & MI8 & WM8 & ST8) & PR8 & B8) & Hc8'). clear Hc8.
  destruct RS8 as (z0 & z1 & z2 & i1 & i2 & i3 & i4 & i5 & i6 & i7 & z3 & z4 & z5 & z6 & F8 & fc8 & ->).
  rewrite ESPA in ST8, PR8. rewrite (ret_pc_even 0x1ee184 ltac:(lia) eq_refl) in Hc8'. fold n in PR8.
  pose proof (newchunk_apart RT AF Σ1 Σ2 m4 b (n + 1) spa) as NB. specialize (fun a => NB a ART4 LV2 FRS2 SP2 ltac:(rewrite SP1; clear - SPA1 LOR LOW; ul) ltac:(clear - Hn; lia)).
  assert (NB0 : forall x, aclient (rt_live RT Σ) [] usp x -> ~ (b <= x < b + (n + 1))).
  { intros x Hx. apply NB. apply (aclient_mono _ _ _ _ _ _ _ Hx); [rewrite LV1; auto| intros e []| clear - SPA1; lia]. }
  assert (SUB02 : forall x sp', sp' <= usp -> aclient (rt_live RT Σ) [] usp x -> aclient (rt_live RT Σ2) (rt_frames RT Σ2) sp' x).
  { intros x sp' Hs Hx. apply (aclient_mono _ _ _ _ _ _ _ Hx); [intros e He; destruct e; apply INL2; exact He| intros e []| exact Hs]. }
  assert (SUB12 : forall x sp', sp' <= spa -> aclient (rt_live RT Σ1) (rt_frames RT Σ1) spa x -> aclient (rt_live RT Σ2) (rt_frames RT Σ2) sp' x).
  { intros x sp' Hs Hx. apply (aclient_mono _ _ _ _ _ _ _ Hx); [rewrite LV2; intros e He; right; exact He| rewrite FRS2; auto| exact Hs]. }
  assert (PRES0_8 : rt_pres_fp (rt_live RT Σ) [] usp W0 m m8).
  { apply (pres_fp_trans _ _ _ _ m m6 m8 PRES0_6). intros a Ha _. apply PR8; [apply (SUB02 _ spa); [clear - SPA1; lia| exact Ha]|].
    pose proof (NB0 _ Ha) as N. clear - N Hn. lia. }
  assert (PRES3_8 : rt_pres_fp (rt_live RT Σ1) (rt_frames RT Σ1) spa W3 m3 m8).
  { apply (pres_fp_trans _ _ _ _ m3 m6 m8 PRES3_6). intros a Ha _. apply PR8; [apply (SUB12 _ spa); [lia| exact Ha]|].
    pose proof (NB _ Ha) as N. clear - N Hn. lia. }
  pose proof (wr_at_transport bsegs m6 m8 _ _ WF6 WM8) as WF8. pose proof (wr_at_transport bsegs m6 m8 _ _ WS6 WM8) as WS8.
  (* [comment removed for export] *)
  destruct (af_acc_live RT AF Σ2 m8 b (n + 1) ART8 INB2) as (WRB8 & ACB8).
  pose proof (store0_w b n (W 0x1ee184) (W spa) gp (W 0xbdae10) z0 z1 z2 (W usp) (W spa) (W b) i1 i2 i3 i4 i5 i6 i7 (W FB) (W d) (W (shad FB)) (W FB)
                (W (-8)) s10 s11 z3 z4 z5 z6 F8 fc8 m8 MI8 B0 Hn ltac:(clear - BT; ul) ACB8 WRB8) as W9.
  rewrite (unsigned_lit FB) in W9 by (clear - FB0 FBlo LOT; lia).
  to_cps W9 c8 Hc8' Σ2 MST. intros c9 Hc9.
  destruct (ASTA_unpack RT Σ2 _ _ c9 Hc9) as (ms9 & (m9 & -> & MU9 & WM9 & MI9 & HG9 & NUL9) & Hc9'). clear Hc9.
  assert (ART9 : ART RT Σ2 m9).
  { apply (af_frame RT AF Σ2 m8 m9 spa ART8 ltac:(rewrite SP2, SP1; clear - SPA1 LOR LOW; ul)); [| exact WM9].
    intros a Ha. apply MU9. cbn [outside]. split; [| exact I]. intros Hin. apply Ha. apply (acl_live _ _ _ b (n + 1)); [exact INB2| clear - Hin Hn; lia]. }
  assert (PRES0_9 : rt_pres_fp (rt_live RT Σ) [] usp W0 m m9).
  { apply (pres_fp_trans _ _ _ _ m m8 m9 PRES0_8). apply (pres_fp_of_munch _ _ _ _ _ m8 m9 MU9). intros x Hx _. pose proof (NB0 _ Hx) as N.
    cbn [outside]. clear - N Hn. lia. }
  assert (PRES3_9 : rt_pres_fp (rt_live RT Σ1) (rt_frames RT Σ1) spa W3 m3 m9).
  { apply (pres_fp_trans _ _ _ _ m3 m8 m9 PRES3_8). apply (pres_fp_of_munch _ _ _ _ _ m8 m9 MU9). intros x Hx _. pose proof (NB _ Hx) as N.
    cbn [outside]. clear - N Hn. lia. }
  pose proof (wr_at_transport bsegs m8 m9 _ _ WF8 WM9) as WF9. pose proof (wr_at_transport bsegs m8 m9 _ _ WS8 WM9) as WS9.
  pose proof (KBridge.stk_grows bsegs m8 m9 _ _ ST8 HG9) as ST9.
  assert (AGP9 : forall (Q : Z -> Prop), (forall y, Q y -> aclient (rt_live RT Σ1) (rt_frames RT Σ1) spa y /\ outside W3 y) -> agree_on Q m3 m9).
  { intros Q HQ. exact (agree_of_pres_fp _ _ _ _ _ _ _ PRES3_9 HQ). }
  assert (STKQ : forall y, spa <= y < USTACK_TOP -> aclient (rt_live RT Σ1) (rt_frames RT Σ1) spa y /\ outside W3 y).
  { intros y Hy. split; [apply acl_stack; exact Hy|]. unfold W3. cbn [outside]. clear - Hy FBlo LOR SPA1. unfold FUZZ_STACK in *. lia. }
  assert (STATQ : forall y, client_static y -> aclient (rt_live RT Σ1) (rt_frames RT Σ1) spa y /\ outside W3 y).
  { intros y Hy. split; [apply acl_static; exact Hy|]. pose proof (client_static_range y Hy) as CR. unfold W3, SEGTOP_A in *. cbn [outside]. clear - CR FBg. lia. }
  assert (SHQ : forall y, shad FB <= y < shad FB + 32 -> aclient (rt_live RT Σ1) (rt_frames RT Σ1) spa y /\ outside W3 y).
  { intros y Hy. split; [apply (acl_fshadow _ _ _ FB 2%nat); [exact INF| change (fs_size 2) with 256; rewrite SHF; exact Hy]|].
    unfold W3. cbn [outside]. unfold shad, SHB in *. clear - Hy FBh FB0 FBlo LOT. Z.div_mod_to_equations. lia. }
  pose proof (rw_cells_agree_nw bsegs m3 m9 _ _ UREC3 ltac:(apply AGP9; intros y Hy; cbn [cells_size csize Nat.add] in Hy; apply STKQ; clear - Hy SPA1 SPT; ul)) as UREC9.
  pose proof (rw_cells_agree_nw bsegs m3 m9 _ _ SH3 ltac:(apply AGP9; intros y Hy; change (Z.of_nat (cells_size fz_sh1)) with 24 in Hy; apply SHQ; clear - Hy; lia)) as SH9.
  pose proof (rw_cells_agree_nw bsegs m3 m9 _ _ LAT3 ltac:(apply AGP9; intros y Hy; apply STATQ; apply client_static_intro; unfold G_LATCH in *; cbn in Hy; lia)) as LAT9.
  assert (STAT09 : forall lo' hi', (forall y, lo' <= y < hi' -> client_static y /\ outside W0 y) -> agree_on (fun y => lo' <= y < hi') m m9).
  { intros lo' hi' H a Ha. destruct (H _ Ha) as (H1 & H2). apply PRES0_9; [apply acl_static; exact H1| exact H2]. }
  pose proof (ro_cells_agree bsegs m m9 _ _ MIM ltac:(apply STAT09; intros y Hy; unfold W0, G_MALLOC_IMPL, G_LATCH in *; cbn in Hy; cbn [outside]; split; [apply client_static_intro; lia| lia])) as MIM9.
  pose proof (ro_cells_agree bsegs m m9 _ _ FIM ltac:(apply STAT09; intros y Hy; unfold W0, G_FREE_IMPL, G_LATCH in *; cbn in Hy; cbn [outside]; split; [apply client_static_intro; lia| lia])) as FIM9.
  assert (ESHO : shad (FB + 144) = shad FB + 18) by (unfold shad; clear - FB64; Z.div_mod_to_equations; lia).
  assert (AOUT9 : acc bsegs m9 (FB + 144) 16).
  { apply (acc_zero_run bsegs m9 (FB + 144) 2); [clear - FB64; Z.div_mod_to_equations; lia| clear - FB0; lia|]. rewrite ESHO.
    exact (bytes_at_sub m9 (shad FB) (cells_bytes fz_sh1) 18 2 (proj2 (proj1 SH9)) ltac:(cbn; lia)). }
  pose proof (stk_of_rw_cells bsegs m9 (shad FB) _ SH9) as SHW9. change (Z.of_nat (cells_size fz_sh1)) with 24 in SHW9.
  assert (SHOUT9 : stk bsegs m9 (shad FB + 16) (shad FB + 24)) by (apply (stk_split bsegs m9 (shad FB) (shad FB + 16) (shad FB + 24) SHW9); lia).
  (* [comment removed for export] *)
  eapply (cps_realizes bsegs _ _ T c9).
  { eapply (a2u_cps RT RC R0 Σ2 PMc gp (W 0xbdae10) z0 z1 z2 (W (b + n)) i3 i4 i5 i6 i7 (W (shad FB)) (W (-8)) s10 s11 z3 z4 z5 z6 s0 F8 fc8 m9
              usp spa lo n d b FB lv' FDO MST eq_refl ART9 MI9 ST9).
    - rewrite SP2, SP1. exact LOW.
    - clear - SPA1 LOR. ul.
    - exact SPA2.
    - clear - SPA1. lia.
    - exact SPT.
    - rewrite FRS2. exact FRS1.
    - exact INB2.
    - intros p k Hin. rewrite LV2 in Hin. destruct Hin as [E|Hin]; [injection E as <- <-; clear - Hn; lia| rewrite LV1 in Hin; exact (POS p k Hin)].
    - exact B16.
    - clear - Hn BSL. lia.
    - rewrite LV2, LV1. cbn [length]. clear - LVB. ul.
    - rewrite CR2, CR1. unfold mcost. destruct (n + 1 <=? 64512); clear - CRB BSL Hn; unfold FUZZ_COST in *; lia.
    - exact UREC9.
    - exact FPI.
    - exact NUL9.
    - apply (wr_at_sub m9 FB 248); [exact WF9| lia| lia| lia].
    - exact AOUT9.
    - exact SHOUT9.
    - exact MIM9.
    - exact FIM9.
    - exact LAT9.
    - exact LVNZ. }
  { exact Hc9'. }
  clear Hc9'. intros c10 Hc10. destruct Hc10 as (Σ3 & Hc10 & LV3 & FRS3 & SP3 & CR3).
  destruct (ASTA_unpack RT Σ3 _ _ c10 Hc10) as (ms10 & (m10 & q0 & q1 & q2 & k0 & k1 & k2 & k3 & k4 & k5 & k6 & k7 & q3 & q4 & q5 & q6 & F10 & fc10 & -> & ART10 & MI10 & ST10 & PR10) & Hc10').
  clear Hc10.
  (* [comment removed for export] *)
  assert (LV3' : rt_live RT Σ3 = (b, n + 1) :: rt_live RT Σ1) by (rewrite LV3; exact LV2).
  assert (FRS3' : rt_frames RT Σ3 = [(FB, 2%nat)]) by (rewrite FRS3, FRS2; exact FRS1).
  assert (SP3' : rt_sp0 RT Σ3 = rt_sp0 RT Σ) by (rewrite SP3, SP2; exact SP1).
  assert (PRES0_10 : rt_pres_fp (rt_live RT Σ) [] usp W0 m m10).
  { apply (pres_fp_trans _ _ _ _ m m9 m10 PRES0_9). intros a Ha _. destruct (NFB _ Ha) as (N1 & _). apply PR10; [apply (SUB02 _ spa); [clear - SPA1; lia| exact Ha]|].
    cbn [outside]. clear - N1. lia. }
  assert (PRES3_10 : rt_pres_fp (rt_live RT Σ1) (rt_frames RT Σ1) spa W3 m3 m10).
  { apply (pres_fp_trans _ _ _ _ m3 m9 m10 PRES3_9). intros a Ha Ho. apply PR10; [apply (SUB12 _ spa); [lia| exact Ha]|].
    unfold W3 in Ho. cbn [outside] in *. clear - Ho. lia. }
  assert (AGF10 : forall (Q : Z -> Prop), (forall y, Q y -> (FB <= y < FB + 144) \/ (shad FB <= y < shad FB + 32)) -> agree_on Q m9 m10).
  { intros Q HQ. apply (agree_of_pres_fp _ _ _ _ _ _ _ PR10). intros y Hy. destruct (HQ y Hy) as [H|H].
    - split; [apply (acl_frame _ _ _ FB 2%nat); [exact INF2| change (fs_size 2) with 256; clear - H; lia]| cbn [outside]; clear - H; lia].
    - split; [apply (acl_fshadow _ _ _ FB 2%nat); [exact INF2| change (fs_size 2) with 256; rewrite SHF; exact H]|].
      cbn [outside]. unfold shad, SHB in *. clear - H FBh FB0 FBlo LOT. Z.div_mod_to_equations. lia. }
  pose proof (wr_at_agree_nw bsegs m9 m10 FB 8 (wr_at_sub m9 FB 248 FB 8 WF9 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(apply AGF10; intros y Hy; cbv beta in Hy; left; clear - Hy; lia)) as WH10.
  pose proof (wr_at_agree_nw bsegs m9 m10 _ _ WS9 ltac:(apply AGF10; intros y Hy; cbv beta in Hy; right; exact Hy)) as WS10.
  assert (STAT010 : forall lo' hi', (forall y, lo' <= y < hi' -> client_static y /\ outside W0 y) -> agree_on (fun y => lo' <= y < hi') m m10).
  { intros lo' hi' H a Ha. destruct (H _ Ha) as (H1 & H2). apply PRES0_10; [apply acl_static; exact H1| exact H2]. }
  pose proof (ro_cells_agree bsegs m m10 _ _ FIM ltac:(apply STAT010; intros y Hy; unfold W0, G_FREE_IMPL, G_LATCH in *; cbn in Hy; cbn [outside]; split; [apply client_static_intro; lia| lia])) as FIM10.
  destruct (lib_ro_cells m10 (af_lib_ro RT AF Σ3 m10 ART10)) as (_ & _ & _ & GOTF10 & _).
  pose proof (fz_wF usp spa lo b gp (W 0xbdae10) q0 q1 q2 k0 k1 k2 k3 k4 k5 k6 k7 (W FB) (W n) (W d) (W (shad FB)) (W FB) (W SHB) (W (-8)) s10 s11
                q3 q4 q5 q6 F10 fc10 m10 ST10 (conj LOB LOT) ltac:(clear - SPA1 LOR; ul) ltac:(clear - SPA1 SPT; ul) MI10 FIM10 GOTF10) as W11.
  to_cps W11 c10 Hc10' Σ3 MST. intros c11 Hc11.
  destruct (ASTA_unpack RT Σ3 _ _ c11 Hc11) as (ms11 & (m11 & -> & MU11 & WM11 & MI11 & ST11) & Hc11'). clear Hc11.
  assert (ART11 : ART RT Σ3 m11).
  { apply (af_frame RT AF Σ3 m10 m11 (spa + -16) ART10 ltac:(rewrite SP3'; clear - SPA1 LOR LOW; ul)); [| exact WM11].
    intros a Ha. apply MU11. cbn [outside]. split; [| exact I]. intros Hin. apply Ha. apply acl_stack. clear - Hin SPA1 SPT. ul. }
  assert (STKLOW : forall x, spa + -16 <= x < spa -> forall live frames, ~ aclient live frames spa x \/ True) by (intros; right; exact I).
  assert (PRES0_11 : rt_pres_fp (rt_live RT Σ) [] usp W0 m m11).
  { apply (pres_fp_trans _ _ _ _ m m10 m11 PRES0_10). apply (pres_fp_of_munch _ _ _ _ _ m10 m11 MU11). intros x Hx _. destruct (NFB _ Hx) as (_ & _ & N3).
    cbn [outside]. clear - N3 SPA1 LOR. unfold FUZZ_STACK in *. lia. }
  assert (PRES3_11 : rt_pres_fp (rt_live RT Σ1) (rt_frames RT Σ1) spa W3 m3 m11).
  { apply (pres_fp_trans _ _ _ _ m3 m10 m11 PRES3_10). apply (pres_fp_of_munch _ _ _ _ _ m10 m11 MU11). intros x Hx _. cbn [outside].
    destruct (aclient_split RT AF Σ1 m2 spa _ ART2 Hx) as [H|H]; rewrite ?SP1 in H; clear - H LOW LOR SPA1; unfold FUZZ_STACK in *; lia. }
  pose proof (wr_at_transport bsegs m10 m11 _ _ WH10 WM11) as WH11. pose proof (wr_at_transport bsegs m10 m11 _ _ WS10 WM11) as WS11.
  pose proof (rw_cells_agree_nw bsegs m3 m11 _ _ UREC3 ltac:(apply (agree_of_pres_fp _ _ _ _ _ _ _ PRES3_11); intros y Hy; cbn [cells_size csize Nat.add] in Hy; apply STKQ; clear - Hy SPA1 SPT; ul)) as UREC11.
  assert (UWF : unwind_ok m11 (W 0x1ee1cc) (W usp) (W spa)).
  { split; [rewrite (unsigned_lit 0x1ee1cc) by lia; unfold ALLOC_RAS; do 7 right; left; reflexivity|]. right.
    exists [0x1edea4]. split; [rewrite (unsigned_lit 0x1ee1cc) by lia; unfold ALLOC_CHAINS; do 2 right; left; reflexivity|].
    cbn [uw_chain]. rewrite ESPA, EUSP. split; [clear - SPA1; lia|]. split; [exact SPT|]. exists s0. split; [exact UREC11| exact FPI]. }
  assert (INB3 : In (b, n + 1) (rt_live RT Σ3)) by (rewrite LV3'; left; reflexivity).
  eapply (cps_realizes bsegs _ _ T c11).
  { eapply (rc_free RT RC Σ3 PMc (W 0x1ee1cc) (W spa) gp (W 0xbdae10) q0 (W 2025576) q2 (W usp) (W spa) (W b) (W 229042) (W 35) (W 2025576) (W 6170748)
              k5 k6 k7 (W FB) (W n) (W d) (W b) (W (shad FB)) (W FB) (W SHB) (W (-8)) s10 s11 q3 q4 q5 q6 F10 fc10 m11
              b (n + 1) lo FDO MST INB3); try reflexivity.
    - exact ART11.
    - exact MI11.
    - unfold call_ok. rewrite ESPA, SP3'. split; [exact ST11|]. split; [exact LOW|]. split; [clear - SPA1 LOR; ul|].
      split; [clear - SPA1 SPT; ul| clear - SPA2; Z.div_mod_to_equations; lia].
    - exact UWF. }
  { exact Hc11'. }
  clear Hc11'. intros c12 Hc12. destruct Hc12 as (Σ4 & v12 & Hc12 & LV4 & FRS4 & SP4 & CR4).
  destruct (ASTA_unpack RT Σ4 _ _ c12 Hc12) as (ms12 & (m12 & RS12 & (ART12 & MI12 & ST12) & PR12) & Hc12'). clear Hc12.
  destruct RS12 as (r0 & r1 & r2 & o1 & o2 & o3 & o4 & o5 & o6 & o7 & r3 & r4 & r5 & r6 & F12 & fc12 & ->).
  rewrite ESPA in ST12, PR12. rewrite (ret_pc_even 0x1ee1cc ltac:(lia) eq_refl) in Hc12'.
  assert (LV4' : rt_live RT Σ4 = rt_live RT Σ).
  { rewrite LV4, LV3', <- LV1. apply live_remove_head. apply (live_fresh RT AF Σ2 m4 [] b (n + 1) (rt_live RT Σ1) ART4 LV2 ltac:(clear - Hn; lia)).
    intros e He. cbn [app] in He. rewrite LV1 in He. destruct e as (pe, ke). exact (POS pe ke He). }
  assert (FRS4' : rt_frames RT Σ4 = [(FB, 2%nat)]) by (rewrite FRS4; exact FRS3').
  rewrite LV4', FRS3' in PR12.
  assert (PRES0_12 : rt_pres_fp (rt_live RT Σ) [] usp W0 m m12).
  { apply (pres_fp_trans _ _ _ _ m m11 m12 PRES0_11). intros a Ha _. apply PR12. apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto| intros e []| clear - SPA1; lia]. }
  assert (PRES3_12 : rt_pres_fp (rt_live RT Σ1) (rt_frames RT Σ1) spa W3 m3 m12).
  { apply (pres_fp_trans _ _ _ _ m3 m11 m12 PRES3_11). intros a Ha _. apply PR12. rewrite <- LV1, <- FRS1. exact Ha. }
  assert (AGF12 : forall (Q : Z -> Prop), (forall y, Q y -> (FB <= y < FB + 248) \/ (shad FB <= y < shad FB + 32)) -> agree_on Q m11 m12).
  { intros Q HQ. apply (agree_of_pres _ _ _ _ _ _ PR12). intros y Hy. destruct (HQ y Hy) as [H|H].
    - apply (acl_frame _ _ _ FB 2%nat); [left; reflexivity| change (fs_size 2) with 256; clear - H; lia].
    - apply (acl_fshadow _ _ _ FB 2%nat); [left; reflexivity| change (fs_size 2) with 256; rewrite SHF; exact H]. }
  pose proof (wr_at_agree_nw bsegs m11 m12 _ _ WH11 ltac:(apply AGF12; intros y Hy; cbv beta in Hy; left; clear - Hy; lia)) as WH12.
  pose proof (wr_at_agree_nw bsegs m11 m12 _ _ WS11 ltac:(apply AGF12; intros y Hy; cbv beta in Hy; right; exact Hy)) as WS12.
  (* [comment removed for export] *)
  destruct (af_frame_release RT AF Σ4 m12 FB 2 [] ART12 FRS4') as (Σ5a & fl & _ & _ & FL0 & FLW & FW & _).
  change (fs_size 2) with 256 in FW. replace (FB + 256 - 8) with (FB + 248) in FW by lia.
  destruct (wr_at_rw_CB m12 FB 8 WH12 ltac:(lia)) as (jh12 & HDJ12). destruct (wr_at_rw_CB m12 (shad FB) 32 WS12 ltac:(lia)) as (js12 & SHJ12).
  change (Z.to_nat 8) with 8%nat in HDJ12. change (Z.to_nat 32) with 32%nat in SHJ12.
  pose proof (fz_wG usp spa lo FB fl gp (W 0xbdae10) r0 r1 r2 v12 o1 o2 o3 o4 o5 o6 o7 (W n) (W d) (W b) (W SHB) s10 s11 r3 r4 r5 r6 F12 fc12 m12 jh12 js12
                (conj LOB LOT) ltac:(clear - SPA1 LOR; ul) ltac:(clear - SPA1 SPT; ul) MI12 FB64 FBg FBlo FBh HDJ12 SHJ12 FW) as W13.
  to_cps W13 c12 Hc12' Σ4 MST. intros c13 Hc13.
  destruct (ASTA_unpack RT Σ4 _ _ c13 Hc13) as (ms13 & (m13 & -> & MU13 & WM13 & MI13) & Hc13'). clear Hc13.
  assert (ART13 : ART RT Σ4 m13).
  { apply (af_frame RT AF Σ4 m12 m13 spa ART12 ltac:(rewrite SP4, SP3'; clear - SPA1 LOR LOW; ul)); [| exact WM13].
    intros a Ha. apply MU13. cbn [outside]. rewrite FRS4' in Ha. split; [| split; [| exact I]]; intros Hin; apply Ha.
    - apply (acl_frame _ _ _ FB 2%nat); [left; reflexivity| change (fs_size 2) with 256; clear - Hin; lia].
    - apply (acl_fshadow _ _ _ FB 2%nat); [left; reflexivity| change (fs_size 2) with 256; rewrite SHF; exact Hin]. }
  destruct (af_frame_release RT AF Σ4 m13 FB 2 [] ART13 FRS4') as (Σ5 & fl' & FLC' & NAC' & FL0' & FLW' & FW' & REL).
  change (fs_size 2) with 256 in FW'. replace (FB + 256 - 8) with (FB + 248) in FW' by lia. rewrite SP4, SP3' in FLW'. rewrite LV4', FRS4' in NAC'.
  assert (AG1213 : forall (Q : Z -> Prop), (forall y, Q y -> (y < FB \/ FB + 8 <= y) /\ (y < shad FB \/ shad FB + 32 <= y)) -> agree_on Q m12 m13).
  { intros Q HQ. apply (agree_of_munch _ _ _ _ MU13). intros y Hy. destruct (HQ y Hy) as (H1 & H2). cbn [outside]. clear - H1 H2. lia. }
  assert (EFL : W fl = W fl').
  { apply (ro_C8_func m13 (FB + 248)); [| exact FW']. apply (ro_cells_agree bsegs m12 m13 _ _ FW). apply AG1213. intros y Hy.
    cbn [cells_size csize Nat.add] in Hy. unfold shad, SHB. clear - Hy FBh FB0 FBlo LOT. Z.div_mod_to_equations. lia. }
  rewrite EFL in Hc13'.
  assert (STKQ' : forall y, spa <= y < USTACK_TOP -> (y < FB \/ FB + 8 <= y) /\ (y < shad FB \/ shad FB + 32 <= y)).
  { intros y Hy. clear - Hy FBlo SHFlo LOR SPA1. unfold FUZZ_STACK in *. lia. }
  assert (FZF13 : rw_cells bsegs m13 (usp + -88) [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 (W RA_FUZZ)]).
  { apply (rw_cells_agree_nw bsegs m12 m13); [apply (rw_cells_agree_nw bsegs m3 m12 _ _ FZF3)|].
    - apply (agree_of_pres_fp _ _ _ _ _ _ _ PRES3_12). intros y Hy. cbn [cells_size csize Nat.add] in Hy. apply STKQ. clear - Hy SPA1 SPT. ul.
    - apply AG1213. intros y Hy. cbn [cells_size csize Nat.add] in Hy. apply STKQ'. clear - Hy SPA1 SPT. ul. }
  (* [comment removed for export] *)
  pose proof (fz_wH usp spa lo fl' gp (W 0xbdae10) r0 r1 r2 o1 o2 o3 o4 o5 o6 o7 (W FB) (W n) (W d) (W b) (W (shad FB)) (W FB) (W SHB) (W (-8)) s10 s11
                r3 r4 r5 r6 F12 fc12 m13 (Z_to_bv 8 1) s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 (W RA_FUZZ)
                (conj LOB LOT) ltac:(clear - LOR; ul) ltac:(clear - SPT; ul) MI13 FL0' ltac:(clear - FLW' LOW; lia) FLC' FZF13) as W14.
  to_cps W14 c13 Hc13' Σ4 MST. intros c14 Hc14.
  destruct (ASTA_unpack RT Σ4 _ _ c14 Hc14) as (ms14 & (m14 & -> & MU14 & WM14 & MI14 & FLC14) & Hc14'). clear Hc14.
  destruct (REL m14 MU14 WM14 FLC14) as (ART14 & FRS5 & LV5 & SP5 & CR5 & AL5 & AM5).
  assert (NFL : forall x, aclient (rt_live RT Σ) [] usp x -> x <> fl').
  { intros x Hx E. subst x. apply NAC'. destruct Hx as [H|[H|[H|[H|H]]]].
    - exfalso. clear - H FLW' LOW LOR. unfold FUZZ_STACK in *. lia.
    - right; left. exact H.
    - right; right; left. exact H.
    - destruct H as (f & k & [] & _).
    - destruct H as (f & k & [] & _). }
  assert (AG1314 : forall (Q : Z -> Prop), (forall y, Q y -> y <> fl') -> agree_on Q m13 m14).
  { intros Q HQ. apply (agree_of_munch _ _ _ _ MU14). intros y Hy. specialize (HQ y Hy). cbn [outside]. clear - HQ. lia. }
  assert (PRES0_14 : rt_pres_fp (rt_live RT Σ) [] usp W0 m m14).
  { apply (pres_fp_trans _ _ _ _ m m12 m14 PRES0_12). intros a Ha _. destruct (NFB _ Ha) as (N1 & N2 & _).
    rewrite (AG1314 (fun y => y <> fl') ltac:(auto) a (NFL _ Ha)). apply (AG1213 (fun y => (y < FB \/ FB + 8 <= y) /\ (y < shad FB \/ shad FB + 32 <= y)) ltac:(auto)).
    clear - N1 N2. lia. }
  assert (STKFL : forall y, lo <= y < USTACK_TOP -> y <> fl') by (intros y Hy; clear - Hy FLW' LOW; lia).
  apply Hk. exists Σ5.
  split; [| split; [rewrite LV5; exact LV4'| split; [exact FRS5| split; [rewrite SP5, SP4; exact SP3'|
            rewrite CR5, CR4, CR3, CR2, CR1; unfold mcost; destruct (n + 1 <=? 64512); clear - BSL Hn; unfold FUZZ_COST; lia]]]].
  eapply ASTA_conseq; [exact (ASTA_switch RT Σ4 Σ5 PMc _ c14 Hc14' AL5 AM5)|]. intros ms <-. exists m14.
  split; [exists r0, r1, r2, o1, o2, o3, o4, o5, o6, o7, r3, r4, r5, r6, F12, fc12; reflexivity|].
  split; [split; [exact ART14| split; [exact MI14|]]|].
  { (* [comment removed for export] *)
    assert (S1 : stk bsegs m14 lo spa).
    { apply (stk_agree_nw bsegs m13 m14); [apply (stk_agree_nw bsegs m12 m13 _ _ ST12)|].
      - apply AG1213. intros y Hy. cbv beta in Hy. clear - Hy FBlo SHFlo. lia.
      - apply AG1314. intros y Hy. cbv beta in Hy. apply STKFL. clear - Hy SPA1 SPT. ul. }
    assert (S2 : stk bsegs m14 spa (usp + -88)).
    { apply (stk_agree_nw bsegs m13 m14); [apply (stk_agree_nw bsegs m12 m13); [apply (stk_agree_nw bsegs m3 m12 _ _ SLOT3)| ]|].
      - apply (agree_of_pres_fp _ _ _ _ _ _ _ PRES3_12). intros y Hy. cbv beta in Hy. apply STKQ. clear - Hy SPA1 SPT. ul.
      - apply AG1213. intros y Hy. cbv beta in Hy. apply STKQ'. clear - Hy SPA1 SPT. ul.
      - apply AG1314. intros y Hy. cbv beta in Hy. apply STKFL. clear - Hy SPA1 LOR SPT. ul. }
    assert (S3 : rw_cells bsegs m14 (usp + -88) [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 (W RA_FUZZ)]).
    { apply (rw_cells_agree_nw bsegs m13 m14 _ _ FZF13). apply AG1314. intros y Hy. cbn [cells_size csize Nat.add] in Hy. apply STKFL. clear - Hy LOR SPT. ul. }
    apply (stk_merge bsegs m14 lo spa usp S1); [| clear - SPA1 LOR; ul].
    apply (stk_merge bsegs m14 spa (usp + -88) usp S2); [| clear - SPA1; lia].
    pose proof (stk_of_rw_cells bsegs m14 (usp + -88) _ S3) as H. cbn [cells_size csize Nat.add] in H. replace (usp + -88 + Z.of_nat 88) with usp in H by lia. exact H. }
  split.
  { rewrite FRS0. intros a Ha Ho. apply PRES0_14; [exact Ha|]. unfold W0, G_LATCH. unfold LIB_FP in Ho. cbn [outside] in *. clear - Ho. lia. }
  assert (STAT014 : forall lo' hi', (forall y, lo' <= y < hi' -> client_static y /\ outside W0 y) -> agree_on (fun y => lo' <= y < hi') m m14).
  { intros lo' hi' H a Ha. destruct (H _ Ha) as (H1 & H2). apply PRES0_14; [apply acl_static; exact H1| exact H2]. }
  split; [| split].
  - apply (ro_cells_agree bsegs m m14 _ _ MIM). apply STAT014. intros y Hy. unfold W0, G_MALLOC_IMPL, G_LATCH in *. cbn in Hy. cbn [outside]. split; [apply client_static_intro; lia| lia].
  - apply (ro_cells_agree bsegs m m14 _ _ FIM). apply STAT014. intros y Hy. unfold W0, G_FREE_IMPL, G_LATCH in *. cbn in Hy. cbn [outside]. split; [apply client_static_intro; lia| lia].
  - exists lv'. apply (rw_cells_agree_nw bsegs m13 m14); [apply (rw_cells_agree_nw bsegs m12 m13); [apply (rw_cells_agree_nw bsegs m3 m12 _ _ LAT3)| ]|].
    + apply (agree_of_pres_fp _ _ _ _ _ _ _ PRES3_12). intros y Hy. apply STATQ. apply client_static_intro. unfold G_LATCH in *. cbn in Hy. lia.
    + apply AG1213. intros y Hy. unfold G_LATCH in *. cbn in Hy. unfold shad, SHB. clear - Hy FBg FB0. Z.div_mod_to_equations. lia.
    + apply AG1314. intros y Hy E. subst y. apply NAC'. right; left. apply client_static_intro. unfold G_LATCH in *. cbn in Hy. lia.
Qed.

(* [comment removed for export] *)
Theorem fuzz_one_ok : fuzz_one_cps RT LIB_A.
Proof using RC R0.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d bs lo
    FDO MST -> -> -> -> D0 BSL INB INPC FRS0 POS LVB CRB FPI LIB0 SSP ART0 MI0 ST0 LOW LOR SPT SPA SPS T c Hc Hk.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  set (usp := bv_unsigned sp) in *. set (n := Z.of_nat (length bs)) in *.
  assert (ESP : sp = W usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  assert (LOB : 0x7fff7f800000 <= lo) by (clear - LOW SP0W; ul).
  assert (EUSP : bv_unsigned (W usp) = usp) by (apply unsigned_lit; clear - LOB LOR SPT; ul).
  assert (FPI' : fp_invalid s0 (W usp)) by (unfold fp_invalid; rewrite EUSP; exact FPI).
  assert (KQ : forall c', FZQ Σ PMc (W RA_FUZZ) gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m c' -> realizes bsegs c' T).
  { intros c' HQ. apply Hk. unfold FZQ in HQ. rewrite ESP. exact HQ. }
  clear Hk. rewrite ESP in Hc. clearbody usp. clear ESP sp.
  destruct (Z.eq_dec (usp mod 32) 0) as [A0|A16].
  - pose proof (fz_wA0 usp lo d n (W RA_FUZZ) gp (W 0xbdae10) t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
                  ST0 ltac:(clear - LOR; ul) LOB ltac:(clear - SPT; ul) A0 (af_client_consts RT AF Σ m ART0) MI0) as W1.
    to_cps W1 c Hc Σ MST. intros c1 Hc1.
    destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & u0 & u1 & u2 & a1' & a2' & a3' & a4' & a5' & a6' & a7' & u3 & u4 & u5 & u6 & -> & MU1 & WM1 & MI1 & ST1 & FZF1) & Hc1').
    clear Hc1. replace (usp - 96) with (usp + -96) in MU1 by lia. unfold fz_frame in FZF1.
    apply (fz_mid_cps Σ PMc (W RA_FUZZ) gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m d bs (usp + -96) m1 u0 u1 u2 a1' a2' a3' a4' a5' a6' a7' u3 u4 u5 u6 F fc
             FDO MST eq_refl D0 BSL INB INPC FRS0 POS LVB CRB FPI' LIB0 ART0 MI0 LOW LOR SPT SPS ltac:(lia) ltac:(clear - A0; Z.div_mod_to_equations; lia)
             MU1 WM1 MI1 ST1) with (c := c1); [| | exact Hc1'| exact KQ].
    + pose proof (stk_of_rw_cells bsegs m1 (usp + -96) _ (rw_cells_head m1 _ _ _ FZF1)) as H. cbn [cells_size csize Nat.add] in H.
      replace (usp + -96 + Z.of_nat 8) with (usp + -88) in H by lia. exact H.
    + pose proof (rw_cells_tail m1 _ _ _ FZF1) as H. cbn [csize] in H. replace (usp + -96 + Z.of_nat 8) with (usp + -88) in H by lia. exact H.
  - assert (A16' : usp mod 32 = 16) by (clear - A16 SPA; Z.div_mod_to_equations; lia).
    pose proof (fz_wA16 usp lo d n (W RA_FUZZ) gp (W 0xbdae10) t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
                  ST0 ltac:(clear - LOR; ul) LOB ltac:(clear - SPT; ul) A16' (af_client_consts RT AF Σ m ART0) MI0) as W1.
    to_cps W1 c Hc Σ MST. intros c1 Hc1.
    destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & u0 & u1 & u2 & a1' & a2' & a3' & a4' & a5' & a6' & a7' & u3 & u4 & u5 & u6 & jg0 & jg1 & -> & MU1 & WM1 & MI1 & ST1 & FZF1) & Hc1').
    clear Hc1. replace (usp - 112) with (usp + -112) in MU1 by lia. unfold fz_frame in FZF1.
    apply (fz_mid_cps Σ PMc (W RA_FUZZ) gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m d bs (usp + -112) m1 u0 u1 u2 a1' a2' a3' a4' a5' a6' a7' u3 u4 u5 u6 F fc
             FDO MST eq_refl D0 BSL INB INPC FRS0 POS LVB CRB FPI' LIB0 ART0 MI0 LOW LOR SPT SPS ltac:(lia) ltac:(clear - A16'; Z.div_mod_to_equations; lia)
             MU1 WM1 MI1 ST1) with (c := c1); [| | exact Hc1'| exact KQ].
    + pose proof (proj1 (proj1 (rw_cells_app m1 (usp + -112) [CB 8 jg0; CB 8 jg1; C8 (W 0)] _) FZF1)) as H0.
      pose proof (stk_of_rw_cells bsegs m1 (usp + -112) _ H0) as H. cbn [cells_size csize Nat.add] in H.
      replace (usp + -112 + Z.of_nat 24) with (usp + -88) in H by lia. exact H.
    + pose proof (rw_cells_skip m1 (usp + -112) [CB 8 jg0; CB 8 jg1; C8 (W 0)] _ FZF1) as H. cbn [cells_size csize Nat.add] in H.
      replace (usp + -112 + Z.of_nat 24) with (usp + -88) in H by lia. exact H.
Qed.

End TOP.
