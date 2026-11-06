(* lib/A/Prog/C_reac_ctrl_parseV.v -- fuzz_ctrl image A (asan, libreac v1.9.0): world facts for the cgif-form glue
   pb_reac_ctrl_parse (lib/A/Prog/C_reac_ctrl_parseP.v), at a state the core's AR describes: the premises of the
   stretches' Sections (reac_ctrl_parseF_pre.PreFOn at the entry, reac_ctrl_parseF_rpost.RPostFOn after
   __asan_stack_malloc_1) and of the acall_kept composition.
   Sections 1-2 are ported from a Theorem Labs lane's lib/B/Prog/C_reac_ctrl_parseW.v @ 258208c7d59, image A addresses
   (B name -> A name): rcpW_shk / rcpW_shc / rcpW_ceil / rcpW_img_lt / rcpW_img_end / rcpW_fgeo / rcpW_block_above /
   rcpW_bytes_nth / rcpW_cover / rcpW_frame (W1) / rcpW_apart_block (W2) / rcpW_apart_frame (W3) / rcpW_apart_img (W4)
   / rcpW_in_frame (W5) / rcpW_block (W6) / rcpW_vis_win (W7) / rcpW_vis_block (W8) / rcpW_vis_frame (W9) / rcpW_win
   (W10) -> rcpV_<same suffix>.  B's W11 (rcpW_rt: ctlrt_of_AR / RT_used_of_AR, with VIS0 / OWNED_RO) is replaced by
   rcpV_rt, route (C): A.ProgWorldCtlRtC.ctl_rt_C_of_AR and A.ProgWorldRtC.RT_used_of_AR_C, no VIS0, no OWNED_RO.
   Section 3 is image A's own (route (C) shadow region, the side-stack premise fpx, the tls premise, .str.4), from
   a Theorem Labs lane's ProgWorld lemmas (ProgWorld_Fs, ProgWorldShadow, ProgWorldTlsApart, ProgWorldTlsOwned,
   ProgWorldBlkApart) and the core.
   Twin rule: every project module is Required without Import and named through a full-path Module alias.
   rule 24: no function proved. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Mem Frame Cells Step PropExec MState ExecF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Img0 AsanRT MemNorm MemNormTr ProgBridge AF0m.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ProgWorld ProgWorld_Fs ProgWorldAstack ProgWorldShadow.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ProgWorldVisWin ProgWorldVisFrame ProgWorldVisHeap.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ProgWorldCtlRtC ProgWorldRtC ACtlRtC ACtlK ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ProgWorldTlsApart ProgWorldTlsOwned ProgWorldBlkApart.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require ImgBounds rng_asan asan_stack_malloc_c RcAsanFP
  RcAsanFPLib asan_stack_malloc_c_on sh_word_on reac_ctrl_parse_c reac_ctrl_parseF bcmp_wrap_c memcmp_c CtrlBase CtrlRo.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YK04 YA0n YM05 YI16 YG0f YG0d YCbq YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YG00 YG01 YG0n YG0v YE01 YG0a YG0s YG0q.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YConstIn.
Import ListNotations.
Local Open Scope Z_scope.

Module LM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module LF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module LC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.
Module LS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.
Module LX := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Module AI0 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Img0.
Module ART := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanRT.
Module MN := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.
Module MNT := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNormTr.
Module PB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgBridge.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AF0m.
Module PW := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorld.
Module PWF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorld_Fs.
Module PWA := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorldAstack.
Module PWS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorldShadow.
Module PWVW := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorldVisWin.
Module PWVF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorldVisFrame.
Module PWVH := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorldVisHeap.
Module PWCC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorldCtlRtC.
Module PWRC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorldRtC.
Module PWTA := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorldTlsApart.
Module PWTO := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorldTlsOwned.
Module PWBA := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorldBlkApart.
Module ARC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlRtC.
Module AK := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlK.
Module SRO := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ShadowRwOn.
Module IB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.ImgBounds.
Module RA := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.rng_asan.
Module SMC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_stack_malloc_c.
Module FP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.RcAsanFP.
Module FPL := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.RcAsanFPLib.
Module SMO := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_stack_malloc_c_on.
Module SWO := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.sh_word_on.
Module PC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_parse_c.
Module PF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_parseF.
Module BW := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.bcmp_wrap_c.
Module MC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.memcmp_c.
Module CB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.CtrlBase.
Module CR := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.CtrlRo.
Module RK11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Module RK04 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK04.
Module RA0n := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0n.
Module RM05 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Module RI16 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI16.
Module RG00 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG00.
Module RG01 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG01.
Module RG0f := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0f.
Module RG0n := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0n.
Module RG0v := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0v.
Module RG0d := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0d.
Module RG0a := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0a.
Module RG0s := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0s.
Module RG0q := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0q.
Module RE01 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YE01.
Module RCbq := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YCbq.
Module RP09 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YP09.
Local Notation rsegs := AI0.rsegs (only parsing).

Section V.
Context {fx : RK11.FPState} {rc : RM05.RunCeil} {SK : RI16.sink_head}.
Variable B : RG0f.asyms.
(* AR_laws of the bundle: the core's own proof (lib/Reusable/YG0q.v AR_laws_ok), no premise. *)
Local Notation LAWS := (RG0q.AR_laws_ok rsegs B).

(* The 8-aligned shadow cover of [a, b] and each shadow byte, in reac_ctrl_parseF.v's shkov / shcov forms. *)
Definition rcpV_shk (RG : LX.footprint) (p n : Z) : Prop :=
  forall a b, p <= a -> a <= b -> b < p + n ->
    LX.rng RG ((a / 8 + ART.ASAN_K) / 8 * 8) ((b / 8 + ART.ASAN_K) / 8 * 8 + 8 - (a / 8 + ART.ASAN_K) / 8 * 8).
Definition rcpV_shc (RG : LX.footprint) (p n : Z) : Prop :=
  forall x, p <= x < p + n -> LX.rng RG (x / 8 + ART.ASAN_K) 1.

(* ---------------------------------------------------------------------------------------------------------
   1. Helpers (B's W helpers, image A). *)

Lemma rcpV_ceil : 0x7fff7f800000 <= RM05.alloc_ceiling <= 0x7fffff800000.
Proof. pose proof (@RG0f.ASAN_CEIL_range rc) as [H _]. unfold RG0f.ASAN_CEIL in H. exact H. Qed.

(* Every image byte lies below IMG_HI = 0x5fe000 (A's ProgBridge.rsegs_spans). *)
Lemma rcpV_img_lt : forall a, RG0d.in_img rsegs a -> a < IB.IMG_HI.
Proof.
  intros a (sg & Hsg & Ha).
  assert (Hm : In (Z.of_N (seg_base sg), Z.of_N (seg_size sg))
                 (map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s))) rsegs))
    by (apply in_map_iff; exists sg; split; [reflexivity | exact Hsg]).
  rewrite PB.rsegs_spans in Hm. unfold IB.IMG_HI.
  cbn [In] in Hm. destruct Hm as [E|[E|[E|[E|[]]]]]; injection E as E1 E2; lia.
Qed.

(* The image range ly_img ends at or above IMG_HI (ALedger's al_img at rsegs' last segment (0xa1000, 0x55d000)). *)
Lemma rcpV_img_end : forall ly S (W : RA0n.world rsegs) m md,
  RG0n.AR rsegs B ly S W m md ->
  IB.IMG_HI <= fst (RG0f.ly_img ly) + snd (RG0f.ly_img ly).
Proof.
  intros ly S W m md (_ & L & _).
  assert (Hm : In (0xa1000, 0x55d000) (map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s))) rsegs)).
  { rewrite PB.rsegs_spans. right; right; right; left. reflexivity. }
  apply in_map_iff in Hm as (sg & Es & Hsg). injection Es as E1 E2.
  pose proof (RG0n.al_img _ _ _ _ L sg Hsg) as [_ J2].
  unfold IB.IMG_HI. lia.
Qed.

(* The geometry of a live fake frame (c, q) and its flag byte inside the side stack. *)
Lemma rcpV_fgeo : forall ly S (W : RA0n.world rsegs) m md c q,
  RG0n.AR rsegs B ly S W m md -> In (c, q) (RG01.frames S) ->
  0 <= c <= 10 /\
  IB.IMG_HI <= RG0f.ly_F ly /\
  RG0f.ly_F ly + RG0f.kFakeFramesOff <= RG0f.frame_addr ly c q /\
  RG0f.frame_addr ly c q + RG00.fs_frame_bytes c <= RG0f.ly_F ly + RG0f.kFakeStackSize /\
  RG0f.frame_addr ly c q mod 64 = 0 /\ 64 <= RG00.fs_frame_bytes c /\
  RG00.fs_frame_bytes c mod 64 = 0 /\
  RG0f.ly_F ly + RG0f.kFakeFlagsOff <= RG0f.flag_addr ly c q /\
  RG0f.flag_addr ly c q < RG0f.ly_F ly + RG0f.kFakeFramesOff /\
  (RG0f.ly_F ly + RG0f.kFakeStackSize <= RG0f.kLowShadowBeg \/
   (RG0f.kHighMemBeg <= RG0f.ly_F ly /\
    RG0f.ly_F ly + RG0f.kFakeStackSize <= RM05.alloc_ceiling)).
Proof.
  intros ly S W m md c q HAR Hin.
  pose proof HAR as (M & _).
  destruct (RG0s.frame_facts B ly S _ c q M Hin)
    as (Hc & _ & [_ HFa] & _ & Hpg & Ho1 & Ho2 & Ho64 & Hb64 & Hbm & Hfl).
  pose proof (PWA.pwfs_F_above B ly S W m md HAR) as Habove.
  unfold SMC.ASAN_GT in Habove.
  unfold RG0f.frame_addr, RG0f.flag_addr, RG0f.page_aligned, RG0f.ASAN_CEIL, IB.IMG_HI in *.
  split; [exact Hc|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [Z.div_mod_to_equations; lia|].
  split; [exact Hb64|]. split; [exact Hbm|]. split; [lia|]. split; [lia|].
  exact HFa.
Qed.

(* The first byte of a caller's block lies above the image. *)
Lemma rcpV_block_above : forall ly S (W : RA0n.world rsegs) m md p n,
  RG0n.AR rsegs B ly S W m md -> In (p, n) (RG0d.ablocks B ly S) ->
  IB.IMG_HI <= p.
Proof.
  intros ly S W m md p n HAR Hin.
  pose proof (rcpV_img_end ly S W m md HAR) as Hend.
  pose proof HAR as (M & _).
  pose proof (RG0n.am_layout _ _ _ _ M) as LO.
  pose proof (RG0f.lo_img _ LO) as (I1 & I2 & I3 & I4).
  apply (RG0s.In_ablocks B) in Hin as (k & Hk & Hst & Hu & Hr).
  pose proof (RG0s.chunk_facts B ly S _ k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
  rewrite <- Hu, G4.
  destruct (RG00.ck_beg k) as [|o|r o|c' p'] eqn:Eb; try solve [destruct GG].
  - cbv zeta in GG. destruct GG as (Gc & _ & _ & _ & Gbase & Gx & _).
    pose proof (RG0s.region_in_prim ly (RG00.prim_class o) LO ltac:(lia))
      as (_ & _ & _ & R4 & _).
    rewrite Gbase. unfold RG0f.kHighMemBeg, IB.IMG_HI in *. lia.
  - destruct GG as (_ & Gfp & Gbase & _ & Gin & _).
    pose proof (RG0n.am_placed _ _ _ _ M) as [PL PD].
    pose proof (proj1 (Forall_forall _ _) PL _ Gin) as (_ & [K1 _] & _). cbn [fst snd] in K1.
    pose proof (RG0s.pairwise_In RG0f.zdisjoint _ _ (RG0f.ly_img ly) _ _
      eq_refl PD Gin ltac:(unfold RG0f.static_extents; apply in_app_iff; right; right; left; reflexivity))
      as D.
    pose proof (RG0a.secondary_geometry (RG00.ck_req k) ltac:(lia) Gfp)
      as (S1 & _ & _ & S4 & _).
    unfold RG0f.zdisjoint in D. cbn [fst snd] in D. rewrite Gbase.
    unfold RG00.kMaxSize, RG00.kPage, RG0f.kImgLo, IB.IMG_HI in *.
    lia.
Qed.

(* A byte list read at a: its i-th byte, read at a + i. *)
Lemma rcpV_bytes_nth : forall (m : word -> option byte) a bs i b,
  LM.bytes_at rsegs m a bs -> nth_error bs i = Some b -> LM.bytes_at rsegs m (a + Z.of_nat i) [b].
Proof.
  intros m a bs i b (H0 & H1 & H2) Hn.
  assert (Hi : (i < length bs)%nat) by (apply nth_error_Some; rewrite Hn; discriminate).
  split; [lia|]. split; [cbn [length]; lia|].
  intros j Hj. cbn [length] in Hj. destruct j as [|j]; [|lia].
  cbn [nth_error]. rewrite <- Hn, <- (H2 i Hi).
  replace (a + Z.of_nat i + Z.of_nat 0) with (a + Z.of_nat i) by lia. reflexivity.
Qed.

(* The shadow word cover of every sub-range [a, b] of [p, p + n), visible, gives both shadow footprint forms. *)
Lemma rcpV_cover : forall (H : word -> bool) p n,
  (forall a b, p <= a -> a <= b -> b < p + n ->
     PB.range_visible H (RA.sh_al8_lo a) (RA.sh_al8_hi a (b - a + 1) - RA.sh_al8_lo a)) ->
  rcpV_shc (PB.RNG_W H) p n /\ rcpV_shk (PB.RNG_W H) p n.
Proof.
  intros H p n Hc.
  unfold RA.sh_al8_lo, RA.sh_al8_hi in Hc.
  split.
  - intros x Hx. apply PB.rng_of_visible.
    pose proof (Hc x x ltac:(lia) ltac:(lia) ltac:(lia)) as V.
    replace (x + (x - x + 1) - 1) with x in V by ring. unfold ART.shadow_addr in V.
    apply (PB.range_visible_sub _ _ _ _ _ V); Z.div_mod_to_equations; lia.
  - intros a b Ha Hab Hb. apply PB.rng_of_visible.
    pose proof (Hc a b Ha Hab Hb) as V.
    replace (a + (b - a + 1) - 1) with b in V by ring. unfold ART.shadow_addr in V. exact V.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   2. W1..W10 (B's, image A). *)

(* W1. The new class-1 frame and its flag byte. *)
Lemma rcpV_frame : forall ly S (W : RA0n.world rsegs) m md pos,
  RG0n.AR rsegs B ly S W m md -> In (1, pos) (RG01.frames S) ->
  let Fr := RG0f.frame_addr ly 1 pos in
  let FL := RG0f.flag_addr ly 1 pos in
  4096 <= Fr /\ Fr + 128 <= RM05.alloc_ceiling /\
  IB.IMG_HI <= FL /\ FL + 1 <= RM05.alloc_ceiling /\ ART.app_mem FL /\
  LF.stk rsegs m FL (FL + 1) /\ PB.range_visible (RA0n.w_H W) FL 1 /\
  IB.IMG_HI <= ART.shadow_addr Fr /\ ART.shadow_addr Fr + 16 <= RM05.alloc_ceiling.
Proof.
  intros ly S W m md pos HAR Hin. cbv zeta.
  destruct (rcpV_fgeo ly S W m md 1 pos HAR Hin) as (_ & HF & Hf1 & Hf2 & _ & _ & _ & Hl1 & Hl2 & Happ).
  destruct (RG0d.al_flag _ _ LAWS ly S W m md 1 pos HAR Hin) as (Hpr & _ & _ & _).
  pose proof rcpV_ceil as Hce.
  assert (E1 : RG00.fs_frame_bytes 1 = 128) by reflexivity.
  rewrite E1 in Hf2.
  set (Fr := RG0f.frame_addr ly 1 pos) in *.
  set (FL := RG0f.flag_addr ly 1 pos) in *.
  unfold IB.IMG_HI, RG0f.kFakeFramesOff, RG0f.kFakeFlagsOff,
    RG0f.kFakeStackSize, RG0f.kLowShadowBeg, RG0f.kHighMemBeg in *.
  assert (P64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [unfold ART.app_mem, ART.LOWMEM_END, ART.HIGHMEM_BEG, ART.APPMEM_END; lia|].
  split.
  { apply (PWA.pwfs_stk_of_present W); [lia | lia |].
    intros a Ha. replace a with FL by lia. exact Hpr. }
  split.
  { unfold PB.range_visible. split; [lia|]. split; [lia|].
    intros a Ha. replace a with FL by lia. exact (proj1 Hpr). }
  unfold ART.shadow_addr, ART.ASAN_K. split; Z.div_mod_to_equations; lia.
Qed.

(* W2. The new frame, its shadow and its flag byte are apart from every byte of a block. *)
Lemma rcpV_apart_block : forall ly S (W : RA0n.world rsegs) m md pos p n a,
  RG0n.AR rsegs B ly S W m md -> In (1, pos) (RG01.frames S) ->
  In (p, n) (RG0d.ablocks B ly S) -> p <= a < p + RG00.req_size n ->
  let Fr := RG0f.frame_addr ly 1 pos in
  let FL := RG0f.flag_addr ly 1 pos in
  ~ (Fr <= a < Fr + 128) /\ a <> FL /\ ~ (ART.shadow_addr Fr <= a < ART.shadow_addr Fr + 16).
Proof.
  intros ly S W m md pos p n a HAR Hin Hb Ha. cbv zeta.
  destruct (rcpV_fgeo ly S W m md 1 pos HAR Hin) as (_ & HF & Hf1 & Hf2 & _ & _ & _ & _ & _ & Happ).
  destruct (RG0d.al_blocks _ _ LAWS ly S W m md p n HAR Hb) as (_ & H4096 & Hbc & [_ Hbapp] & Hbo & _).
  destruct (RG0d.al_flag _ _ LAWS ly S W m md 1 pos HAR Hin) as (_ & Hfo & _).
  destruct (RG0d.al_sep _ _ LAWS ly S W m md HAR) as [Hpw _].
  pose proof (RG0s.pairwise_In RG0f.zdisjoint _ (p, RG00.req_size n)
    (RG0f.frame_addr ly 1 pos, RG00.fs_frame_bytes 1) _ _ eq_refl Hpw) as D.
  assert (D' : RG0f.zdisjoint (p, RG00.req_size n)
                 (RG0f.frame_addr ly 1 pos, RG00.fs_frame_bytes 1)).
  { apply D.
    - apply in_map_iff. exists (p, n). split; [reflexivity | exact Hb].
    - apply in_map_iff. exists (1, pos). split; [reflexivity | exact Hin]. }
  clear D. unfold RG0f.zdisjoint in D'. cbn [fst snd] in D'.
  pose proof rcpV_ceil as Hce.
  assert (E1 : RG00.fs_frame_bytes 1 = 128) by reflexivity.
  rewrite E1 in Hf2, D'.
  set (Fr := RG0f.frame_addr ly 1 pos) in *.
  unfold IB.IMG_HI, RG0f.kFakeFramesOff, RG0f.kFakeStackSize,
    RG0f.kLowShadowBeg, RG0f.kHighMemBeg, RG0f.ASAN_CEIL in *.
  split; [lia|]. split.
  - intros E. apply (proj2 (Hbo a Ha)). rewrite E. exact Hfo.
  - unfold ART.shadow_addr, ART.ASAN_K. Z.div_mod_to_equations. lia.
Qed.

(* W3. ... and apart from every byte of another frame and of that frame's shadow. *)
Lemma rcpV_apart_frame : forall ly S (W : RA0n.world rsegs) m md pos c q a,
  RG0n.AR rsegs B ly S W m md -> In (1, pos) (RG01.frames S) ->
  In (c, q) (RG01.frames S) -> (c, q) <> (1, pos) ->
  (RG0f.frame_addr ly c q <= a < RG0f.frame_addr ly c q + RG00.fs_frame_bytes c \/
   ART.shadow_addr (RG0f.frame_addr ly c q) <= a <
     ART.shadow_addr (RG0f.frame_addr ly c q) + RG00.fs_frame_bytes c / 8) ->
  let Fr := RG0f.frame_addr ly 1 pos in
  let FL := RG0f.flag_addr ly 1 pos in
  ~ (Fr <= a < Fr + 128) /\ a <> FL /\ ~ (ART.shadow_addr Fr <= a < ART.shadow_addr Fr + 16).
Proof.
  intros ly S W m md pos c q a HAR Hin Hcq Hne Ha. cbv zeta.
  destruct (rcpV_fgeo ly S W m md 1 pos HAR Hin) as (_ & HF & Hf1 & Hf2 & Hfm & _ & _ & Hl1 & Hl2 & Happ).
  destruct (rcpV_fgeo ly S W m md c q HAR Hcq) as (_ & _ & Hg1 & Hg2 & Hgm & Hgb & Hgbm & _).
  pose proof HAR as (M & _).
  destruct (RG0s.frame_facts B ly S _ 1 pos M Hin) as (C1 & P1 & _).
  destruct (RG0s.frame_facts B ly S _ c q M Hcq) as (C2 & P2 & _).
  pose proof (RG0s.frames_apart c q 1 pos C2 P2 C1 P1 Hne) as D.
  unfold RG0f.zdisjoint in D. cbn [fst snd] in D.
  pose proof rcpV_ceil as Hce.
  assert (E1 : RG00.fs_frame_bytes 1 = 128) by reflexivity.
  rewrite E1 in Hf2, D.
  unfold RG0f.frame_addr, RG0f.flag_addr in *.
  unfold IB.IMG_HI, RG0f.kFakeFramesOff, RG0f.kFakeFlagsOff,
    RG0f.kFakeStackSize, RG0f.kLowShadowBeg, RG0f.kHighMemBeg,
    ART.shadow_addr, ART.ASAN_K in *.
  destruct Ha as [Ha|Ha].
  - split; [lia|]. split; [lia|]. Z.div_mod_to_equations. lia.
  - split; [Z.div_mod_to_equations; lia|]. split; [Z.div_mod_to_equations; lia|].
    Z.div_mod_to_equations. lia.
Qed.

(* W4. ... and apart from every image byte. *)
Lemma rcpV_apart_img : forall ly S (W : RA0n.world rsegs) m md pos a,
  RG0n.AR rsegs B ly S W m md -> In (1, pos) (RG01.frames S) ->
  RG0d.in_img rsegs a ->
  let Fr := RG0f.frame_addr ly 1 pos in
  let FL := RG0f.flag_addr ly 1 pos in
  ~ (Fr <= a < Fr + 128) /\ a <> FL /\ ~ (ART.shadow_addr Fr <= a < ART.shadow_addr Fr + 16).
Proof.
  intros ly S W m md pos a HAR Hin Himg. cbv zeta.
  pose proof (rcpV_img_lt a Himg) as Ha.
  destruct (rcpV_fgeo ly S W m md 1 pos HAR Hin) as (_ & HF & Hf1 & _ & _ & _ & _ & Hl1 & _).
  set (Fr := RG0f.frame_addr ly 1 pos) in *.
  set (FL := RG0f.flag_addr ly 1 pos) in *.
  unfold IB.IMG_HI, RG0f.kFakeFramesOff, RG0f.kFakeFlagsOff in *.
  split; [lia|]. split; [lia|]. unfold ART.shadow_addr, ART.ASAN_K. Z.div_mod_to_equations. lia.
Qed.

(* W5. A byte range inside a frame of S. *)
Lemma rcpV_in_frame : forall ly S (W : RA0n.world rsegs) m md c q lo len,
  RG0n.AR rsegs B ly S W m md -> In (c, q) (RG01.frames S) -> 0 <= len ->
  RG0f.frame_addr ly c q <= lo -> lo + len <= RG0f.frame_addr ly c q + RG00.fs_frame_bytes c ->
  lo + len <= RM05.alloc_ceiling /\ IB.IMG_HI <= lo /\
  (forall i, 0 <= i < len -> LM.ro_addr rsegs (LM.wa (lo + i)) = false) /\
  (forall p n a, In (p, n) (RG0d.ablocks B ly S) -> p <= a < p + RG00.req_size n ->
     ~ (lo <= a < lo + len)) /\
  LF.stk rsegs m lo (lo + len).
Proof.
  intros ly S W m md c q lo len HAR Hcq Hlen Hlo Hhi.
  destruct (rcpV_fgeo ly S W m md c q HAR Hcq) as (_ & HF & Hg1 & Hg2 & _ & _ & _ & _ & _ & Happ).
  destruct (RG0d.al_frames _ _ LAWS ly S W m md c q HAR Hcq) as (_ & _ & Hby & _).
  destruct (RG0d.al_sep _ _ LAWS ly S W m md HAR) as [Hpw _].
  pose proof rcpV_ceil as Hce.
  assert (P64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HB : forall p n a, In (p, n) (RG0d.ablocks B ly S) ->
                 p <= a < p + RG00.req_size n -> ~ (lo <= a < lo + len)).
  { intros p n a Hb Ha.
    pose proof (RG0s.pairwise_In RG0f.zdisjoint _ (p, RG00.req_size n)
      (RG0f.frame_addr ly c q, RG00.fs_frame_bytes c) _ _ eq_refl Hpw) as D.
    assert (D' : RG0f.zdisjoint (p, RG00.req_size n)
                   (RG0f.frame_addr ly c q, RG00.fs_frame_bytes c)).
    { apply D.
      - apply in_map_iff. exists (p, n). split; [reflexivity | exact Hb].
      - apply in_map_iff. exists (c, q). split; [reflexivity | exact Hcq]. }
    unfold RG0f.zdisjoint in D'. cbn [fst snd] in D'. lia. }
  set (F := RG0f.frame_addr ly c q) in *.
  unfold IB.IMG_HI, RG0f.kFakeFramesOff, RG0f.kFakeStackSize,
    RG0f.kLowShadowBeg, RG0f.kHighMemBeg in Happ, HF, Hg1, Hg2.
  split; [lia|]. split; [unfold IB.IMG_HI; lia|].
  split; [intros i Hi; apply MNT.ro_addr_above_img; unfold IB.IMG_HI; lia|].
  split; [exact HB|].
  apply (PWA.pwfs_stk_of_present W); [lia | lia |].
  intros a Ha. exact (proj1 (Hby a ltac:(lia))).
Qed.

(* W6. A caller's block: placement, above the image. *)
Lemma rcpV_block : forall ly S (W : RA0n.world rsegs) m md p n,
  RG0n.AR rsegs B ly S W m md -> In (p, n) (RG0d.ablocks B ly S) ->
  4096 <= p /\ p + RG00.req_size n <= RM05.alloc_ceiling /\ IB.IMG_HI <= p /\
  (forall i, 0 <= i < RG00.req_size n -> ART.app_mem (p + i)).
Proof.
  intros ly S W m md p n HAR Hb.
  destruct (RG0d.al_blocks _ _ LAWS ly S W m md p n HAR Hb) as (_ & H4096 & Hbc & [_ Hbapp] & _).
  pose proof (rcpV_block_above ly S W m md p n HAR Hb) as Hab.
  pose proof rcpV_ceil as Hce.
  split; [exact H4096|]. split; [exact Hbc|]. split; [exact Hab|].
  intros i Hi. unfold ART.app_mem, ART.LOWMEM_END, ART.HIGHMEM_BEG, ART.APPMEM_END.
  unfold RG0f.kLowShadowBeg, RG0f.kHighMemBeg, RG0f.ASAN_CEIL in Hbapp.
  lia.
Qed.

(* W7. Footprint visibility of a sub-range of the caller's stack window. *)
Lemma rcpV_vis_win : forall STK sp0 FP ly S (W0 : RA0n.world rsegs) mem0 md0 own lyc Sc
    (W : RA0n.world rsegs) memc mdc k lo len,
  RCbq.ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  sp0 - STK <= lo -> lo + len <= sp0 -> 0 <= len ->
  LX.rng (PB.RNG_W (RA0n.w_H W)) lo len /\
  rcpV_shc (PB.RNG_W (RA0n.w_H W)) lo len /\
  rcpV_shk (PB.RNG_W (RA0n.w_H W)) lo len.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k lo len HJ Hlo Hhi Hlen.
  destruct HJ as (HAR & HLE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
  destruct Hstk as (_ & HSTK & Hceil & Hsp0 & Hsphi & H47 & _).
  destruct HLE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & E10 & E11 & _).
  pose proof rcpV_ceil as Hce.
  change (2 ^ 47) with 140737488355328 in H47.
  assert (P64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  split.
  - apply PB.rng_of_visible. unfold PB.range_visible.
    split; [lia|]. split; [lia|]. intros a Ha. exact (proj1 (Hpres a ltac:(lia))).
  - apply rcpV_cover. intros a b Ha Hab Hb.
    destruct (PWVW.win_sh_vis B LAWS lyc Sc W memc mdc a (b - a + 1) HAR
                ltac:(lia) ltac:(lia) ltac:(lia)) as [E|V]; [lia | exact V].
Qed.

(* W8. The same for a sub-range of a block of S. *)
Lemma rcpV_vis_block : forall ly S (W : RA0n.world rsegs) m md p n lo len,
  RG0n.AR rsegs B ly S W m md -> In (p, n) (RG0d.ablocks B ly S) ->
  p <= lo -> lo + len <= p + RG00.req_size n -> 0 <= len ->
  LX.rng (PB.RNG_W (RA0n.w_H W)) lo len /\
  rcpV_shc (PB.RNG_W (RA0n.w_H W)) lo len /\
  rcpV_shk (PB.RNG_W (RA0n.w_H W)) lo len.
Proof.
  intros ly S W m md p n lo len HAR Hb Hlo Hhi Hlen.
  split.
  - apply PB.rng_of_visible.
    exact (PWVH.heap_vis B LAWS ly S W m md p n lo len HAR Hb Hlo Hhi).
  - apply rcpV_cover. intros a b Ha Hab Hb'.
    destruct (PWVH.heap_sh_vis B LAWS ly S W m md p n a (b - a + 1) HAR Hb
                ltac:(lia) ltac:(lia) ltac:(lia)) as [E|V]; [lia | exact V].
Qed.

(* W9. The same for a sub-range of a frame of S. *)
Lemma rcpV_vis_frame : forall ly S (W : RA0n.world rsegs) m md c q lo len,
  RG0n.AR rsegs B ly S W m md -> In (c, q) (RG01.frames S) ->
  RG0f.frame_addr ly c q <= lo -> lo + len <= RG0f.frame_addr ly c q + RG00.fs_frame_bytes c ->
  0 <= len ->
  LX.rng (PB.RNG_W (RA0n.w_H W)) lo len /\
  rcpV_shc (PB.RNG_W (RA0n.w_H W)) lo len /\
  rcpV_shk (PB.RNG_W (RA0n.w_H W)) lo len.
Proof.
  intros ly S W m md c q lo len HAR Hcq Hlo Hhi Hlen.
  destruct (rcpV_fgeo ly S W m md c q HAR Hcq) as (_ & _ & _ & _ & Hfm & Hb64 & Hbm & _).
  split.
  - apply PB.rng_of_visible.
    exact (proj1 (PWVF.frame_vis B LAWS ly S W m md c q lo len HAR Hcq Hlo Hhi)).
  - apply rcpV_cover. intros a b Ha Hab Hb.
    destruct (PWVF.frame_vis B LAWS ly S W m md c q a (b - a + 1) HAR Hcq
                ltac:(lia) ltac:(lia)) as [_ Hsh].
    destruct (Hsh ltac:(lia) ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia)) as [E|V];
      [lia | exact V].
Qed.

(* W10. The caller's stack window at the current memory of a journal: present (stk), shadow-zero (addressable). *)
Lemma rcpV_win : forall STK sp0 FP ly S (W0 : RA0n.world rsegs) mem0 md0 own lyc Sc
    (W : RA0n.world rsegs) memc mdc k lo hi,
  RCbq.ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  sp0 - STK <= lo -> lo <= hi -> hi <= sp0 ->
  LF.stk rsegs memc lo hi /\ ART.addressable memc lo (hi - lo) /\ RM05.alloc_ceiling <= lo /\
  ART.HIGHMEM_BEG <= lo /\ hi <= ART.APPMEM_END.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k lo hi HJ Hlo Hlh Hhi.
  destruct HJ as (HAR & HLE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
  destruct Hstk as (_ & HSTK & Hceil & Hsp0 & Hsphi & H47 & _).
  destruct HLE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & E10 & E11 & _).
  pose proof rcpV_ceil as Hce.
  change (2 ^ 47) with 140737488355328 in H47.
  assert (P64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  split.
  { apply (PWA.pwfs_stk_of_present W); [lia | lia |].
    intros a Ha. apply Hpres. lia. }
  split.
  { exact (PWS.ctl_stack_shadow_of_AR B LAWS lyc Sc W memc mdc lo (hi - lo) HAR
             ltac:(lia) ltac:(lia) ltac:(lia)). }
  unfold ART.HIGHMEM_BEG, ART.APPMEM_END. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   3. View helpers (B's lib/B/Prog/C_reac_ctrl_classify_box_frame.v cls_addressable_of_view / cls_ra_transfer /
   cls_sh_in_frame / cls_frame_al64 / cls_app_of_in_app / cls_stk_of_pres / cls_img_lt / cls_ret_pc_ok /
   cls_byte_signed_small, image A; the visibility step is A's ProgWorldVisFrame.vis_of_aview). *)

Lemma rcpV_byte_signed_small : forall b : byte, bv_unsigned b < 128 -> bv_signed b = bv_unsigned b.
Proof.
  intros b Hb. unfold bv_signed. apply bv_swrap_small. change (bv_half_modulus 8) with 128.
  pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R. lia.
Qed.

(* At a byte the hidden set does not hide, the core's view is ctrl's mrd (B's cls_aview_mrd). *)
Lemma rcpV_aview_mrd : forall (H : word -> bool) (mem : word -> option byte) a,
  H (Z_to_bv 64 a) = false ->
  RG0n.aview rsegs H mem a = option_map (fun b : byte => bv_unsigned b) (LM.mrd rsegs mem (LM.wa a)).
Proof.
  intros H mem a Hh. unfold RG0n.aview, RP09.mbyte, RK04.mrestrict. cbv beta. rewrite Hh.
  unfold LM.mrd, LM.wa. reflexivity.
Qed.

(* An application range whose shadow the VIEW reads as addressable is addressable in ctrl's sense. *)
Lemma rcpV_addressable_of_view : forall (W : RA0n.world rsegs) (mem : word -> option byte) p n,
  0 <= p -> 0 <= n -> p + n <= ART.APPMEM_END ->
  (forall i, 0 <= i < n -> ART.app_mem (p + i)) ->
  RG0v.range_addressable (RG0n.aview rsegs (RA0n.w_H W) mem) RG0f.SHADOW_OFF p n ->
  ART.addressable mem p n.
Proof.
  intros W mem p n H0 Hn Hp Happ HR. split; [exact H0|]. split; [exact Hn|]. split; [exact Hp|].
  intros i Hi. split; [exact (Happ i Hi)|].
  destruct (HR (p + i) ltac:(lia)) as (s & Es & Hok).
  assert (Esh : RG0v.shadow_of_addr RG0f.SHADOW_OFF (p + i) = ART.shadow_addr (p + i))
    by (unfold RG0v.shadow_of_addr, RG0f.SHADOW_OFF, ART.shadow_addr, ART.ASAN_K; lia).
  rewrite Esh in Es.
  assert (Hv : RA0n.w_H W (Z_to_bv 64 (ART.shadow_addr (p + i))) = false)
    by (apply (PWVF.vis_of_aview rsegs W mem); rewrite Es; discriminate).
  rewrite (rcpV_aview_mrd (RA0n.w_H W) mem (ART.shadow_addr (p + i)) Hv) in Es.
  destruct (LM.mrd rsegs mem (LM.wa (ART.shadow_addr (p + i)))) as [b|] eqn:Eb; cbn in Es;
    [|discriminate Es].
  injection Es as Es. subst s. exists b. split; [reflexivity|].
  unfold RG0v.saddr_ok in Hok. assert (Hsm : bv_unsigned b < 128) by (destruct Hok; lia).
  unfold ART.shadow_ok. rewrite (rcpV_byte_signed_small b Hsm). destruct Hok; [left | right]; lia.
Qed.

Lemma rcpV_ra_transfer : forall (rd rd' : RG0f.reader) p n,
  (forall x, p <= x < p + n -> rd' (RG0v.shadow_of_addr RG0f.SHADOW_OFF x) = rd (RG0v.shadow_of_addr RG0f.SHADOW_OFF x)) ->
  RG0v.range_addressable rd RG0f.SHADOW_OFF p n -> RG0v.range_addressable rd' RG0f.SHADOW_OFF p n.
Proof. intros rd rd' p n E H x Hx. rewrite (E x Hx). exact (H x Hx). Qed.

Lemma rcpV_sh_in_frame : forall fa bs x, fa mod 8 = 0 -> bs mod 8 = 0 -> fa <= x < fa + bs ->
  RG0n.in_zr (RG0v.shadow_of_addr RG0f.SHADOW_OFF x) (RG0f.shadow_addr fa, bs / 8).
Proof.
  intros fa bs x H1 H2 H3. unfold RG0n.in_zr, RG0f.shadow_addr, RG0v.shadow_of_addr. cbn [fst snd].
  assert (L1 : fa / 8 <= x / 8) by (apply Z.div_le_mono; lia).
  assert (E : fa + bs = 8 * (fa / 8 + bs / 8)).
  { pose proof (Z.div_mod fa 8 ltac:(lia)) as Da. pose proof (Z.div_mod bs 8 ltac:(lia)) as Db. lia. }
  assert (L2 : x / 8 < fa / 8 + bs / 8) by (apply Z.div_lt_upper_bound; lia).
  lia.
Qed.

Lemma rcpV_app_of_in_app : forall lo len a, RG0f.in_app lo len -> lo <= a < lo + len -> ART.app_mem a.
Proof.
  intros lo len a [H0 H1] Ha. pose proof (@RM05.alloc_ceiling_lt rc) as Hc.
  unfold ART.app_mem, ART.LOWMEM_END, ART.HIGHMEM_BEG, ART.APPMEM_END.
  unfold RG0f.kLowShadowBeg, RG0f.kHighMemBeg, RG0f.ASAN_CEIL in H1. lia.
Qed.

Lemma rcpV_stk_of_pres : forall (H : word -> bool) (mem : word -> option byte) lo hi,
  0 <= lo -> hi <= 2 ^ 64 -> (forall a, lo <= a < hi -> RG0n.apresent H mem a) -> LF.stk rsegs mem lo hi.
Proof.
  intros H mem lo hi Hlo Hhi Hp. split; [exact Hlo|]. split; [exact Hhi|]. intros a Ha.
  destruct (Hp a Ha) as [_ [b Hb]]. unfold LM.wa. split.
  - unfold wview. rewrite Hb. discriminate.
  - exists b. unfold LM.mrd. rewrite Hb. reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   4. Route (C) runtime facts (W11's replacement): asan_cells, ro_agree, the two shadow regions of ctl_rt_C, and the
   bcmp wrapper's cells, from A.ProgWorldCtlRtC.ctl_rt_C_of_AR and A.ProgWorldRtC.RT_used_of_AR_C (no VIS0, no
   OWNED_RO). *)
Hypothesis TS : AF.CtrlTSyms B.

Lemma rcpV_rt : forall RLO RHI ly S (W : RA0n.world rsegs) m md,
  RG0n.AR rsegs B ly S W m md ->
  RE01.arodata_okS rsegs B RLO RHI (RG0n.aview rsegs (RA0n.w_H W) m) ->
  MN.ro_agree rsegs m /\ ART.asan_cells m /\
  SRO.shadow_rw_on (ARC.cut_shadow B ly S) m /\ SRO.shadow_rw_on ARC.img_shadow m /\
  LM.bytes_at rsegs m BW.REAL_BCMP (LM.le8 (LM.wa BW.BCMP)) /\
  LM.bytes_at rsegs m BW.REAL_MEMCMP (LM.le8 (LM.wa MC.MEMCMP)) /\
  LM.bytes_at rsegs m BW.GOT_CF (LM.le8 (LM.wa BW.CF)) /\ LM.bytes_at rsegs m (BW.CF + 254) [Z_to_bv 8 1] /\
  LM.bytes_at rsegs m (BW.CF + 255) [Z_to_bv 8 1].
Proof.
  intros RLO RHI ly S W m md HAR Hro.
  destruct (PWCC.ctl_rt_C_of_AR B TS LAWS RLO RHI ly S W m md HAR
              (PW.arodata_okP_of_S B RLO RHI RLO RHI _ Hro (Z.le_refl _) (Z.le_refl _)))
    as (Hc & Hcut & Himg & Hra).
  destruct (PWRC.RT_used_of_AR_C B TS LAWS ly S W m md HAR)
    as (_ & _ & _ & _ & Hcf & _ & _ & Hreal).
  destruct Hcf as (Hgcf & _ & _ & _ & _ & _ & H240 & _).
  pose proof (proj1 (Forall_forall _ _) Hreal) as HR.
  split; [exact Hra|]. split; [exact Hc|]. split; [exact Hcut|]. split; [exact Himg|].
  split.
  { exact (HR (0xa17f0, 0x97b0c)
             ltac:(unfold ART.RT_REALS; cbn [In]; repeat (first [left; reflexivity | right]))
             ltac:(unfold PW.REAL_USED; cbn [fst In]; left; reflexivity)). }
  split.
  { exact (HR (0xa17e8, 0x97bdc)
             ltac:(unfold ART.RT_REALS; cbn [In]; repeat (first [left; reflexivity | right]))
             ltac:(unfold PW.REAL_USED; cbn [fst In]; right; left; reflexivity)). }
  split; [exact Hgcf|].
  pose proof (rcpV_bytes_nth m _ _ 14 (Z_to_bv 8 1) H240 eq_refl) as H254.
  pose proof (rcpV_bytes_nth m _ _ 15 (Z_to_bv 8 1) H240 eq_refl) as H255.
  replace (BW.CF + 254) with (ART.RT_CF + 240 + Z.of_nat 14) by (unfold BW.CF, ART.RT_CF; lia).
  replace (BW.CF + 255) with (ART.RT_CF + 240 + Z.of_nat 15) by (unfold BW.CF, ART.RT_CF; lia).
  split; [exact H254 | exact H255].
Qed.

(* ---------------------------------------------------------------------------------------------------------
   5. The stretches' shadow region R (reac_ctrl_parse_c.reac_ctrl_parse_shadow_R) inside ctl_rt_C's regions, one
   disjunct per region (route (C) recipe section 2(c)): the real-stack frame's 16 shadow bytes -> (Z) (the stack entry
   of zero_shadow_ranges); the class-1 block shadow -> (FA); o's shadow words -> (F) of o's frame; f's shadow words
   -> (L) of f's block; .str.4's shadow word -> img_shadow. *)
Lemma rcpV_srR : forall ly S (W : RA0n.world rsegs) m md f n o Sp,
  RG0n.AR rsegs B ly S W m md ->
  SRO.shadow_rw_on (ARC.cut_shadow B ly S) m -> SRO.shadow_rw_on ARC.img_shadow m ->
  RG0f.ly_stk_lo ly <= (Sp - 128) / 32 * 32 - 128 -> Sp <= RG0f.ly_stk_hi ly ->
  (o <> 0 -> exists co po, In (co, po) (RG01.frames S) /\ RG0f.frame_addr ly co po <= o /\
     o + 36 <= RG0f.frame_addr ly co po + RG00.fs_frame_bytes co) ->
  (50 <= n -> exists Lf, In (f, Lf) (RG0d.ablocks B ly S) /\ 50 <= RG00.req_size Lf) ->
  SRO.shadow_rw_on (PC.reac_ctrl_parse_shadow_R f n o Sp (RG0f.ly_F ly)) m.
Proof.
  intros ly S W m md f n o Sp HAR Hcut Himg Hlo Hhi Ho Hf.
  apply (SRO.shadow_rw_on_mono (fun a => ARC.cut_shadow B ly S a \/ ARC.img_shadow a));
    [| exact (SRO.shadow_rw_on_union _ _ m Hcut Himg)].
  intros a Ha.
  assert (EshA : forall x, ART.shadow_addr x = RG0f.shadow_addr x)
    by (intros x; unfold ART.shadow_addr, ART.ASAN_K, RG0f.shadow_addr, RG0f.SHADOW_OFF; lia).
  unfold PC.reac_ctrl_parse_shadow_R in Ha.
  destruct Ha as [Ha|[Ha|[(Hne & Ha)|[(Hn50 & Ha)|(Hn50 & Ha)]]]].
  - (* the real-stack frame's 16 shadow bytes: (Z), the stack entry of zero_shadow_ranges *)
    left. right. right. left.
    exists (RG0f.ly_stk_lo ly, RG0f.ly_stk_hi ly - RG0f.ly_stk_lo ly).
    split; [left; reflexivity|]. cbn [fst snd].
    unfold RG0v.shadow_of_addr. rewrite !EshA in Ha. unfold RG0f.shadow_addr in Ha.
    set (A := (Sp - 128) / 32 * 32) in *.
    assert (HA : A mod 32 = 0 /\ Sp - 160 < A <= Sp - 128) by (unfold A; Z.div_mod_to_equations; lia).
    Z.div_mod_to_equations. lia.
  - (* the class-1 block shadow: (FA), the fake stack's frames-area shadow *)
    left. right. right. right.
    unfold SMO.asan_stack_malloc_shadow_R in Ha. rewrite !EshA in Ha.
    unfold SMC.fs_frame in Ha. cbn [Z.of_nat Pos.of_succ_nat] in Ha.
    unfold RG0f.shadow_addr, RG0f.kFakeFramesOff, RG0f.kFakeStackSize in *.
    change (2 ^ 20) with 1048576 in Ha. Z.div_mod_to_equations. lia.
  - (* o's shadow words: (F) of o's frame *)
    left. left. destruct (Ho Hne) as (co & po & Hin & Hl & Hh).
    destruct (rcpV_fgeo ly S W m md co po HAR Hin) as (_ & _ & _ & _ & Hfm & Hb64 & Hbm & _).
    exists co, po. split; [exact Hin|].
    unfold SWO.sh_word_on, RA.sh_al8_lo, RA.sh_al8_hi in Ha. destruct Ha as (_ & Ha).
    rewrite !EshA in Ha. unfold RG0f.shadow_addr, RG0f.SHADOW_OFF in *.
    set (fa := RG0f.frame_addr ly co po) in *.
    Z.div_mod_to_equations. lia.
  - (* f's shadow words: (L) of f's block *)
    left. right. left. destruct (Hf Hn50) as (Lf & Hin & HL).
    exists f, Lf. split; [exact Hin|].
    unfold SWO.sh_word_on, RA.sh_al8_lo, RA.sh_al8_hi in Ha. destruct Ha as (_ & Ha).
    rewrite !EshA in Ha. unfold RG0f.shadow_addr, RG0f.SHADOW_OFF in *.
    Z.div_mod_to_equations. lia.
  - (* .str.4's shadow word: img_shadow *)
    right. unfold SWO.sh_word_on, RA.sh_al8_lo, RA.sh_al8_hi in Ha. destruct Ha as (_ & Ha).
    rewrite !EshA in Ha. unfold RG0f.shadow_addr, RG0f.SHADOW_OFF, PC.REAC_CTRL_PARSE_BC in Ha.
    exists (8 * (a - 0x7fff8000)). unfold CR.IMG_LO, CR.IMG_HI, RG0f.shadow_addr, RG0f.SHADOW_OFF.
    split; [Z.div_mod_to_equations; lia|]. rewrite Z.mul_comm, Z.div_mul by lia. lia.
Qed.

End V.
