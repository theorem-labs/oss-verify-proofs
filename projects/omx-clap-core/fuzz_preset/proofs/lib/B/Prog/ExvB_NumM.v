(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Does not rest on tex_word_specX; memnorm only through EXB's exv_rm keep and the step's own memnorm keep (kit 4f18c75d4900). *)
(* Theorem Labs, 2026-10: fuzz_preset, image B (asan-ubsan, rebuilt pin f8f98a95bc52, unstripped twin 3b5e1a099b53),
   ex_value's NUMBER SEGMENT, sub-piece M: EXB (lib/B/Prog/ExvB_Stmt.v) across the segment's own writes. Proves
   lib/B/Prog/ExvB_NumCut.v's EXN_keepM, EXN_keepM_cur and EXN_keep_spill as exn_keepM, exn_keepM_cur and
   exn_keep_spill, from EXV_HYP alone. No machine walk: every byte EXB reads, other than the journal's, lies outside the
   write zone EXN_wz (and outside in->p / in->differs for the _cur form), so its view is kept:
   - the s1 window [s1 - STK_RT_STRTOD, s1 + 160) is on the real stack inside [sp - STK, sp): sp is 16-aligned, so
     s1 = (sp - 288) land -32 is sp - 288 or sp - 304, and STK = (n + 1) * 304 + the callees' need >= 304 +
     STK_RT_STRTOD (prh_img_B: pi_frame F_ex_value = 304);
   - the frame (1, pos) is 32-aligned application memory below alloc_ceiling, apart from every live block and every
     older frame (alx_sep: sep_block_frame_x / sep_frames_pos_x), and no image byte (frm_img_x); its two shadow bytes
     shadow_addr f + 4 / + 8 are the shadow of [f + 32, f + 40) / [f + 64, f + 72) and lie in the shadow range, which
     is not application memory;
   - the scratch, the text and every Lam block are inside live allocator blocks (application memory below the
     ceiling, no image byte: blk_img_x); errno and alloc.c's statics are image bytes below kLowMemEnd (api_env,
     S1ImgB.pst_in_img_B), apart from each other (by computation on prh_img_B and strtod_c);
   - the tree's footprint misses the scratch, the cursor, the stack window and errno (EXV_PRE); its root is at home at
     the entry (a Lam block, an OLDER frame, or the real stack above sp) and its blocks are Lam blocks
     (ExvB_Open_kt.exv_node_D), so it misses the frame's slots and the frame's shadow bytes;
   - a visible byte stays visible because presence grows (exm_vis), so every shadow hull is kept;
   - exv_rm: its room half reads only Sc, which the step keeps; its memnorm half `memnorm (e_mem E) -> memnorm memc`
     is chained with the step's own keep `memnorm memc -> memnorm memc'` (the premise EXN_keepM / EXN_keepM_cur take).
   The journal-free engine helpers (exw_val_kept, exw_garr8_kept, exw_ra_kept) are ExvB_Num_eng.v's (ex_ws_x.v's,
   restated: ex_ws_x waits for its rebind on the kit).
   Rule 24: proves no function (kind: segment lemma).
   Numerals, classified (no ADDRESS; every program address above is in a comment, read off the neutral listing):
   LENGTH - 288, 304 (ex_value's frame and its 32-alignment slack, B 0x8352c `addi sp, sp, -288` / 0x8356c
   `andi sp, sp, -32`), 160 (EXN_wz's s1 spill bound), 128, 120 (fs_frame_bytes 1 and the flag-pointer slot), 32, 40,
   64, 72 (the frame's end / num slots), 8, 36, 40 (the cursor cells, struct ex), 4 (errno), 56 (a tree node), 16
   (stack alignment), 4096 (a page), 2 ^ 47, 2 ^ 64 (address-space bounds), 0; WORD - 1 (the fake-frame class), 64
   (the word width of Z_to_bv), 5 (the register-index width of bvmap). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YK1b YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import FCiface YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YStrtodRowX YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExvB_Stmt ExvB_NumPure ExvB_NumCut.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require ExvB_Num_eng S1ImgB ExvB_Open_kt.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

#[local] Existing Instance prh_img_B.

Section p. Context {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Variable E : exv_e.
Variable pos : Z.
Hypothesis HYP : EXV_HYP B ARx SK.

(* ---- pure helpers ---- *)
Lemma exm_req_ge : forall n, n <= req_size n.
Proof. intros n. unfold req_size. destruct (Z.eqb_spec n 0); lia. Qed.

Lemma exm_strtod_nn : 0 <= STK_RT_STRTOD.
Proof. unfold STK_RT_STRTOD. assert (H : ESTACK = 4096) by reflexivity. lia. Qed.

Local Ltac exm_lia := pose proof asan_consts; pose proof exm_strtod_nn;
  unfold shadow_addr, SHADOW_OFF, app_addr, in_app, ASAN_CEIL, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd,
    kHighShadowEnd in *; lia.

(* a visible byte stays visible when presence grows (an image byte reads the segments either way) *)
Lemma exm_vis : forall segs H (m m' : word -> option byte) s,
  (forall a, apresent H m a -> apresent H m' a) -> aview segs H m s <> None -> aview segs H m' s <> None.
Proof.
intros segs H m m' s HP Hv. cbv [aview YP09.mbyte mrestrict] in Hv |- *.
destruct (H (Z_to_bv 64 s)) eqn:Hh; [exact Hv|].
destruct (m (Z_to_bv 64 s)) as [b|] eqn:Hm.
- destruct (HP s (conj Hh (ex_intro _ b Hm))) as [_ [b' Hb']]. rewrite Hb'. cbn. discriminate.
- destruct (m' (Z_to_bv 64 s)); [cbn; discriminate | exact Hv].
Qed.

Section a.
Variables (fxc : YK11.FPState) (lyc : alayout) (Sc : astate) (Hpc : list Z) (Wc : world rsegs)
  (regs : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (k : Z)
  (regs' : bvmap 5 word) (memc' : word -> option byte) (mdc' : Model) (k' : Z).
Hypothesis PRE : EXV_PRE B ARx E.
Hypothesis HB : EXB (fx := fxc) B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos.
Hypothesis HJ' : ajournal_x (SK := SK) rsegs B prh_pst ARx (exv_STK E + e_d E) (exv_sp E + e_d E) (exv_FP E)
  (e_ly E) (e_S E) (e_Hp E) (e_W E) (e_mem E) (e_md E) [(1, pos)] lyc Sc Hpc Wc memc' mdc' k'.
Hypothesis HK : forall z, 0 <= z < 2 ^ 64 -> ~ EXN_wz B E pos lyc z -> ~ (e_q E <= z < e_q E + 8) ->
  ~ (e_q E + 32 <= z < e_q E + 36) -> aview rsegs (w_H Wc) memc' z = aview rsegs (w_H Wc) memc z.
Hypothesis HG : forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) memc' a.
Hypothesis HMN : YAkMemnorm.memnorm rsegs memc -> YAkMemnorm.memnorm rsegs memc'.
Hypothesis HR : EXN_regs_kept regs regs'.

(* the bytes that may change *)
Definition Zc (z : Z) : Prop :=
  EXN_wz B E pos lyc z \/ (e_q E <= z < e_q E + 8) \/ (e_q E + 32 <= z < e_q E + 36).

Lemma exm_HK : forall z, 0 <= z < 2 ^ 64 -> ~ Zc z -> aview rsegs (w_H Wc) memc' z = aview rsegs (w_H Wc) memc z.
Proof.
intros z Hz Hn. apply HK; [exact Hz | intros H; apply Hn; left; exact H | intros H; apply Hn; right; left; exact H
  | intros H; apply Hn; right; right; exact H].
Qed.

Lemma exm_nz : forall z,
  ~ (exv_s1 E - STK_RT_STRTOD <= z < exv_s1 E + 160) ->
  ~ (frame_addr lyc 1 pos + 32 <= z < frame_addr lyc 1 pos + 40) ->
  ~ (frame_addr lyc 1 pos + 64 <= z < frame_addr lyc 1 pos + 72) ->
  z <> shadow_addr (frame_addr lyc 1 pos) + 4 -> z <> shadow_addr (frame_addr lyc 1 pos) + 8 ->
  ~ (e_scr E <= z < e_scr E + exv_len E + 1) -> ~ (as_errno B <= z < as_errno B + 4) ->
  ~ (e_q E <= z < e_q E + 8) -> ~ (e_q E + 32 <= z < e_q E + 36) -> ~ Zc z.
Proof. intros z H1 H2 H3 H4 H5 H6 H7 H8 H9 HZ. unfold Zc, EXN_wz in HZ. tauto. Qed.

(* the numbers every separation below uses *)
Lemma exm_geo :
  exv_sp E mod 16 = 0 /\ alloc_ceiling + exv_STK E <= exv_sp E /\ 304 + STK_RT_STRTOD <= exv_STK E /\
  exv_sp E - 304 <= exv_s1 E /\ exv_s1 E <= exv_sp E - 288 /\
  exv_sp E <= e_q E /\ e_q E + 40 <= exv_sp E + e_d E /\ exv_sp E + e_d E <= 2 ^ 47 /\
  frames Sc = [(1, pos)] ++ frames (e_S E) /\ In (1, pos) (frames Sc) /\
  frame_addr lyc 1 pos mod 32 = 0 /\ 4096 <= frame_addr lyc 1 pos /\ frame_addr lyc 1 pos + 128 <= alloc_ceiling /\
  in_app (frame_addr lyc 1 pos) 128 /\
  0 <= as_errno B /\ as_errno B + 4 <= kLowMemEnd /\ (forall a, as_errno B <= a < as_errno B + 4 -> in_img rsegs a) /\
  (forall c p0, frame_addr (e_ly E) c p0 = frame_addr lyc c p0) /\
  ly_stk_hi (e_ly E) <= 2 ^ 47 /\ ARx lyc Sc Hpc Wc memc mdc.
Proof.
pose proof PRE as HPRE. unfold EXV_PRE in HPRE. cbv zeta in HPRE.
destruct HPRE as (HFP & _ & _ & _ & _ & _ & _ & _ & Hspq & Hqd & Hwin & _).
destruct HFP as ((_ & _ & _ & _ & _ & Hastk & _) & _).
destruct Hastk as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & _ & Htop1 & Htop2).
destruct Hwin as (Hd0 & Hd16 & Hdtop & _).
pose proof HB as HB0. unfold EXB in HB0. cbv zeta in HB0. destruct HB0 as (HJ & _).
destruct HJ as (HAR & Hly & _ & _ & _ & Hfrs & _).
pose proof (eh_laws B ARx SK HYP) as LAWS.
assert (Hin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (alx_frames rsegs B ARx LAWS _ _ _ _ _ _ 1 pos HAR Hin) as (Hal32 & Happ & _).
destruct (frames_bounds_x rsegs B ARx LAWS _ _ _ _ _ _ 1 pos HAR Hin) as (F1 & F2 & _).
change (fs_frame_bytes 1) with 128 in Happ, F2.
destruct (eh_errno B ARx SK HYP) as ((E0 & E4) & Eimg & _).
destruct Hly as (_ & _ & _ & _ & _ & HF & _ & _ & _ & _ & Ehi & _).
assert (HSTK : 304 + STK_RT_STRTOD <= exv_STK E).
{ unfold exv_STK, STK_ex_value, zmaxl. cbn [fold_right pi_frame prh_img_B]. lia. }
pose proof (ExvB_Open_kt.exv_s1_le E) as (S1 & S1m).
unfold exv_sp in *.
split; [exact Hal|]. split; [lia|]. split; [exact HSTK|]. split; [lia|]. split; [lia|].
split; [exact Hspq|]. split; [exact Hqd|]. split; [lia|]. split; [exact Hfrs|]. split; [exact Hin|].
split; [exact Hal32|]. split; [exact F1|]. split; [exact F2|]. split; [exact Happ|].
split; [exact E0|]. split; [exact E4|]. split; [exact Eimg|].
split; [intros c p0; unfold frame_addr; rewrite HF; reflexivity|].
split; [lia | exact HAR].
Qed.

Local Ltac geo := pose proof exm_geo as (Gsp & Gst & GSTK & GS1a & GS1b & Gq0 & Gq40 & Gd47 & Gfrs & Gin & Gf32 & Gf0 &
  Gfc & Gfapp & Ge0 & Ge4 & Geimg & Gfa & Ghi & GAR).

Local Ltac exb := pose proof HB as HB0; unfold EXB in HB0; cbv zeta in HB0;
  destruct HB0 as (HJ & HWIN & HFR & HFZ & HHp & HAB & HRM & HLED & HCNT & R2 & R8 & R9 & R18 & R24 & R25 & R26 & R19
    & R3 & R4 & HSV & H176 & HFL & HSRC & HTB & HWD & HSB & HQR & HTREE).

(* the scratch's block *)
Lemma exm_scr : exists bs ms, In (bs, ms) (ablocks B lyc Sc) /\ bs <= e_scr E /\
  e_scr E + exv_len E + 1 <= bs + req_size ms /\ (In bs Hpc -> bs + cf_head <= e_scr E) /\
  (bs + req_size ms <= frame_addr lyc 1 pos \/ frame_addr lyc 1 pos + 128 <= bs) /\
  4096 <= bs /\ bs + req_size ms <= alloc_ceiling /\ in_app bs (req_size ms) /\
  (forall z, bs <= z < bs + req_size ms -> ~ in_img rsegs z).
Proof.
pose proof (eh_laws B ARx SK HYP) as LAWS. geo. exb.
destruct HSB as (bs & ms & Hin & Hb1 & Hb2 & Hhp).
destruct (alx_blocks rsegs B ARx LAWS _ _ _ _ _ _ _ _ GAR Hin) as (_ & B4 & Bc & Bapp & _).
pose proof (sep_block_frame_x rsegs B ARx LAWS _ _ _ _ _ _ bs ms 1 pos GAR Hin Gin) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 1) with 128 in Hd.
pose proof (exm_req_ge ms) as Hrq.
exists bs, ms. split; [exact Hin|]. split; [exact Hb1|]. split; [lia|]. split; [exact Hhp|]. split; [exact Hd|].
split; [exact B4|]. split; [exact Bc|]. split; [exact Bapp|].
intros z Hz. exact (blk_img_x rsegs B ARx LAWS _ _ _ _ _ _ bs ms z GAR Hin Hz).
Qed.

(* a byte of a live allocator block: apart from the own frame, application memory below the ceiling, no image byte *)
Lemma exm_blk0 : forall b m z, In (b, m) (ablocks B lyc Sc) -> b <= z < b + req_size m ->
  ~ (frame_addr lyc 1 pos <= z < frame_addr lyc 1 pos + 128) /\ 4096 <= z < alloc_ceiling /\ app_addr z /\
  ~ in_img rsegs z.
Proof.
intros b m z Hin Hz. pose proof (eh_laws B ARx SK HYP) as LAWS. geo.
destruct (alx_blocks rsegs B ARx LAWS _ _ _ _ _ _ _ _ GAR Hin) as (_ & B4 & Bc & Bapp & _).
pose proof (sep_block_frame_x rsegs B ARx LAWS _ _ _ _ _ _ b m 1 pos GAR Hin Gin) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 1) with 128 in Hd.
split; [lia|]. split; [lia|].
split; [exact (in_app_addr _ _ _ Bapp Hz) | exact (blk_img_x rsegs B ARx LAWS _ _ _ _ _ _ b m z GAR Hin Hz)].
Qed.

Lemma exm_blk : forall b m z, In (b, m) (ablocks B lyc Sc) -> b <= z < b + req_size m ->
  ~ (e_scr E <= z < e_scr E + exv_len E + 1) ->
  ~ Zc z /\ 4096 <= z < alloc_ceiling /\ app_addr z /\ ~ (frame_addr lyc 1 pos <= z < frame_addr lyc 1 pos + 128).
Proof.
intros b m z Hin Hz Hs. destruct (exm_blk0 b m z Hin Hz) as (Hf & Hr & Hap & Hni). geo.
assert (He : ~ (as_errno B <= z < as_errno B + 4)) by (intros He; exact (Hni (Geimg z He))).
split; [|split; [lia | split; [exact Hap | exact Hf]]].
apply exm_nz; try exact Hs; try exact He; exm_lia.
Qed.

(* a byte of an older fake frame (live at the entry) *)
Lemma exm_ofrm0 : forall c p0 z, In (c, p0) (frames (e_S E)) ->
  frame_addr lyc c p0 <= z < frame_addr lyc c p0 + fs_frame_bytes c ->
  ~ (frame_addr lyc 1 pos <= z < frame_addr lyc 1 pos + 128) /\ 4096 <= z < alloc_ceiling /\ app_addr z.
Proof.
intros c p0 z Hin Hz. pose proof (eh_laws B ARx SK HYP) as LAWS. geo.
assert (Hin' : In (c, p0) (frames Sc)) by (rewrite Gfrs; right; exact Hin).
destruct (frames_bounds_x rsegs B ARx LAWS _ _ _ _ _ _ c p0 GAR Hin') as (H0 & Hc & Happ).
apply in_split in Hin as (l2 & l3 & E2).
pose proof (sep_frames_pos_x rsegs B ARx LAWS _ _ _ _ _ _ (1, pos) (c, p0) [] l2 l3 GAR
  ltac:(rewrite Gfrs, E2; reflexivity)) as Hd.
unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 1) with 128 in Hd.
pose proof (fs_frame_bytes_nonneg c).
split; [lia|]. split; [lia|]. exact (in_app_addr _ _ _ Happ Hz).
Qed.

(* the own frame outside its two open slots *)
Lemma exm_frm : forall z, frame_addr lyc 1 pos <= z < frame_addr lyc 1 pos + 128 ->
  ~ (frame_addr lyc 1 pos + 32 <= z < frame_addr lyc 1 pos + 40) ->
  ~ (frame_addr lyc 1 pos + 64 <= z < frame_addr lyc 1 pos + 72) -> ~ Zc z.
Proof.
intros z Hz H1 H2. pose proof (eh_laws B ARx SK HYP) as LAWS. geo.
destruct exm_scr as (bs & ms & _ & Hs1 & Hs2 & _ & Hd & _ & _ & _ & _).
assert (Hni : ~ in_img rsegs z).
{ apply (frm_img_x rsegs B ARx LAWS _ _ _ _ _ _ 1 pos z GAR Gin). change (fs_frame_bytes 1) with 128. lia. }
assert (He : ~ (as_errno B <= z < as_errno B + 4)) by (intros He; exact (Hni (Geimg z He))).
pose proof (in_app_addr _ _ _ Gfapp Hz) as Hap.
apply exm_nz; try exact H1; try exact H2; try exact He; exm_lia.
Qed.

(* the real stack from s1 + 160 up, outside the two cursor cells *)
Lemma exm_stk : forall z, exv_s1 E + 160 <= z < 2 ^ 47 -> ~ (e_q E <= z < e_q E + 8) ->
  ~ (e_q E + 32 <= z < e_q E + 36) -> ~ Zc z.
Proof.
intros z Hz H1 H2. geo.
destruct exm_scr as (bs & ms & _ & Hs1 & Hs2 & _ & _ & _ & Hbc & _ & _).
apply exm_nz; try exact H1; try exact H2; exm_lia.
Qed.

(* the shadow byte of an address below 2 ^ 47 outside the frame's two open slots *)
Lemma exm_sh : forall y, 0 <= y < 2 ^ 47 -> ~ (frame_addr lyc 1 pos + 32 <= y < frame_addr lyc 1 pos + 40) ->
  ~ (frame_addr lyc 1 pos + 64 <= y < frame_addr lyc 1 pos + 72) ->
  ~ Zc (shadow_addr y) /\ 0 <= shadow_addr y < 2 ^ 64.
Proof.
intros y Hy H1 H2. geo.
destruct exm_scr as (bs & ms & _ & Hs1 & Hs2 & _ & _ & Hb4 & Hbc & Hbapp & _).
split; [|exm_lia]. apply exm_nz; exm_lia.
Qed.

(* alloc.c's statics *)
Lemma exm_pst : forall z, Exists (in_zr z) prh_pst -> ~ Zc z /\ 0 <= z < 2 ^ 64.
Proof.
intros z Hz. pose proof (S1ImgB.pst_in_img_B z Hz) as Hi. pose proof (eh_laws B ARx SK HYP) as LAWS. geo.
pose proof (eh_errno_B B ARx SK HYP) as HEB.
assert (Hr : 0 <= z < kLowMemEnd /\ ~ (as_errno B <= z < as_errno B + 4)).
{ rewrite HEB. unfold prh_pst in Hz.
  cbn [pi_g_live pi_gz_live pi_g_peak pi_gz_peak pi_g_count pi_gz_count pi_g_fail pi_gz_fail pi_g_ran_out
    pi_gz_ran_out pi_g_most pi_gz_most pi_g_own_ran_out pi_gz_own_ran_out prh_img_B] in Hz.
  try change (Z.of_nat 8) with 8 in Hz. try change (Z.of_nat 1) with 1 in Hz. unfold YF0m.TFIB_ERRNO, kLowMemEnd.
  repeat (apply Exists_cons in Hz; destruct Hz as [Hz|Hz]; [unfold in_zr in Hz; cbn [fst snd] in Hz; lia|]).
  apply Exists_nil in Hz. destruct Hz. }
destruct exm_scr as (bs & ms & _ & Hs1 & Hs2 & _ & _ & _ & _ & _ & Hsimg).
assert (Hnf : ~ (frame_addr lyc 1 pos <= z < frame_addr lyc 1 pos + 128)).
{ intros Hf. apply (frm_img_x rsegs B ARx LAWS _ _ _ _ _ _ 1 pos z GAR Gin); [|exact Hi].
  change (fs_frame_bytes 1) with 128. lia. }
assert (Hns : ~ (e_scr E <= z < e_scr E + exv_len E + 1)).
{ intros Hs. apply (Hsimg z); [lia | exact Hi]. }
destruct Hr as (Hrz & He).
split; [|exm_lia]. apply exm_nz; try exact Hns; try exact He; exm_lia.
Qed.

(* a harness block's hidden head *)
Lemma exm_head : forall a kk z, In (a - cf_head, kk + cf_head) (ablocks B lyc Sc) -> In (a - cf_head) Hpc ->
  0 <= kk -> a - cf_head <= z < a - cf_head + 8 -> ~ Zc z /\ 0 <= z < 2 ^ 64.
Proof.
intros a kk z Hin Hhp Hk Hz. pose proof (eh_head B ARx SK HYP) as CH. pose proof (eh_laws B ARx SK HYP) as LAWS. geo.
pose proof (exm_req_ge (kk + cf_head)) as Hrq.
destruct exm_scr as (bs & ms & Hbs & Hs1 & Hs2 & HsHp & _ & _ & _ & _ & _).
assert (Hns : ~ (e_scr E <= z < e_scr E + exv_len E + 1)).
{ destruct (Z.eq_dec bs (a - cf_head)) as [Eb|Nb].
  - subst bs. specialize (HsHp Hhp). lia.
  - pose proof (sep_blocks_x rsegs B ARx LAWS _ _ _ _ _ _ bs ms (a - cf_head) (kk + cf_head) GAR Hbs Hin
      ltac:(congruence)) as Hd.
    unfold zdisjoint in Hd; cbn [fst snd] in Hd. lia. }
destruct (exm_blk (a - cf_head) (kk + cf_head) z Hin ltac:(lia) Hns) as (Hn & Hr & _).
pose proof asan_consts. split; [exact Hn | lia].
Qed.

(* a byte of a Lam block (a harness block's user range) *)
Lemma exm_lam : forall b kk z, In (b, kk) (e_Lam E) -> b <= z < b + kk ->
  ~ (frame_addr lyc 1 pos <= z < frame_addr lyc 1 pos + 128) /\ 4096 <= z < alloc_ceiling /\ app_addr z /\
  ~ in_img rsegs z.
Proof.
intros b kk z Hin Hz. exb. destruct HLED as (_ & _ & HBk & _). rewrite Forall_forall in HBk.
destruct (HBk (b, kk) Hin) as (K0 & Kin & _ & _ & _). cbn [fst snd] in K0, Kin.
pose proof (@cf_head_nonneg cp) as CH0. pose proof (exm_req_ge (kk + cf_head)) as Hrq.
apply (exm_blk0 (b - cf_head) (kk + cf_head) z Kin). lia.
Qed.

(* the text *)
Lemma exm_txt : forall x, e_x0 E <= x < e_x0 E + Z.of_nat (length (e_x E)) ->
  ~ Zc x /\ 0 <= x < 2 ^ 47 /\ ~ (frame_addr lyc 1 pos <= x < frame_addr lyc 1 pos + 128).
Proof.
intros x Hx. change (Z.of_nat (length (e_x E))) with (exv_len E) in Hx. exb.
pose proof PRE as HPRE. unfold EXV_PRE in HPRE. cbv zeta in HPRE.
destruct HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Psx & _).
destruct (HTB ltac:(lia)) as (b & m & Hin & Hb1 & Hb2 & _).
pose proof (exm_req_ge m).
destruct (exm_blk b m x Hin ltac:(lia) ltac:(lia)) as (Hn & Hr & _ & Hf).
pose proof asan_consts. split; [exact Hn|]. split; [lia | exact Hf].
Qed.

(* the tree's root, at home at the entry *)
Lemma exm_root : prhex_home (e_ly E) (e_S E) (e_Lam E) (e_regs E) (e_v E) 56 ->
  forall x, e_v E <= x < e_v E + 56 ->
  ~ (frame_addr lyc 1 pos <= x < frame_addr lyc 1 pos + 128) /\ 0 <= x < 2 ^ 47 /\ (app_addr x \/ exv_sp E <= x).
Proof.
intros Hh x Hx. geo. pose proof asan_consts. pose proof exm_strtod_nn.
destruct Hh as [(b & kk & Hin & H1 & H2) | [(c & p0 & Hin & H1 & H2) | (H1 & H2)]].
- destruct (exm_lam b kk x Hin ltac:(lia)) as (Hf & Hr & Hap & _). split; [exact Hf|]. split; [lia | left; exact Hap].
- rewrite !Gfa in H1, H2. destruct (exm_ofrm0 c p0 x Hin ltac:(lia)) as (Hf & Hr & Hap).
  split; [exact Hf|]. split; [lia | left; exact Hap].
- change (spZ (e_regs E)) with (exv_sp E) in H1. split; [lia|]. split; [lia | right; lia].
Qed.

(* a footprint byte of the tree *)
Lemma exm_footz : forall x, ~ (frame_addr lyc 1 pos <= x < frame_addr lyc 1 pos + 128) -> 0 <= x < 2 ^ 47 ->
  (app_addr x \/ exv_sp E <= x) -> ~ (e_scr E <= x < e_scr E + exv_len E + 1) -> ~ (e_q E <= x < e_q E + 40) ->
  ~ (exv_sp E - exv_STK E <= x < exv_sp E) -> ~ (as_errno B <= x < as_errno B + 4) -> ~ Zc x.
Proof.
intros x Hf Hr Ha Hs Hq Hst He. geo.
apply exm_nz; try exact Hs; try exact He; exm_lia.
Qed.

(* the shadow facts *)
Lemma exm_ra : forall y n,
  (forall x, y <= x < y + n -> 0 <= x < 2 ^ 47 /\ ~ (frame_addr lyc 1 pos + 32 <= x < frame_addr lyc 1 pos + 40) /\
     ~ (frame_addr lyc 1 pos + 64 <= x < frame_addr lyc 1 pos + 72)) ->
  range_addressable (aview rsegs (w_H Wc) memc) SHADOW_OFF y n ->
  range_addressable (aview rsegs (w_H Wc) memc') SHADOW_OFF y n.
Proof.
intros y n Hx. apply (ExvB_Num_eng.exw_ra_kept rsegs (w_H Wc) memc memc' y n). intros x Hr.
destruct (Hx x Hr) as (H0 & H1 & H2). destruct (exm_sh x H0 H1 H2) as [Hn Hb].
change (shadow_of_addr SHADOW_OFF x) with (shadow_addr x). exact (exm_HK _ Hb Hn).
Qed.

Lemma exm_hull : forall x n, shadow_hull_vis (aview rsegs (w_H Wc) memc) x n ->
  shadow_hull_vis (aview rsegs (w_H Wc) memc') x n.
Proof. intros x n H s Hs. exact (exm_vis rsegs (w_H Wc) memc memc' s HG (H s Hs)). Qed.

(* the ledger reads the statics and the hidden heads *)
Lemma exm_ledger :
  prh_ledger (PI := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B lyc Sc Hpc Wc memc
    (e_Lam E) (e_peak E) (e_cnt E) (e_fail E) (e_ran E) (e_most E) (e_own E) ->
  prh_ledger (PI := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B lyc Sc Hpc Wc memc'
    (e_Lam E) (e_peak E) (e_cnt E) (e_fail E) (e_ran E) (e_most E) (e_own E).
Proof.
intros (HG0 & HND & HBk & HP).
assert (VK : forall a n v, (forall x, a <= x < a + Z.of_nat n -> ~ Zc x /\ 0 <= x < 2 ^ 64) ->
  val_mem rsegs (mrestrict (w_H Wc) memc) a n v -> val_mem rsegs (mrestrict (w_H Wc) memc') a n v).
{ intros a n v Hx. apply (ExvB_Num_eng.exw_val_kept rsegs (w_H Wc) memc memc' a n v). intros x Hxr.
  destruct (Hx x Hxr) as [Hn Hb]. exact (exm_HK x Hb Hn). }
split; [|split; [exact HND|split; [|exact HP]]].
- destruct HG0 as (G1 & G2 & G3 & G4 & G5 & (GM & GMr) & (GO & GOr) & GR).
  refine (conj (VK _ _ _ _ G1) (conj (VK _ _ _ _ G2) (conj (VK _ _ _ _ G3) (conj (VK _ _ _ _ G4)
    (conj (VK _ _ _ _ G5) (conj (conj (VK _ _ _ _ GM) GMr) (conj (conj (VK _ _ _ _ GO) GOr) GR))))))); intros x Hx; apply exm_pst; unfold prh_pst.
  + apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. exact Hx.
  + apply Exists_cons_tl, Exists_cons_hd. unfold in_zr. cbn [fst snd]. exact Hx.
  + apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd. unfold in_zr. cbn [fst snd]. exact Hx.
  + apply Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_hd. unfold in_zr. cbn [fst snd]. exact Hx.
  + apply Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_hd. unfold in_zr.
    cbn [fst snd]. exact Hx.
  + do 5 apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. exact Hx.
  + do 6 apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. exact Hx.
- revert HBk. apply Forall_impl. intros [a kk] (K0 & Kin & Khp & Kal & Kv). cbn [fst snd] in *.
  refine (conj K0 (conj Kin (conj Khp (conj Kal _)))).
  apply (VK (a - cf_head) 8%nat kk); [|exact Kv].
  intros x Hx. change (Z.of_nat 8) with 8 in Hx. exact (exm_head a kk x Kin Khp K0 Hx).
Qed.

(* EXB at the new state *)
Lemma exm_main : EXB (fx := fxc) B ARx SK E lyc Sc Hpc Wc regs' memc' mdc' k' pos.
Proof.
pose proof asan_consts as AC. pose proof exm_strtod_nn as SNN.
pose proof HR as (K2 & K8 & K9 & K18 & K24 & K25 & K26 & K19 & K3 & K4).
pose proof PRE as HPRE. unfold EXV_PRE in HPRE. cbv zeta in HPRE.
destruct HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Pv0 & _).
exb. geo.
assert (SP' : spZ regs' = spZ regs) by (unfold spZ; rewrite K2; reflexivity).
assert (MG : mem_grows (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) memc')).
{ intros x Hx. unfold mrestrict in *. destruct (w_H Wc x) eqn:Hh; [exact Hx|].
  destruct (memc x) as [b|] eqn:Hm; [|exfalso; exact (Hx eq_refl)].
  destruct (HG (bv_unsigned x)) as [_ [b' Hb']].
  { split; rewrite Z_to_bv_bv_unsigned; [exact Hh | exists b; exact Hm]. }
  rewrite Z_to_bv_bv_unsigned in Hb'. rewrite Hb'. discriminate. }
unfold EXB. cbv zeta.
split; [exact HJ'|].
split.
{ intros a Ha Hf.
  assert (Hq1 : ~ (e_q E <= a < e_q E + 8)).
  { intros Hq. apply Hf. exists (e_q E, e_q E + 8).
    split; [unfold exv_FP; right; left; reflexivity | cbn [fst snd]; lia]. }
  assert (Hq2 : ~ (e_q E + 32 <= a < e_q E + 36)).
  { intros Hq. apply Hf. exists (e_q E + 32, e_q E + 36).
    split; [unfold exv_FP; right; right; right; left; reflexivity | cbn [fst snd]; lia]. }
  rewrite (exm_HK a ltac:(lia) (exm_stk a ltac:(lia) Hq1 Hq2)). exact (HWIN a Ha Hf). }
split; [exact HFR|]. split; [exact HFZ|]. split; [exact HHp|]. split; [exact HAB|].
split; [destruct HRM as [HRo HRn]; split; [exact HRo | intros Hm0; exact (HMN (HRn Hm0))]|].
split; [exact (exm_ledger HLED)|].
split; [exact HCNT|].
split; [rewrite K2; exact R2|]. split; [rewrite K8; exact R8|]. split; [rewrite K9; exact R9|].
split; [rewrite K18; exact R18|]. split; [rewrite K24; exact R24|]. split; [rewrite K25; exact R25|].
split; [rewrite K26; exact R26|]. split; [rewrite K19; exact R19|]. split; [rewrite K3; exact R3|].
split; [rewrite K4; exact R4|].
split.
{ intros o r Hin. pose proof (ExvB_Open_kt.exv_saved_rng o r Hin) as Ho.
  apply (ExvB_Num_eng.exw_val_kept rsegs (w_H Wc) memc memc'); [|exact (HSV o r Hin)].
  intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply exm_HK; [lia|]. apply exm_stk; lia. }
split.
{ apply (ExvB_Num_eng.exw_val_kept rsegs (w_H Wc) memc memc'); [|exact H176].
  intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply exm_HK; [lia|]. apply exm_stk; lia. }
split.
{ rewrite (rdword_ext (aview rsegs (w_H Wc) memc) (aview rsegs (w_H Wc) memc') (frame_addr lyc 1 pos + 120));
    [exact HFL|].
  intros kk Hk. apply exm_HK; [lia|]. apply exm_frm; lia. }
split.
{ destruct HSRC as (Hby & H4096 & Hce & Ham & Hra & Hhull).
  split; [|split; [exact H4096|split; [exact Hce|split; [exact Ham|split]]]].
  - apply (ExvB_Num_eng.exw_garr8_kept rsegs (w_H Wc) memc memc'); [|exact Hby]. intros a Ha.
    destruct (exm_txt a Ha) as (Hn & Hr & _). apply exm_HK; [lia | exact Hn].
  - apply exm_ra; [|exact Hra]. intros x Hx. destruct (exm_txt x Hx) as (_ & Hr & Hf). lia.
  - intros Hn. apply exm_hull. exact (Hhull Hn). }
split; [exact HTB|].
split.
{ destruct HWD as (W1 & W2 & W3 & W4 & W5 & W6).
  split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. split.
  - intros a Ha. destruct (W4 a Ha) as (Wa & Wb & _).
    split; [eapply writable_at_grows; [exact MG | exact Wa]|]. split; [exact Wb|]. lia.
  - split.
    + apply exm_ra; [|exact W5]. intros x Hx.
      destruct exm_scr as (bs & ms & _ & Hs1 & Hs2 & _ & Hd & Hb4 & Hbc & _ & _). lia.
    + intros Hn. apply exm_hull. exact (W6 Hn). }
split; [exact HSB|].
split; [apply exm_ra; [|exact HQR]; intros x Hx; lia|].
destruct Pv0 as [Pv0 | ((_ & Phome & _) & _ & HDJ)]; [left; exact Pv0|].
destruct HTREE as [Hv | (Hnd & Hhome & Hra & Hhull)]; [left; exact Hv|]. right.
change (spZ (e_regs E)) with (exv_sp E) in HDJ.
pose proof (exm_root Phome) as ROOT.
assert (FT : forall x, PRH_Reader.pj_footR (e_v E) (e_D E) x ->
  ~ (frame_addr lyc 1 pos <= x < frame_addr lyc 1 pos + 128) /\ 0 <= x < 2 ^ 47 /\ (app_addr x \/ exv_sp E <= x)).
{ intros x [Hx | (b & Hb & Hx)]; [exact (ROOT x Hx)|].
  pose proof (ExvB_Open_kt.exv_node_D (e_t E) _ _ (e_v E) (e_D E) Hnd b Hb) as Hl.
  destruct b as [b kk]. unfold prh_lin in Hl. cbn [fst snd] in Hl.
  unfold PRH_Reader.pj_holdsR in Hx. cbn [fst snd] in Hx.
  destruct (exm_lam b kk x Hl Hx) as (Hf & Hr & Hap & _). split; [exact Hf|]. split; [lia | left; exact Hap]. }
split.
{ apply (PRH_Reader.pj_nodeR_frame rsegs (e_t E) (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) memc')
    (prh_lin (e_Lam E)) (e_v E) (e_D E) Hnd).
  intros x Hx. destruct (FT x Hx) as (Hf & Hr & Ha). destruct (HDJ x Hx) as (Hs & Hq & Hst & He). split.
  - apply (mbyte_of_aview rsegs). apply exm_HK; [lia|]. exact (exm_footz x Hf Hr Ha Hs Hq Hst He).
  - intros Hw. eapply writable_at_grows; [exact MG | exact Hw]. }
split; [unfold prhex_home in *; rewrite SP'; exact Hhome|].
split; [apply exm_ra; [|exact Hra]; intros x Hx; destruct (ROOT x Hx) as (Hf & Hr & _); lia|].
apply exm_hull. exact Hhull.
Qed.
End a.

(* ---- the three statements ---- *)
Lemma exn_keepM_cur : EXN_keepM_cur B ARx SK E pos.
Proof.
unfold EXN_keepM_cur. intros fxc lyc Sc Hpc Wc regs memc mdc k regs' memc' mdc' k' HPRE HB HJ' HK HG HMN HR.
eapply exm_main; eassumption.
Qed.

Lemma exn_keepM : EXN_keepM B ARx SK E pos.
Proof.
unfold EXN_keepM. intros fxc lyc Sc Hpc Wc regs memc mdc k regs' memc' mdc' k' HPRE HB HJ' HK HG HMN HR.
pose proof exn_keepM_cur as KC. unfold EXN_keepM_cur in KC.
apply (KC fxc lyc Sc Hpc Wc regs memc mdc k regs' memc' mdc' k' HPRE HB HJ'); [|exact HG | exact HMN | exact HR].
intros z Hz Hw _ _. exact (HK z Hz Hw).
Qed.

Lemma exn_keep_spill : EXN_keep_spill E.
Proof.
unfold EXN_keep_spill. intros Wc memc memc' o v Hs HE. unfold exv_spill in *.
apply (ExvB_Num_eng.exw_val_kept rsegs (w_H Wc) memc memc' (exv_s1 E + o) 8%nat v); [|exact Hs].
intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply HE. lia.
Qed.
End p.

Print Assumptions exn_keepM.
Print Assumptions exn_keepM_cur.
Print Assumptions exn_keep_spill.
