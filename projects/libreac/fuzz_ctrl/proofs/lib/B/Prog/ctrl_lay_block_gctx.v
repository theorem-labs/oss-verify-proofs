(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/reac_box_model_block_glue.v, with its module paths and module names changed; 694 of its 807 lines of code are new or changed and 2299 lines of the source are left out. *)
(* ctrl_lay_block (0x86104) on fuzz_ctrl's ASan+UBSan build, image B (libreac v1.9.0): the SHARED world-side lemmas of
   regions R2 / R3 of the cgif glue pb_ctrl_lay_block (a Theorem Labs lane, hand a Theorem Labs lane; consumers a Theorem Labs lane).
   rule 24: no function proved here.

   PLAN OF RECORD: ctrl_lay_block-B-glue-plan.md sections 3, 4 (a working note, not in this delivery).
   Statements asked by a Theorem Labs lane (gctx-statements.v (not in this delivery)) over the definitions of
   ctrl_lay_block_gD3.v (lay_LWF, lay_pure, lay_data, lay_ctx):
   - lay_cut_ctx: every Section CUTS fact (ctrl_lay_block_cutsF.v) at B.MemNorm.normalize of a cut memory, from the
     cut's journal / AR, the read-only view, the output block's home and write right (awr_byte), and the stretch's
     read facts;
   - lay_journal_lwf: the journal across a lifted stretch whose writes are lay_LWF (B.ProgWorld.ajournal_of_fsteps);
   - lay_kept_lwf / lay_kept_E: acall_kept across the stretch's writes (from the cut's AR), and antitone in E;
   - lay_cut_facts / lay_frame1_fresh: what a cut's journal gives lay_kept_lwf (the output block off the image, the
     window above the allocation ceiling, the class-1 frame fresh);
   - lay_F_above / lay_F_vis / lay_Fsh_vis: the side stack and its frames' shadow at any AR state;
   - lay_fp0_facts / lay_tls0_facts: FP0 / TLS0 of Section CUTS at the normalized memory of a cut (the B twins of
     a Theorem Labs lane's A glue LayBase.lay_fp0_facts :299 / lay_tls0_facts :375, for B's per-byte home of the output block);
   - lay_blk_not_img: the output block is apart from the image, from the caller's own journal (YCbq.awr_byte_cases);
   - route (C), lay_RR_cover: a Theorem Labs lane's ctrl_lay_block_shadow_R (the _on run's SR0 region) at a cut lies in the cut's
     own shadow regions of a Theorem Labs lane (B.ACtlRtC.cut_shadow: the window by the machine stack's zero-shadow
     range Z, the class-0 / class-1 blocks by the side stack's frames area, the output block by its home's frame F or
     live block L) and the image hull (B.ACtlRtC.img_shadow I: the read-only ranges by lay_img_ro, the JOIN blocks by
     their addresses); lay_cut_ctx takes SR0 from it (no AR_states_vis0_shadow).

   CLOSURE: as ctrl_lay_block_gbase.v (the _F files Required QUALIFIED; lib.Reusable twins and B.<module> names in
   full; lib.Reusable.YM05.alloc_ceiling written explicitly). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YK1b YI04 YI16 YM05 YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YK0h YK0i YK14 YK1a YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YN3v YI09 YI08 YI00 YI0f.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YE01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YB1v YK04R YA0nR YF0m YG0s.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Img0 B.AsanRT B.ProgBridge B.ProgWorld B.MemNorm B.MemNormF
  B.MemNormTr B.ShadowRwOn B.ACtlRtC.
(* the proved B ProgWorld statements, by their lemmas (a Theorem Labs lane) *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ProgWorldShadow B.ProgWorld_Fs B.ProgWorldTlsApart
  B.ProgWorldTlsOwned B.ProgWorldVisWin B.ProgWorldBlkApart.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require PropExec ExecF MState Mem Frame Step Cells RngBytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require ImgBounds CtrlBase CtrlRo asan_stack_malloc_c RcAsanFP
  rng_asan sh_word_on asan_stack_malloc_c_on ctrl_lay_block_c ctrl_lay_blockF_on C_ctrl_lay_block.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import ctrl_lay_block_gbase ctrl_lay_block_gD3.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcLay.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Local Notation rget := lib.Reusable.YK11.getr.
#[local] Notation SEGS := lib.Reusable.YB1v.tfibsegs.

(* ================================================================================================================
   1. Pure helpers.
   ================================================================================================================ *)
(* ly_dj from pointwise apartness, for two non-empty ranges. *)
Lemma lay_dj_of_pt : forall x1 x2 y1 y2, x1 < x2 -> y1 < y2 ->
  (forall a, x1 <= a < x2 -> a < y1 \/ y2 <= a) -> RcLay.ly_dj x1 x2 y1 y2.
Proof.
  intros x1 x2 y1 y2 Hx Hy H. unfold RcLay.ly_dj.
  destruct (Z_le_gt_dec x2 y1) as [E|E]; [left; exact E|].
  destruct (Z_le_gt_dec y2 x1) as [E'|E']; [right; exact E'|].
  exfalso. destruct (H (Z.max x1 y1) ltac:(lia)) as [D|D]; lia.
Qed.

(* Off the image, no byte is read-only. *)
Lemma lay_ro_false : forall a, 0 <= a < 2 ^ 64 -> ~ in_img SEGS a ->
  lib.Lib.Mem.ro_addr B.Img0.rsegs (lib.Lib.Mem.wa a) = false.
Proof.
  intros a Ha Hni. unfold lib.Lib.Mem.ro_addr. rewrite (lib.Lib.Mem.wa_unsigned a Ha).
  change B.Img0.rsegs with SEGS. rewrite (find_segment_none SEGS a Hni). reflexivity.
Qed.

(* A byte the view reads is visible. *)
Lemma lay_vis_of_view : forall {fx : lib.Reusable.YK11.FPState} (W : world SEGS) m a,
  aview SEGS (w_H W) m a <> None -> w_H W (Z_to_bv 64 a) = false.
Proof.
  intros fx W m a H. destruct (aview SEGS (w_H W) m a) as [v|] eqn:E; [|exfalso; exact (H eq_refl)].
  exact (proj1 (LayLib.view_mrd W m a v E)).
Qed.

(* The class geometry at cid 1 (B.ProgWorld.ctl_fs_geom). *)
Lemma lay_geom1 : forall FS pos,
  B.Prog.asan_stack_malloc_c.fs_frame FS 1 pos = FS + fs_frame_off 1 pos /\
  B.Prog.asan_stack_malloc_c.fs_B 1 = fs_frame_bytes 1 /\ fs_frame_bytes 1 = 128 /\
  fs_frame_off 1 pos = 36864 + 1048576 + pos * 128 /\
  (forall a, B.AsanRT.shadow_addr a = lib.Reusable.YG0f.shadow_addr a).
Proof.
  intros FS pos. destruct (B.ProgWorld.ctl_fs_geom FS 1 pos ltac:(lia)) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
  change (Z.to_nat 1) with 1%nat in *.
  assert (E128 : fs_frame_bytes 1 = 128) by reflexivity.
  split; [exact G3|]. split; [exact G2|]. split; [exact E128|]. split; [|exact G7].
  unfold fs_frame_off, kFakeFramesOff. rewrite E128. reflexivity.
Qed.

(* ---- route (C): the 8-aligned shadow-word cover (sh_word_on, the form of ctrl_lay_block_shadow_R's ranges) against
   the cut's shadow regions of B.ACtlRtC.  ASAN_K = SHADOW_OFF = 0x7fff8000 = 8 * 268431360. ---- *)
(* (I) a range 64 bytes inside the image hull: its cover is image shadow *)
Lemma lay_shw_img : forall q n a, lay_img_in q n -> B.Prog.sh_word_on.sh_word_on q n a -> B.ACtlRtC.img_shadow a.
Proof.
  intros q n a (H1 & H2) (_ & Ha1 & Ha2).
  unfold B.Prog.rng_asan.sh_al8_lo, B.Prog.rng_asan.sh_al8_hi, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in Ha1, Ha2.
  unfold B.Prog.CtrlRo.IMG_LO, B.Prog.CtrlRo.IMG_HI in H1, H2.
  unfold B.ACtlRtC.img_shadow. exists (8 * (a - SHADOW_OFF)).
  unfold B.Prog.CtrlRo.IMG_LO, B.Prog.CtrlRo.IMG_HI, lib.Reusable.YG0f.shadow_addr.
  rewrite (Z.mul_comm 8 (a - SHADOW_OFF)), Z.div_mul by lia. unfold SHADOW_OFF.
  split; [Z.div_mod_to_equations; lia | lia].
Qed.

(* (Z) the cover of a window inside the page-aligned machine stack [lo, hi) lies in the stack's zero-shadow range *)
Lemma lay_shw_stack : forall lo hi S0 K a, lo mod 4096 = 0 -> hi mod 4096 = 0 -> lo <= S0 - K -> S0 <= hi ->
  0 < K -> B.Prog.sh_word_on.sh_word_on (S0 - K) K a ->
  lib.Reusable.YG0v.shadow_of_addr SHADOW_OFF lo <= a <
  lib.Reusable.YG0v.shadow_of_addr SHADOW_OFF lo + (hi - lo) / 8.
Proof.
  intros lo hi S0 K a Hlo Hhi H1 H2 HK (_ & Ha1 & Ha2).
  unfold B.Prog.rng_asan.sh_al8_lo, B.Prog.rng_asan.sh_al8_hi, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in Ha1, Ha2.
  replace (S0 - K + K - 1) with (S0 - 1) in Ha2 by lia.
  unfold lib.Reusable.YG0v.shadow_of_addr, SHADOW_OFF.
  Z.div_mod_to_equations. lia.
Qed.

(* (A) the class-0 / class-1 block shadow (asan_stack_malloc_shadow_R) lies in the frames-area shadow *)
Lemma lay_shw_fs : forall F (c : nat) a, (c = 0 \/ c = 1)%nat ->
  B.Prog.asan_stack_malloc_c_on.asan_stack_malloc_shadow_R F c a ->
  lib.Reusable.YG0f.shadow_addr (F + kFakeFramesOff) <= a < lib.Reusable.YG0f.shadow_addr (F + kFakeStackSize).
Proof.
  intros F c a Hc (H1 & H2).
  unfold B.Prog.asan_stack_malloc_c.fs_frame, B.Prog.asan_stack_malloc_c.fs_B, B.AsanRT.shadow_addr,
    B.AsanRT.ASAN_K in H1, H2.
  unfold lib.Reusable.YG0f.shadow_addr, SHADOW_OFF, kFakeFramesOff, kFakeStackSize.
  destruct Hc as [-> | ->]; cbn [Z.of_nat] in H1, H2; Z.div_mod_to_equations; lia.
Qed.

(* a word of the cover of [q, q + n) is the shadow word of a byte x of the range *)
Lemma lay_shw_byte : forall q n a, 0 <= q -> 0 < n -> B.Prog.sh_word_on.sh_word_on q n a ->
  exists x, q <= x < q + n /\ a / 8 = B.AsanRT.shadow_addr x / 8.
Proof.
  intros q n a Hq Hn (_ & Ha1 & Ha2).
  unfold B.Prog.rng_asan.sh_al8_lo, B.Prog.rng_asan.sh_al8_hi in Ha1, Ha2.
  unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in *.
  destruct (Z_le_gt_dec (64 * (a / 8 - 268431360)) q) as [Hle | Hgt].
  - exists q. split; [lia|]. Z.div_mod_to_equations. lia.
  - exists (64 * (a / 8 - 268431360)). split; Z.div_mod_to_equations; lia.
Qed.

(* (L) that byte's word lies in the shadow-word cover of a live block holding the byte *)
Lemma lay_shw_blk : forall b rs x a, b <= x <= b + rs - 1 -> a / 8 = B.AsanRT.shadow_addr x / 8 ->
  lib.Reusable.YG0f.shadow_addr b / 8 * 8 <= a < lib.Reusable.YG0f.shadow_addr (b + rs - 1) / 8 * 8 + 8.
Proof.
  intros b rs x a Hx Ha.
  unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, lib.Reusable.YG0f.shadow_addr, SHADOW_OFF in *.
  Z.div_mod_to_equations. lia.
Qed.

(* (F) and in the shadow of a 64-aligned frame (of a size divisible by 64) holding the byte *)
Lemma lay_shw_al64 : forall FA N x a, FA mod 64 = 0 -> N mod 64 = 0 -> FA <= x < FA + N ->
  a / 8 = B.AsanRT.shadow_addr x / 8 ->
  lib.Reusable.YG0f.shadow_addr FA <= a < lib.Reusable.YG0f.shadow_addr FA + N / 8.
Proof.
  intros FA N x a H1 H2 Hx Ha.
  unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, lib.Reusable.YG0f.shadow_addr, SHADOW_OFF in *.
  Z.div_mod_to_equations. lia.
Qed.

(* ================================================================================================================
   2. The Section: B's bundle; the B ProgWorld statements it reads are PROVED (a Theorem Labs lane) and cited by their lemmas.
   ================================================================================================================ *)
Section GC.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Context {SK : lib.Reusable.YI16.sink_head}.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HWX : lib.Reusable.YK04.wx_segs_nowrap SEGS.
Hypothesis CTS : lib.Reusable.YF0m.CtrlTSyms B.
Let ctl_stack_shadow_of_AR : B.ProgWorld.ctl_stack_shadow_of_AR_stmt B := B.ProgWorldShadow.ctl_stack_shadow_of_AR B.
Let ctl_fp_of_AR : B.ProgWorld.ctl_fp_of_AR_stmt B := B.ProgWorld_Fs.ctl_fp_of_AR B.
Let fp_tls_apart : B.ProgWorld.fp_tls_apart_stmt B := B.ProgWorldTlsApart.fp_tls_apart B.
Let fp_tls_owned : B.ProgWorld.fp_tls_owned_stmt B := B.ProgWorldTlsOwned.fp_tls_owned B.
Let win_sh_vis : B.ProgWorld.win_sh_vis_stmt B := B.ProgWorldVisWin.win_sh_vis B.
Let ctl_block_apart_fs : B.ProgWorld.ctl_block_apart_fs_stmt B := B.ProgWorldBlkApart.ctl_block_apart_fs B.

(* ---- 2a. The side stack (A ProgWorld_Fs.v pw_F_in_owned / pw_F_not_img / pw_F_above / pw_F_present :224-283,
   same proofs with B's last segment (0xa2000, 0x55c000), B.ProgBridge.rsegs_spans) ---- *)
Lemma lay_F_in_owned : forall ly, In (ly_F ly, kFakeStackSize) (owned_extents ly).
Proof. intros ly. unfold owned_extents. right; right; right; left. reflexivity. Qed.

Lemma lay_ext_range : forall lo len, in_app lo len -> 4096 <= lo /\ lo + len <= 0x7fffff800000.
Proof.
  intros lo len [H0 H]. pose proof ASAN_CEIL_range as [CR _].
  unfold kLowShadowBeg, kHighMemBeg in H. lia.
Qed.

Lemma lay_F_not_img : forall ly a, layout_ok ly ->
  ly_F ly <= a < ly_F ly + kFakeStackSize -> ~ in_zr a (ly_img ly).
Proof.
  intros ly a LO Ha.
  assert (EX : Exists (in_zr a) (owned_extents ly)).
  { apply Exists_exists. exists (ly_F ly, kFakeStackSize).
    split; [apply lay_F_in_owned | unfold in_zr; cbn [fst snd]; lia]. }
  exact (proj2 (proj2 (lib.Reusable.YG0s.owned_extents_bound ly a LO EX))).
Qed.

Lemma lay_F_above : forall ly S (W : world SEGS) m md, AR SEGS B ly S W m md ->
  B.Prog.asan_stack_malloc_c.ASAN_GT <= ly_F ly.
Proof.
  intros ly S W m md (M & L & _).
  pose proof (am_layout _ _ _ _ M) as LO.
  pose proof (lo_img _ LO) as (I1 & I2 & I3 & I4).
  pose proof (proj1 (Forall_forall _ _) (lo_app _ LO) _ (lay_F_in_owned ly)) as F1.
  cbn [fst snd] in F1. destruct (lay_ext_range _ _ F1) as [F0 _].
  assert (Hm : In (663552, 5619712) (map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s))) B.Img0.rsegs)).
  { rewrite B.ProgBridge.rsegs_spans. right; right; right; left. reflexivity. }
  apply in_map_iff in Hm as (sg & Es & Hsg). injection Es as E1 E2.
  pose proof (al_img _ _ _ _ L sg Hsg) as [_ J2]. rewrite E1, E2 in J2.
  unfold B.Prog.asan_stack_malloc_c.ASAN_GT. unfold kImgLo in I1.
  destruct (Z_lt_le_dec (ly_F ly) 65536) as [Hlt|Hge].
  - exfalso. apply (lay_F_not_img ly 65536 LO); [unfold kFakeStackSize; lia|].
    unfold in_zr. lia.
  - destruct (Z_lt_le_dec (ly_F ly) (fst (ly_img ly) + snd (ly_img ly))) as [Hlt2|Hge2].
    + exfalso. apply (lay_F_not_img ly (ly_F ly) LO); [unfold kFakeStackSize; lia|].
      unfold in_zr. lia.
    + lia.
Qed.

(* the n-th entry of the bundle's areas: the side stack (AF 0, kFakeStackSize) and its frames' shadow *)
Lemma lay_areas_F : forall ly S rd, ARm B ly S rd ->
  range_vis B ly rd (AF 0, kFakeStackSize) /\
  range_vis B ly rd (ASh (AF kFakeFramesOff), (kFakeStackSize - kFakeFramesOff) / 8).
Proof.
  intros ly S rd M. pose proof (am_areas _ _ _ _ M) as AA. unfold aareas in AA.
  apply Forall_app in AA as [_ AA]. apply Forall_app in AA as [_ AA]. apply Forall_app in AA as [_ AA].
  apply Forall_cons_iff in AA as [AF AA].
  do 4 (apply Forall_cons_iff in AA as [_ AA]).
  apply Forall_cons_iff in AA as [ASH _].
  split; [exact AF | exact ASH].
Qed.

Lemma lay_F_present : forall ly S (W : world SEGS) m md a,
  AR SEGS B ly S W m md -> ly_F ly <= a < ly_F ly + kFakeStackSize -> apresent (w_H W) m a.
Proof.
  intros ly S W m md a (M & L & _) Ha.
  pose proof (am_layout _ _ _ _ M) as LO.
  pose proof (proj1 (Forall_forall _ _) (lo_app _ LO) _ (lay_F_in_owned ly)) as F1.
  cbn [fst snd] in F1. destruct (lay_ext_range _ _ F1) as [F0 F2].
  destruct (lay_areas_F _ _ _ M) as [AF _].
  specialize (AF (a - ly_F ly) ltac:(cbn [snd]; lia)).
  cbn [fst aeval] in AF.
  replace (ly_F ly + 0 + (a - ly_F ly)) with a in AF by lia.
  apply (lib.Reusable.YG0s.aview_present SEGS ly S md (w_H W) m a L); [lia | | exact AF].
  apply (lay_F_not_img ly a LO). exact Ha.
Qed.

(* (5) the side stack is visible at any AR state *)
Lemma lay_F_vis : forall ly S (W : world SEGS) m md, AR SEGS B ly S W m md ->
  B.ProgBridge.range_visible (w_H W) (ly_F ly) B.Prog.asan_stack_malloc_c.FS_SIZE.
Proof.
  intros ly S W m md HAR. pose proof HAR as (M & _). pose proof (am_layout _ _ _ _ M) as LO.
  pose proof (proj1 (Forall_forall _ _) (lo_app _ LO) _ (lay_F_in_owned ly)) as F1.
  cbn [fst snd] in F1. destruct (lay_ext_range _ _ F1) as [F0 F2].
  assert (EFS : B.Prog.asan_stack_malloc_c.FS_SIZE = kFakeStackSize) by reflexivity.
  rewrite EFS. split; [lia|]. split; [unfold kFakeStackSize in *; lia|].
  intros a Ha. exact (proj1 (lay_F_present ly S W m md a HAR Ha)).
Qed.

(* the shadow of the class-1 frame area is visible at any AR state (the areas' (ASh (AF kFakeFramesOff), ..) entry) *)
Lemma lay_Fsh_vis : forall ly S (W : world SEGS) m md, AR SEGS B ly S W m md -> ly_F ly mod 8 = 0 ->
  B.ProgBridge.range_visible (w_H W)
    (B.AsanRT.shadow_addr (B.Prog.asan_stack_malloc_c.fs_frame (ly_F ly) 1 0))
    (B.Prog.asan_stack_malloc_c.fs_M 1 * B.Prog.asan_stack_malloc_c.fs_B 1 / 8).
Proof.
  intros ly S W m md HAR H8. pose proof HAR as (M & _). pose proof (am_layout _ _ _ _ M) as LO.
  pose proof (proj1 (Forall_forall _ _) (lo_app _ LO) _ (lay_F_in_owned ly)) as F1.
  cbn [fst snd] in F1. destruct (lay_ext_range _ _ F1) as [F0 F2].
  destruct (lay_areas_F _ _ _ M) as [_ ASH].
  destruct (lay_geom1 (ly_F ly) 0) as (Q1 & _ & _ & Q4 & Q5).
  assert (EM : B.Prog.asan_stack_malloc_c.fs_M 1 * B.Prog.asan_stack_malloc_c.fs_B 1 / 8 = 131072) by reflexivity.
  rewrite EM, Q1, Q4, Q5. unfold lib.Reusable.YG0f.shadow_addr, SHADOW_OFF.
  replace (ly_F ly + (36864 + 1048576 + 0 * 128)) with ((ly_F ly + 36864) + 131072 * 8) by lia.
  rewrite Z.div_add by lia.
  assert (HX : 0 <= (ly_F ly + 36864) / 8 <= ly_F ly + 36864)
    by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
  unfold B.ProgBridge.range_visible.
  unfold kFakeStackSize in F2.
  split; [lia|]. split; [lia|].
  intros a Ha.
  assert (EN : (kFakeStackSize - kFakeFramesOff) / 8 = 1441792) by reflexivity.
  specialize (ASH (a - (2147450880 + (ly_F ly + 36864) / 8))).
  cbn [fst snd aeval] in ASH. rewrite EN in ASH.
  unfold lib.Reusable.YG0f.shadow_addr, SHADOW_OFF, kFakeFramesOff in ASH.
  replace (ly_F ly + (4096 + 32768)) with (ly_F ly + 36864) in ASH by lia.
  replace (2147450880 + (ly_F ly + 36864) / 8 + (a - (2147450880 + (ly_F ly + 36864) / 8))) with a in ASH by lia.
  apply (lay_vis_of_view W m a). apply ASH. lia.
Qed.

(* ---- 2b. (4) acall_kept is antitone in E ---- *)
Lemma lay_kept_E : forall lyc Sc (W W' : world SEGS) memc mem' slo shi (E E' : Z -> Prop),
  (forall a, E a -> E' a) ->
  acall_kept SEGS B lyc Sc W memc W' mem' slo shi E -> acall_kept SEGS B lyc Sc W memc W' mem' slo shi E'.
Proof.
  intros lyc Sc W W' memc mem' slo shi E E' HE (K1 & K2 & K3 & K4 & K5 & K6).
  split; [exact K1|]. split.
  { intros b m i Hin Hi HN. apply (K2 b m i Hin Hi). intros H; apply HN; apply HE; exact H. }
  split; [exact K3|]. split.
  { intros cid pos a Hin Hr HN. apply (K4 cid pos a Hin Hr). intros H; apply HN; apply HE; exact H. }
  split; [exact K5 | exact K6].
Qed.

(* ---- 2c. (2) the journal across a lifted stretch whose normalized run writes only lay_LWF ---- *)
Lemma lay_awr_grow : forall STK sp0 FP bl0 blc lyc ly' own pos a,
  ly_F ly' = ly_F lyc ->
  awr_byte STK sp0 FP bl0 blc lyc own a -> awr_byte STK sp0 FP bl0 blc ly' ((1, pos) :: own) a.
Proof.
  intros STK sp0 FP bl0 blc lyc ly' own pos a EF [Hw | [Hb | [Ht | (cid & q & Hin & Hr)]]].
  - left. exact Hw.
  - right; left. exact Hb.
  - right; right; left. exact Ht.
  - right; right; right. exists cid, q. split; [right; exact Hin|]. unfold frame_addr in *. rewrite EF. exact Hr.
Qed.

Lemma lay_journal_lwf : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc ly' S' (W' : world SEGS) memR mdR k
    (regs : bvmap 5 word) (p pos : Z) (ms1 ms3 s0 : machine_state) md3 RNG,
  ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 ((1, pos) :: own) ly' S' W' memR mdR k ->
  ablocks B ly' S' = ablocks B lyc Sc -> ly_F ly' = ly_F lyc -> 0 <= pos < B.Prog.asan_stack_malloc_c.fs_M 1 ->
  sp0 - STK <= spZ regs - C_ctrl_lay_block.CTRL_LAY_BLOCK_STK -> spZ regs <= sp0 ->
  (forall a, p + 18 <= a < p + 50 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
  B.MemNorm.ro_agree B.Img0.rsegs memR ->
  ms_mem ms1 = memR ->
  lib.Reusable.YK04R.fsteps SEGS RNG ms1 ms3 -> lib.Reusable.YK04R.fp_avoids (w_H W') RNG ->
  B.MemNorm.ms_rel B.Img0.rsegs ms3 s0 -> B.MemNorm.ro_same B.Img0.rsegs memR (ms_mem ms3) ->
  lib.Lib.Frame.munch (lay_LWF (spZ regs) p (B.Prog.asan_stack_malloc_c.fs_frame (ly_F lyc) 1 pos))
    (B.MemNorm.normalize B.Img0.rsegs memR) (ms_mem s0) ->
  same_but_materialized mdR md3 ->
  ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 ((1, pos) :: own) ly' S' W' (ms_mem ms3) md3 k.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc ly' S' W' memR mdR k regs p pos ms1 ms3 s0 md3 RNG
    HJ Eab EF Hpos Hlo Hhi Hawr Hro Ems1 Hrun Hfp HREL HROS MU Hsame.
  destruct HREL as (_ & _ & _ & _ & _ & _ & _ & HMR).
  assert (MU' : lib.Lib.Frame.munch (lay_LWF (spZ regs) p (B.Prog.asan_stack_malloc_c.fs_frame (ly_F lyc) 1 pos))
                  memR (ms_mem ms3))
    by exact (B.MemNorm.munch_rel B.Img0.rsegs _ memR (B.MemNorm.normalize B.Img0.rsegs memR) (ms_mem ms3)
                (ms_mem s0) (B.MemNorm.mem_rel_normalize B.Img0.rsegs memR Hro) HMR HROS MU).
  subst memR.
  apply (B.ProgWorld.ajournal_of_fsteps B LAWS HWX STK sp0 FP ly S W0 mem0 md0 ((1, pos) :: own) ly' S' W' ms1 ms3
           mdR md3 k RNG _ HJ Hrun Hfp MU' Hsame).
  intros a Ha Hout.
  assert (EK : C_ctrl_lay_block.CTRL_LAY_BLOCK_STK = 4512) by reflexivity.
  assert (EKc : ctrl_lay_block_c.CTRL_LAY_BLOCK_K = 4512) by reflexivity.
  destruct (lay_geom1 (ly_F lyc) pos) as (Q1 & Q2 & Q3 & Q4 & Q5).
  unfold lay_LWF in Hout. cbn [lib.Lib.Frame.outside] in Hout. rewrite EKc in Hout. rewrite EK in Hlo.
  set (fr1 := B.Prog.asan_stack_malloc_c.fs_frame (ly_F lyc) 1 pos) in *.
  assert (C : (spZ regs - 4512 <= a < spZ regs) \/ (p + 18 <= a < p + 50) \/ (fr1 <= a < fr1 + 128) \/
              (B.AsanRT.shadow_addr fr1 <= a < B.AsanRT.shadow_addr fr1 + 16)) by lia.
  destruct C as [C | [C | [C | C]]].
  - left. lia.
  - rewrite Eab. apply (lay_awr_grow STK sp0 FP _ _ lyc ly' own pos a EF). exact (Hawr a C).
  - right; right; right. exists 1, pos. split; [left; reflexivity|]. left.
    unfold in_zr, frame_addr. cbn [fst snd]. rewrite EF, Q3. subst fr1. rewrite Q1 in C. lia.
  - right; right; right. exists 1, pos. split; [left; reflexivity|]. right.
    unfold in_zr, frame_addr. cbn [fst snd]. rewrite EF, Q3. subst fr1. rewrite Q1, Q5 in C.
    change (128 / 8) with 16. lia.
Qed.

(* ---- 2d. FP0 / TLS0 at the normalized memory of a cut ---- *)
(* TLS0 (A glue LayBase.lay_tls0_facts :351): the cells read at the normalized memory are the real memory's
   (B.MemNormTr.asan_tls_cells_normalize), apart by fp_tls_apart_stmt. *)
Lemma lay_tls0_facts : forall ly S (W : world SEGS) m md lo hi,
  AR SEGS B ly S W m md -> B.MemNorm.ro_agree B.Img0.rsegs m ->
  ly_stk_lo ly <= lo -> hi <= ly_stk_hi ly ->
  ctrl_lay_block_c.ctrl_lay_block_tls (B.MemNorm.normalize B.Img0.rsegs m) B.AsanRT.RT_TP (ly_F ly) lo hi.
Proof.
  intros ly S W m md lo hi HAR Hro Hlo Hhi DT TS C T DB k HT.
  exact (fp_tls_apart CTS LAWS ly S W m md [0%nat; 1%nat] lo hi HAR ltac:(repeat constructor) Hlo Hhi DT TS C T DB k
           (proj1 (B.MemNormTr.asan_tls_cells_normalize m _ _ _ _ _ _ _ Hro) HT)).
Qed.

(* Where an output-block byte lies, at a state S that keeps the caller's frames and blocks: a heap block byte (not
   owned, apart from the side stack) or a byte of a frame of class 2 or more (past the class-0 / class-1 frames). *)
Lemma lay_blk_pt : forall ly S (W : world SEGS) m md lyc Sc p a,
  AR SEGS B ly S W m md ->
  (forall c q, In (c, q) (frames Sc) -> In (c, q) (frames S)) ->
  ablocks B ly S = ablocks B lyc Sc -> ly_F ly = ly_F lyc ->
  C_ctrl_lay_block.tctrl_lay_block_home B lyc Sc (p + 18) 32 ->
  (forall a, p + 18 <= a < p + 50 -> ~ in_img SEGS a) ->
  p + 18 <= a < p + 50 ->
  app_addr a /\ a < lib.Reusable.YM05.alloc_ceiling /\
  (((a < ly_F ly \/ ly_F ly + kFakeStackSize <= a) /\ ~ aowned B ly S a) \/
   (ly_F ly + kFakeFramesOff + 2 * 2 ^ 20 <= a /\ a < ly_F ly + kFakeStackSize)).
Proof.
  intros ly S W m md lyc Sc p a HAR Hsub Eab EF Hhome HNI Ha.
  destruct (Hhome a ltac:(lia)) as [(Himg & _ & _) | [(b & mm & i & Hin & Hi & ->) | (cid & q & Hin & Hc & Hr)]].
  - exfalso. exact (HNI a Ha Himg).
  - rewrite <- Eab in Hin.
    destruct (al_blocks _ _ LAWS ly S W m md b mm HAR Hin) as (_ & H4096 & Hceil & Happ & Hb & _).
    split; [apply (in_app_addr b (req_size mm) (b + i) Happ); lia|]. split; [lia|]. left.
    split; [|exact (proj2 (Hb (b + i) ltac:(lia)))].
    destruct (ctl_block_apart_fs LAWS ly S W m md b mm HAR Hin) as [D|D]; [left | right]; lia.
  - pose proof (Hsub cid q Hin) as HinS. pose proof HAR as (M & _).
    destruct (lib.Reusable.YG0s.frame_facts B ly S _ cid q M HinS) as (Q1 & Q2 & Q3 & _ & _ & Q6 & Q7 & _).
    destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid q HAR HinS) as (_ & FB2 & _).
    unfold in_zr, frame_rng, frame_addr in Hr. cbn [fst snd] in Hr. rewrite <- EF in Hr.
    unfold frame_addr in FB2. unfold kFakeFramesOff in Q6 |- *.
    assert (HO : 4096 + 32768 + 2 * 1048576 <= fs_frame_off cid q).
    { assert (cid * 2 ^ 20 >= 2 * 1048576) by nia. lia. }
    split; [apply (in_app_addr (ly_F ly) kFakeStackSize a Q3); lia|]. split; [lia|]. right.
    change (2 * 2 ^ 20) with (2 * 1048576). lia.
Qed.

(* FP0 (A glue LayBase.lay_fp0_facts :275, for B's per-byte home): ctl_fp_of_AR with cs = [0; 1], the window
   [sp - 4512, sp), ctrl_lay_block_W / ctrl_lay_block_D (ctrl_lay_block_c.v:19-20).  The window is above every
   allocator extent; f is an image global below the side stack; an output-block byte is a heap block byte (not owned,
   so apart from the thread cells by fp_tls_owned_stmt; apart from the side stack by ctl_block_apart_fs_stmt) or a
   byte of a frame of class 2 or more (past the class-0 / class-1 areas; the side stack is apart from the thread
   cells by layout_ok's lo_disj); every byte is an application address, apart from the side stack's shadow. *)
Lemma lay_fp0_facts : forall ly S (W : world SEGS) m md lyc Sc (sp p f : Z),
  AR SEGS B ly S W m md -> B.MemNorm.ro_agree B.Img0.rsegs m ->
  (forall c q, In (c, q) (frames Sc) -> In (c, q) (frames S)) ->
  ablocks B ly S = ablocks B lyc Sc -> ly_F ly = ly_F lyc ->
  lib.Reusable.YM05.alloc_ceiling <= sp - 4512 -> sp <= B.AsanRT.APPMEM_END ->
  0 <= f -> f + 24 <= B.Prog.asan_stack_malloc_c.ASAN_GT ->
  C_ctrl_lay_block.tctrl_lay_block_home B lyc Sc (p + 18) 32 ->
  (forall a, p + 18 <= a < p + 50 -> ~ in_img SEGS a) ->
  B.Prog.RcAsanFP.fp [0%nat; 1%nat] (B.MemNorm.normalize B.Img0.rsegs m) B.AsanRT.RT_TP (ly_F ly) (sp - 4512) sp
    (ctrl_lay_block_c.ctrl_lay_block_W p sp) (ctrl_lay_block_c.ctrl_lay_block_D p f).
Proof.
  intros ly S W m md lyc Sc sp p f HAR Hro Hsub Eab EF Hc Hsp Hf0 Hf1 Hhome HNI.
  pose proof HAR as (M & _). pose proof (am_layout _ _ _ _ M) as LO.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (lay_F_above ly S W m md HAR) as HGT. unfold B.Prog.asan_stack_malloc_c.ASAN_GT in HGT, Hf1.
  assert (EXT : forall e, In e (owned_extents ly) -> 4096 <= fst e /\ fst e + snd e <= lib.Reusable.YM05.alloc_ceiling).
  { intros e He. pose proof (proj1 (Forall_forall _ _) (lo_app _ LO) e He) as [E0 E1].
    unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in E1. lia. }
  destruct (EXT (ly_F ly, kFakeStackSize) ltac:(unfold owned_extents; cbn; tauto)) as [F0 F1].
  destruct (EXT (ly_T ly, kThreadObjSize) ltac:(unfold owned_extents; cbn; tauto)) as [T0 T1].
  destruct (EXT (ly_C ly, 256) ltac:(unfold owned_extents; cbn; tauto)) as [CC0 CC1].
  destruct (EXT (ly_D ly, 4096) ltac:(unfold owned_extents; cbn; tauto)) as [D0 D1].
  cbn [fst snd] in F0, F1, T0, T1, CC0, CC1, D0, D1.
  pose proof (proj1 (Forall_forall _ _) (lo_app _ LO) (ly_F ly, kFakeStackSize)
                ltac:(unfold owned_extents; cbn; tauto)) as FAPP.
  cbn [fst snd] in FAPP.
  pose proof (lo_disj _ LO) as LD.
  assert (DTF : zdisjoint (ly_T ly, kThreadObjSize) (ly_F ly, kFakeStackSize))
    by exact (pairwise_In2 zdisjoint _ _ _ [(ly_prim ly, kPrimResvSize); (ly_Q ly, kPtrArrayResv)] []
                [(ly_NB ly, kNodesBlockSize); (ly_SB ly, kStoreBlockSize); (ly_C ly, 256); (ly_D ly, 4096);
                 (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly); ly_img ly] LD eq_refl).
  assert (DFC : zdisjoint (ly_F ly, kFakeStackSize) (ly_C ly, 256))
    by exact (pairwise_In2 zdisjoint _ _ _
                [(ly_prim ly, kPrimResvSize); (ly_Q ly, kPtrArrayResv); (ly_T ly, kThreadObjSize)]
                [(ly_NB ly, kNodesBlockSize); (ly_SB ly, kStoreBlockSize)]
                [(ly_D ly, 4096); (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly); ly_img ly] LD eq_refl).
  assert (DFD : zdisjoint (ly_F ly, kFakeStackSize) (ly_D ly, 4096))
    by exact (pairwise_In2 zdisjoint _ _ _
                [(ly_prim ly, kPrimResvSize); (ly_Q ly, kPtrArrayResv); (ly_T ly, kThreadObjSize)]
                [(ly_NB ly, kNodesBlockSize); (ly_SB ly, kStoreBlockSize); (ly_C ly, 256)]
                [(ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly); ly_img ly] LD eq_refl).
  unfold zdisjoint in DTF, DFC, DFD. cbn [fst snd] in DTF, DFC, DFD.
  assert (Etsd : ly_tsd ly = 0x5fd9f8) by (rewrite (am_tsd _ _ _ _ M), (B.ProgWorld.as_tsd_TSD B CTS); reflexivity).
  assert (ET : bv_unsigned (Z_to_bv 64 (ly_T ly)) = ly_T ly)
    by (apply B.ProgWorld.pws_u64; unfold kThreadObjSize in T1; lia).
  assert (ED : bv_unsigned (Z_to_bv 64 (ly_D ly)) = ly_D ly) by (apply B.ProgWorld.pws_u64; lia).
  assert (EC : bv_unsigned (Z_to_bv 64 (ly_C ly)) = ly_C ly) by (apply B.ProgWorld.pws_u64; lia).
  assert (ETS : bv_unsigned (Z_to_bv 64 0x5fd9f8) = 0x5fd9f8) by (apply B.ProgWorld.pws_u64; lia).
  assert (EDT : bv_unsigned (Z_to_bv 64 (B.AsanRT.RT_TP + 32)) = B.AsanRT.RT_TP + 32)
    by (apply B.ProgWorld.pws_u64; unfold B.AsanRT.RT_TP; lia).
  assert (EF00 : B.Prog.asan_stack_malloc_c.fs_frame (ly_F ly) 0%nat 0 = ly_F ly + 36864)
    by (unfold B.Prog.asan_stack_malloc_c.fs_frame, B.Prog.asan_stack_malloc_c.fs_B; cbn [Z.of_nat]; lia).
  (* where each output-block byte lies *)
  pose proof (fun a Ha => lay_blk_pt ly S W m md lyc Sc p a HAR Hsub Eab EF Hhome HNI Ha) as PT.
  assert (Hp18 : 0 <= p + 18) by (pose proof (PT (p + 18) ltac:(lia)) as (X & _); unfold app_addr in X; lia).
  apply B.MemNormTr.fp_normalize; [exact Hro|].
  apply (ctl_fp_of_AR CTS LAWS ly S W m md [0%nat; 1%nat] (sp - 4512) sp _ _ HAR).
  - repeat constructor.
  - unfold B.Prog.asan_stack_malloc_c.FS_SIZE, kFakeStackSize in *. lia.
  - intros a Ha. unfold B.AsanRT.app_mem, B.AsanRT.HIGHMEM_BEG. right. lia.
  - (* the writes vs the thread cells and the side stack's header *)
    unfold B.Prog.RcAsanFP.fp_dj, ctrl_lay_block_c.ctrl_lay_block_W, ctrl_lay_block_c.CTRL_LAY_BLOCK_K.
    rewrite Etsd, EF00.
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold B.Prog.RcAsanFP.fp_tls. rewrite ?ET, ?ED, ?EC, ?ETS, ?EDT.
      unfold B.Prog.asan_stack_malloc_c.TLS_INDEX, B.Prog.asan_stack_malloc_c.REAL_TLS_GET_ADDR,
        B.Prog.asan_stack_malloc_c.TSD_KEY_INITED, B.Prog.asan_stack_malloc_c.TSD_KEY,
        B.Prog.asan_stack_malloc_c.GOT_CF, B.Prog.asan_stack_malloc_c.CF, B.Prog.asan_stack_malloc_c.GOT_VERBOSITY,
        B.Prog.asan_stack_malloc_c.VERBOSITY, B.Prog.asan_stack_malloc_c.DTLS_TPOFF, B.AsanRT.RT_TP.
      unfold kThreadObjSize, kFakeStackSize in *.
      cbn [app]; repeat (apply Forall_cons || apply Forall_nil); unfold RcLay.ly_dj; cbn [fst snd]; lia.
    + apply Forall_forall. intros d Hd. cbn [fst snd]. apply in_app_or in Hd. destruct Hd as [Hd | Hd].
      * assert (Hne : fst d < snd d).
        { revert Hd. unfold B.Prog.RcAsanFP.fp_tls. cbn [In]. intros Hd.
          repeat (destruct Hd as [<- | Hd]; [cbn [fst snd]; lia|]). destruct Hd. }
        apply lay_dj_of_pt; [lia | exact Hne|]. intros a Ha.
        destruct (Z_lt_le_dec a (fst d)) as [L1|L1]; [left; exact L1|].
        destruct (Z_lt_le_dec a (snd d)) as [L2|L2]; [|right; exact L2].
        exfalso. destruct (PT a Ha) as (Happ & Hce & [(HF & Hno) | (HF1 & HF2)]).
        -- apply Hno. apply (fp_tls_owned CTS LAWS ly S W m md a HAR). apply Exists_exists. exists d.
           rewrite Etsd. split; [exact Hd | lia].
        -- revert Hd. unfold B.Prog.RcAsanFP.fp_tls. rewrite ?ET, ?ED, ?EC, ?ETS, ?EDT. cbn [In]. intros Hd.
           unfold B.Prog.asan_stack_malloc_c.TLS_INDEX, B.Prog.asan_stack_malloc_c.REAL_TLS_GET_ADDR,
             B.Prog.asan_stack_malloc_c.TSD_KEY_INITED, B.Prog.asan_stack_malloc_c.TSD_KEY,
             B.Prog.asan_stack_malloc_c.GOT_CF, B.Prog.asan_stack_malloc_c.CF,
             B.Prog.asan_stack_malloc_c.GOT_VERBOSITY, B.Prog.asan_stack_malloc_c.VERBOSITY,
             B.Prog.asan_stack_malloc_c.DTLS_TPOFF, B.AsanRT.RT_TP in *.
           unfold kThreadObjSize, kFakeStackSize, kFakeFramesOff in *.
           repeat (destruct Hd as [<- | Hd]; [cbn [fst snd] in *; lia|]). destruct Hd.
      * destruct Hd as [<- | []]. cbn [fst snd].
        apply lay_dj_of_pt; [lia | lia|]. intros a Ha.
        destruct (PT a Ha) as (Happ & Hce & [([HF | HF] & Hno) | (HF1 & HF2)]);
          unfold kFakeStackSize, kFakeFramesOff in *; lia.
  - (* the data ranges vs the class-0 / class-1 side-stack bytes *)
    unfold B.Prog.RcAsanFP.fp_dj, ctrl_lay_block_c.ctrl_lay_block_D.
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold B.Prog.RcAsanFP.fp_w, B.Prog.RcAsanFP.fp_w1. cbn [flat_map app].
      unfold B.Prog.asan_stack_malloc_c.fs_hint, B.Prog.asan_stack_malloc_c.fs_flag,
        B.Prog.asan_stack_malloc_c.fs_frame, B.Prog.asan_stack_malloc_c.fs_M, B.Prog.asan_stack_malloc_c.fs_B.
      cbn [Z.of_nat]. unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K.
      repeat (apply Forall_cons || apply Forall_nil); unfold RcLay.ly_dj; cbn [fst snd]; left.
      all: Z.div_mod_to_equations; lia.
    + apply Forall_forall. intros d Hd. cbn [fst snd].
      assert (Hne : fst d < snd d /\
                    ((ly_F ly <= fst d /\ snd d <= ly_F ly + kFakeFramesOff + 2 * 2 ^ 20) \/
                     (B.AsanRT.shadow_addr (ly_F ly) <= fst d /\
                      snd d <= B.AsanRT.shadow_addr (ly_F ly + kFakeStackSize)))).
      { revert Hd. unfold B.Prog.RcAsanFP.fp_w, B.Prog.RcAsanFP.fp_w1. cbn [flat_map app In].
        unfold B.Prog.asan_stack_malloc_c.fs_hint, B.Prog.asan_stack_malloc_c.fs_flag,
          B.Prog.asan_stack_malloc_c.fs_frame, B.Prog.asan_stack_malloc_c.fs_M, B.Prog.asan_stack_malloc_c.fs_B.
        cbn [Z.of_nat]. unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, kFakeFramesOff, kFakeStackSize.
        intros Hd. repeat (destruct Hd as [<- | Hd]; [cbn [fst snd]; Z.div_mod_to_equations; lia|]). destruct Hd. }
      destruct Hne as (Hne & Hloc).
      apply lay_dj_of_pt; [lia | exact Hne|]. intros a Ha.
      destruct (Z_lt_le_dec a (fst d)) as [L1|L1]; [left; exact L1|].
      destruct (Z_lt_le_dec a (snd d)) as [L2|L2]; [|right; exact L2].
      exfalso. destruct (PT a Ha) as (Happ & Hce & [([HF | HF] & Hno) | (HF1 & HF2)]);
        unfold app_addr, in_app in *; unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, kFakeFramesOff, kFakeStackSize,
          kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *;
        Z.div_mod_to_equations; lia.
Qed.

(* ---- 2e. the output block is apart from the image: each byte is a byte the caller lets the call write
   (YCbq.awr_byte_cases on the caller's journal: a stack, heap-block or own-frame byte) ---- *)
Lemma lay_blk_not_img : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k p,
  ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  (forall a, p + 18 <= a < p + 50 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
  forall a, p + 18 <= a < p + 50 -> ~ in_img SEGS a.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k p HJ Hawr a Ha Himg.
  pose proof (B.ProgWorld.pws_segs_low a Himg) as HL.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
  destruct (awr_byte_cases SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ (Hawr a Ha))
    as (_ & [(Hc & _) | [(_ & b & n & Hin & Hr & _) | (cid & q & Hown & [(_ & Hr) | (Hs & _)])]]).
  - unfold kLowMemEnd in HL. lia.
  - exact (blk_img SEGS B LAWS _ _ _ _ _ b n a HAR Hin Hr Himg).
  - assert (Hin : In (cid, q) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
    unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr.
    exact (frm_img SEGS B LAWS _ _ _ _ _ cid q a HAR Hin Hr Himg).
  - unfold kLowMemEnd in HL. lia.
Qed.

(* The class-1 frame of a cut is not a frame of the caller's state (the frames of an AR state are pairwise apart,
   sep_frames_pos). *)
Lemma lay_frame1_fresh : forall ly' S' (W' : world SEGS) m' md' Sc pos,
  AR SEGS B ly' S' W' m' md' -> frames S' = (1, pos) :: frames Sc -> ~ In (1, pos) (frames Sc).
Proof.
  intros ly' S' W' m' md' Sc pos HAR Efr Hin. destruct (in_split _ _ Hin) as (l2 & l3 & El).
  pose proof (sep_frames_pos SEGS B LAWS _ _ _ _ _ (1, pos) (1, pos) [] l2 l3 HAR) as SEP.
  rewrite Efr, El in SEP. specialize (SEP eq_refl). unfold zdisjoint, frame_rng in SEP. cbn [fst snd] in SEP.
  assert (fs_frame_bytes 1 = 128) by reflexivity. lia.
Qed.

(* What a cut's journal gives about the output block and the window, for lay_kept_lwf / lay_cut_ctx: the block is off
   the image (each byte the caller lets the call write is a stack, heap-block or own-frame byte; the own frames are
   frames of the cut state), the window is above the allocation ceiling, and the class-1 frame is fresh. *)
Lemma lay_cut_facts : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc ly' S' (W' : world SEGS) mem' md' k
    (regs : bvmap 5 word) (p pos : Z),
  ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 ((1, pos) :: own) ly' S' W' mem' md' k ->
  frames S' = (1, pos) :: frames Sc -> ablocks B ly' S' = ablocks B lyc Sc -> ly_F ly' = ly_F lyc ->
  sp0 - STK <= spZ regs - C_ctrl_lay_block.CTRL_LAY_BLOCK_STK -> spZ regs <= sp0 ->
  (forall a, p + 18 <= a < p + 50 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
  (forall a, p + 18 <= a < p + 50 -> ~ in_img SEGS a) /\
  lib.Reusable.YM05.alloc_ceiling <= spZ regs - C_ctrl_lay_block.CTRL_LAY_BLOCK_STK /\
  ~ In (1, pos) (frames Sc).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc ly' S' W' mem' md' k regs p pos HJ Efr Eab EF Hlo Hhi Hawr.
  pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _ & _).
  pose proof Hstk as (Hal0 & Hstk0 & Hceil & Hslo & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  split; [|split; [lia | exact (lay_frame1_fresh ly' S' W' mem' md' Sc pos HAR Efr)]].
  intros a Ha Himg. pose proof (B.ProgWorld.pws_segs_low a Himg) as HL. unfold kLowMemEnd in HL.
  destruct (Hawr a Ha) as [Hw | [(_ & b & n & Hin & Hr) | [(b & n & Hin & _ & Hr) | (cid & q & Hown & [Hr | Hr])]]].
  - lia.
  - rewrite <- Eab in Hin. exact (blk_img SEGS B LAWS _ _ _ _ _ b n a HAR Hin Hr Himg).
  - rewrite <- Eab in Hin. exact (blk_img SEGS B LAWS _ _ _ _ _ b n a HAR Hin Hr Himg).
  - assert (HinS : In (cid, q) (frames S')) by (rewrite Hfrs; right; apply in_or_app; left; exact Hown).
    unfold in_zr, frame_addr in Hr. cbn [fst snd] in Hr. rewrite <- EF in Hr.
    exact (frm_img SEGS B LAWS _ _ _ _ _ cid q a HAR HinS Hr Himg).
  - assert (HinS : In (cid, q) (frames S')) by (rewrite Hfrs; right; apply in_or_app; left; exact Hown).
    destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid q HAR HinS) as (G0 & _).
    unfold in_zr, frame_addr in Hr. cbn [fst snd] in Hr. unfold frame_addr in G0. rewrite <- EF in Hr.
    unfold lib.Reusable.YG0f.shadow_addr, SHADOW_OFF in Hr.
    assert (0 <= (ly_F ly' + fs_frame_off cid q) / 8) by (apply Z.div_pos; lia). lia.
Qed.

(* ---- 2f. (3) what the call keeps, across the stretch's lay_LWF writes on the real memory, from the cut's AR (the
   output block joins E; the class-1 frame (1, pos) and its shadow are in no kept class of Sc: (1, pos) is not a frame
   of Sc, the side stack is apart from the image (frm_img) and from the blocks (ctl_block_apart_fs_stmt), every other
   frame is apart (sep_frames_pos), and a frame's shadow lies strictly between the low and the high application
   memory; the window is above the allocation ceiling) ---- *)
Lemma lay_kept_lwf : forall lyc Sc ly' S' (W W' : world SEGS) memc memR mem3 md' (regs : bvmap 5 word) (p pos : Z)
    (E : Z -> Prop),
  AR SEGS B ly' S' W' memR md' ->
  frames S' = (1, pos) :: frames Sc -> ablocks B ly' S' = ablocks B lyc Sc -> ly_F ly' = ly_F lyc ->
  0 <= pos < B.Prog.asan_stack_malloc_c.fs_M 1 ->
  lib.Reusable.YM05.alloc_ceiling <= spZ regs - C_ctrl_lay_block.CTRL_LAY_BLOCK_STK ->
  C_ctrl_lay_block.tctrl_lay_block_home B lyc Sc (p + 18) 32 ->
  (forall a, p + 18 <= a < p + 50 -> ~ in_img SEGS a) ->
  acall_kept SEGS B lyc Sc W memc W' memR (spZ regs - C_ctrl_lay_block.CTRL_LAY_BLOCK_STK) (spZ regs) E ->
  lib.Lib.Frame.munch (lay_LWF (spZ regs) p (B.Prog.asan_stack_malloc_c.fs_frame (ly_F lyc) 1 pos)) memR mem3 ->
  (forall a, spZ regs - C_ctrl_lay_block.CTRL_LAY_BLOCK_STK <= a < spZ regs -> apresent (w_H W') mem3 a) ->
  acall_kept SEGS B lyc Sc W memc W' mem3 (spZ regs - C_ctrl_lay_block.CTRL_LAY_BLOCK_STK) (spZ regs)
    (fun a => E a \/ C_ctrl_lay_block.tctrl_lay_block_out p a).
Proof.
  intros lyc Sc ly' S' W W' memc memR mem3 md' regs p pos E HAR Efr Eab EF Hpos Hc Hhome HNI
    (K1 & K2 & K3 & K4 & K5 & K6) MU Hp.
  assert (EK : C_ctrl_lay_block.CTRL_LAY_BLOCK_STK = 4512) by reflexivity.
  assert (EKc : ctrl_lay_block_c.CTRL_LAY_BLOCK_K = 4512) by reflexivity.
  rewrite EK in *.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (Hspr : 0 <= spZ regs < 2 ^ 64) by (unfold spZ; apply bv_unsigned_in_range).
  pose proof HAR as (M & _).
  assert (Hsub : forall c q, In (c, q) (frames Sc) -> In (c, q) (frames S')) by (intros c q H; rewrite Efr; right; exact H).
  assert (Hin1 : In (1, pos) (frames S')) by (rewrite Efr; left; reflexivity).
  pose proof (lay_frame1_fresh ly' S' W' memR md' Sc pos HAR Efr) as Hnin.
  destruct (lib.Reusable.YG0s.frame_facts B ly' S' _ 1 pos M Hin1) as (_ & _ & FAPP & _ & FPA & FQ6 & FQ7 & FQ8 & _).
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 pos HAR Hin1) as (FB0 & FB1 & FB2).
  destruct (lay_geom1 (ly_F lyc) pos) as (Q1 & Q2 & Q3 & Q4 & Q5). rewrite Q3 in FQ7.
  pose proof (fun a Ha => lay_blk_pt ly' S' W' memR md' lyc Sc p a HAR Hsub Eab EF Hhome HNI Ha) as PT.
  set (fr1 := B.Prog.asan_stack_malloc_c.fs_frame (ly_F lyc) 1 pos) in *.
  assert (Efr1 : fr1 = frame_addr ly' 1 pos) by (rewrite Q1; unfold frame_addr; rewrite EF; reflexivity).
  rewrite <- Efr1 in FB0. rewrite <- Efr1, Q3 in FB1, FB2.
  assert (SH : kLowMemEnd <= B.AsanRT.shadow_addr fr1 /\ B.AsanRT.shadow_addr fr1 + 16 <= kHighMemBeg).
  { unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, kLowMemEnd, kHighMemBeg. Z.div_mod_to_equations. lia. }
  unfold kLowMemEnd, kHighMemBeg in SH.
  (* the bytes the stretch does not write keep their raw value and their view *)
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> lib.Lib.Frame.outside (lay_LWF (spZ regs) p fr1) a ->
            mem3 (Z_to_bv 64 a) = memR (Z_to_bv 64 a) /\ aview SEGS (w_H W') mem3 a = aview SEGS (w_H W') memR a).
  { intros a Ha Ho. assert (E3 : mem3 (Z_to_bv 64 a) = memR (Z_to_bv 64 a)).
    { apply MU. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
      rewrite Z.mod_small by lia. exact Ho. }
    split; [exact E3|]. apply aview_eq_of. unfold mrestrict. rewrite E3. reflexivity. }
  assert (OUT : forall a, ~ (spZ regs - 4512 <= a < spZ regs) -> ~ (p + 18 <= a < p + 50) -> ~ (fr1 <= a < fr1 + 128) ->
            ~ (B.AsanRT.shadow_addr fr1 <= a < B.AsanRT.shadow_addr fr1 + 16) ->
            lib.Lib.Frame.outside (lay_LWF (spZ regs) p fr1) a).
  { intros a H1 H2 H3 H4. unfold lay_LWF. rewrite EKc. cbn [lib.Lib.Frame.outside]. tauto. }
  (* every output-block byte is an application address below the ceiling *)
  assert (BLKB : forall a, p + 18 <= a < p + 50 -> app_addr a /\ a < lib.Reusable.YM05.alloc_ceiling)
    by (intros a Ha; destruct (PT a Ha) as (X1 & X2 & _); split; assumption).
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha Hn.
    assert (Ho : lib.Lib.Frame.outside (lay_LWF (spZ regs) p fr1) a).
    { apply OUT; [exact Hn | intros Hb; destruct (BLKB a Hb); lia | lia | lia]. }
    destruct (KM a ltac:(lia) Ho) as [_ KV]. rewrite KV. exact (K1 a Ha Hn).
  - intros b m i Hin Hi HN.
    assert (HNE : ~ E (b + i)) by (intros H; apply HN; left; exact H).
    assert (HNO : ~ (p + 18 <= b + i < p + 50)) by (intros H; apply HN; right; exact H).
    assert (HinS : In (b, m) (ablocks B ly' S')) by (rewrite Eab; exact Hin).
    destruct (al_blocks _ _ LAWS ly' S' W' memR md' b m HAR HinS) as (_ & H4096 & Hceil & Happ & _).
    pose proof (ctl_block_apart_fs LAWS ly' S' W' memR md' b m HAR HinS) as DFS.
    pose proof (in_app_addr b (req_size m) (b + i) Happ ltac:(lia)) as Hai.
    assert (Ho : lib.Lib.Frame.outside (lay_LWF (spZ regs) p (fr1)) (b + i)).
    { apply OUT; [lia | exact HNO | | ].
      - subst fr1. rewrite Q1. rewrite <- EF. unfold kFakeStackSize, kFakeFramesOff in *. lia.
      - unfold app_addr, kLowShadowBeg, kHighMemBeg, kLowMemEnd in *. lia. }
    destruct (KM (b + i) ltac:(lia) Ho) as [_ KV]. rewrite KV. exact (K2 b m i Hin Hi HNE).
  - intros a Hi Hs He.
    pose proof (B.ProgWorld.pws_segs_low a Hi) as HL.
    assert (Ho : lib.Lib.Frame.outside (lay_LWF (spZ regs) p fr1) a).
    { apply OUT; [unfold kLowMemEnd in HL; lia | intros Hb; exact (HNI a Hb Hi) | | unfold kLowMemEnd in *; lia].
      intros Hf. apply (frm_img SEGS B LAWS _ _ _ _ _ 1 pos a HAR Hin1); [rewrite <- Efr1, Q3; lia | exact Hi]. }
    destruct (KM a ltac:(unfold kLowMemEnd in HL; lia) Ho) as [_ KV]. rewrite KV. exact (K3 a Hi Hs He).
  - intros cid q a Hin Hr HN.
    assert (HNE : ~ E a) by (intros H; apply HN; left; exact H).
    assert (HNO : ~ (p + 18 <= a < p + 50)) by (intros H; apply HN; right; exact H).
    pose proof (Hsub cid q Hin) as HinS.
    destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid q HAR HinS) as (G0 & G1 & G2).
    destruct (lib.Reusable.YG0s.frame_facts B ly' S' _ cid q M HinS) as (_ & _ & _ & _ & _ & GQ6 & GQ7 & GQ8 & GQ9 & GQ10 & _).
    assert (Hne : (cid, q) <> (1, pos)) by (intros Eq; rewrite Eq in Hin; exact (Hnin Hin)).
    destruct (in_split _ _ Hin) as (l2 & l3 & El).
    pose proof (sep_frames_pos SEGS B LAWS _ _ _ _ _ (1, pos) (cid, q) [] l2 l3 HAR) as SEP.
    rewrite Efr, El in SEP. specialize (SEP eq_refl).
    unfold zdisjoint, frame_rng in SEP. cbn [fst snd] in SEP. rewrite <- Efr1, Q3 in SEP.
    unfold frame_addr in G0, G1, G2, SEP, FPA. unfold page_aligned in FPA.
    pose proof Hr as Hr0.
    unfold in_zr, frame_rng, frame_addr in Hr. cbn [fst snd] in Hr. rewrite <- EF in Hr.
    assert (Ho : lib.Lib.Frame.outside (lay_LWF (spZ regs) p fr1) a).
    { apply OUT; [ | exact HNO | | ].
      all: rewrite ?Q5 in *; unfold fr1 in *; rewrite Q1 in *; rewrite <- ?EF in *;
        unfold lib.Reusable.YG0f.shadow_addr, SHADOW_OFF, B.AsanRT.ASAN_K in *; unfold in_app in G2, FB2;
        unfold kLowMemEnd, kHighMemBeg, kLowShadowBeg, kFakeStackSize, kFakeFramesOff in *;
        destruct Hr as [Hr | Hr]; Z.div_mod_to_equations; lia. }
    assert (Ha64 : 0 <= a < 2 ^ 64).
    { destruct Hr as [Hr | Hr]; unfold lib.Reusable.YG0f.shadow_addr, SHADOW_OFF in Hr; unfold in_app in G2;
        Z.div_mod_to_equations; lia. }
    destruct (KM a Ha64 Ho) as [_ KV].
    rewrite KV. exact (K4 cid q a Hin Hr0 HNE).
  - intros a Ha Hn Hpr.
    assert (Ho : lib.Lib.Frame.outside (lay_LWF (spZ regs) p fr1) a).
    { apply OUT; [exact Hn | intros Hb; destruct (BLKB a Hb); lia | lia | lia]. }
    destruct (K5 a Ha Hn Hpr) as [Hh (bb & Hb)]. destruct (KM a ltac:(lia) Ho) as [E3 _].
    split; [exact Hh|]. exists bb. rewrite E3. exact Hb.
  - exact Hp.
Qed.

(* ---- 2g'. route (C): the region of the _on run's SR0 (a Theorem Labs lane's ctrl_lay_block_shadow_R at the cut's entry sp S0)
   lies in the cut's own shadow regions (a Theorem Labs lane, B.ACtlRtC): the window [S0 - K, S0) by the machine
   stack's zero-shadow range (Z, the first entry of zero_shadow_ranges; the stack is page-aligned, layout_ok); the
   class-0 / class-1 blocks of the side stack by its frames-area shadow (A, cut_shadow's fourth disjunct); the output
   block [p + 18, p + 50) byte by byte by its home (tctrl_lay_block_home): a frame of class 2 or more of Sc (F: a
   frame of the cut, 64-aligned) or a live block of Sc (L: the block's shadow-word cover), never the image (the block
   is off the image at a cut, lay_cut_facts); f / template / g / md / name by the image hull (I, lay_img_ro) and the
   two JOIN blocks (I, by their addresses 0x21a20 / 0x21a60). ---- *)
Lemma lay_RR_cover : forall ly S (W : world SEGS) m mdl lyc Sc (S0 p f md g : Z) (fr mb nb : list byte),
  AR SEGS B ly S W m mdl ->
  (forall c q, In (c, q) (frames Sc) -> In (c, q) (frames S)) ->
  ablocks B ly S = ablocks B lyc Sc -> ly_F ly = ly_F lyc ->
  ly_stk_lo ly <= S0 - ctrl_lay_block_c.CTRL_LAY_BLOCK_K -> S0 <= ly_stk_hi ly ->
  0 <= p -> C_ctrl_lay_block.tctrl_lay_block_home B lyc Sc (p + 18) 32 ->
  (forall a, p + 18 <= a < p + 50 -> ~ in_img SEGS a) ->
  lay_img_ro f md g fr mb nb ->
  forall a, ctrl_lay_block_c.ctrl_lay_block_shadow_R S0 (ly_F lyc) p f md g fr mb nb a ->
    B.ACtlRtC.cut_shadow B ly S a \/ B.ACtlRtC.img_shadow a.
Proof.
  intros ly S W m mdl lyc Sc S0 p f md g fr mb nb HAR Hsub Eab EF Hwlo Hwhi Hp Hhome HNI (Rf & Rtm & Rg & Rmd) a HR.
  pose proof HAR as (M & _).
  pose proof (lo_top _ (am_layout _ _ _ _ M)) as (_ & _ & _ & _ & PLO & PHI & _).
  unfold page_aligned in PLO, PHI.
  unfold ctrl_lay_block_c.ctrl_lay_block_shadow_R in HR.
  destruct HR as [Hw | [H0 | [H1 | [Hb | [Hf | [(Hk & Ht) | [(Hg & Hal & Hgw) | [(Hk & Hmd & Hm) |
    [(Hk & Hmd & Hbb & Hh & Hr & Hn) | [(Hk & Hj) | (Hk & Hj)]]]]]]]]]].
  - (* the window: (Z) at the machine stack *)
    left. unfold B.ACtlRtC.cut_shadow. right; right; left.
    exists (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly).
    split; [unfold zero_shadow_ranges; left; reflexivity|]. cbn [fst snd].
    exact (lay_shw_stack _ _ S0 ctrl_lay_block_c.CTRL_LAY_BLOCK_K a PLO PHI Hwlo Hwhi
             ltac:(unfold ctrl_lay_block_c.CTRL_LAY_BLOCK_K; lia) Hw).
  - (* the class-0 block: (A) *)
    left. unfold B.ACtlRtC.cut_shadow. right; right; right. rewrite EF.
    exact (lay_shw_fs (ly_F lyc) 0 a (or_introl eq_refl) H0).
  - (* the class-1 block: (A) *)
    left. unfold B.ACtlRtC.cut_shadow. right; right; right. rewrite EF.
    exact (lay_shw_fs (ly_F lyc) 1 a (or_intror eq_refl) H1).
  - (* the output block, by the home of the byte whose shadow word holds a *)
    destruct (lay_shw_byte (p + 18) 32 a ltac:(lia) ltac:(lia) Hb) as (x & Hx & Hax).
    destruct (Hhome x Hx) as [(Himg & _) | [(b & nn & i & Hin & Hi & Ex) | (cid & pos & Hin & Hc & Hr)]].
    + exfalso. exact (HNI x ltac:(lia) Himg).
    + (* (L) a live block of Sc, a live block of the cut *)
      left. unfold B.ACtlRtC.cut_shadow. right; left. exists b, nn.
      split; [rewrite Eab; exact Hin|].
      exact (lay_shw_blk b (req_size nn) x a ltac:(lia) Hax).
    + (* (F) a frame of Sc, a frame of the cut (64-aligned: the side stack is page-aligned) *)
      left. unfold B.ACtlRtC.cut_shadow. left. exists cid, pos. split; [exact (Hsub cid pos Hin)|].
      destruct (lib.Reusable.YG0s.frame_facts B ly S _ cid pos M (Hsub cid pos Hin)) as (Hc0 & _ & _ & _ & FPA & _).
      unfold page_aligned in FPA.
      assert (EFB : fs_frame_bytes cid = 64 * 2 ^ cid)
        by (unfold fs_frame_bytes; rewrite Z.shiftl_mul_pow2 by lia; lia).
      unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr.
      assert (EFA : frame_addr lyc cid pos = frame_addr ly cid pos) by (unfold frame_addr; rewrite EF; reflexivity).
      rewrite EFA in Hr.
      apply (lay_shw_al64 (frame_addr ly cid pos) (fs_frame_bytes cid) x a); [| | exact Hr | exact Hax].
      * assert (E64 : frame_addr ly cid pos = 64 * (64 * (ly_F ly / 4096) + 576 + cid * 16384 + pos * 2 ^ cid)).
        { pose proof (Z.div_mod (ly_F ly) 4096 ltac:(lia)) as DM. rewrite FPA in DM.
          unfold frame_addr, fs_frame_off. rewrite EFB. change (Z.shiftl 1 kStackSizeLog) with 1048576.
          unfold kFakeFramesOff. lia. }
        rewrite E64, Z.mul_comm. apply Z_mod_mult.
      * rewrite EFB, Z.mul_comm. apply Z_mod_mult.
  - (* f: (I) *)
    right. exact (lay_shw_img f 24 a Rf Hf).
  - (* the template: (I) *)
    right. exact (lay_shw_img _ 32 a (Rtm Hk) Ht).
  - (* the g bytes: (I) *)
    right. exact (lay_shw_img g _ a (Rg Hg Hal) Hgw).
  - (* the model row: (I) *)
    right. exact (lay_shw_img md 296 a (proj1 (Rmd Hk Hmd)) Hm).
  - (* its name: (I) *)
    right. exact (lay_shw_img _ _ a (proj2 (Rmd Hk Hmd) Hbb Hh Hr) Hn).
  - (* JOIN_0014: (I) *)
    right. refine (lay_shw_img _ 32 a _ Hj).
    lazymatch goal with |- lay_img_in ?J _ => let v := eval vm_compute in J in change J with v end.
    unfold lay_img_in, B.Prog.CtrlRo.IMG_LO, B.Prog.CtrlRo.IMG_HI. lia.
  - (* JOIN_0013: (I) *)
    right. refine (lay_shw_img _ 32 a _ Hj).
    lazymatch goal with |- lay_img_in ?J _ => let v := eval vm_compute in J in change J with v end.
    unfold lay_img_in, B.Prog.CtrlRo.IMG_LO, B.Prog.CtrlRo.IMG_HI. lia.
Qed.

(* ---- 2g. (1) every Section CUTS fact at the normalized memory of a cut ---- *)
Lemma lay_cut_ctx : forall RLO RHI STK sp0 FP ly S W0 mem0 md0 own lyc Sc ly' S' (W' : world SEGS) mem' md' k
    (regs : bvmap 5 word) (p f md g : Z) (fr ob tb mb nb gb : list byte) (pos : Z),
  ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 ((1, pos) :: own) ly' S' W' mem' md' k ->
  frames S' = (1, pos) :: frames Sc -> ablocks B ly' S' = ablocks B lyc Sc -> ly_F ly' = ly_F lyc ->
  sp0 - STK <= spZ regs - C_ctrl_lay_block.CTRL_LAY_BLOCK_STK -> spZ regs <= sp0 ->
  rget regs 4 = w64 (as_tp B) ->
  arodata_okS SEGS B RLO RHI (aview SEGS (w_H W') mem') ->
  C_ctrl_lay_block.tctrl_lay_block_home B lyc Sc (p + 18) 32 ->
  (forall a, p + 18 <= a < p + 50 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
  0 <= f -> f + 24 <= B.Prog.asan_stack_malloc_c.ASAN_GT ->
  lay_pure (rget regs 2) p f md g (ly_F lyc) fr tb mb nb gb ->
  lay_data W' mem' p f md g fr ob tb mb nb gb ->
  lay_img_ro f md g fr mb nb ->
  lay_ctx (rget regs 2) (rget regs 4) (B.MemNorm.normalize B.Img0.rsegs mem') p f md g (ly_F lyc) fr ob tb mb nb gb
    (B.ProgBridge.RNG_W (w_H W')).
Proof.
  intros RLO RHI STK sp0 FP ly S W0 mem0 md0 own lyc Sc ly' S' W' mem' md' k regs p f md g fr ob tb mb nb gb pos
    HJ Efr Eab EF Hlo Hhi Htp HRO Hhome HAWR Hf0 Hf1 HP HD HIR.
  destruct (lay_cut_facts STK sp0 FP ly S W0 mem0 md0 own lyc Sc ly' S' W' mem' md' k regs p pos HJ Efr Eab EF Hlo Hhi
              HAWR) as (HNI & _ & _).
  pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _ & _).
  pose proof Hstk as (Hal0 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (EK : C_ctrl_lay_block.CTRL_LAY_BLOCK_STK = 4512) by reflexivity.
  assert (EKc : ctrl_lay_block_c.CTRL_LAY_BLOCK_K = 4512) by reflexivity.
  rewrite EK in Hlo.
  pose proof (@lib.Reusable.YM05.alloc_ceiling_value rc) as [[Hc0 _] _].
  assert (Hspr : 0 <= spZ regs < 2 ^ 64) by (unfold spZ; apply bv_unsigned_in_range).
  assert (Hsub : forall c q, In (c, q) (frames Sc) -> In (c, q) (frames S')) by (intros c q H; rewrite Efr; right; exact H).
  assert (Hin1 : In (1, pos) (frames S')) by (rewrite Efr; left; reflexivity).
  pose proof HAR as (M & _).
  destruct (lib.Reusable.YG0s.frame_facts B ly' S' _ 1 pos M Hin1) as (_ & _ & _ & _ & FPA & _).
  unfold page_aligned in FPA.
  pose proof HP as (Rp & Rf & Rmd & Rg & SP16 & DJ1 & DJ2 & DJ3 & DJ3g & DJ3m & F8 & F24 & FL & K9 & AOL & TM & P0
    & P50 & DB1 & DB2 & DB3 & DBN & MDPp & GPp & AP50 & ARDJ & FPT & FPG & FPM).
  pose proof HD as (FBr & BLKr & AFr & ARr & MDr & GPr & ATMr & Vrow & Vrowsh & Vrec & Vrecsh & Vtm & Vg).
  (* the runtime facts and the window at the cut *)
  destruct (lay_rt_facts B LAWS CTS RLO RHI ly' S' W' mem' md' HAR
              (B.ProgWorld.arodata_okP_of_S B RLO RHI RLO RHI _ HRO (Z.le_refl _) (Z.le_refl _)))
    as (Hro & AC0 & SRC & SRI).
  assert (Hwlo : ly_stk_lo ly' <= spZ regs - 4512) by (rewrite Eslo; lia).
  assert (Hwhi : spZ regs <= ly_stk_hi ly') by (rewrite Eshi; lia).
  (* SR0, route (C): the run's region at the cut, inside the cut's own shadow regions *)
  pose proof (B.ShadowRwOn.shadow_rw_on_mono _ _ _
                (lay_RR_cover ly' S' W' mem' md' lyc Sc (spZ regs) p f md g fr mb nb HAR Hsub Eab EF
                   ltac:(rewrite EKc; exact Hwlo) Hwhi ltac:(pose proof HP as (Rp0 & _); lia) Hhome HNI HIR)
                (B.ShadowRwOn.shadow_rw_on_union _ _ _ SRC SRI)) as SR0.
  destruct (lay_win_facts B LAWS ly' S' W' mem' md' (spZ regs - 4512) (spZ regs) HAR Hro
              Hwlo ltac:(lia) Hwhi ltac:(intros a Ha; apply Hpres; lia)) as (ST0 & AW0 & HHM & HAE & Hcw).
  replace (spZ regs - (spZ regs - 4512)) with 4512 in AW0 by lia.
  (* the thread pointer *)
  assert (ETP : bv_unsigned (rget regs 4) = B.AsanRT.RT_TP).
  { rewrite Htp. unfold w64. rewrite (B.ProgWorld.as_tp_RT_TP B CTS). apply B.ProgWorld.pws_u64.
    unfold B.AsanRT.RT_TP. lia. }
  (* the block is off the image, so no byte of it is read-only *)
  assert (BRO : forall i, 0 <= i < Z.of_nat (lib.Lib.Cells.cells_size [lib.Lib.Cells.CB 32 ob]) ->
                  lib.Lib.Mem.ro_addr B.Img0.rsegs (lib.Lib.Mem.wa (p + 18 + i)) = false).
  { intros i Hi. change (Z.of_nat (lib.Lib.Cells.cells_size [lib.Lib.Cells.CB 32 ob])) with 32 in Hi.
    apply lay_ro_false; [lia | apply HNI; lia]. }
  unfold lay_ctx. cbv zeta. rewrite ETP, EKc. change (bv_unsigned (rget regs 2)) with (spZ regs).
  split; [exact Rp|]. split; [exact Rf|]. split; [exact Rmd|]. split; [exact Rg|]. split; [exact SP16|].
  split; [exact ST0|].
  split; [exact DJ1|]. split; [exact DJ2|]. split; [exact DJ3|]. split; [exact DJ3g|]. split; [exact DJ3m|].
  split; [exact F8|]. split; [exact F24|]. split; [exact FL|].
  split; [exact (B.MemNorm.bytes_at_normalize B.Img0.rsegs mem' f fr Hro FBr)|].
  split; [exact K9|]. split; [exact AOL|]. split; [exact TM|]. split; [exact P0|]. split; [exact P50|].
  split; [exact (B.MemNormTr.rw_cells_normalize mem' (p + 18) _ Hro BRO BLKr)|].
  split; [exact DB1|]. split; [exact DB2|]. split; [exact DB3|]. split; [exact DBN|].
  split.
  { intros Hk Hmd. destruct (MDPp Hk Hmd) as (M8 & ML & Mname). destruct (MDr Hk Hmd) as (MB & MA & MN).
    split; [exact M8|]. split; [exact ML|]. split; [exact (B.MemNorm.bytes_at_normalize B.Img0.rsegs mem' md mb Hro MB)|].
    intros Hbb Hh Hr. destruct (MN Hbb Hh Hr) as (NB & _).
    split; [exact (Mname Hbb Hh Hr) | exact (B.MemNorm.bytes_at_normalize B.Img0.rsegs mem' _ nb Hro NB)]. }
  split.
  { intros Hg Hal. destruct (GPp Hg Hal) as (GL & GDJ & _). destruct (GPr Hg Hal) as (GB & _).
    split; [exact GL|]. split; [exact (B.MemNorm.bytes_at_normalize B.Img0.rsegs mem' g gb Hro GB) | exact GDJ]. }
  split; [exact (B.MemNorm.mem_inv_normalize B.Img0.rsegs mem')|].
  split; [exact AC0|]. split; [exact SR0|]. split; [exact HHM|]. split; [exact HAE|]. split; [exact AW0|].
  split; [exact (B.MemNormTr.addressable_normalize mem' f 24 Hro AFr)|].
  split; [exact (B.MemNormTr.addressable_normalize mem' (p + 18) 32 Hro ARr)|].
  split; [exact AP50|]. split; [exact ARDJ|].
  split; [intros Hk; exact (B.MemNormTr.addressable_normalize mem' _ 32 Hro (ATMr Hk))|].
  split.
  { intros Hg Hal. destruct (GPr Hg Hal) as (_ & GA). destruct (GPp Hg Hal) as (_ & _ & A1 & A2 & A3).
    split; [exact (B.MemNormTr.addressable_normalize mem' g _ Hro GA)|]. split; [exact A1|]. split; [exact A2 | exact A3]. }
  split.
  { intros Hk Hmd. destruct (MDr Hk Hmd) as (_ & MA & MN).
    split; [exact (B.MemNormTr.addressable_normalize mem' md 296 Hro MA)|].
    intros Hbb Hh Hr. destruct (MN Hbb Hh Hr) as (_ & NA). exact (B.MemNormTr.addressable_normalize mem' _ _ Hro NA). }
  split.
  { rewrite <- EF. exact (lay_fp0_facts ly' S' W' mem' md' lyc Sc (spZ regs) p f HAR Hro Hsub Eab EF ltac:(lia)
                            ltac:(lia) Hf0 Hf1 Hhome HNI). }
  split; [exact FPT|]. split; [exact FPG|]. split; [exact FPM|].
  split; [rewrite <- EF; exact (lay_tls0_facts ly' S' W' mem' md' (spZ regs - 4512) (spZ regs) HAR Hro Hwlo Hwhi)|].
  split; [exact (B.ProgBridge.rng_bytes_RNG_W _)|].
  split.
  { pose proof (B.ProgBridge.rng_of_visible _ _ _ (B.ProgBridge.img_vis_W W')) as R.
    unfold B.Prog.ImgBounds.IMG_LO, B.Prog.ImgBounds.IMG_HI in R. exact R. }
  split.
  { apply B.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|].
    intros a Ha. exact (proj1 (Hpres a ltac:(lia))). }
  split.
  { destruct (win_sh_vis LAWS ly' S' W' mem' md' (spZ regs - 4512) 4512 HAR Hwlo ltac:(lia) ltac:(lia)) as [E0 | V];
      [lia|].
    apply B.ProgBridge.rng_of_visible.
    unfold ctrl_lay_block_c.sh_lo, ctrl_lay_block_c.sh_len.
    unfold B.Prog.rng_asan.sh_al8_lo, B.Prog.rng_asan.sh_al8_hi in V. exact V. }
  split.
  { rewrite <- EF. apply B.ProgBridge.rng_of_visible. exact (lay_F_vis ly' S' W' mem' md' HAR). }
  split.
  { rewrite <- EF. apply B.ProgBridge.rng_of_visible. apply (lay_Fsh_vis ly' S' W' mem' md' HAR).
    Z.div_mod_to_equations. lia. }
  split; [exact (B.ProgBridge.rng_of_visible _ _ _ Vrow)|].
  split; [exact (B.ProgBridge.rng_of_visible _ _ _ Vrowsh)|].
  split; [exact (B.ProgBridge.rng_of_visible _ _ _ Vrec)|].
  split; [exact (B.ProgBridge.rng_of_visible _ _ _ Vrecsh)|].
  split.
  { unfold ctrl_lay_blockF_on.rguard. destruct (Z.eq_dec (RcLay.ly_k fr) 2) as [E2 | N2]; [right | left; exact N2].
    destruct (Vtm E2) as (V1 & V2). split; [exact (B.ProgBridge.rng_of_visible _ _ _ V1)|].
    unfold ctrl_lay_block_c.sh_cover. exact (B.ProgBridge.rng_of_visible _ _ _ V2). }
  { unfold ctrl_lay_blockF_on.rguard. destruct (Z.eq_dec g 0) as [E0 | N0]; [left; exact E0|].
    destruct (Z.eq_dec (RcLay.ly_al fr) 0) as [A0 | NA0]; [right; left; exact A0|]. right; right.
    destruct (Vg N0 NA0) as (V1 & V2). split; [exact (B.ProgBridge.rng_of_visible _ _ _ V1)|].
    unfold ctrl_lay_block_c.sh_cover. exact (B.ProgBridge.rng_of_visible _ _ _ V2). }
Qed.

End GC.
