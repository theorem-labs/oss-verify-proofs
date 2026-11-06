(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3060 of its 3101 lines of code are new or changed and 207 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/reac_box_catalogue_match.v, with its module paths and numbers changed; 1731 of its 2038 lines of code are new or changed and 2794 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/C_reac_box_catalogue_matchLibW.v, with its module paths and module names changed; 345 of its 371 lines of code are new or changed and 2012 lines of the source are left out. *)
(* lib/B/Prog/C_reac_box_catalogue_matchPfV.v -- fuzz_ctrl image B (asan-ubsan, libreac v1.9.0): one shared lemma of
   pb_reac_box_catalogue_match (the cgif-form world walk of reac_box_catalogue_match, 0x84e40), the footprint's
   side-stack visibility from AR.  Every re-based stretch 2-6 of C_reac_box_catalogue_matchLib.v /
   C_reac_box_catalogue_matchLibW.v takes, at RNG := ProgBridge.RNG_W (w_H W), rng premises over the side stack's
   header [FS, fs_frame FS 0 0) and over every range of fp_w [0; 1; 2] FS (the class-0/1/2 hint words, flag bytes,
   frames and the frames' shadow), FS := ly_F ly.  cmPf_fs_vis states them as visibility facts at any state with AR.
   It Requires no other piece of the glue (PfI / PfB / PfZ), so the middle piece and the last piece both use it.
   rule 24: no function proved; a bridge lemma over the core's world.

   PROOF (Qed lemmas used by name):
     the side-stack bytes (header, hints, flags, frames)  <- B.ProgWorld_Fs.pw_F_present: AR's am_areas entry
                                                             (AF 0, kFakeStackSize) (YG0n.v:137), every byte present;
     the frames' shadow                                   <- AR's am_areas entry
                                                             (ASh (AF kFakeFramesOff), (kFakeStackSize - kFakeFramesOff) / 8)
                                                             (YG0n.v:139): every byte the view reads, so visible
                                                             (B.ProgWorldVisFrame.vis_of_aview).
   CANDIDATE FOR lib/B/ProgWorld.v (owner a Theorem Labs lane): ProgWorld's frame_vis covers live frames only; this lemma covers
   the whole class-0/1/2 frame areas and their shadow, which every fake-stack stretch's footprint names. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
(* The six collided modules by the unambiguous lib.Reusable path (porter's gate). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YM05.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK04 YA0n YG00 YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.asan_stack_malloc_c B.Prog.RcAsanFP B.AsanRT B.Img0
  B.ProgBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ProgWorld_Fs B.ProgWorldVisFrame.
(* for cmPf_base_of_AR *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YCbq YF0m YI00 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ProgWorld B.ProgWorldRtC B.ProgWorldShadow
  B.Prog.CtrlBase B.Prog.bcmp_wrap_c B.Prog.memcmp_c B.Prog.reac_ctrl_parse_c B.Prog.reac_box_catalogue_match_c
  B.Prog.reac_box_catalogue_match B.Prog.reac_box_catalogue_matchF_on B.Prog.C_reac_box_catalogue_matchLib
  B.Prog.C_reac_box_catalogue_match B.ProgWorldBlkApart B.ProgWorldTlsApart.
(* route (C): ctl_rt_C's regions, and the narrowed shadow fact of reac_box_catalogue_match's _on run *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ShadowRwOn B.ACtlRtC B.ProgWorldCtlRtC B.Prog.CtrlRo
  B.Prog.rng_asan B.Prog.sh_word_on B.Prog.asan_stack_malloc_c_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Mem PropExec Image.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcLay.
Import ListNotations.
Local Open Scope Z_scope.

(* ctrl's side-stack geometry as numerals (C_reac_box_catalogue_matchLibW.v's fs_num, image-independent). *)
Local Ltac cmV_fs_num :=
  unfold B.Prog.asan_stack_malloc_c.fs_hint, B.Prog.asan_stack_malloc_c.fs_flag, B.Prog.asan_stack_malloc_c.fs_frame,
    B.Prog.asan_stack_malloc_c.fs_M, B.Prog.asan_stack_malloc_c.fs_B in *;
  cbn [Z.of_nat Pos.of_succ_nat] in *;
  repeat first [ change (2 ^ 15) with 32768 in * | change (2 ^ (15 - 0)) with 32768 in *
               | change (2 ^ (14 - 0)) with 16384 in * | change (2 ^ (15 - 1)) with 16384 in *
               | change (2 ^ (14 - 1)) with 8192 in * | change (2 ^ (15 - 2)) with 8192 in *
               | change (2 ^ (14 - 2)) with 4096 in * | change (2 ^ 14) with 16384 in *
               | change (2 ^ 13) with 8192 in * | change (2 ^ 12) with 4096 in *
               | change (2 ^ 20) with 1048576 in * | change (2 ^ 0) with 1 in * | change (2 ^ 1) with 2 in *
               | change (2 ^ 2) with 4 in * ].

Section V.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : lib.Reusable.YG0f.asyms.

Lemma cmPf_fs_vis : forall ly S (W : lib.Reusable.YA0n.world B.Img0.rsegs) (m : word -> option byte) md,
  lib.Reusable.YG0n.AR B.Img0.rsegs B ly S W m md ->
  B.ProgBridge.range_visible (lib.Reusable.YA0n.w_H W) (lib.Reusable.YG0f.ly_F ly)
    (B.Prog.asan_stack_malloc_c.fs_frame (lib.Reusable.YG0f.ly_F ly) 0 0 - lib.Reusable.YG0f.ly_F ly) /\
  Forall (fun iv : Z * Z => B.ProgBridge.range_visible (lib.Reusable.YA0n.w_H W) (fst iv) (snd iv - fst iv))
    (B.Prog.RcAsanFP.fp_w [0%nat; 1%nat; 2%nat] (lib.Reusable.YG0f.ly_F ly)).
Proof.
  intros ly S W m md HAR.
  pose proof HAR as (M & L & _).
  pose proof (lib.Reusable.YG0n.am_layout _ _ _ _ M) as LO.
  pose proof (proj1 (Forall_forall _ _) (lib.Reusable.YG0f.lo_app _ LO) _ (lib.B.ProgWorld_Fs.pw_F_in_owned ly)) as F1.
  cbn [fst snd] in F1. destruct (lib.B.ProgWorld_Fs.pw_ext_range _ _ F1) as [F0 F2].
  remember (lib.Reusable.YG0f.ly_F ly) as FS eqn:EFS. try rewrite <- EFS in F0. try rewrite <- EFS in F2.
  (* every side-stack byte: present (pw_F_present), so visible *)
  assert (VFS : forall lo len, FS <= lo -> lo + len <= FS + lib.Reusable.YG0f.kFakeStackSize -> 0 <= len ->
                  B.ProgBridge.range_visible (lib.Reusable.YA0n.w_H W) lo len).
  { intros lo len H1 H2 H3. unfold lib.Reusable.YG0f.kFakeStackSize in *.
    split; [lia|]. split; [change (2 ^ 64) with 18446744073709551616; lia|].
    intros a Ha.
    assert (Ha' : lib.Reusable.YG0f.ly_F ly <= a < lib.Reusable.YG0f.ly_F ly + lib.Reusable.YG0f.kFakeStackSize)
      by (rewrite <- EFS; unfold lib.Reusable.YG0f.kFakeStackSize; lia).
    exact (proj1 (lib.B.ProgWorld_Fs.pw_F_present B ly S W m md a HAR Ha')). }
  (* the frames' shadow: am_areas' entry (ASh (AF kFakeFramesOff), (kFakeStackSize - kFakeFramesOff) / 8) *)
  pose proof (lib.Reusable.YG0n.am_areas _ _ _ _ M) as AA. unfold lib.Reusable.YG0n.aareas in AA.
  apply Forall_app in AA as [_ AA]. apply Forall_app in AA as [_ AA]. apply Forall_app in AA as [_ AA].
  apply Forall_cons_iff in AA as [_ AA]. apply Forall_cons_iff in AA as [_ AA].
  apply Forall_cons_iff in AA as [_ AA]. apply Forall_cons_iff in AA as [_ AA].
  apply Forall_cons_iff in AA as [_ AA]. apply Forall_cons_iff in AA as [ASH _].
  assert (VSH : forall lo len,
             lib.Reusable.YG0f.shadow_addr (FS + lib.Reusable.YG0f.kFakeFramesOff) <= lo ->
             lo + len <= lib.Reusable.YG0f.shadow_addr (FS + lib.Reusable.YG0f.kFakeFramesOff) +
                         (lib.Reusable.YG0f.kFakeStackSize - lib.Reusable.YG0f.kFakeFramesOff) / 8 -> 0 <= len ->
             B.ProgBridge.range_visible (lib.Reusable.YA0n.w_H W) lo len).
  { intros lo len H1 H2 H3.
    assert (Hb : 0 <= lib.Reusable.YG0f.shadow_addr (FS + lib.Reusable.YG0f.kFakeFramesOff) /\
                 lib.Reusable.YG0f.shadow_addr (FS + lib.Reusable.YG0f.kFakeFramesOff) +
                   (lib.Reusable.YG0f.kFakeStackSize - lib.Reusable.YG0f.kFakeFramesOff) / 8 <= 2 ^ 64).
    { unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF, lib.Reusable.YG0f.kFakeFramesOff,
        lib.Reusable.YG0f.kFakeStackSize in *.
      change (2 ^ 64) with 18446744073709551616. Z.div_mod_to_equations. lia. }
    split; [lia|]. split; [lia|].
    intros a Ha.
    pose proof (ASH (a - lib.Reusable.YG0f.shadow_addr (FS + lib.Reusable.YG0f.kFakeFramesOff))
                  ltac:(cbn [snd]; lia)) as Hv.
    cbn [fst lib.Reusable.YG0f.aeval] in Hv. rewrite <- EFS in Hv.
    replace (lib.Reusable.YG0f.shadow_addr (FS + lib.Reusable.YG0f.kFakeFramesOff) +
             (a - lib.Reusable.YG0f.shadow_addr (FS + lib.Reusable.YG0f.kFakeFramesOff))) with a in Hv by lia.
    exact (lib.B.ProgWorldVisFrame.vis_of_aview B.Img0.rsegs W m a Hv). }
  split.
  - apply VFS; cmV_fs_num; unfold lib.Reusable.YG0f.kFakeStackSize; lia.
  - unfold B.Prog.RcAsanFP.fp_w, B.Prog.RcAsanFP.fp_w1. apply Forall_forall. intros iv Hin.
    cbn [flat_map app In] in Hin.
    cmV_fs_num.
    repeat (destruct Hin as [<- | Hin]); try destruct Hin; cbn [fst snd];
      first
        [ apply VFS; unfold lib.Reusable.YG0f.kFakeStackSize; lia
        | apply VSH;
          unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF,
            lib.Reusable.YG0f.kFakeFramesOff, lib.Reusable.YG0f.kFakeStackSize;
          Z.div_mod_to_equations; lia ].
Qed.

(* ==== cmPf_base_of_AR: the base facts of every re-based stretch of C_reac_box_catalogue_matchLib.v (cmBase, its CLAUSE
   MAP) at ANY state with AR, from the ProgWorld layer: the ONE shared "cmBase from AR" lemma of the glue.
   PROVED statements, used by name: ProgWorldCtlRtC.ctl_rt_C_of_AR (1: asan_cells and ro_agree, its first and fourth
   conjuncts) with cmPf_shrwR_of_AR (1: the run's region R, from its cut_shadow / img_shadow conjuncts),
   ProgWorldShadow.ctl_stack_shadow_of_AR (2), ProgWorld_Fs.ctl_fp_of_AR (3), ProgWorldRtC.RT_used_of_AR_C (5),
   ProgWorld.ctl_out_bytes and
   ProgWorldShadow.ctl_block_shadow_of_AR (6), ProgWorld.aview_vis_mrd / ProgWorldVisFrame.vis_of_aview (7),
   ProgWorldShadow.ctl_zshadow_of_AR (8), ProgWorldShadow.ctl_gshadow_of_AR (9; ProgWorld's AMENDED
   ctl_gshadow_of_AR_stmt, with the image bound), ProgWorld.as_tp_RT_TP / as_tsd_TSD.
   ctl_block_apart_fs_stmt (3: the record apart from the side stack) is PROVED: ProgWorldBlkApart.ctl_block_apart_fs.
   fp_tls_apart_stmt (4) is PROVED: ProgWorldTlsApart.fp_tls_apart.
   No ProgWorld statement is a premise (route (C): neither AR_states_vis0_shadow nor AR_states_owned_ro).
   The core bundle law CtrlTSyms B is a premise (it fixes the rows: the table's zero-shadow range is Tfib_zero_shadow's
   entry 37, (0x9f620, 0xcb8) = the table's data [0x9f620, 0xa02d8) only, never its redzone; the BC's partial-granule
   row is Tfib_const_shadow's entry 15, z1 (ANum 0x7fffc240) 7).  The read-only view is arodata_okP at the state
   (APostBase.arodata_ok_journalP keeps it along a journal; at the entry ProgWorld.arodata_okP_of_S). ==== *)

(* A byte of an image_bytes read is the segments' rom byte. *)
Lemma cmV_image_nth : forall (sg : list Segment) n A bs, lib.Lib.Image.image_bytes sg A n = Some bs ->
  forall i, (i < n)%nat -> lib.Lib.PropExec.seg_rom sg (lib.Lib.Mem.wa (A + Z.of_nat i)) = nth_error bs i.
Proof.
  intros sg. induction n as [|n IH]; intros A bs H i Hi; [lia|].
  cbn [lib.Lib.Image.image_bytes] in H.
  destruct (lib.Lib.PropExec.seg_rom sg (lib.Lib.Mem.wa A)) as [b|] eqn:E; [|discriminate H].
  destruct (lib.Lib.Image.image_bytes sg (A + 1) n) as [bs'|] eqn:E2; [|discriminate H].
  injection H as <-. destruct i as [|i].
  - cbn [nth_error]. rewrite Z.add_0_r. exact E.
  - cbn [nth_error]. rewrite <- (IH (A + 1) bs' E2 i ltac:(lia)). f_equal. f_equal. lia.
Qed.

(* fp's write-apart premise for a stack window above the allocator's extents: the thread cells (image cells, the TSD at
   0x5fd9f8, C + 152 / T + 48 / DB + 24 in the owned extents ly_C / ly_T / ly_D) and the side stack's header lie below
   the window. *)
Lemma cmV_dj_win_tls : forall (Sp FS tsd C T D : Z),
  0x7fff7f800000 <= Sp - 9136 -> Sp < 2 ^ 64 -> tsd = 0x5fd9f8 ->
  4096 <= C -> C + 256 <= Sp - 9136 -> 4096 <= T -> T + 4096 <= Sp - 9136 -> 4096 <= D -> D + 4096 <= Sp - 9136 ->
  0 <= FS -> FS + 36864 <= Sp - 9136 ->
  B.Prog.RcAsanFP.fp_dj (lib.B.Prog.reac_box_catalogue_match_c.reac_box_catalogue_match_W Sp)
    (B.Prog.RcAsanFP.fp_tls B.AsanRT.RT_TP (Z_to_bv 64 (B.AsanRT.RT_TP + 32)) (Z_to_bv 64 tsd) (Z_to_bv 64 C)
       (Z_to_bv 64 T) (Z_to_bv 64 D) 0 ++ (FS, B.Prog.asan_stack_malloc_c.fs_frame FS 0 0) :: nil).
Proof.
  intros Sp FS tsd C T D H1 H2 Htsd HC0 HC1 HT0 HT1 HD0 HD1 HF0 HF1. subst tsd.
  assert (P64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  unfold B.Prog.RcAsanFP.fp_dj, lib.B.Prog.reac_box_catalogue_match_c.reac_box_catalogue_match_W,
    lib.B.Prog.reac_box_catalogue_match_c.CM_K, B.Prog.RcAsanFP.fp_tls.
  rewrite !lib.B.ProgWorld.pws_u64 by (rewrite P64; unfold B.AsanRT.RT_TP; lia).
  apply Forall_forall. intros w Hw. destruct Hw as [<- | []].
  apply Forall_forall. intros d Hd. cbn [In app] in Hd.
  repeat (destruct Hd as [<- | Hd]); try destruct Hd;
    unfold lib.Prog.RcLay.ly_dj; cbn [fst snd];
    unfold B.AsanRT.RT_TP, B.Prog.asan_stack_malloc_c.TLS_INDEX, B.Prog.asan_stack_malloc_c.REAL_TLS_GET_ADDR,
      B.Prog.asan_stack_malloc_c.TSD_KEY_INITED, B.Prog.asan_stack_malloc_c.TSD_KEY, B.Prog.asan_stack_malloc_c.GOT_CF,
      B.Prog.asan_stack_malloc_c.CF, B.Prog.asan_stack_malloc_c.GOT_VERBOSITY, B.Prog.asan_stack_malloc_c.VERBOSITY,
      B.Prog.asan_stack_malloc_c.DTLS_TPOFF, B.Prog.asan_stack_malloc_c.fs_frame;
    cbn [Z.of_nat]; lia.
Qed.

(* fp's data-apart premise for the record [f, f + 50) of a live block apart from the side stack (ctl_block_apart_fs):
   the side stack's class bytes are apart by that, the frames' shadow bytes because a block lies in application
   memory and the shadow does not (in_app). *)
Lemma cmV_dj_rec_fs : forall (f rs FS CEIL : Z),
  50 <= rs -> 4096 <= f ->
  (f + rs <= 0x7fff7000 \/ (0x10007fff8000 <= f /\ f + rs <= CEIL)) -> CEIL <= 0x7fffff800000 ->
  (f + rs <= FS \/ FS + 11571200 <= f) -> 4096 <= FS -> FS + 11571200 <= 0x7fffff800000 ->
  B.Prog.RcAsanFP.fp_dj ((f, f + 50) :: nil) (B.Prog.RcAsanFP.fp_w [0%nat; 1%nat; 2%nat] FS).
Proof.
  intros f rs FS CEIL Hrs Hf Happ HC Hap HF0 HF1.
  unfold B.Prog.RcAsanFP.fp_dj, B.Prog.RcAsanFP.fp_w, B.Prog.RcAsanFP.fp_w1.
  apply Forall_forall. intros w Hw. destruct Hw as [<- | []].
  apply Forall_forall. intros d Hd. cbn [flat_map app In] in Hd.
  cmV_fs_num.
  repeat (destruct Hd as [<- | Hd]); try destruct Hd;
    unfold lib.Prog.RcLay.ly_dj; cbn [fst snd];
    unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; Z.div_mod_to_equations; lia.
Qed.

(* Core: the world's laws. *)
Hypothesis LAWS : lib.Reusable.YG0d.AR_laws B.Img0.rsegs B.

(* ==== Route (C) (GLUESW-BRIEF A3): the narrowed shadow fact of reac_box_catalogue_match's _on run,
   shadow_rw_on (reac_box_catalogue_match_shadow_R f len Sp FS) m, at ANY state with AR, from ctl_rt_C
   (B.ProgWorldCtlRtC.ctl_rt_C_of_AR: no AR_states_vis0_shadow, no AR_states_owned_ro).  No universal shadow_rw.
   cmPf_R_cut is the region inclusion R a -> cut_shadow B ly S a \/ img_shadow a, part by part
   (ROUTEC-P1-RESULT.md (c)):
     (W)  [shadow_addr (Sp - 9136), shadow_addr Sp)  <- cut_shadow's (Z) disjunct, zero_shadow_ranges' stack entry
          (ly_stk_lo, ly_stk_hi - ly_stk_lo) (YG0n.v:188-189); exact at the top because ly_stk_lo is page-aligned
          (layout_ok's lo_top, YG0f.v:322-324);
     (FS) asan_stack_malloc_shadow_R FS c, c <= 2   <- the frames-area disjunct (the 4th), FS = ly_F ly: the class-c
          block [shadow_addr (FS + 36864 + c * 2^20), + 131072) lies in [shadow_addr (FS + kFakeFramesOff),
          shadow_addr (FS + kFakeStackSize));
     (D)  sh_word_on f 50                            <- the live-block disjunct (L), (f, n) in ablocks, 50 <= req_size n;
     (T)  sh_word_on CM_T 3256, (BC) sh_word_on REAC_CTRL_PARSE_BC 6  <- img_shadow: both word covers shadow bytes of
          [IMG_LO, IMG_HI) (0x9f620 and 0x21200 lie in [0x10000, 0x5fe000)). ==== *)
Lemma cmPf_R_cut : forall ly S (f len Sp FS : Z),
  lib.Reusable.YG0f.page_aligned (lib.Reusable.YG0f.ly_stk_lo ly) ->
  lib.Reusable.YG0f.ly_stk_lo ly <= Sp - 9136 -> Sp <= lib.Reusable.YG0f.ly_stk_hi ly ->
  FS = lib.Reusable.YG0f.ly_F ly ->
  (50 <= len -> exists n, In (f, n) (lib.Reusable.YG0d.ablocks B ly S) /\ 50 <= lib.Reusable.YG00.req_size n) ->
  forall a, lib.B.Prog.reac_box_catalogue_match_c.reac_box_catalogue_match_shadow_R f len Sp FS a ->
    B.ACtlRtC.cut_shadow B ly S a \/ B.ACtlRtC.img_shadow a.
Proof.
  intros ly S f len Sp FS Hal Hslo Hshi EFS Hlive a HR.
  unfold lib.Reusable.YG0f.page_aligned in Hal.
  unfold lib.B.Prog.reac_box_catalogue_match_c.reac_box_catalogue_match_shadow_R in HR.
  destruct HR as [HW | [(c & Hc & HFS) | (Hl & [HD | [HT | HBC]])]].
  - (* (W): the (Z) disjunct at the stack entry of zero_shadow_ranges *)
    left. right; right; left.
    exists (lib.Reusable.YG0f.ly_stk_lo ly, lib.Reusable.YG0f.ly_stk_hi ly - lib.Reusable.YG0f.ly_stk_lo ly).
    split; [unfold lib.Reusable.YG0n.zero_shadow_ranges; left; reflexivity|].
    cbn [fst snd].
    unfold lib.B.Prog.reac_box_catalogue_match_c.CM_K, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in HW.
    unfold lib.Reusable.YG0v.shadow_of_addr, lib.Reusable.YG0f.SHADOW_OFF.
    Z.div_mod_to_equations. lia.
  - (* (FS): the frames-area disjunct *)
    left. right; right; right.
    unfold B.Prog.asan_stack_malloc_c_on.asan_stack_malloc_shadow_R, B.Prog.asan_stack_malloc_c.fs_frame in HFS.
    rewrite Z.mul_0_l, Z.add_0_r in HFS. change (2 ^ 20) with 1048576 in HFS.
    unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in HFS.
    unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF, lib.Reusable.YG0f.kFakeFramesOff,
      lib.Reusable.YG0f.kFakeStackSize.
    subst FS. Z.div_mod_to_equations. lia.
  - (* (D): the live-block disjunct (L) at (f, n) *)
    left. right; left.
    destruct (Hlive Hl) as (n & Hin & Hn).
    exists f, n. split; [exact Hin|].
    unfold B.Prog.sh_word_on.sh_word_on, B.Prog.rng_asan.sh_al8_lo, B.Prog.rng_asan.sh_al8_hi in HD.
    destruct HD as [_ HD].
    unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in HD.
    unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF.
    Z.div_mod_to_equations. lia.
  - (* (T): img_shadow *)
    right. exists (8 * (a - lib.Reusable.YG0f.SHADOW_OFF)).
    unfold B.Prog.sh_word_on.sh_word_on, B.Prog.rng_asan.sh_al8_lo, B.Prog.rng_asan.sh_al8_hi in HT.
    destruct HT as [_ HT].
    unfold lib.B.Prog.reac_box_catalogue_match_c.CM_T, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in HT.
    unfold B.Prog.CtrlRo.IMG_LO, B.Prog.CtrlRo.IMG_HI, lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF.
    Z.div_mod_to_equations. lia.
  - (* (BC): img_shadow *)
    right. exists (8 * (a - lib.Reusable.YG0f.SHADOW_OFF)).
    unfold B.Prog.sh_word_on.sh_word_on, B.Prog.rng_asan.sh_al8_lo, B.Prog.rng_asan.sh_al8_hi in HBC.
    destruct HBC as [_ HBC].
    unfold lib.B.Prog.reac_ctrl_parse_c.REAC_CTRL_PARSE_BC, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in HBC.
    unfold B.Prog.CtrlRo.IMG_LO, B.Prog.CtrlRo.IMG_HI, lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF.
    Z.div_mod_to_equations. lia.
Qed.

(* cmBase's clause (1) in its narrowed form at any state with AR: ctl_rt_C_of_AR's two shadow conjuncts, joined by
   shadow_rw_on_union and narrowed to R by shadow_rw_on_mono over cmPf_R_cut.  The page alignment of ly_stk_lo is
   AR's layout_ok (lo_top). *)
Lemma cmPf_shrwR_of_AR : forall (RLO RHI : Z) ly S (W : lib.Reusable.YA0n.world B.Img0.rsegs)
    (m : word -> option byte) md (f len Sp FS : Z),
  lib.Reusable.YF0m.CtrlTSyms B ->
  lib.Reusable.YG0n.AR B.Img0.rsegs B ly S W m md ->
  B.Prog.CtrlBase.arodata_okP B.Img0.rsegs RLO RHI B (lib.Reusable.YG0n.aview B.Img0.rsegs (lib.Reusable.YA0n.w_H W) m) ->
  lib.Reusable.YG0f.ly_stk_lo ly <= Sp - 9136 -> Sp <= lib.Reusable.YG0f.ly_stk_hi ly ->
  FS = lib.Reusable.YG0f.ly_F ly ->
  (50 <= len -> exists n, In (f, n) (lib.Reusable.YG0d.ablocks B ly S) /\ 50 <= lib.Reusable.YG00.req_size n) ->
  B.ShadowRwOn.shadow_rw_on (lib.B.Prog.reac_box_catalogue_match_c.reac_box_catalogue_match_shadow_R f len Sp FS) m.
Proof.
  intros RLO RHI ly S W m md f len Sp FS HTS HAR HRO Hslo Hshi EFS Hlive.
  destruct (lib.B.ProgWorldCtlRtC.ctl_rt_C_of_AR B HTS LAWS RLO RHI ly S W m md HAR HRO) as (_ & Hcut & Himg & _).
  pose proof HAR as (M & _).
  pose proof (lib.Reusable.YG0f.lo_top _ (lib.Reusable.YG0n.am_layout _ _ _ _ M)) as (_ & _ & _ & _ & Hal & _).
  apply (B.ShadowRwOn.shadow_rw_on_mono (fun a => B.ACtlRtC.cut_shadow B ly S a \/ B.ACtlRtC.img_shadow a)).
  - exact (cmPf_R_cut ly S f len Sp FS Hal Hslo Hshi EFS Hlive).
  - exact (B.ShadowRwOn.shadow_rw_on_union _ _ m Hcut Himg).
Qed.

Lemma cmPf_base_of_AR : forall (RLO RHI : Z) ly S (W : lib.Reusable.YA0n.world B.Img0.rsegs) (m : word -> option byte)
    md (f len Sp : Z) (fb : list byte),
  (* core bundle law *)
  lib.Reusable.YF0m.CtrlTSyms B ->
  (* no ProgWorld statement is a premise: clause (1) is ctl_rt_C_of_AR's (route (C)) *)
  (* the state *)
  lib.Reusable.YG0n.AR B.Img0.rsegs B ly S W m md ->
  B.Prog.CtrlBase.arodata_okP B.Img0.rsegs RLO RHI B (lib.Reusable.YG0n.aview B.Img0.rsegs (lib.Reusable.YA0n.w_H W) m) ->
  (* the table: read-only span and not runtime-owned (C_reac_box_catalogue_match.v:94-95) *)
  RLO <= C_reac_box_catalogue_match.A_CM_TBL ->
  C_reac_box_catalogue_match.A_CM_TBL + C_reac_box_catalogue_match.CM_ROWS <= RHI ->
  (forall a, C_reac_box_catalogue_match.A_CM_TBL <= a < C_reac_box_catalogue_match.A_CM_TBL + C_reac_box_catalogue_match.CM_ROWS ->
     ~ Exists (lib.Reusable.YG0n.in_zr a) (lib.Reusable.YG0f.as_owned_static B) /\
     ~ (lib.Reusable.YG0f.as_errno B <= a < lib.Reusable.YG0f.as_errno B + 4)) ->
  (* the stack window [Sp - 9136, Sp) inside the stack, above the allocation ceiling (astk_ok) *)
  lib.Reusable.YM05.alloc_ceiling <= lib.Reusable.YG0f.ly_stk_lo ly ->
  lib.Reusable.YG0f.ly_stk_lo ly <= Sp - 9136 -> Sp <= lib.Reusable.YG0f.ly_stk_hi ly ->
  (* the record: a live block of at least 50 bytes when len >= 50, its bytes (C_reac_box_catalogue_match.v:88-92) *)
  0 <= f < 2 ^ 64 -> length fb = 50%nat ->
  (50 <= len -> exists n, In (f, n) (lib.Reusable.YG0d.ablocks B ly S) /\ 50 <= lib.Reusable.YG00.req_size n) ->
  (50 <= len -> lib.Reusable.YI00.garr8 B.Img0.rsegs (lib.Reusable.YK04.mrestrict (lib.Reusable.YA0n.w_H W) m) f
                  (map (fun b : byte => bv_unsigned b) fb)) ->
  C_reac_box_catalogue_matchLib.cmBase m (lib.Reusable.YG0d.w64 (lib.Reusable.YG0f.as_tp B)) f len Sp
    (lib.Reusable.YG0f.ly_F ly) fb.
Proof.
  intros RLO RHI ly S W m md f len Sp fb HTS HAR HRO HRLO HRHI Htbl Hceil Hslo Hshi Rf Hfb Hlive Hbytes.
  assert (P64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  pose proof (@lib.Reusable.YG0f.ASAN_CEIL_range rc) as [[CR0 CR1] _].
  unfold lib.Reusable.YG0f.ASAN_CEIL in CR0, CR1.
  pose proof HAR as (M & L & _).
  pose proof (lib.Reusable.YG0n.am_layout _ _ _ _ M) as LO.
  pose proof (lib.Reusable.YG0f.lo_app _ LO) as LA. unfold lib.Reusable.YG0f.owned_extents in LA.
  apply Forall_cons_iff in LA as [_ LA]. apply Forall_cons_iff in LA as [_ LA].
  apply Forall_cons_iff in LA as [ALT LA]. apply Forall_cons_iff in LA as [ALF LA].
  apply Forall_cons_iff in LA as [_ LA]. apply Forall_cons_iff in LA as [_ LA].
  apply Forall_cons_iff in LA as [ALC LA]. apply Forall_cons_iff in LA as [ALD _].
  cbn [fst snd] in ALT, ALF, ALC, ALD.
  unfold lib.Reusable.YG0f.in_app, lib.Reusable.YG0f.ASAN_CEIL, lib.Reusable.YG0f.kLowShadowBeg,
    lib.Reusable.YG0f.kHighMemBeg, lib.Reusable.YG0f.kThreadObjSize, lib.Reusable.YG0f.kFakeStackSize
    in ALT, ALF, ALC, ALD.
  assert (Etp : bv_unsigned (lib.Reusable.YG0d.w64 (lib.Reusable.YG0f.as_tp B)) = B.AsanRT.RT_TP).
  { rewrite (lib.B.ProgWorld.as_tp_RT_TP B HTS). reflexivity. }
  assert (Hcs : Forall (fun c => (c <= 6)%nat) [0%nat; 1%nat; 2%nat]) by (repeat constructor; lia).
  (* (1) route (C): asan_cells and ro_agree from ctl_rt_C_of_AR (its first and fourth conjuncts), the run's region R
     from cmPf_shrwR_of_AR *)
  destruct (lib.B.ProgWorldCtlRtC.ctl_rt_C_of_AR B HTS LAWS RLO RHI ly S W m md HAR HRO) as (AC & _ & _ & RO).
  pose proof (cmPf_shrwR_of_AR RLO RHI ly S W m md f len Sp (lib.Reusable.YG0f.ly_F ly) HTS HAR HRO Hslo Hshi
                eq_refl Hlive) as SR.
  (* (2) ctl_stack_shadow_of_AR *)
  pose proof (lib.B.ProgWorldShadow.ctl_stack_shadow_of_AR B LAWS ly S W m md (Sp - 9136) 9136 HAR Hslo
                ltac:(lia) ltac:(lia)) as AWw.
  pose proof AWw as (AW0 & _ & AW2 & AWb).
  (* (3) ctl_fp_of_AR *)
  assert (FP : B.Prog.RcAsanFP.fp [0%nat; 1%nat; 2%nat] m B.AsanRT.RT_TP (lib.Reusable.YG0f.ly_F ly) (Sp - 9136) Sp
                 (lib.B.Prog.reac_box_catalogue_match_c.reac_box_catalogue_match_W Sp)
                 (lib.B.Prog.reac_box_catalogue_match_c.reac_box_catalogue_match_D f len)).
  { apply (lib.B.ProgWorld_Fs.ctl_fp_of_AR B HTS LAWS ly S W m md [0%nat; 1%nat; 2%nat] (Sp - 9136) Sp _ _ HAR Hcs).
    - unfold B.Prog.asan_stack_malloc_c.FS_SIZE. lia.
    - intros a Ha. pose proof (AWb (a - (Sp - 9136)) ltac:(lia)) as [Hap _].
      replace (Sp - 9136 + (a - (Sp - 9136))) with a in Hap by lia. exact Hap.
    - apply cmV_dj_win_tls.
      + lia.
      + rewrite P64. unfold B.AsanRT.APPMEM_END in AW2. lia.
      + rewrite (lib.Reusable.YG0n.am_tsd _ _ _ _ M). exact (lib.B.ProgWorld.as_tsd_TSD B HTS).
      + lia.
      + lia.
      + lia.
      + lia.
      + lia.
      + lia.
      + lia.
      + lia.
    - unfold lib.B.Prog.reac_box_catalogue_match_c.reac_box_catalogue_match_D.
      destruct (Z.ltb_spec len 50) as [Hl | Hl]; [constructor|].
      destruct (Hlive Hl) as (n & Hin & Hn50).
      destruct (lib.Reusable.YG0d.al_blocks _ _ LAWS ly S W m md f n HAR Hin) as (_ & H4096 & Hcb & Happ & _).
      unfold lib.Reusable.YG0f.in_app, lib.Reusable.YG0f.ASAN_CEIL, lib.Reusable.YG0f.kLowShadowBeg,
        lib.Reusable.YG0f.kHighMemBeg in Happ.
      pose proof (lib.B.ProgWorldBlkApart.ctl_block_apart_fs B LAWS ly S W m md f n HAR Hin) as Hap.
      unfold lib.Reusable.YG0f.kFakeStackSize in Hap.
      apply (cmV_dj_rec_fs f (lib.Reusable.YG00.req_size n) (lib.Reusable.YG0f.ly_F ly) lib.Reusable.YM05.alloc_ceiling);
        lia. }
  (* (4) ProgWorldTlsApart.fp_tls_apart *)
  assert (TL : C_reac_box_catalogue_matchLib.cmRB_tls_dj m (lib.Reusable.YG0d.w64 (lib.Reusable.YG0f.as_tp B))
                 (lib.Reusable.YG0f.ly_F ly) Sp).
  { unfold C_reac_box_catalogue_matchLib.cmRB_tls_dj, lib.B.Prog.reac_box_catalogue_match_c.reac_box_catalogue_match_tls.
    rewrite Etp. intros DT TS C T DB k Hc.
    exact (lib.B.ProgWorldTlsApart.fp_tls_apart B HTS LAWS ly S W m md [0%nat; 1%nat; 2%nat] (Sp - 9136) Sp HAR Hcs
             Hslo Hshi DT TS C T DB k Hc). }
  (* (5) RT_used_of_AR_C (route (C), no AR_states_vis0_shadow): the bcmp wrapper's cells; RT_used_C has two shadow
     conjuncts where RT_used had one, so CF / REALS sit one slot later *)
  pose proof (lib.B.ProgWorldRtC.RT_used_of_AR_C B HTS LAWS ly S W m md HAR) as (_ & _ & _ & _ & CFc & _ & _ & REALS).
  assert (CL : lib.B.Prog.reac_box_catalogue_matchF_on.aCL m).
  { destruct CFc as (CF1 & _ & _ & _ & _ & _ & CF240 & _).
    rewrite Forall_forall in REALS.
    pose proof (REALS (0xa2610, 0x98930) ltac:(unfold B.AsanRT.RT_REALS; right; right; left; reflexivity)
                  ltac:(unfold B.ProgWorld.REAL_USED; left; reflexivity)) as RB.
    pose proof (REALS (0xa2608, 0x98a00)
                  ltac:(unfold B.AsanRT.RT_REALS; do 9 right; left; reflexivity)
                  ltac:(unfold B.ProgWorld.REAL_USED; right; left; reflexivity)) as RM.
    destruct CF240 as (_ & _ & H240).
    unfold lib.B.Prog.reac_box_catalogue_matchF_on.aCL.
    split; [exact RB|]. split; [exact RM|]. split; [exact CF1|].
    split.
    - split; [unfold B.Prog.bcmp_wrap_c.CF, B.Prog.asan_stack_malloc_c.CF; lia|].
      split; [unfold B.Prog.bcmp_wrap_c.CF, B.Prog.asan_stack_malloc_c.CF; rewrite P64; cbn [length Z.of_nat]; lia|].
      intros i Hi. cbn [length] in Hi. assert (Ei : i = 0%nat) by lia. subst i.
      exact (H240 14%nat ltac:(cbn; lia)).
    - split; [unfold B.Prog.bcmp_wrap_c.CF, B.Prog.asan_stack_malloc_c.CF; lia|].
      split; [unfold B.Prog.bcmp_wrap_c.CF, B.Prog.asan_stack_malloc_c.CF; rewrite P64; cbn [length Z.of_nat]; lia|].
      intros i Hi. cbn [length] in Hi. assert (Ei : i = 0%nat) by lia. subst i.
      exact (H240 15%nat ltac:(cbn; lia)). }
  (* (6) the record: ctl_out_bytes and ctl_block_shadow_of_AR *)
  assert (HFB : 50 <= len -> lib.Lib.Mem.bytes_at B.Img0.rsegs m f fb /\ B.AsanRT.addressable m f 50).
  { intros Hl. destruct (Hlive Hl) as (n & Hin & Hn50).
    destruct (lib.Reusable.YG0d.al_blocks _ _ LAWS ly S W m md f n HAR Hin) as (_ & H4096 & Hcb & _ & _).
    split.
    - refine (proj1 (lib.B.ProgWorld.ctl_out_bytes W m f fb ltac:(lia) _ _ (Hbytes Hl))).
      + rewrite Hfb. rewrite P64. cbn [Z.of_nat]. lia.
      + intros i Hi. rewrite Hfb in Hi.
        exact (lib.Reusable.YCbq.blk_img B.Img0.rsegs B LAWS ly S W m md f n (f + Z.of_nat i) HAR Hin ltac:(lia)).
    - exact (lib.B.ProgWorldShadow.ctl_block_shadow_of_AR B LAWS ly S W m md f n f 50 HAR Hin ltac:(lia) ltac:(lia)
               ltac:(lia)). }
  (* (7) the table's bytes: the read-only view (arodata_okP) is the rom, and the view of a visible byte is mrd *)
  assert (BT : lib.Lib.Mem.bytes_at B.Img0.rsegs m lib.B.Prog.reac_box_catalogue_match_c.CM_T
                 lib.B.Prog.reac_box_catalogue_match.CM_TBL).
  { unfold C_reac_box_catalogue_match.A_CM_TBL, C_reac_box_catalogue_match.CM_ROWS in HRLO, HRHI, Htbl.
    split; [unfold lib.B.Prog.reac_box_catalogue_match_c.CM_T; lia|].
    split; [rewrite lib.B.Prog.reac_box_catalogue_match.CM_TBL_len, P64;
            unfold lib.B.Prog.reac_box_catalogue_match_c.CM_T; cbn [Z.of_nat]; lia|].
    intros i Hi. rewrite lib.B.Prog.reac_box_catalogue_match.CM_TBL_len in Hi.
    pose proof (cmV_image_nth B.Img0.rsegs 3256 lib.B.Prog.reac_box_catalogue_match_c.CM_T
                  lib.B.Prog.reac_box_catalogue_match.CM_TBL lib.B.Prog.reac_box_catalogue_match.CM_TBL_eq i Hi) as Ei.
    destruct (nth_error lib.B.Prog.reac_box_catalogue_match.CM_TBL i) as [b|] eqn:Eb.
    2:{ apply nth_error_None in Eb. rewrite lib.B.Prog.reac_box_catalogue_match.CM_TBL_len in Eb. lia. }
    assert (Hv : lib.Reusable.YG0n.aview B.Img0.rsegs (lib.Reusable.YA0n.w_H W) m
                   (lib.B.Prog.reac_box_catalogue_match_c.CM_T + Z.of_nat i) = Some (bv_unsigned b)).
    { unfold lib.B.Prog.reac_box_catalogue_match_c.CM_T in *.
      destruct (Htbl (0x9f620 + Z.of_nat i) ltac:(lia)) as [Hno Hne].
      rewrite (HRO (0x9f620 + Z.of_nat i)); [| right; lia | exact Hno | exact Hne].
      assert (Ei' : lib.Lib.PropExec.seg_rom B.Img0.rsegs (lib.Lib.Mem.wa (0x9f620 + Z.of_nat i)) = Some b)
        by (rewrite Ei; try exact Eb; reflexivity).
      exact (f_equal (option_map (fun b0 : byte => bv_unsigned b0)) Ei'). }
    assert (Hvis : lib.Reusable.YA0n.w_H W (Z_to_bv 64 (lib.B.Prog.reac_box_catalogue_match_c.CM_T + Z.of_nat i)) = false)
      by (apply (lib.B.ProgWorldVisFrame.vis_of_aview B.Img0.rsegs W m); rewrite Hv; discriminate).
    pose proof (eq_trans (eq_sym Hv) (lib.B.ProgWorld.aview_vis_mrd W m _ Hvis)) as Hm.
    change (lib.Lib.Mem.wa (lib.B.Prog.reac_box_catalogue_match_c.CM_T + Z.of_nat i)) with
      (Z_to_bv 64 (lib.B.Prog.reac_box_catalogue_match_c.CM_T + Z.of_nat i)).
    destruct (lib.Lib.Mem.mrd B.Img0.rsegs m (Z_to_bv 64 (lib.B.Prog.reac_box_catalogue_match_c.CM_T + Z.of_nat i)))
      as [b'|] eqn:Em; [|discriminate Hm].
    cbn [option_map] in Hm. injection Hm as Hm. apply bv_eq in Hm. subst b. reflexivity. }
  (* (8) the table's data granules: Tfib_zero_shadow's entry 37 through ctl_zshadow_of_AR *)
  assert (AT : C_reac_box_catalogue_matchLib.cmRB_tbl_addr m).
  { unfold C_reac_box_catalogue_matchLib.cmRB_tbl_addr.
    assert (Hz : In (0x9f620, 0xa02d8 - 0x9f620) (lib.Reusable.YG0f.as_zero_shadow B)).
    { rewrite (lib.Reusable.YF0m.ts_zsh B HTS). apply (nth_error_In _ 37). reflexivity. }
    apply (lib.B.ProgWorldShadow.ctl_zshadow_of_AR B LAWS ly S W m md _ lib.B.Prog.reac_box_catalogue_match_c.CM_T
             3256 HAR Hz); unfold lib.B.Prog.reac_box_catalogue_match_c.CM_T; cbn [fst snd]; Z.div_mod_to_equations;
      lia. }
  (* (9) the BC's partial granule: Tfib_const_shadow's entry 15 through ctl_gshadow_of_AR *)
  assert (ABC : C_reac_box_catalogue_matchLib.cmRB_bc_addr m).
  { unfold C_reac_box_catalogue_matchLib.cmRB_bc_addr.
    assert (Hrow : In (lib.Reusable.YG0f.z1 (lib.Reusable.YG0f.ANum (lib.Reusable.YG0f.shadow_addr 0x21200)) 7)
                      (lib.Reusable.YF0m.Tfib_const ly)).
    { unfold lib.Reusable.YF0m.Tfib_const. apply in_or_app; right. apply in_or_app; right.
      apply (nth_error_In _ 15). reflexivity. }
    apply (lib.B.ProgWorldShadow.ctl_gshadow_of_AR B HTS LAWS ly S W m md 0x21200 7
             lib.B.Prog.reac_ctrl_parse_c.REAC_CTRL_PARSE_BC 6 HAR Hrow);
      unfold lib.Reusable.YG0f.kImgLo, lib.Reusable.YG0f.kImgEnd, lib.B.Prog.reac_ctrl_parse_c.REAC_CTRL_PARSE_BC;
      try reflexivity; lia. }
  (* cmBase *)
  unfold C_reac_box_catalogue_matchLib.cmBase.
  split; [exact (conj AC (conj SR RO))|].
  split; [exact AWw|].
  split; [rewrite Etp; exact FP|].
  split; [exact TL|]. split; [exact CL|]. split; [exact HFB|]. split; [exact BT|]. split; [exact AT | exact ABC].
Qed.
End V.
