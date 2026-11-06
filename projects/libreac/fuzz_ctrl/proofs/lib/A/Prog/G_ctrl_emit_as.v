(* fuzz_ctrl image A (libreac v1.9.0), ctrl_emit_as (0x849d8): the top-level cgif-form glue of a Theorem Labs lane.
   `pb_ctrl_emit_as` (Part 6) proves A/Prog/C_ctrl_emit_as.v `pb_ctrl_emit_as_stmt B GLOBS RLO RHI`.

   The composition. The call's run state (ro_agree, asan_cells, shadow_rw, the window addressable, fp,
   ctrl_emit_as_tls, the window's shadow cover) comes from the AR conjunct of the call's journal through ProgWorld
   (Parts 1-3). GE_entry.ge_entry runs the first lifted stretch, GE_pre.ge_pre, from 0x849d8; its post is
   ctrl_emit_asF2.aMid = aQg m [(LO, SP0)] \/ aAtLay (ctrl_emit_asF2.v:668):
   - aQg m [(LO, SP0)] (EE = false, the early return; the run writes its own stack window only): the journal at
     the end memory by GE_jrnl.ge_jrnl_win, the kept bytes by GE_post.ge_keep_ret, then GE_post.ge_post and SRr_ret;
   - aAtLay (the call site 0x84cec): the call-site facts move to the real memory (MemNorm.ms_rel); the jal
     (GE_cut.ge_steps with GE_jal.ge_jal_lay), the walk's configuration at 0x855f4 (GE_cut.ge_at_cfg), and
     a Theorem Labs lane's PLAIN contract, the binder TLAY (SRr_bind; its premises from the spec and the first stretch). In
     TLAY's continuation Part 5 (gc_ret) builds the run state at the memory the call returns, from TLAY's post and
     ProgWorld, and Part 6's gc_stretch2 runs the second stretch RE-BASED on that memory (GE_post2.ge_post2, a Theorem Labs lane's
     ctrl_emit_as_post_lay_F, post aQg m5 aWL), carries the journal across it (GE_jrnl.ge_jrnl, window and output),
     composes the kept bytes of the three steps (GE_post.ge_keep_lay) and closes with GE_post.ge_post.

   Hypotheses of pb_ctrl_emit_as beyond the statement's binders:
     HTS      : A.AF0m.CtrlTSyms B                  the bundle is ctrl's (AF0m.v:293); no binder of the statement gives it.
     VIS0     : A.ProgWorld.AR_states_vis0_shadow B  ProgWorld.v, a Theorem Labs lane's named core fact; no proof.
     (AR_states_owned_ro is NOT a binder: a Theorem Labs lane's ProgWorldOwnedRo.AR_states_owned_ro_of_AR proves it from HTS.)
     (Names and types are the shared form: a Theorem Labs lane, adopted by a Theorem Labs lane 06:21Z.)
     (ctlrt_of_AR, ProgWorld.v:234, is NOT a binder: a Theorem Labs lane's ProgWorldCtlRt.ctlrt_of_AR proves it.)
     (ctl_stack_shadow_of_AR is NOT a binder: a Theorem Labs lane's ProgWorldShadow.ctl_stack_shadow_of_AR proves it, a Theorem Labs lane 08:24Z.)
     HRLO     : RLO = PA_RLO,  HRHI : RHI = PA_RHI  TLAY is stated at PI_ctrl's read-only bounds, the spec at RLO / RHI.
   Used directly, proved: ProgWorld_Fs.ctl_fp_of_AR, ProgWorld.as_tp_RT_TP, ProgWorldVisWin.win_sh_vis, AF0m.ts_tsd;
   the proof of ProgWorld_Rt.ctl_tls_of_AR is adapted in Part 2 (ProgWorld_Rt.v does not build here).

   PROVISIONAL: A.AF0m, A.ProgWorld and A.ProgWorld_Fs build only with a Theorem Labs lane's port_core_refused stand-ins
   (workspace only), until the placeholder names are gone.

   Memory-checking runtime: before each load or store the code loads a shadow byte at (a >> 3) + 0x7fff8000 and
   compares it; with the range addressable the check passes and the error path is not reached.

   Glue closure rule (two Theorem Labs lanes): ctrl_emit_asF2 is Required qualified only; the six duplicated modules
   (YI04 YI16 YK11 YK1b YM05 YO09) are written lib.Reusable.<X>. rule 24: At ossv/recipes c5e779efe8c (2026-10-31), no released proof of ctrl_emit_as outside this unit. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import GEbase.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AF0m.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Open Scope Z_scope.

(* ===================================================================================================== *)
(* Part 1. Facts carried by a VIEW equality (the form a caller-journal post gives), and visibility.       *)
(* ===================================================================================================== *)
Section b. Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
#[local] Notation SEGS := AB1v.tfibsegs.

(* ---------------------------------------------------------------------------------------------------------
   Helpers: a byte the world does not hide is read by the world's reader exactly as lib.Lib reads it, and two
   such reads that agree as numbers agree as bytes. Off the image, lib.Lib's read and wview are the memory. *)
Lemma gcv_aview_mrd : forall (H : word -> bool) (m : word -> option byte) a,
  H (Z_to_bv 64 a) = false ->
  aview SEGS H m a = option_map (fun b : byte => bv_unsigned b) (mrd rsegs m (wa a)).
Proof. intros H m a Hh. unfold aview, mbyte, mrestrict, mrd, wa. rewrite Hh. reflexivity. Qed.

Lemma gcv_omap_inj : forall x y : option byte,
  option_map (fun b : byte => bv_unsigned b) x = option_map (fun b : byte => bv_unsigned b) y -> x = y.
Proof.
  intros [x|] [y|] E; cbn in E; try discriminate; [|reflexivity].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.

Lemma gcv_mrd : forall (W W2 : world SEGS) (mc m5 : word -> option byte) a,
  w_H W (Z_to_bv 64 a) = false -> w_H W2 (Z_to_bv 64 a) = false ->
  aview SEGS (w_H W2) m5 a = aview SEGS (w_H W) mc a ->
  mrd rsegs m5 (wa a) = mrd rsegs mc (wa a).
Proof.
  intros W W2 mc m5 a H1 H2 E. apply gcv_omap_inj.
  rewrite <- (gcv_aview_mrd _ m5 a H2), <- (gcv_aview_mrd _ mc a H1). exact E.
Qed.

Lemma gcv_mrd_noimg : forall (m : word -> option byte) x, 0 <= x < 2 ^ 64 -> ~ in_img SEGS x ->
  mrd rsegs m (wa x) = m (wa x).
Proof.
  intros m x Hx Hn. unfold mrd. destruct (m (wa x)) as [b|]; [reflexivity|].
  unfold wa. exact (YCbq.seg_rom_none rsegs x Hx Hn).
Qed.

Lemma gcv_wview_noimg : forall (m : word -> option byte) x, 0 <= x < 2 ^ 64 -> ~ in_img SEGS x ->
  wview rsegs m (wa x) = m (wa x).
Proof.
  intros m x Hx Hn. unfold wview, wa. destruct (m (Z_to_bv 64 x)) as [b|]; [reflexivity|].
  rewrite (unsigned_lit x Hx). rewrite (YCbq.find_segment_none rsegs x Hn). reflexivity.
Qed.

Lemma gcv_bytes : forall (m m' : word -> option byte) a (bs : list byte),
  bytes_at rsegs m a bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> mrd rsegs m' (wa (a + i)) = mrd rsegs m (wa (a + i))) ->
  bytes_at rsegs m' a bs.
Proof.
  intros m m' a bs (H0 & H1 & HB) HE. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite (HE (Z.of_nat i) ltac:(lia)). exact (HB i Hi).
Qed.

(* (a) writable cells carried by the view, off the image *)
Lemma gc_rw_view : forall (W W2 : world SEGS) (mc m5 : word -> option byte) (a : Z) (cs : list cell),
  rw_cells rsegs mc a cs ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) ->
     ~ in_img SEGS (a + i) /\ w_H W (Z_to_bv 64 (a + i)) = false /\ w_H W2 (Z_to_bv 64 (a + i)) = false /\
     aview SEGS (w_H W2) m5 (a + i) = aview SEGS (w_H W) mc (a + i)) ->
  rw_cells rsegs m5 a cs.
Proof.
  intros W W2 mc m5 a cs ((Hwf & Hb) & (H0 & H1 & Hw)) HV.
  pose proof (cells_bytes_length cs Hwf) as Hl.
  split; [split; [exact Hwf|] | split; [exact H0|]; split; [exact H1|]].
  - apply (gcv_bytes mc m5 a (cells_bytes cs) Hb).
    intros i Hi. rewrite Hl in Hi. destruct (HV i Hi) as (_ & Hh1 & Hh2 & E).
    exact (gcv_mrd W W2 mc m5 _ Hh1 Hh2 E).
  - intros i Hi. destruct (HV i Hi) as (Hn & Hh1 & Hh2 & E).
    assert (Hr : 0 <= a + i < 2 ^ 64) by lia.
    pose proof (gcv_mrd W W2 mc m5 _ Hh1 Hh2 E) as M.
    rewrite (gcv_mrd_noimg m5 (a + i) Hr Hn), (gcv_mrd_noimg mc (a + i) Hr Hn) in M.
    rewrite (gcv_wview_noimg m5 (a + i) Hr Hn), M.
    rewrite <- (gcv_wview_noimg mc (a + i) Hr Hn). exact (Hw i Hi).
Qed.

(* (b) bytes carried by the view *)
Lemma gc_bytes_view : forall (W W2 : world SEGS) (mc m5 : word -> option byte) (a : Z) (bs : list byte),
  bytes_at rsegs mc a bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) ->
     w_H W (Z_to_bv 64 (a + i)) = false /\ w_H W2 (Z_to_bv 64 (a + i)) = false /\
     aview SEGS (w_H W2) m5 (a + i) = aview SEGS (w_H W) mc (a + i)) ->
  bytes_at rsegs m5 a bs.
Proof.
  intros W W2 mc m5 a bs Hb HV. apply (gcv_bytes mc m5 a bs Hb).
  intros i Hi. destruct (HV i Hi) as (Hh1 & Hh2 & E). exact (gcv_mrd W W2 mc m5 _ Hh1 Hh2 E).
Qed.

(* (c) addressability carried by the view of the shadow bytes *)
Lemma gc_addr_view : forall (W W2 : world SEGS) (mc m5 : word -> option byte) (p n : Z),
  addressable mc p n ->
  (forall i, 0 <= i < n ->
     w_H W (Z_to_bv 64 (shadow_addr (p + i))) = false /\ w_H W2 (Z_to_bv 64 (shadow_addr (p + i))) = false /\
     aview SEGS (w_H W2) m5 (shadow_addr (p + i)) = aview SEGS (w_H W) mc (shadow_addr (p + i))) ->
  addressable m5 p n.
Proof.
  intros W W2 mc m5 p n (H0 & H1 & H2 & HA) HV.
  split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (HA i Hi) as (Happ & b & Hb & Hok). split; [exact Happ|].
  destruct (HV i Hi) as (Hh1 & Hh2 & E). exists b. split; [|exact Hok].
  rewrite (gcv_mrd W W2 mc m5 _ Hh1 Hh2 E). exact Hb.
Qed.

(* (d) the stack window's shadow cover, from a Theorem Labs lane's win_sh_vis form (A/ProgWorldVisWin.v:56, rng_asan.v:80-81) *)
Lemma gcv_al8_mono : forall x y, x <= y -> AsanRT.shadow_addr x / 8 * 8 <= AsanRT.shadow_addr y / 8 * 8.
Proof.
  intros x y Hxy. apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|].
  unfold AsanRT.shadow_addr. pose proof (Z.div_le_mono x y 8 ltac:(lia) Hxy). lia.
Qed.

Lemma gc_shcov_of_al8 : forall (H : word -> bool) (lo len : Z), 0 < len ->
  range_visible H (A.Prog.rng_asan.sh_al8_lo lo) (A.Prog.rng_asan.sh_al8_hi lo len - A.Prog.rng_asan.sh_al8_lo lo) ->
  sh_cov_vis H lo (lo + len - 1).
Proof.
  intros H lo len Hlen (R0 & R1 & RV). unfold A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi in *.
  unfold sh_cov_vis. intros x y Hx Hy.
  pose proof (gcv_al8_mono lo x Hx) as Mx. pose proof (gcv_al8_mono y (lo + len - 1) Hy) as My.
  set (Slo := AsanRT.shadow_addr lo / 8 * 8) in *.
  set (Shi := AsanRT.shadow_addr (lo + len - 1) / 8 * 8) in *.
  set (Sx := AsanRT.shadow_addr x / 8 * 8) in *.
  set (Sy := AsanRT.shadow_addr y / 8 * 8) in *.
  split; [lia|]. split; [lia|]. intros a Ha. apply RV. lia.
Qed.

(* (e) visibility facts survive a world step (wle W W2: hidden set shrinks) *)
Lemma gc_vis_wle : forall (W W2 : world SEGS) lo len, wle W W2 -> range_visible (w_H W) lo len -> range_visible (w_H W2) lo len.
Proof.
  intros W W2 lo len Hle (R0 & R1 & RV). split; [exact R0|]. split; [exact R1|].
  intros a Ha. pose proof (RV a Ha) as Hf. destruct (w_H W2 (Z_to_bv 64 a)) eqn:E; [|reflexivity].
  rewrite (Hle _ E) in Hf. discriminate.
Qed.

Lemma gc_shcov_wle : forall (W W2 : world SEGS) a b, wle W W2 -> sh_cov_vis (w_H W) a b -> sh_cov_vis (w_H W2) a b.
Proof. intros W W2 a b Hle HC x y Hx Hy. exact (gc_vis_wle W W2 _ _ Hle (HC x y Hx Hy)). Qed.

(* (f) the read-only data fact carried by a view equality on the non-owned image bytes *)
Lemma gc_ro_view : forall (B : asyms) (W W2 : world SEGS) (mc m5 : word -> option byte) (rlo rhi : Z),
  (forall a, rlo <= a < rhi -> in_img SEGS a) ->
  arodata_okS SEGS B rlo rhi (aview SEGS (w_H W) mc) ->
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     aview SEGS (w_H W2) m5 a = aview SEGS (w_H W) mc a) ->
  arodata_okS SEGS B rlo rhi (aview SEGS (w_H W2) m5).
Proof.
  intros B W W2 mc m5 rlo rhi Hrel Hro Heq a Hseg Hno He.
  assert (Hi : in_img SEGS a).
  { destruct Hseg as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | lia] | exact (Hrel a Hr)]. }
  rewrite (Heq a Hi Hno He). exact (Hro a Hseg Hno He).
Qed.

End b.

(* ===================================================================================================== *)
(* Part 2. The thread cells: their values from AR's const rows at CtrlTSyms B (a Theorem Labs lane's ctl_tls_of_AR proof,  *)
(*         ProgWorld_Rt.v (not in this delivery), adapted: that file does not build here), and their apartness from the side  *)
(*         stack's class-0 / class-1 bytes and the window's shadow (ctrl_emit_as_tls).                    *)
(* ===================================================================================================== *)
Section b. Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
#[local] Notation SEGS := AB1v.tfibsegs.

(* Two byte lists the same memory holds at one address, of one length, are equal. *)
Lemma gct_bytes_uniq : forall m a l1 l2,
  bytes_at rsegs m a l1 -> bytes_at rsegs m a l2 -> length l1 = length l2 -> l1 = l2.
Proof.
  intros m a l1 l2 (_ & _ & H1) (_ & _ & H2) HL.
  apply nth_error_ext. intros i.
  destruct (Nat.lt_ge_cases i (length l1)) as [Hi|Hi].
  - rewrite <- (H1 i Hi). rewrite <- (H2 i) by lia. reflexivity.
  - rewrite (proj2 (nth_error_None l1 i) Hi). rewrite (proj2 (nth_error_None l2 i)) by lia. reflexivity.
Qed.

Lemma gct_le8_uniq : forall m a x y, bytes_at rsegs m a (le8 x) -> bytes_at rsegs m a (le8 y) -> x = y.
Proof.
  intros m a x y H1 H2.
  rewrite <- (le_bytes_to_word_le8 x), <- (le_bytes_to_word_le8 y).
  f_equal. apply (gct_bytes_uniq m a); [exact H1 | exact H2 | reflexivity].
Qed.

Lemma gct_le4_zero : forall m a k, 0 <= k < 2 ^ 32 ->
  bytes_at rsegs m a (le4 (Z_to_bv 64 k)) -> bytes_at rsegs m a (le4 (Z_to_bv 64 0)) -> k = 0.
Proof.
  intros m a k Hk H1 H2.
  assert (E : le4 (Z_to_bv 64 k) = le4 (Z_to_bv 64 0)).
  { apply (gct_bytes_uniq m a); [exact H1 | exact H2 | reflexivity]. }
  pose proof (le_bytes_to_word_le4 (Z_to_bv 64 k)) as Q1.
  rewrite E, le_bytes_to_word_le4 in Q1.
  change (Z_to_bv 64 k) with (wa k) in Q1. change (Z_to_bv 64 0) with (wa 0) in Q1.
  rewrite !wa_unsigned in Q1 by lia.
  rewrite Z.mod_0_l, Z.mod_small in Q1 by lia. lia.
Qed.

(* The thread cells that asan_tls_cells reads pin its words: a second instance at the same thread pointer names the
   same words and the same key. *)
Lemma gct_pin : forall m Cv Tv Dv DT TS C T DB k,
  asan_tls_cells m RT_TP (wa 0x5db830) (wa 0x5fcbb8) (wa Cv) (wa Tv) (wa Dv) 0 ->
  asan_tls_cells m RT_TP DT TS C T DB k ->
  DT = wa 0x5db830 /\ TS = wa 0x5fcbb8 /\ C = wa Cv /\ T = wa Tv /\ DB = wa Dv /\ k = 0.
Proof.
  intros m Cv Tv Dv DT TS C T DB k
    (_ & _ & A3 & _ & _ & _ & A7 & A8 & A9 & A10 & _ & _ & _ & _ & _ & _ & A17 & _ & _)
    (_ & _ & B3 & _ & _ & B6 & B7 & B8 & B9 & B10 & _ & _ & _ & _ & _ & _ & B17 & _ & _).
  pose proof (gct_le8_uniq _ _ _ _ B3 A3) as EDT.
  pose proof (gct_le4_zero _ _ _ B6 B7 A7) as Ek.
  pose proof (gct_le8_uniq _ _ _ _ B8 A8) as ETS.
  subst k TS.
  pose proof (gct_le8_uniq _ _ _ _ B9 A9) as EC. subst C.
  pose proof (gct_le8_uniq _ _ _ _ B10 A10) as ET.
  pose proof (gct_le8_uniq _ _ _ _ B17 A17) as EDB.
  repeat split; assumption.
Qed.

(* The side stack is above the image (A/ProgWorld_Fs.v pw_F_above). *)
Lemma gct_F_above : forall (B : asyms) ly S (W : world SEGS) m md,
  AR SEGS B ly S W m md -> ASAN_GT <= ly_F ly.
Proof.
  intros B ly S W m md (M & L & _).
  pose proof (am_layout _ _ _ _ M) as LO.
  pose proof (lo_img _ LO) as (I1 & I2 & I3 & I4).
  assert (FO : In (ly_F ly, kFakeStackSize) (owned_extents ly)).
  { unfold owned_extents. right; right; right; left. reflexivity. }
  pose proof (proj1 (Forall_forall _ _) (lo_app _ LO) _ FO) as F1. cbn [fst snd] in F1.
  destruct F1 as [F0 _].
  assert (Hm : In (659456, 5623808) (map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s))) rsegs)).
  { rewrite rsegs_spans. right; right; right; left. reflexivity. }
  apply in_map_iff in Hm as (sg & Es & Hsg). injection Es as E1 E2.
  rewrite <- ge_segs in Hsg.
  pose proof (al_img _ _ _ _ L sg Hsg) as [_ J2]. rewrite E1, E2 in J2.
  assert (NI : forall a, ly_F ly <= a < ly_F ly + kFakeStackSize -> ~ in_zr a (ly_img ly)).
  { intros a Ha.
    assert (EX : Exists (in_zr a) (owned_extents ly)).
    { apply Exists_exists. exists (ly_F ly, kFakeStackSize).
      split; [exact FO | unfold in_zr; cbn [fst snd]; lia]. }
    exact (proj2 (proj2 (YG0s.owned_extents_bound ly a LO EX))). }
  unfold ASAN_GT. unfold kImgLo in I1.
  destruct (Z_lt_le_dec (ly_F ly) 65536) as [Hlt|Hge].
  - exfalso. apply (NI 65536); [unfold kFakeStackSize; lia|].
    unfold in_zr. lia.
  - destruct (Z_lt_le_dec (ly_F ly) (fst (ly_img ly) + snd (ly_img ly))) as [Hlt2|Hge2].
    + exfalso. apply (NI (ly_F ly)); [unfold kFakeStackSize; lia|].
      unfold in_zr. lia.
    + lia.
Qed.

(* The shadow map is monotone; it sends application addresses above the low application range and the high
   application range below the high application memory. *)
Lemma gct_sh_mono : forall x y, x <= y -> shadow_addr x <= shadow_addr y.
Proof. intros x y H. unfold shadow_addr. apply Z.add_le_mono_r. apply Z.div_le_mono; lia. Qed.

Lemma gct_sh_ge0 : forall x, 0 <= x -> ASAN_K <= shadow_addr x.
Proof. intros x H. unfold shadow_addr. pose proof (Z.div_pos x 8 H ltac:(lia)). lia. Qed.

Lemma gct_sh_hi : forall x, x <= APPMEM_END -> shadow_addr x <= HIGHMEM_BEG.
Proof.
  intros x H. pose proof (gct_sh_mono x APPMEM_END H) as M.
  assert (E : shadow_addr APPMEM_END = HIGHMEM_BEG) by reflexivity. lia.
Qed.

Lemma gct_sh_ceil : forall x, x <= 0x7fffff800000 -> shadow_addr x < HIGHMEM_BEG.
Proof.
  intros x H. pose proof (gct_sh_mono x 0x7fffff800000 H) as M.
  assert (E : shadow_addr 0x7fffff800000 < HIGHMEM_BEG) by (vm_compute; reflexivity). lia.
Qed.

(* An interval apart from the side stack, from its shadow and from the shadow of the stack window is apart from the
   class-0 and class-1 side-stack footprint and from the shadow of any window [lo, hi) inside the stack. *)
Lemma gct_apart : forall (F slo shi lo hi a b : Z),
  0 <= F -> slo <= lo -> lo <= hi -> hi <= shi ->
  (b <= F \/ F + kFakeStackSize <= a) ->
  (b <= shadow_addr F \/ shadow_addr (F + kFakeStackSize) <= a) ->
  (b <= shadow_addr slo \/ shadow_addr shi <= a) ->
  Forall (fun d => RcLay.ly_dj a b (fst d) (snd d)) (fp_w [0%nat; 1%nat] F ++ [(shadow_addr lo, shadow_addr hi)]).
Proof.
  intros F slo shi lo hi a b HF H1 H2 H3 HA HB HC.
  unfold fp_w, fp_w1, fs_hint, fs_flag, fs_frame, fs_M, fs_B. simpl.
  unfold kFakeStackSize in HA.
  repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; unfold RcLay.ly_dj.
  all: first
    [ lia
    | match goal with |- _ <= shadow_addr ?x \/ shadow_addr ?y <= _ =>
        remember x as x0 eqn:Ex; remember y as y0 eqn:Ey;
        first
          [ pose proof (gct_sh_mono F x0 ltac:(lia));
            pose proof (gct_sh_mono y0 (F + kFakeStackSize) ltac:(unfold kFakeStackSize; lia));
            clear Ex Ey; lia
          | pose proof (gct_sh_mono slo x0 ltac:(lia)); pose proof (gct_sh_mono y0 shi ltac:(lia));
            clear Ex Ey; lia ]
      end ].
Qed.

(* An image interval (below ASAN_GT). *)
Lemma gct_img : forall F slo shi lo hi a b,
  0x5fe000 <= F -> 0 <= slo -> slo <= lo -> lo <= hi -> hi <= shi ->
  0 <= a -> b <= 0x5fe000 ->
  Forall (fun d => RcLay.ly_dj a b (fst d) (snd d)) (fp_w [0%nat; 1%nat] F ++ [(shadow_addr lo, shadow_addr hi)]).
Proof.
  intros F slo shi lo hi a b HF Hs0 Hs1 Hs2 Hs3 Ha Hb.
  pose proof (gct_sh_ge0 F ltac:(lia)) as S1. pose proof (gct_sh_ge0 slo Hs0) as S3.
  unfold ASAN_K in S1, S3.
  apply (gct_apart F slo shi); lia.
Qed.

(* An interval inside an application extent [X, X + len) apart from the side stack's extent. *)
Lemma gct_own : forall F slo shi lo hi X len a b,
  0 <= F -> (F + 0xb09000 <= 0x7fff7000 \/ (0x10007fff8000 <= F /\ F + 0xb09000 <= 0x7fffff800000)) ->
  0x10007fff8000 <= slo -> slo <= lo -> lo <= hi -> hi <= shi -> shi <= 0x800000000000 ->
  (X + len <= 0x7fff7000 \/ 0x10007fff8000 <= X) -> (F + 0xb09000 <= X \/ X + len <= F) ->
  X <= a -> b <= X + len ->
  Forall (fun d => RcLay.ly_dj a b (fst d) (snd d)) (fp_w [0%nat; 1%nat] F ++ [(shadow_addr lo, shadow_addr hi)]).
Proof.
  intros F slo shi lo hi X len a b HF FIN Hs0 Hs1 Hs2 Hs3 Hs4 HX HD Ha Hb.
  pose proof (gct_sh_ge0 F HF) as S1.
  pose proof (gct_sh_ceil (F + kFakeStackSize) ltac:(unfold kFakeStackSize; lia)) as S2.
  pose proof (gct_sh_ge0 slo ltac:(lia)) as S3.
  pose proof (gct_sh_hi shi ltac:(unfold APPMEM_END; lia)) as S4.
  unfold ASAN_K, HIGHMEM_BEG in S1, S2, S3, S4.
  apply (gct_apart F slo shi); try lia; unfold kFakeStackSize; lia.
Qed.

Lemma gc_tls_dj : forall (B : asyms) ly S (W : world SEGS) (m : word -> option byte) md (lo hi : Z),
  AR_laws SEGS B ->
  AR SEGS B ly S W m md ->
  asan_tls_cells m RT_TP (wa 0x5db830) (wa 0x5fcbb8) (wa (ly_C ly)) (wa (ly_T ly)) (wa (ly_D ly)) 0 ->
  ly_stk_lo ly <= lo -> lo <= hi -> hi <= ly_stk_hi ly ->
  ctrl_emit_as_c.ctrl_emit_as_tls m RT_TP (ly_F ly) lo hi.
Proof.
  intros B ly S W m md lo hi _ HAR H0 Hlo Hlh Hhi.
  pose proof (gct_F_above B ly S W m md HAR) as HGT. unfold ASAN_GT in HGT.
  destruct HAR as (M & _).
  pose proof (am_layout _ _ _ _ M) as LO. clear M.
  pose proof (lo_app _ LO) as LA. unfold owned_extents in LA.
  apply Forall_cons_iff in LA as [_ LA]. apply Forall_cons_iff in LA as [_ LA].
  apply Forall_cons_iff in LA as [AT LA]. apply Forall_cons_iff in LA as [AF LA].
  apply Forall_cons_iff in LA as [_ LA]. apply Forall_cons_iff in LA as [_ LA].
  apply Forall_cons_iff in LA as [AC LA]. apply Forall_cons_iff in LA as [AD _].
  cbn [fst snd] in AT, AF, AC, AD.
  pose proof (lo_disj _ LO) as PD. unfold static_extents, owned_extents in PD.
  cbn [app pairwise] in PD.
  destruct PD as (_ & _ & PT & PF & _).
  apply Forall_cons_iff in PT as [DTF _].
  apply Forall_cons_iff in PF as [_ PF]. apply Forall_cons_iff in PF as [_ PF].
  apply Forall_cons_iff in PF as [DFC PF]. apply Forall_cons_iff in PF as [DFD _].
  unfold zdisjoint in DTF, DFC, DFD. cbn [fst snd] in DTF, DFC, DFD.
  pose proof (lo_top _ LO) as (_ & _ & _ & Hhm & _ & _ & Hlm).
  pose proof ASAN_CEIL_range as [CR _].
  unfold in_app, kLowShadowBeg, kHighMemBeg, kThreadObjSize, kFakeStackSize in AT, AF, AC, AD.
  unfold kHighMemEnd in Hhm. unfold kHighMemBeg in Hlm.
  unfold kThreadObjSize, kFakeStackSize in DTF, DFC, DFD.
  assert (FIN : ly_F ly + 0xb09000 <= 0x7fff7000 \/
                (0x10007fff8000 <= ly_F ly /\ ly_F ly + 0xb09000 <= 0x7fffff800000)) by (clear - AF CR; lia).
  assert (XC : ly_C ly + 256 <= 0x7fff7000 \/ 0x10007fff8000 <= ly_C ly) by (clear - AC; lia).
  assert (XT : ly_T ly + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= ly_T ly) by (clear - AT; lia).
  assert (XD : ly_D ly + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= ly_D ly) by (clear - AD; lia).
  assert (BC : 0 <= ly_C ly < 2 ^ 64) by (clear - AC CR; lia).
  assert (BT : 0 <= ly_T ly < 2 ^ 64) by (clear - AT CR; lia).
  assert (BD : 0 <= ly_D ly < 2 ^ 64) by (clear - AD CR; lia).
  assert (DTF' : ly_F ly + 0xb09000 <= ly_T ly \/ ly_T ly + 4096 <= ly_F ly) by (clear - DTF; lia).
  clear AT AF AC AD DTF CR LO.
  intros DT TS C T DB k H1.
  destruct (gct_pin _ _ _ _ _ _ _ _ _ _ H0 H1) as (-> & -> & -> & -> & -> & ->).
  clear H0 H1.
  unfold fp_dj, fp_tls.
  rewrite !wa_unsigned by lia.
  remember (fp_w [0%nat; 1%nat] (ly_F ly) ++ [(shadow_addr lo, shadow_addr hi)]) as D eqn:HD.
  unfold TLS_INDEX, REAL_TLS_GET_ADDR, TSD_KEY_INITED, TSD_KEY, GOT_CF, CF, GOT_VERBOSITY, VERBOSITY, DTLS_TPOFF,
    RT_TP.
  repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; subst D.
  - apply (gct_img _ (ly_stk_lo ly) (ly_stk_hi ly)); lia.
  - apply (gct_img _ (ly_stk_lo ly) (ly_stk_hi ly)); lia.
  - apply (gct_img _ (ly_stk_lo ly) (ly_stk_hi ly)); lia.
  - apply (gct_img _ (ly_stk_lo ly) (ly_stk_hi ly)); lia.
  - apply (gct_img _ (ly_stk_lo ly) (ly_stk_hi ly)); lia.
  - apply (gct_img _ (ly_stk_lo ly) (ly_stk_hi ly)); lia.
  - apply (gct_img _ (ly_stk_lo ly) (ly_stk_hi ly)); lia.
  - apply (gct_img _ (ly_stk_lo ly) (ly_stk_hi ly)); lia.
  - apply (gct_own _ (ly_stk_lo ly) (ly_stk_hi ly) _ _ (ly_C ly) 256); [lia | exact FIN | lia .. ].
  - apply (gct_own _ (ly_stk_lo ly) (ly_stk_hi ly) _ _ (ly_T ly) 4096); [lia | exact FIN | lia .. ].
  - apply (gct_img _ (ly_stk_lo ly) (ly_stk_hi ly)); lia.
  - apply (gct_img _ (ly_stk_lo ly) (ly_stk_hi ly)); lia.
  - apply (gct_img _ (ly_stk_lo ly) (ly_stk_hi ly)); lia.
  - apply (gct_img _ (ly_stk_lo ly) (ly_stk_hi ly)); lia.
  - apply (gct_img _ (ly_stk_lo ly) (ly_stk_hi ly)); lia.
  - apply (gct_own _ (ly_stk_lo ly) (ly_stk_hi ly) _ _ (ly_D ly) 4096); [lia | exact FIN | lia .. ].
Qed.

(* ---------------------------------------------------------------------------------------------------------
   The thread cells at the image's own thread pointer, from AR's const rows under CtrlTSyms (adapted from
   A/ProgWorld_Rt.v ctl_tls_of_AR, with its byte bridge). *)

Lemma gctr_nth_le_bytes : forall (n : nat) (z : Z) (i : nat), (i < n)%nat ->
  nth_error (Z_to_le_bytes n z) i = Some (Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat i))).
Proof.
  induction n as [|n IH]; intros z i Hi; [lia|].
  destruct i as [|i]; cbn [Z_to_le_bytes nth_error].
  - change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
  - rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. f_equal. lia.
Qed.

Lemma gctr_le_byte_shiftr : forall (z : Z) (w k : nat), (k < w)%nat ->
  Z_to_bv 8 (lib.Reusable.YG0f.le_byte z w k) = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k)).
Proof.
  intros z w k Hk. apply Z_to_bv8_mod.
  unfold lib.Reusable.YG0f.le_byte.
  change (2 ^ 8) with 256. rewrite Z.mod_mod by lia.
  change 256 with (2 ^ 8). apply shiftr_mod_mod8; lia.
Qed.

Lemma gctr_le8_eq : forall v z, v mod 2 ^ 64 = z mod 2 ^ 64 -> le8 (wa v) = Z_to_le_bytes 8 z.
Proof.
  intros v z H. unfold le8, word_to_le_bytes, wa.
  rewrite Z_to_bv_unsigned. change (bv_wrap 64 v) with (v mod 2 ^ 64).
  rewrite H. apply (Z_to_le_bytes_mod 8 z 64). cbn [Z.of_nat]. lia.
Qed.

Lemma gctr_le4_eq : forall v z, v mod 2 ^ 32 = z mod 2 ^ 32 -> le4 (wa v) = Z_to_le_bytes 4 z.
Proof.
  intros v z H. unfold le4, wa.
  rewrite Z_to_bv_unsigned. change (bv_wrap 64 v) with (v mod 2 ^ 64).
  rewrite (Z_to_le_bytes_mod 4 v 64) by (cbn [Z.of_nat]; lia).
  rewrite <- (Z_to_le_bytes_mod 4 v 32) by (cbn [Z.of_nat]; lia).
  rewrite <- (Z_to_le_bytes_mod 4 z 32) by (cbn [Z.of_nat]; lia).
  rewrite H. reflexivity.
Qed.

Lemma gctr_le1_eq : forall v z, v mod 2 ^ 8 = z mod 2 ^ 8 -> [Z_to_bv 8 v] = Z_to_le_bytes 1 z.
Proof.
  intros v z H. cbn [Z_to_le_bytes].
  apply f_equal2; [apply Z_to_bv8_mod; exact H | reflexivity].
Qed.

(* A byte the core's view reads is visible, and ctrl's mrd reads it (A/ProgWorld.v aview_vis_mrd,
   A/ProgWorld_Fs.v pw_view_mrd). *)
Lemma gctr_view_mrd : forall (W : world SEGS) (m : word -> option byte) (a v : Z),
  aview SEGS (w_H W) m a = Some v -> mrd rsegs m (wa a) = Some (Z_to_bv 8 v).
Proof.
  intros W m a v Hv.
  assert (Hh : w_H W (Z_to_bv 64 a) = false).
  { destruct (w_H W (Z_to_bv 64 a)) eqn:Hh; [|reflexivity]. exfalso.
    unfold lib.Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, lib.Reusable.YK04.mrestrict in Hv. rewrite Hh in Hv.
    unfold lib.Reusable.YK11.seg_rom in Hv.
    rewrite (lib.Reusable.YK04.memory_read1_hidden SEGS (w_H W) (lib.Reusable.YA0n.w_Hoff W) _ Hh) in Hv.
    cbn [option_map] in Hv. discriminate Hv. }
  assert (E : aview SEGS (w_H W) m a =
              option_map (fun b : byte => bv_unsigned b) (mrd rsegs m (Z_to_bv 64 a))).
  { unfold lib.Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, lib.Reusable.YK04.mrestrict, mrd.
    rewrite Hh. reflexivity. }
  rewrite E in Hv. unfold wa.
  destruct (mrd rsegs m (Z_to_bv 64 a)) as [b|]; cbn [option_map] in Hv; [|discriminate Hv].
  injection Hv as <-. rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* A row of the core's world that holds over the view is ctrl's bytes_at at its address. *)
Lemma gctr_cell_bytes_at : forall (W : world SEGS) (m : word -> option byte) (B : asyms) (ly : alayout)
    (ea ev : lib.Reusable.YG0f.aexp) (w : nat) (A : Z) (bs : list byte),
  lib.Reusable.YG0f.cell_holds B ly (aview SEGS (w_H W) m)
    (lib.Reusable.YG0f.ACell ea w (lib.Reusable.YG0f.AV ev)) ->
  A = lib.Reusable.YG0f.aeval B ly ea -> 0 <= A -> A + Z.of_nat w <= 2 ^ 64 ->
  bs = Z_to_le_bytes w (lib.Reusable.YG0f.aeval B ly ev) ->
  bytes_at rsegs m A bs.
Proof.
  intros W m B ly ea ev w A bs Hc -> H0 H1 ->.
  unfold bytes_at. rewrite length_Z_to_le_bytes.
  split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite ?length_Z_to_le_bytes in Hi.
  unfold lib.Reusable.YG0f.cell_holds in Hc.
  cbn [lib.Reusable.YG0f.c_val lib.Reusable.YG0f.c_at lib.Reusable.YG0f.c_w] in Hc.
  specialize (Hc i Hi).
  rewrite (gctr_nth_le_bytes w _ i Hi).
  rewrite (gctr_view_mrd W m _ _ Hc).
  apply (f_equal (@Some byte)). apply gctr_le_byte_shiftr. exact Hi.
Qed.

Lemma gctr_in_app_bounds : forall (lo len : Z), in_app lo len -> 4096 <= lo /\ lo + len <= 0x7fffff800000.
Proof.
  intros lo len [H0 [H|[H1 H2]]]; pose proof ASAN_CEIL_range as [CR _];
    unfold kLowShadowBeg, kHighMemBeg in *; lia.
Qed.

(* membership of a row in image A's const table *)
Ltac gctr_inconst :=
  unfold A.AF0m.Tfib_const, A.AF0m.Tfib_const_sym, A.AF0m.Tfib_const_abs, A.AF0m.Tfib_const_shadow;
  cbn [app]; repeat first [ apply in_eq | apply in_cons ].

(* the side goals of gctr_cell_bytes_at: the row's membership (from the const-table hypothesis), its address, its
   bounds and its bytes (with the hypotheses as_tp B = .. and ly_tsd ly = ..) *)
Ltac gctr_row :=
  first
    [ match goal with H : forall c, In c _ -> lib.Reusable.YG0f.cell_holds _ _ _ c |- _ => apply H end;
      gctr_inconst
    | cbn [lib.Reusable.YG0f.aeval];
      repeat match goal with
             | H : as_tp _ = _ |- _ => progress rewrite H
             | H : ly_tsd _ = _ |- _ => progress rewrite H
             end;
      first
        [ lia
        | first [apply gctr_le8_eq | apply gctr_le4_eq | apply gctr_le1_eq]; first [reflexivity | f_equal; lia] ] ].

Lemma gc_tls_TS : forall (B : asyms) ly S (W : world SEGS) (m : word -> option byte) md,
  A.AF0m.CtrlTSyms B -> AR_laws SEGS B -> AR SEGS B ly S W m md ->
  asan_tls_cells m RT_TP (wa 0x5db830) (wa 0x5fcbb8) (wa (ly_C ly)) (wa (ly_T ly)) (wa (ly_D ly)) 0.
Proof.
  intros B ly S W m md HTS _ HAR.
  destruct HAR as (HM & _).
  pose proof (am_const _ _ _ _ HM) as Hconst.
  pose proof (am_layout _ _ _ _ HM) as Hlay.
  pose proof (am_tsd _ _ _ _ HM) as Hlytsd.
  assert (Hrow : forall c, In c (A.AF0m.Tfib_const ly) ->
            lib.Reusable.YG0f.cell_holds B ly (aview SEGS (w_H W) m) c).
  { intros c Hc. apply (proj1 (Forall_forall _ _) Hconst). rewrite (A.AF0m.ts_const B HTS ly). exact Hc. }
  assert (Htp : as_tp B = 0x5db810) by (rewrite (A.AF0m.ts_tp B HTS); reflexivity).
  assert (Htsdly : ly_tsd ly = 0x5fcbb8) by (rewrite Hlytsd, (A.AF0m.ts_tsd B HTS); reflexivity).
  pose proof (proj1 (Forall_forall _ _) (lo_app _ Hlay)) as Happ.
  assert (HT : 4096 <= ly_T ly /\ ly_T ly + 4096 <= 0x7fffff800000).
  { apply gctr_in_app_bounds.
    exact (Happ (ly_T ly, kThreadObjSize) ltac:(unfold owned_extents; cbn [In]; tauto)). }
  assert (HC : 4096 <= ly_C ly /\ ly_C ly + 256 <= 0x7fffff800000).
  { apply gctr_in_app_bounds. exact (Happ (ly_C ly, 256) ltac:(unfold owned_extents; cbn [In]; tauto)). }
  assert (HD : 4096 <= ly_D ly /\ ly_D ly + 4096 <= 0x7fffff800000).
  { apply gctr_in_app_bounds. exact (Happ (ly_D ly, 4096) ltac:(unfold owned_extents; cbn [In]; tauto)). }
  destruct HT as [HT0 HT1]. destruct HC as [HC0 HC1]. destruct HD as [HD0 HD1].
  clear Happ Hconst Hlytsd.
  unfold asan_tls_cells.
  rewrite (wa_unsigned 0x5db830) by lia.
  rewrite (wa_unsigned 0x5fcbb8) by lia.
  rewrite (wa_unsigned (ly_C ly)) by lia.
  rewrite (wa_unsigned (ly_T ly)) by lia.
  rewrite (wa_unsigned (ly_D ly)) by lia.
  unfold TLS_INDEX, REAL_TLS_GET_ADDR, MUSL_TLS_GET_ADDR, TSD_KEY_INITED, TSD_KEY, GOT_CF, CF, GOT_VERBOSITY,
    VERBOSITY, DTLS_TPOFF, RT_TP.
  repeat match goal with |- _ /\ _ => split end.
  (* 1. TLS_INDEX: the two words at 0xa07b0 / 0xa07b8 *)
  - apply (proj2 (bytes_at_app rsegs m _ _ _)). split.
    + eapply (gctr_cell_bytes_at W m B ly (lib.Reusable.YG0f.ANum 0xa07b0) (lib.Reusable.YG0f.ANum 1) 8%nat);
        gctr_row.
    + rewrite length_le8.
      eapply (gctr_cell_bytes_at W m B ly (lib.Reusable.YG0f.ANum 0xa07b8)
                (lib.Reusable.YG0f.ANum 0xfffffffffffff800) 8%nat); gctr_row.
  (* 2. REAL_TLS_GET_ADDR *)
  - eapply (gctr_cell_bytes_at W m B ly (lib.Reusable.YG0f.ANum 0xa1870) (lib.Reusable.YG0f.ANum 0x98800) 8%nat);
      gctr_row.
  (* 3. TP - 8 holds DT = TP + 32 *)
  - eapply (gctr_cell_bytes_at W m B ly (lib.Reusable.YG0f.ATp (-8)) (lib.Reusable.YG0f.ANum 0x5db830) 8%nat);
      gctr_row.
  (* 4. DT + 8 holds TP + 2048 *)
  - eapply (gctr_cell_bytes_at W m B ly (lib.Reusable.YG0f.ANum 0x5db838) (lib.Reusable.YG0f.ANum 0x5dc010) 8%nat);
      gctr_row.
  (* 5. TSD_KEY_INITED *)
  - eapply (gctr_cell_bytes_at W m B ly (lib.Reusable.YG0f.ANum 0xa80e0) (lib.Reusable.YG0f.ANum 1) 1%nat);
      gctr_row.
  (* 6, 7. 0 <= k < 2 ^ 32 *)
  - lia.
  - lia.
  (* 8. TSD_KEY *)
  - eapply (gctr_cell_bytes_at W m B ly (lib.Reusable.YG0f.ANum 0xa80e4) (lib.Reusable.YG0f.ANum 0) 4%nat);
      gctr_row.
  (* 9. TP - 88 holds TS = the TSD main block *)
  - eapply (gctr_cell_bytes_at W m B ly (lib.Reusable.YG0f.ATp (-88)) (lib.Reusable.YG0f.ATsd 0) 8%nat);
      gctr_row.
  (* 10. TS + 8 * k holds C *)
  - eapply (gctr_cell_bytes_at W m B ly (lib.Reusable.YG0f.ATsd 0) (lib.Reusable.YG0f.AC 0) 8%nat);
      gctr_row.
  (* 11. C + 152 holds T *)
  - eapply (gctr_cell_bytes_at W m B ly (lib.Reusable.YG0f.AC 152) (lib.Reusable.YG0f.AT 0) 8%nat);
      gctr_row.
  (* 12. the two words at T + 48 *)
  - exists (wa 0x5dbf48), (wa 0x5dc024).
    apply (proj2 (bytes_at_app rsegs m _ _ _)). split.
    + eapply (gctr_cell_bytes_at W m B ly (lib.Reusable.YG0f.AT 48) (lib.Reusable.YG0f.ANum 0x5dbf48) 8%nat);
        gctr_row.
    + rewrite length_le8.
      eapply (gctr_cell_bytes_at W m B ly (lib.Reusable.YG0f.AT 56) (lib.Reusable.YG0f.ANum 0x5dc024) 8%nat);
        gctr_row.
  (* 13. GOT_CF *)
  - eapply (gctr_cell_bytes_at W m B ly (lib.Reusable.YG0f.ANum 0x9fac0) (lib.Reusable.YG0f.ANum 0x13a3a8) 8%nat);
      gctr_row.
  (* 14. CF + 137 *)
  - eapply (gctr_cell_bytes_at W m B ly (lib.Reusable.YG0f.ANum 0x13a431) (lib.Reusable.YG0f.ANum 1) 1%nat);
      gctr_row.
  (* 15. GOT_VERBOSITY *)
  - eapply (gctr_cell_bytes_at W m B ly (lib.Reusable.YG0f.ANum 0x9fb20) (lib.Reusable.YG0f.ANum 0x138318) 8%nat);
      gctr_row.
  (* 16. VERBOSITY *)
  - eapply (gctr_cell_bytes_at W m B ly (lib.Reusable.YG0f.ANum 0x138318) (lib.Reusable.YG0f.ANum 0) 4%nat);
      gctr_row.
  (* 17. DTLS_TPOFF *)
  - eapply (gctr_cell_bytes_at W m B ly (lib.Reusable.YG0f.ANum 0xa07c0) (lib.Reusable.YG0f.ANum 8) 8%nat);
      gctr_row.
  (* 18. TP + 8 holds DB *)
  - eapply (gctr_cell_bytes_at W m B ly (lib.Reusable.YG0f.ATp 8) (lib.Reusable.YG0f.AD 0) 8%nat);
      gctr_row.
  (* 19. DB <> 0 *)
  - lia.
  (* 20. DB + 24 holds TP *)
  - eapply (gctr_cell_bytes_at W m B ly (lib.Reusable.YG0f.AD 24) (lib.Reusable.YG0f.ATp 0) 8%nat);
      gctr_row.
Qed.

Lemma gc_tls_AR' : forall (B : asyms) ly S (W : world SEGS) (m : word -> option byte) md (lo hi : Z),
  A.AF0m.CtrlTSyms B -> AR_laws SEGS B -> AR SEGS B ly S W m md ->
  ly_stk_lo ly <= lo -> lo <= hi -> hi <= ly_stk_hi ly ->
  ctrl_emit_as_c.ctrl_emit_as_tls m RT_TP (ly_F ly) lo hi.
Proof.
  intros B ly S W m md lo hi HTS HL HAR H1 H2 H3.
  exact (gc_tls_dj B ly S W m md lo hi HL HAR (gc_tls_TS B ly S W m md HTS HL HAR) H1 H2 H3).
Qed.

End b.

(* ===================================================================================================== *)
(* Part 3. The side-stack premise `fp` of the lifted stretch, from a Theorem Labs lane's PROVED ctl_fp_of_AR.               *)
(* ===================================================================================================== *)
Section b. Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
#[local] Notation SEGS := AB1v.tfibsegs.

(* rule 24: no function proved. World / layout helper lemmas for the glue of ctrl_emit_as (image A): the side-stack
   premise `fp [0; 1]` of the lifted stretches, from a Theorem Labs lane's ctl_fp_of_AR (taken as the premise HFP) and AR. *)

Lemma gcfp_u64 : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  apply Z.mod_small. exact Hz.
Qed.

(* Two members of a pairwise list, the earlier one first. *)
Lemma gcfp_pw : forall (X : Type) (Rl : X -> X -> Prop) (l : list X) (i j : nat) (x y : X),
  lib.Reusable.YG0f.pairwise Rl l -> (i < j)%nat -> nth_error l i = Some x -> nth_error l j = Some y -> Rl x y.
Proof.
  intros X Rl l. induction l as [|a t IH]; intros i j x y HP Hij Hi Hj.
  - destruct i; discriminate Hi.
  - cbn [lib.Reusable.YG0f.pairwise] in HP. destruct HP as [HF HP].
    destruct i as [|i], j as [|j]; try lia.
    + cbn [nth_error] in Hi, Hj. injection Hi as <-. apply nth_error_In in Hj.
      exact (proj1 (Forall_forall _ _) HF y Hj).
    + cbn [nth_error] in Hi, Hj. exact (IH i j x y HP ltac:(lia) Hi Hj).
Qed.

(* A range below the image end, or inside the side stack above its class-1 band, is apart from every range of
   fp_w [0; 1] FS (hint words, flag bytes, class-0 / class-1 frames and their shadow). *)
Lemma gcfp_w01 : forall FS x y,
  ASAN_GT <= FS ->
  (FS + FS_SIZE <= kLowShadowBeg \/ (kHighMemBeg <= FS /\ FS + FS_SIZE <= ASAN_CEIL)) ->
  (y <= ASAN_GT \/ (FS + kFakeFramesOff + 2 * 2 ^ 20 <= x /\ y <= FS + FS_SIZE)) ->
  Forall (fun r => RcLay.ly_dj x y (fst r) (snd r)) (fp_w [0%nat; 1%nat] FS).
Proof.
  intros FS x y HGT Hin Hxy. pose proof ASAN_CEIL_range as [CR _].
  unfold fp_w, fp_w1. cbn [flat_map app].
  unfold fs_hint, fs_flag, fs_frame, fs_M, fs_B, shadow_addr, ASAN_K.
  unfold ASAN_GT, FS_SIZE, kLowShadowBeg, kHighMemBeg, kFakeFramesOff in *.
  repeat (first [apply Forall_nil | apply Forall_cons]); unfold RcLay.ly_dj; cbn [fst snd];
    Z.div_mod_to_equations; lia.
Qed.

Lemma gc_fp_emit : forall (B : asyms) ly S (W : world SEGS) (m : word -> option byte) md
    (lo hi f q d s o R cid pos cid' pos' : Z),
  AR_laws SEGS B ->
  (forall ly S (W : world SEGS) (m : word -> option byte) md (cs : list nat) (lo hi : Z) (Wr D : list ivl),
     AR SEGS B ly S W m md ->
     Forall (fun c => (c <= 6)%nat) cs ->
     ly_F ly + FS_SIZE <= lo ->
     (forall a, lo <= a < hi -> app_mem a) ->
     fp_dj Wr
       (fp_tls RT_TP (Z_to_bv 64 (RT_TP + 32)) (Z_to_bv 64 (ly_tsd ly)) (Z_to_bv 64 (ly_C ly))
          (Z_to_bv 64 (ly_T ly)) (Z_to_bv 64 (ly_D ly)) 0 ++
        (ly_F ly, fs_frame (ly_F ly) 0 0) :: nil) ->
     fp_dj D (fp_w cs (ly_F ly)) ->
     fp cs m RT_TP (ly_F ly) lo hi Wr D) ->
  AR SEGS B ly S W m md ->
  ly_stk_lo ly <= lo -> lo <= hi -> hi <= ly_stk_hi ly ->
  IMG_LO <= f -> f + 24 <= IMG_HI -> IMG_LO <= q -> q + 296 <= IMG_HI -> IMG_LO <= s -> s + 6 <= IMG_HI ->
  In (cid, pos) (frames S) -> 2 <= cid -> frame_addr ly cid pos <= o -> o + R <= frame_addr ly cid pos + fs_frame_bytes cid -> 0 <= R ->
  In (cid', pos') (frames S) -> 2 <= cid' -> frame_addr ly cid' pos' <= d -> d + 6 <= frame_addr ly cid' pos' + fs_frame_bytes cid' ->
  IMG_LO <= as_tsd B -> as_tsd B + 8 <= IMG_HI ->
  fp [0%nat; 1%nat] m RT_TP (ly_F ly) lo hi [(lo, hi); (o, o + R)]
     [(f, f + 24); (q, q + 296); (d, d + 6); (s, s + 6); (o, o + R)].
Proof.
  intros B ly S W m md lo hi f q d s o R cid pos cid' pos' LAWS HFP HAR Hlo Hlh Hhi
    Hf0 Hf1 Hq0 Hq1 Hs0 Hs1 Hin Hc2 Ho0 Ho1 HR Hin' Hc2' Hd0 Hd1 Ht0 Ht1.
  pose proof HAR as (M & L & _).
  pose proof (am_layout _ _ _ _ M) as LO.
  pose proof (am_tsd _ _ _ _ M) as Etsd.
  pose proof ASAN_CEIL_range as [CR _].
  pose proof (lo_stk_ceil _ LO) as SC.
  pose proof (lo_top _ LO) as (_ & _ & _ & T4 & _ & _ & T7).
  (* the owned extents the thread cells and the side stack live in *)
  pose proof (proj1 (Forall_forall _ _) (lo_app _ LO)) as Happ.
  assert (AF : in_app (ly_F ly) kFakeStackSize)
    by (apply (Happ (ly_F ly, kFakeStackSize)); unfold owned_extents; cbn [In]; tauto).
  assert (AC : in_app (ly_C ly) 256) by (apply (Happ (ly_C ly, 256)); unfold owned_extents; cbn [In]; tauto).
  assert (AT : in_app (ly_T ly) kThreadObjSize)
    by (apply (Happ (ly_T ly, kThreadObjSize)); unfold owned_extents; cbn [In]; tauto).
  assert (AD : in_app (ly_D ly) 4096) by (apply (Happ (ly_D ly, 4096)); unfold owned_extents; cbn [In]; tauto).
  clear Happ.
  unfold in_app, kLowShadowBeg, kHighMemBeg, kFakeStackSize, kThreadObjSize in AF, AC, AT, AD.
  assert (AF' : ly_F ly + FS_SIZE <= kLowShadowBeg \/ (kHighMemBeg <= ly_F ly /\ ly_F ly + FS_SIZE <= ASAN_CEIL))
    by (destruct AF as [_ AF]; exact AF).
  assert (FB : 4096 <= ly_F ly /\ ly_F ly + FS_SIZE <= ASAN_CEIL) by (unfold FS_SIZE; lia).
  assert (CB : 4096 <= ly_C ly /\ ly_C ly + 256 <= ASAN_CEIL) by lia.
  assert (TB : 4096 <= ly_T ly /\ ly_T ly + 4096 <= ASAN_CEIL) by lia.
  assert (DB : 4096 <= ly_D ly /\ ly_D ly + 4096 <= ASAN_CEIL) by lia.
  clear AF AC AT AD.
  (* the static extents are pairwise apart (lo_disj): side stack against T, C, D and the image *)
  pose proof (gcfp_pw _ _ _ 2 3 (ly_T ly, kThreadObjSize) (ly_F ly, kFakeStackSize) (lo_disj _ LO)
                ltac:(lia) eq_refl eq_refl) as DTF.
  pose proof (gcfp_pw _ _ _ 3 6 (ly_F ly, kFakeStackSize) (ly_C ly, 256) (lo_disj _ LO)
                ltac:(lia) eq_refl eq_refl) as DFC.
  pose proof (gcfp_pw _ _ _ 3 7 (ly_F ly, kFakeStackSize) (ly_D ly, 4096) (lo_disj _ LO)
                ltac:(lia) eq_refl eq_refl) as DFD.
  pose proof (gcfp_pw _ _ _ 3 9 (ly_F ly, kFakeStackSize) (ly_img ly) (lo_disj _ LO)
                ltac:(lia) eq_refl eq_refl) as DFI.
  unfold zdisjoint in DTF, DFC, DFD, DFI. cbn [fst snd] in DTF, DFC, DFD, DFI.
  unfold kFakeStackSize, kThreadObjSize in DTF, DFC, DFD, DFI.
  (* the side stack is above the image: ly_img starts at kImgLo and holds image A's last segment, which ends at
     ASAN_GT (A.ProgBridge.rsegs_spans) *)
  assert (HGT : ASAN_GT <= ly_F ly).
  { pose proof (lo_img _ LO) as (I1 & _ & _ & _).
    assert (Hm : In (659456, 5623808) (map (fun sg => (Z.of_N (seg_base sg), Z.of_N (seg_size sg))) A.Img0.rsegs)).
    { rewrite A.ProgBridge.rsegs_spans. right; right; right; left. reflexivity. }
    apply in_map_iff in Hm as (sg & Es & Hsg). injection Es as E1 E2.
    pose proof (al_img _ _ _ _ L sg Hsg) as [_ J2]. rewrite E1, E2 in J2.
    unfold kImgLo in I1. unfold ASAN_GT. lia. }
  clear DFI.
  (* the two class->=2 frames: inside the side stack, above the class-1 band *)
  pose proof (lib.Reusable.YG0s.frame_facts B ly S _ cid pos M Hin) as (_ & _ & _ & _ & _ & FO1 & FO2 & _).
  pose proof (lib.Reusable.YG0s.frame_facts B ly S _ cid' pos' M Hin') as (_ & _ & _ & _ & _ & FO1' & FO2' & _).
  unfold frame_addr in Ho0, Ho1, Hd0, Hd1.
  unfold kFakeFramesOff, kFakeStackSize in FO1, FO2, FO1', FO2'.
  unfold IMG_LO, IMG_HI, ASAN_GT, FS_SIZE, kLowShadowBeg, kHighMemBeg, kHighMemEnd in *.
  apply (HFP ly S W m md [0%nat; 1%nat] lo hi _ _ HAR).
  - constructor; [cbv beta; lia|]. constructor; [cbv beta; lia|]. constructor.
  - lia.
  - intros a Ha. unfold app_mem, HIGHMEM_BEG, APPMEM_END. right. lia.
  - unfold fp_dj, fp_tls. cbn [app].
    rewrite (gcfp_u64 (RT_TP + 32)) by (unfold RT_TP; lia).
    rewrite (gcfp_u64 (ly_tsd ly)) by lia.
    rewrite (gcfp_u64 (ly_C ly)) by lia.
    rewrite (gcfp_u64 (ly_T ly)) by lia.
    rewrite (gcfp_u64 (ly_D ly)) by lia.
    rewrite Etsd.
    unfold fs_frame, fs_B, TLS_INDEX, REAL_TLS_GET_ADDR, TSD_KEY_INITED, TSD_KEY, GOT_CF, CF, GOT_VERBOSITY,
      VERBOSITY, DTLS_TPOFF, RT_TP.
    repeat (first [apply Forall_nil | apply Forall_cons]); unfold RcLay.ly_dj; cbn [fst snd]; lia.
  - unfold fp_dj. apply Forall_forall. intros w Hw.
    apply (gcfp_w01 (ly_F ly) (fst w) (snd w) HGT AF').
    cbn [In] in Hw. destruct Hw as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd];
      unfold ASAN_GT, FS_SIZE, kFakeFramesOff; lia.
Qed.

End b.

From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import GE_row GE_img GE_buf GE_jrnl.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require ctrl_emit_asF2.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ProgWorldVisWin ACtlK ProgWorld ProgWorld_Fs
ProgWorldCtlRt ProgWorldShadow ProgWorldOwnedRo.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcEmitLib RcSynthLib RcFinLib.

(* ===================================================================================================== *)
(* Part 4. The statements the glue's parts are typed by.                                                  *)
(* ===================================================================================================== *)
Section b. Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Context {SK : lib.Reusable.YI16.sink_head}.
#[local] Notation SEGS := AB1v.tfibsegs.
#[local] Notation VAL := (@pa_val _ ctrl_listing PI_ctrl).
#[local] Notation BASE := (@pa_val _ ctrl_listing PI_ctrl A_TEXT).
#[local] Notation PA_RLO := (@pa_relro_lo _ ctrl_listing PI_ctrl).
#[local] Notation PA_RHI := (@pa_relro_hi _ ctrl_listing PI_ctrl).

(* ctrl_emit_asF2.v's Local Abbreviations at row := CROW r, g := 0 (as GE_post.v writes them). *)
Local Abbreviation EEr r n mb :=
  (RcEmit.em_E (RcFin.ubat (CROW r) 21) (RcFin.ubat (CROW r) 22) n (RcEmit.em_hid mb)).
Local Abbreviation LENr r n := (RcEmit.em_len (RcFin.ubat (CROW r) 21) n).
Local Abbreviation RRr r n mb := (if EEr r n mb then LENr r n else 0).
Local Abbreviation BLKr r md mb nb tb gb :=
  (RcFin.fin (RcFin.ubat (CROW r) 20) (RcFin.ubat (CROW r) 18) (RcFin.ubat (CROW r) 19)
     (RcLay.ly_lay (RcLay.ly_k (CROW r)) tb (RcLay.ly_Z md mb nb (RcLay.ly_bb (RcLay.ly_k (CROW r)))) 0
        (RcLay.ly_ao (CROW r)) (RcLay.ly_al (CROW r)) gb)).

Section e.
Variable B : asyms.
Variable GLOBS : list (Z * Z).
Variables RLO RHI : Z.

(* ---- a Theorem Labs lane's ProgWorld statements, as the glue's parts take them. Three are ProgWorld's own names;
   ctlrt_of_AR (ProgWorld.v:234) and ctl_fp_of_AR (ProgWorld.v:205) are taken in their conclusion form at
   CtrlTSyms B: Part 6 derives each from a Theorem Labs lane's proved ProgWorldCtlRt.ctlrt_of_AR, resp. ProgWorld_Fs.ctl_fp_of_AR.
   A.ACtlK.asan_cells_at /\ shadow_rw_at /\ ro_agree_at is A.ACtlCut.ctl_rt unfolded (ACtlCut.v:192). ---- *)
Definition ge_ctlrt_stmt : Prop :=
  AR_laws SEGS B -> A.ProgWorld.AR_states_vis0_shadow B -> A.ProgWorld.AR_states_owned_ro B ->
  forall (rl rh : Z) ly S (W : world SEGS) (m : word -> option byte) md,
    AR SEGS B ly S W m md ->
    arodata_okP SEGS rl rh B (aview SEGS (w_H W) m) ->
    A.ACtlK.asan_cells_at m /\ A.ACtlK.shadow_rw_at m /\ A.ACtlK.ro_agree_at m.

Definition ge_stack_shadow_stmt : Prop := A.ProgWorld.ctl_stack_shadow_of_AR_stmt B.

Definition ge_fp_stmt : Prop :=
  AR_laws SEGS B ->
  forall ly S (W : world SEGS) (m : word -> option byte) md (cs : list nat) (lo hi : Z) (Wr D : list ivl),
    AR SEGS B ly S W m md ->
    Forall (fun c => (c <= 6)%nat) cs ->
    ly_F ly + FS_SIZE <= lo ->
    (forall a, lo <= a < hi -> app_mem a) ->
    fp_dj Wr
      (fp_tls RT_TP (Z_to_bv 64 (RT_TP + 32)) (Z_to_bv 64 (ly_tsd ly)) (Z_to_bv 64 (ly_C ly))
         (Z_to_bv 64 (ly_T ly)) (Z_to_bv 64 (ly_D ly)) 0 ++
       (ly_F ly, fs_frame (ly_F ly) 0 0) :: nil) ->
    fp_dj D (fp_w cs (ly_F ly)) ->
    fp cs m RT_TP (ly_F ly) lo hi Wr D.

(* ---- the run state at the memory ctrl_lay_block returns, as the re-based second stretch takes it ----
   a Theorem Labs lane's premise list (lead 05:1xZ): aJ m5 (asan_cells, shadow_rw, the window addressable, the output
   addressable, fp, ctrl_emit_as_tls), the window below the call's frame present (stk), the read-only bytes
   (ro_agree: the real memory; the stretch runs on normalize rsegs m5), the frame cells at SP0 + -128, the row's
   bytes and addressability, the six output cells with the laid block at p + 18, and the footprint facts at
   RNG_W (w_H W2). Instantiation: ra .. a5 := getr regs 1 .. 15 as in GE_pre, row := CROW r, g := 0,
   o := p, f := the row, s := round_trip.box, tb := gb := []. *)
Definition ge_ret (W2 : world SEGS) (m5 : word -> option byte) (regs : bvmap 5 word) (FS p md d n r : Z)
    (mb nb db sb j0 : list byte) (P : word) (ns : Z) : Prop :=
  asan_cells m5 /\ shadow_rw m5 /\
  addressable m5 (bv_unsigned (getr regs 2) - 4640) 4640 /\
  addressable m5 p (LENr r n) /\
  fp [0%nat; 1%nat] m5 (bv_unsigned (getr regs 4)) FS (bv_unsigned (getr regs 2) - 4640) (bv_unsigned (getr regs 2))
    [(bv_unsigned (getr regs 2) - 4640, bv_unsigned (getr regs 2)); (p, p + LENr r n)]
    [(VAL (A_OBJ A_FRAMES) + ROW_BYTES * r, VAL (A_OBJ A_FRAMES) + ROW_BYTES * r + 24); (md, md + 296);
     (d, d + 6); (VAL (A_OBJ A_BOX), VAL (A_OBJ A_BOX) + 6); (p, p + LENr r n)] /\
  ctrl_emit_as_c.ctrl_emit_as_tls m5 (bv_unsigned (getr regs 4)) FS (bv_unsigned (getr regs 2) - 4640)
    (bv_unsigned (getr regs 2)) /\
  stk rsegs m5 (bv_unsigned (getr regs 2) - 4640) (bv_unsigned (getr regs 2) + -128) /\
  ro_agree rsegs m5 /\
  length j0 = 8%nat /\
  rw_cells rsegs m5 (bv_unsigned (getr regs 2) + -128)
    (CB 8 j0 :: C8 P :: C8 (Z_to_bv 64 ns) ::
     [C8 (getr regs 27); C8 (getr regs 26); C8 (getr regs 25); C8 (getr regs 24); C8 (getr regs 23);
      C8 (getr regs 22); C8 (getr regs 21); C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18);
      C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)]) /\
  bytes_at rsegs m5 (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r) (CROW r) /\
  addressable m5 (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r) 24 /\
  rw_cells rsegs m5 p [CB 6 db] /\ rw_cells rsegs m5 (p + 6) [CB 6 sb] /\
  rw_cells rsegs m5 (p + 12)
    [CB 6 [Z_to_bv 8 136; Z_to_bv 8 25; Z_to_bv 8 ((bv_unsigned (getr regs 15) mod 65536) mod 256);
           Z_to_bv 8 ((bv_unsigned (getr regs 15) mod 65536) / 256); nth 0 (CROW r) (Z_to_bv 8 0);
           nth 1 (CROW r) (Z_to_bv 8 0)]] /\
  rw_cells rsegs m5 (p + 18)
    [CB 32 (RcLay.ly_lay (RcLay.ly_k (CROW r)) [] (RcLay.ly_Z md mb nb (RcLay.ly_bb (RcLay.ly_k (CROW r)))) 0
              (RcLay.ly_ao (CROW r)) (RcLay.ly_al (CROW r)) [])] /\
  rw_cells rsegs m5 (p + 50) [CB (Z.to_nat (LENr r n - 52)) (repeat (Z_to_bv 8 0) (Z.to_nat (LENr r n - 52)))] /\
  rw_cells rsegs m5 (p + LENr r n + -2) [CB 2 (repeat (Z_to_bv 8 0) 2)] /\
  range_visible (w_H W2) (bv_unsigned (getr regs 2) - 4640) 4640 /\
  sh_cov_vis (w_H W2) (bv_unsigned (getr regs 2) - 4640) (bv_unsigned (getr regs 2) - 1) /\
  range_visible (w_H W2) (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r) 24 /\
  sh_cov_vis (w_H W2) (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r) (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r + 23) /\
  sh_cov_vis (w_H W2) md (md + 295) /\
  range_visible (w_H W2) p (LENr r n) /\ sh_cov_vis (w_H W2) p (p + LENr r n - 1).

(* ---- the second lifted stretch and the post ----
   From the call's premises (with the statement's image binders and the run state at the call memory, as ge_pre
   takes them), the first stretch's writes (window and output, raw memory), ctrl_lay_block's post (a Theorem Labs lane's
   tctrl_lay_block_post conjuncts: the journal, frames, blocks, tcj_kept), the register map at the return point and
   the run state `ge_ret` at the returned memory, the walk from 0x84cf0 reaches the statement's post. Part 6 proves
   it (gc_stretch2) from GE_post2.ge_post2 (the re-based stretch), GE_post.ge_keep_lay and GE_post.ge_post. *)
Definition ge_stretch2 : Prop :=
  forall (HBRF : reac_braid_encode_ns0_c.reac_braid_encode_ns0_contract_F)
    (HFNF : ctrl_finish_c.ctrl_finish_contract_F)
    (LAWS : AR_laws SEGS B)
    (HIMGSH : img_shadow_vis SEGS B)
    (HGM : globs_marked SEGS B GLOBS)
    (HFR_glob : In (VAL (A_OBJ A_FRAMES), 11 * ROW_BYTES) GLOBS)
    (HFR_al : VAL (A_OBJ A_FRAMES) mod 8 = 0)
    (HCAT_glob : In (VAL (A_OBJ A_CAT), 11 * CAT_BYTES) GLOBS)
    (HCAT_al : VAL (A_OBJ A_CAT) mod 8 = 0)
    (HBOX_glob : In (VAL (A_OBJ A_BOX), 6) GLOBS)
    (HROWS : forall r, 3 <= r <= 9 -> forall (H : word -> bool) mem,
       arodata_okS SEGS B RLO RHI (aview SEGS H mem) ->
       garr8 SEGS (mrestrict H mem) (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r) (map bv_unsigned (CROW r)))
    (HFR_rng : IMG_LO + 64 <= VAL (A_OBJ A_FRAMES) /\ VAL (A_OBJ A_FRAMES) + 11 * ROW_BYTES + 64 <= IMG_HI)
    (HCAT_rng : IMG_LO + 64 <= VAL (A_OBJ A_CAT) /\ VAL (A_OBJ A_CAT) + 11 * CAT_BYTES + 64 <= IMG_HI)
    (HBOX_rng : IMG_LO + 64 <= VAL (A_OBJ A_BOX) /\ VAL (A_OBJ A_BOX) + 6 + 64 <= IMG_HI)
    (RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a)
    STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k (regs : bvmap 5 word)
    (p md d c16 n r i ns : Z) (mb nb db sb : list byte)
    (mc : word -> option byte) (W2 : world SEGS) ly2 S2 (regs2 : bvmap 5 word) (mem2 : word -> option byte)
    (md2 : Model) (j0 : list byte) (P : word),
  (* the call's premises (tctrl_emit_as_spec, word for word) *)
  ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  arodata_okS SEGS B RLO RHI (aview SEGS (w_H W) memc) ->
  lib.Reusable.YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 10 = w64 p ->
  getr regs 11 = w64 (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r) -> 3 <= r <= 9 ->
  getr regs 12 = w64 md -> md = VAL (A_OBJ A_CAT) + CAT_BYTES * i -> 0 <= i < 11 ->
  getr regs 13 = w64 d ->
  getr regs 14 = w64 (VAL (A_OBJ A_BOX)) ->
  getr regs 15 = w64 c16 -> 0 <= c16 < 2 ^ 64 ->
  getr regs 16 = w64 n -> - 2 ^ 31 <= n < 2 ^ 31 ->
  getr regs 17 = w64 0 ->
  getr regs 29 = w64 ns -> - 2 ^ 31 <= ns <= 0 ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - TEMIT_STK -> spZ regs <= sp0 ->
  count_cid 1 (frames Sc) < fs_frames 1 -> count_cid 0 (frames Sc) < fs_frames 0 ->
  0 < p -> p mod 8 = 0 -> p + 1492 <= 2 ^ 47 - 8 -> amem_range p 1492 ->
  (forall x, p <= x < p + 1492 -> ~ in_img SEGS x) ->
  twr_ok (PI := PI_ctrl) B STK sp0 FP ly S lyc Sc own W memc (spZ regs) p 1492 ->
  afobj SEGS B lyc Sc W memc p 1492 ->
  (exists cid pos, In (cid, pos) (frames Sc) /\ 2 <= cid /\ frame_addr lyc cid pos <= p /\
                   p + 1492 <= frame_addr lyc cid pos + fs_frame_bytes cid) ->
  (exists cid pos, In (cid, pos) (frames Sc) /\ 2 <= cid /\ frame_addr lyc cid pos <= d /\
                   d + 6 <= frame_addr lyc cid pos + fs_frame_bytes cid) ->
  tfr_hull lyc Sc p 1492 ->
  length db = 6%nat -> garr8 SEGS (mrestrict (w_H W) memc) d (map bv_unsigned db) ->
  tsrc_ok (PI := PI_ctrl) W memc (spZ regs) d 6 -> (forall x, d <= x < d + 6 -> ~ in_img SEGS x) ->
  (p + 1492 <= d \/ d + 6 <= p) ->
  (d + 6 <= spZ regs - TEMIT_STK \/ spZ regs <= d) ->
  d mod 8 = 0 ->
  length sb = 6%nat ->
  garr8 SEGS (mrestrict (w_H W) memc) (VAL (A_OBJ A_BOX)) (map bv_unsigned sb) ->
  garr8 SEGS (mrestrict (w_H W) memc) md (map bv_unsigned mb) -> length mb = 296%nat ->
  ((RcLay.ly_bb r = 5 \/ RcLay.ly_bb r = 6) -> RcSynth.has mb <> 0 -> RcSynth.rname mb <> 0 ->
     RcBox.name_ok nb /\
     garr8 SEGS (mrestrict (w_H W) memc) (RcSynth.rname mb) (map bv_unsigned nb) /\
     (exists q sz, In (q, sz) GLOBS /\ q <= RcSynth.rname mb /\ RcSynth.rname mb + Z.of_nat (length nb) <= q + sz) /\
     (forall x, RcSynth.rname mb <= x < RcSynth.rname mb + Z.of_nat (length nb) -> in_roP SEGS RLO RHI x /\
        ~ Exists (in_zr x) (as_owned_static B) /\ ~ (as_errno B <= x < as_errno B + 4))) ->
  (* the run state at the call memory, as ge_pre takes it (FS := the layout's side stack) *)
  ro_agree rsegs memc -> asan_cells memc -> shadow_rw memc ->
  addressable memc (spZ regs - 4640) 4640 ->
  fp [0%nat; 1%nat] memc (bv_unsigned (getr regs 4)) (ly_F lyc) (spZ regs - 4640) (spZ regs)
    [(spZ regs - 4640, spZ regs); (p, p + RRr r n mb)]
    [(VAL (A_OBJ A_FRAMES) + ROW_BYTES * r, VAL (A_OBJ A_FRAMES) + ROW_BYTES * r + 24); (md, md + 296);
     (d, d + 6); (VAL (A_OBJ A_BOX), VAL (A_OBJ A_BOX) + 6); (p, p + RRr r n mb)] ->
  ctrl_emit_as_c.ctrl_emit_as_tls memc (bv_unsigned (getr regs 4)) (ly_F lyc) (spZ regs - 4640) (spZ regs) ->
  sh_cov_vis (w_H W) (spZ regs - 4640) (spZ regs - 1) ->
  (* the first stretch reached the call site: the gate is open and the memory changed only in its writes *)
  EEr r n mb = true ->
  munch [(spZ regs - 4640, spZ regs); (p, p + LENr r n)] memc mc -> wmono rsegs memc mc ->
  (* ctrl_lay_block's post at the return *)
  wle W W2 ->
  ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + EV_LAY) ->
  frames S2 = frames Sc -> ablocks B ly2 S2 = ablocks B lyc Sc ->
  tcj_kept (PI := PI_ctrl) B TLAY_STK lyc Sc W mc W2 mem2 (spZ regs + -128) (fun a => p + 18 <= a < p + 50) ->
  (* the register map at the return point: the callee-saved registers of the call site *)
  getr regs2 2 = Z_to_bv 64 (spZ regs + -128) -> getr regs2 3 = getr regs 3 -> getr regs2 4 = getr regs 4 ->
  getr regs2 18 = Z_to_bv 64 n -> getr regs2 19 = Z_to_bv 64 (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r) ->
  getr regs2 20 = Z_to_bv 64 p -> getr regs2 21 = getr regs 15 -> getr regs2 22 = Z_to_bv 64 md ->
  getr regs2 23 = Z_to_bv 64 d -> getr regs2 24 = Z_to_bv 64 0 -> getr regs2 25 = Z_to_bv 64 (VAL (A_OBJ A_BOX)) ->
  getr regs2 26 = Z_to_bv 64 (LENr r n) -> getr regs2 27 = Z_to_bv 64 ASAN_K ->
  (* the run state at the returned memory *)
  ge_ret W2 mem2 regs (ly_F lyc) p md d n r mb nb db sb j0 P ns ->
  SRr SEGS W2 (mkCfg (lib.Reusable.YK11.mkst regs2 (Z_to_bv 64 0x84cf0) mem2 (seg_rom SEGS)) md2)
    (tctrl_emit_as_post (SK := SK) B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p md c16 n r mb nb db sb).

(* ---- small facts ---- *)
Lemma gc_ro_P : forall rl rh rd, arodata_okS SEGS B rl rh rd -> arodata_okP SEGS rl rh B rd.
Proof. intros rl rh rd H a Ha. exact (H a Ha). Qed.

Lemma gc_munch_sub : forall (W1 W2 : list ivl) (m m' : word -> option byte),
  munch W1 m m' -> (forall x, outside W2 x -> outside W1 x) -> munch W2 m m'.
Proof. intros W1 W2 m m' H Hs x Hx. apply H. apply Hs. exact Hx. Qed.

Lemma gc_u64 : forall a, 0 <= a < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 a) = a.
Proof. intros a Ha. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. exact Ha. Qed.

End e.

End b.

(* ===================================================================================================== *)
(* Part 5. The run state at the memory ctrl_lay_block returns, from a Theorem Labs lane's post and ProgWorld.        *)
(* ===================================================================================================== *)
Section b. Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Context {SK : lib.Reusable.YI16.sink_head}.
#[local] Notation SEGS := AB1v.tfibsegs.
#[local] Notation VAL := (@pa_val _ ctrl_listing PI_ctrl).
Local Abbreviation LENr r n := (RcEmit.em_len (RcFin.ubat (CROW r) 21) n).
Local Abbreviation EEr r n mb :=
  (RcEmit.em_E (RcFin.ubat (CROW r) 21) (RcFin.ubat (CROW r) 22) n (RcEmit.em_hid mb)).
Section e.
Variable B : asyms.
Variable GLOBS : list (Z * Z).
Variables RLO RHI : Z.

(* rule 24: no function proved. A world / memory helper of the glue of ctrl_emit_as (image A): the run state
   `ge_ret` at the memory ctrl_lay_block returns, from the call's premises, the first stretch's writes and
   ctrl_lay_block's post. *)

(* The shadow byte of a byte of [p, p + len) lies in the shadow of the frame that tfr_hull names. *)
Lemma gcr_sh_in : forall F FB p len x,
  F mod 32 = 0 -> F <= p / 64 * 64 -> (p + len - 1) / 64 * 64 + 64 <= F + FB -> p <= x < p + len ->
  0 <= AsanRT.shadow_addr x - YG0f.shadow_addr F < FB / 8.
Proof.
  intros F FB p len x Hal H1 H2 Hx. unfold AsanRT.shadow_addr, YG0f.shadow_addr, SHADOW_OFF, ASAN_K.
  pose proof (Z.div_mod F 32 ltac:(lia)) as D32.
  pose proof (Z.div_mod F 8 ltac:(lia)) as DF. pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as BF.
  pose proof (Z.div_mod FB 8 ltac:(lia)) as DB. pose proof (Z.mod_pos_bound FB 8 ltac:(lia)) as BB.
  pose proof (Z.div_mod x 8 ltac:(lia)) as DX. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as BX.
  pose proof (Z.div_mod p 64 ltac:(lia)) as DP. pose proof (Z.mod_pos_bound p 64 ltac:(lia)) as BP.
  pose proof (Z.div_mod (p + len - 1) 64 ltac:(lia)) as DQ.
  pose proof (Z.mod_pos_bound (p + len - 1) 64 ltac:(lia)) as BQ.
  pose proof (Z.div_mod x 64 ltac:(lia)) as DX64. pose proof (Z.mod_pos_bound x 64 ltac:(lia)) as BX64.
  lia.
Qed.

(* The shadow byte of an application byte is not an application byte of the same small range. *)
Lemma gcr_sh_out : forall p len x, 0 <= p -> 50 <= len -> amem_range p len -> p <= x < p + len ->
  ~ (p + 18 <= AsanRT.shadow_addr x < p + 50).
Proof.
  intros p len x Hp Hl HA Hx. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HA.
  unfold AsanRT.shadow_addr, ASAN_K.
  pose proof (Z.div_mod x 8 ltac:(lia)) as DX. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as BX.
  lia.
Qed.

Lemma gc_ret :
  forall (HRT : ge_ctlrt_stmt B) (VIS0 : A.ProgWorld.AR_states_vis0_shadow B)
    (OWNED_RO : A.ProgWorld.AR_states_owned_ro B) (HSS : ge_stack_shadow_stmt B)
    (HFP : ge_fp_stmt B) (HTS : A.AF0m.CtrlTSyms B) (HTP : as_tp B = RT_TP) (HTSD : as_tsd B = 0x5fcbb8)
    (LAWS : AR_laws SEGS B)
    (HIMGSH : img_shadow_vis SEGS B)
    (HGM : globs_marked SEGS B GLOBS) (HFR_glob : In (VAL (A_OBJ A_FRAMES), 11 * ROW_BYTES) GLOBS)
    (HROWS : forall r, 3 <= r <= 9 -> forall (H : word -> bool) mem,
       arodata_okS SEGS B RLO RHI (aview SEGS H mem) ->
       garr8 SEGS (mrestrict H mem) (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r) (map bv_unsigned (CROW r)))
    (HFR_rng : IMG_LO + 64 <= VAL (A_OBJ A_FRAMES) /\ VAL (A_OBJ A_FRAMES) + 11 * ROW_BYTES + 64 <= IMG_HI)
    (HCAT_rng : IMG_LO + 64 <= VAL (A_OBJ A_CAT) /\ VAL (A_OBJ A_CAT) + 11 * CAT_BYTES + 64 <= IMG_HI)
    (HBOX_rng : IMG_LO + 64 <= VAL (A_OBJ A_BOX) /\ VAL (A_OBJ A_BOX) + 6 + 64 <= IMG_HI)
    (RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a)
    STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k (regs : bvmap 5 word)
    (p md d n r i ns : Z) (mb nb db sb : list byte)
    (mc : word -> option byte) (W2 : world SEGS) ly2 S2 (mem2 : word -> option byte) (md2 : Model)
    (j0 : list byte) (P : word),
  ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  arodata_okS SEGS B RLO RHI (aview SEGS (w_H W) memc) ->
  getr regs 4 = w64 (as_tp B) ->
  3 <= r <= 9 -> md = VAL (A_OBJ A_CAT) + CAT_BYTES * i -> 0 <= i < 11 ->
  sp0 - STK <= spZ regs - TEMIT_STK -> spZ regs <= sp0 -> spZ regs mod 16 = 0 ->
  0 < p -> p + 1492 <= 2 ^ 47 - 8 -> amem_range p 1492 ->
  (forall x, p <= x < p + 1492 -> ~ in_img SEGS x) ->
  twr_ok (PI := PI_ctrl) B STK sp0 FP ly S lyc Sc own W memc (spZ regs) p 1492 ->
  afobj SEGS B lyc Sc W memc p 1492 ->
  (exists cid pos, In (cid, pos) (frames Sc) /\ 2 <= cid /\ frame_addr lyc cid pos <= p /\
                   p + 1492 <= frame_addr lyc cid pos + fs_frame_bytes cid) ->
  (exists cid pos, In (cid, pos) (frames Sc) /\ 2 <= cid /\ frame_addr lyc cid pos <= d /\
                   d + 6 <= frame_addr lyc cid pos + fs_frame_bytes cid) ->
  tfr_hull lyc Sc p 1492 ->
  length mb = 296%nat ->
  EEr r n mb = true ->
  (* the call site 0x84cec, on the real memory mc *)
  munch [(spZ regs - 4640, spZ regs); (p, p + LENr r n)] memc mc -> wmono rsegs memc mc ->
  length j0 = 8%nat ->
  rw_cells rsegs mc (spZ regs + -128)
    (CB 8 j0 :: C8 P :: C8 (Z_to_bv 64 ns) ::
     [C8 (getr regs 27); C8 (getr regs 26); C8 (getr regs 25); C8 (getr regs 24); C8 (getr regs 23);
      C8 (getr regs 22); C8 (getr regs 21); C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18);
      C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)]) ->
  rw_cells rsegs mc p [CB 6 db] -> rw_cells rsegs mc (p + 6) [CB 6 sb] ->
  rw_cells rsegs mc (p + 12)
    [CB 6 [Z_to_bv 8 136; Z_to_bv 8 25; Z_to_bv 8 ((bv_unsigned (getr regs 15) mod 65536) mod 256);
           Z_to_bv 8 ((bv_unsigned (getr regs 15) mod 65536) / 256); nth 0 (CROW r) (Z_to_bv 8 0);
           nth 1 (CROW r) (Z_to_bv 8 0)]] ->
  rw_cells rsegs mc (p + 50) [CB (Z.to_nat (LENr r n - 52)) (repeat (Z_to_bv 8 0) (Z.to_nat (LENr r n - 52)))] ->
  rw_cells rsegs mc (p + LENr r n + -2) [CB 2 (repeat (Z_to_bv 8 0) 2)] ->
  addressable mc p (LENr r n) ->
  (* ctrl_lay_block's post (a Theorem Labs lane's tctrl_lay_block_post conjuncts) *)
  wle W W2 ->
  ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + EV_LAY) ->
  frames S2 = frames Sc ->
  garr8 SEGS (mrestrict (w_H W2) mem2) (p + 18) (C_reac_box_model_block.bmb_z (RcLay.ly_Z md mb nb (RcLay.ly_bb r))) ->
  tcj_kept (PI := PI_ctrl) B TLAY_STK lyc Sc W mc W2 mem2 (spZ regs + -128) (fun a => p + 18 <= a < p + 50) ->
  ge_ret W2 mem2 regs (ly_F lyc) p md d n r mb nb db sb j0 P ns.
Proof.
  intros HRT VIS0 OWNED_RO HSS HFP HTS HTP HTSD LAWS HIMGSH HGM HFR_glob HROWS HFR_rng HCAT_rng HBOX_rng RELRO_IMG
    STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p md d n r i ns mb nb db sb mc W2 ly2 S2 mem2 md2
    j0 P HJ HRO Htp Hr Hmd Hi Hslo Hshi Hsp16 Hp Hpe Hpam Hpni Hptw Hpfo HPC HDC Hpfh Hmbl HE
    MUc WMc Lj0 FRc P1 P2 P3 P5 P6 AOc Hle HJ2 FR2 GA KEPT.
  (* ---- the two journals: AR, the layout, the presence clause, the stack bounds ---- *)
  pose proof HJ as (HAR & HLE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRES & HSTK & _).
  destruct HSTK as (_ & _ & HCEIL & HSLO & HSHI & H47 & _).
  destruct HLE as (_ & _ & _ & _ & _ & ECF & _ & _ & _ & EClo & EChi & _).
  pose proof HJ2 as (HAR2 & HLE2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRES2 & _).
  destruct HLE2 as (_ & _ & _ & _ & _ & E2F & _ & _ & _ & E2lo & E2hi & _).
  pose proof asan_consts as (CV & _ & _ & _ & _).
  assert (HT : TEMIT_STK = 4640) by reflexivity.
  pose proof (RcEmitLib.em_len_rng _ _ _ _ HE) as RLE.
  destruct KEPT as (K1 & K2 & K3 & K4 & K5 & K6).
  (* ---- the read-only data at (W, mc) and at (W2, mem2) ---- *)
  assert (IMGO : forall a, in_img SEGS a -> outside [(spZ regs - 4640, spZ regs); (p, p + LENr r n)] a).
  { intros a Hia. pose proof (ctrl_segs_low a Hia) as Hlow. cbn [outside].
    split; [unfold kLowMemEnd in Hlow; lia | split; [intros Ha; apply (Hpni a); [lia | exact Hia] | exact I]]. }
  assert (HROc : arodata_okS SEGS B RLO RHI (aview SEGS (w_H W) mc))
    by exact (ge_ro_keep B (w_H W) RLO RHI memc mc _ RELRO_IMG HRO MUc IMGO).
  assert (HRO2 : arodata_okS SEGS B RLO RHI (aview SEGS (w_H W2) mem2))
    by exact (gc_ro_view B W W2 mc mem2 RLO RHI RELRO_IMG HROc K3).
  destruct (HRT LAWS VIS0 OWNED_RO RLO RHI ly2 S2 W2 mem2 md2 HAR2 (gc_ro_P B _ _ _ HRO2)) as (RAC & RSW & RRO).
  (* ---- the frames ---- *)
  assert (Htp' : bv_unsigned (getr regs 4) = RT_TP).
  { rewrite Htp, HTP. unfold w64. apply gc_u64. unfold RT_TP. lia. }
  pose proof HPC as (cid & pos & HinP & Hc2 & HfaP & HfeP).
  pose proof HDC as (cid' & pos' & HinD & Hc2' & HfaD & HfeD).
  assert (EFA : forall c q, frame_addr ly2 c q = frame_addr lyc c q).
  { intros c q. unfold frame_addr. rewrite E2F, ECF. reflexivity. }
  pose proof Hpfh as (ch & ph & Hinh & _ & Hh1 & Hh2).
  destruct (al_frames _ _ LAWS lyc Sc W memc mdc ch ph HAR Hinh) as (Hal & _ & _ & Hshpres).
  (* ---- the output cells other than the laid block ---- *)
  assert (OUT : forall a cs, rw_cells rsegs mc a cs ->
     p <= a -> a + Z.of_nat (cells_size cs) <= p + LENr r n ->
     (a + Z.of_nat (cells_size cs) <= p + 18 \/ p + 50 <= a) ->
     rw_cells rsegs mem2 a cs).
  { intros a cs Hc Ha1 Ha2 Ha3. apply (gc_rw_view W W2 mc mem2 a cs Hc).
    intros j Hj.
    assert (Hx : p <= a + j < p + 1492) by lia.
    destruct (Hptw (a + j) Hx) as (_ & (Hh0 & _) & _ & _).
    assert (Hh : w_H W (Z_to_bv 64 (a + j)) = false) by exact Hh0.
    split; [apply Hpni; exact Hx|].
    split; [exact Hh|].
    split.
    - destruct (w_H W2 (Z_to_bv 64 (a + j))) eqn:E; [|reflexivity].
      rewrite (Hle _ E) in Hh. discriminate.
    - apply (K4 cid pos); [exact HinP | left; unfold in_zr, frame_rng; cbn [fst snd]; lia | cbv beta; lia]. }
  unfold ge_ret. change (bv_unsigned (getr regs 2)) with (spZ regs).
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _
    (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))))))))))))))))))).
  - (* asan_cells *) exact RAC.
  - (* shadow_rw *) exact RSW.
  - (* the window addressable *)
    apply (HSS LAWS ly2 S2 W2 mem2 md2); [exact HAR2 | lia | lia | lia].
  - (* the output addressable *)
    apply (gc_addr_view W W2 mc mem2 p (LENr r n) AOc).
    intros j Hj.
    pose proof (gcr_sh_in (frame_addr lyc ch ph) (fs_frame_bytes ch) p 1492 (p + j) Hal Hh1 Hh2 ltac:(lia))
      as Hs.
    destruct (Hshpres _ Hs) as ((Hh & _) & _).
    replace (YG0f.shadow_addr (frame_addr lyc ch ph) +
             (AsanRT.shadow_addr (p + j) - YG0f.shadow_addr (frame_addr lyc ch ph)))
      with (AsanRT.shadow_addr (p + j)) in Hh by lia.
    split; [exact Hh|]. split.
    + destruct (w_H W2 (Z_to_bv 64 (AsanRT.shadow_addr (p + j)))) eqn:E; [|reflexivity].
      rewrite (Hle _ E) in Hh. discriminate.
    + apply (K4 ch ph); [exact Hinh | right; unfold in_zr; cbn [fst snd]; lia | cbv beta].
      exact (gcr_sh_out p 1492 (p + j) ltac:(lia) ltac:(lia) Hpam ltac:(lia)).
  - (* fp *)
    rewrite Htp'. replace (ly_F lyc) with (ly_F ly2) by congruence.
    apply (gc_fp_emit B ly2 S2 W2 mem2 md2 (spZ regs - 4640) (spZ regs) _ md d _ p (LENr r n) cid pos cid' pos'
             LAWS (HFP LAWS) HAR2); rewrite ?FR2, ?EFA; try lia; try assumption.
    all: try (unfold ROW_BYTES, CAT_BYTES in *; lia).
    all: rewrite HTSD; unfold IMG_LO, IMG_HI; lia.
  - (* the thread cells *)
    rewrite Htp'. replace (ly_F lyc) with (ly_F ly2) by congruence.
    exact (gc_tls_AR' B ly2 S2 W2 mem2 md2 (spZ regs - 4640) (spZ regs) HTS LAWS HAR2
             ltac:(lia) ltac:(lia) ltac:(lia)).
  - (* the window below the call's frame present *)
    apply (ge_present_stk (w_H W2) mem2); [lia | lia | intros a Ha; apply HPRES2; lia].
  - (* ro_agree *) exact RRO.
  - (* length j0 *) exact Lj0.
  - (* the frame cells at spZ regs + -128 *)
    apply (gc_rw_view W W2 mc mem2 _ _ FRc).
    intros j Hj. cbn [cells_size csize] in Hj.
    split; [intros Hia; pose proof (ctrl_segs_low _ Hia); unfold kLowMemEnd in *; lia|].
    split; [exact (proj1 (HPRES (spZ regs + -128 + j) ltac:(lia)))|].
    split; [exact (proj1 (HPRES2 (spZ regs + -128 + j) ltac:(lia)))|].
    apply K1; [lia | lia |].
    cbv beta. intros Hin. destruct (Hptw (spZ regs + -128 + j) ltac:(lia)) as (_ & _ & _ & Hes).
    apply Hes. unfold ESTACK. lia.
  - (* the row's bytes *) exact (ge_row_bytes B RLO RHI HROWS HFR_rng W2 mem2 r HRO2 Hr).
  - (* the row addressable *)
    exact (ge_row_addr B GLOBS HGM HFR_glob HFR_rng _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ r HJ2 Hr).
  - (* db *) apply OUT; [exact P1 | cbn [cells_size csize]; lia .. ].
  - (* sb *) apply OUT; [exact P2 | cbn [cells_size csize]; lia .. ].
  - (* the header *) apply OUT; [exact P3 | cbn [cells_size csize]; lia .. ].
  - (* the laid block *)
    rewrite (ge_row_LB r md mb nb [] [] Hr).
    assert (HZl : length (RcLay.ly_Z md mb nb (RcLay.ly_bb r)) = 32%nat).
    { unfold RcLay.ly_Z. destruct (md =? 0); [reflexivity|].
      destruct (RcSynth.rc mb (RcLay.ly_bb r) =? 1); [exact (RcSynthLib.rs_synth_len mb _ nb Hmbl) | reflexivity]. }
    assert (HB : bytes_at rsegs mem2 (p + 18) (RcLay.ly_Z md mb nb (RcLay.ly_bb r))).
    { apply (ge_bytes_of_garr8 W2 mem2); [lia | rewrite HZl; lia | exact GA]. }
    unfold rw_cells, cells_at, wr_at.
    split; [split; [cbn [cells_wf cell_wf]; split; [exact HZl | exact I] | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact HB]|].
    cbn [cells_size csize].
    split; [lia|]. split; [lia|].
    intros j Hj.
    assert (Hx : 0 <= p + 18 + j < 2 ^ 64) by lia.
    assert (Hn : ~ in_img SEGS (p + 18 + j)) by (apply Hpni; lia).
    rewrite (gcv_wview_noimg mem2 _ Hx Hn), <- (gcv_mrd_noimg mem2 _ Hx Hn).
    destruct HB as (_ & _ & HBn).
    replace (p + 18 + j) with (p + 18 + Z.of_nat (Z.to_nat j)) by lia.
    rewrite (HBn (Z.to_nat j) ltac:(rewrite HZl; lia)).
    intros E. apply nth_error_None in E. rewrite HZl in E. lia.
  - (* the zeros *) apply OUT; [exact P5 | cbn [cells_size csize]; lia .. ].
  - (* the trailer *) apply OUT; [exact P6 | cbn [cells_size csize]; lia .. ].
  - (* the window visible *)
    exact (proj1 (ge_win B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + EV_LAY) regs HJ2 Hslo Hshi)).
  - (* the window's shadow cover *)
    destruct (A.ProgWorldVisWin.win_sh_vis B LAWS ly2 S2 W2 mem2 md2 (spZ regs - 4640) 4640 HAR2
                ltac:(lia) ltac:(lia) ltac:(lia)) as [E0 | V]; [lia |].
    replace (spZ regs - 1) with (spZ regs - 4640 + 4640 - 1) by lia.
    exact (gc_shcov_of_al8 (w_H W2) (spZ regs - 4640) 4640 ltac:(lia) V).
  - (* the row visible *) exact (ge_row_vis HFR_rng W2 r Hr).
  - (* the row's shadow cover *)
    exact (ge_row_shcov B HIMGSH HFR_rng _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ r HJ2 Hr).
  - (* md's shadow cover *)
    exact (ge_md_shcov B HIMGSH HCAT_rng _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ md i HJ2 Hmd Hi).
  - (* the output visible *)
    destruct (ge_buf_rw B STK sp0 FP ly S lyc Sc own W memc regs p (LENr r n) Hp Hpe Hptw ltac:(lia)) as [VB _].
    exact (gc_vis_wle W W2 _ _ Hle VB).
  - (* the output's shadow cover *)
    exact (gc_shcov_wle W W2 _ _ Hle
             (ge_buf_shcov B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k p (LENr r n) LAWS HJ Hp Hpe Hpfh
                ltac:(lia))).
Qed.

End e. End b.

From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import GE_lift GE_entry GE_cut GE_jal.
(* the glue's parts for the two stretches and the post, Required qualified (their names are written with the module) *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require GE_pre GE_post GE_post2.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Regs6ss.
Import ListNotations.
Open Scope Z_scope.
(* The closure leaves zify's euclidean-division conversion switched off (A/AE2q.v and its siblings set the flag
   to false); the composition's arithmetic over shadow addresses (x / 8) needs it on. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* ===================================================================================================== *)
(* Part 6. The composition.                                                                               *)
(* ===================================================================================================== *)
Section b. Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Context {SK : lib.Reusable.YI16.sink_head}.
#[local] Notation SEGS := AB1v.tfibsegs.
#[local] Notation VAL := (@pa_val _ ctrl_listing PI_ctrl).
#[local] Notation BASE := (@pa_val _ ctrl_listing PI_ctrl A_TEXT).
#[local] Notation PA_RLO := (@pa_relro_lo _ ctrl_listing PI_ctrl).
#[local] Notation PA_RHI := (@pa_relro_hi _ ctrl_listing PI_ctrl).

(* ctrl_emit_asF2.v's Local Abbreviations at row := CROW r, g := 0 (as GE_post.v writes them). *)
Local Abbreviation EEr r n mb :=
  (RcEmit.em_E (RcFin.ubat (CROW r) 21) (RcFin.ubat (CROW r) 22) n (RcEmit.em_hid mb)).
Local Abbreviation LENr r n := (RcEmit.em_len (RcFin.ubat (CROW r) 21) n).
Local Abbreviation RRr r n mb := (if EEr r n mb then LENr r n else 0).
Local Abbreviation BLKr r md mb nb tb gb :=
  (RcFin.fin (RcFin.ubat (CROW r) 20) (RcFin.ubat (CROW r) 18) (RcFin.ubat (CROW r) 19)
     (RcLay.ly_lay (RcLay.ly_k (CROW r)) tb (RcLay.ly_Z md mb nb (RcLay.ly_bb (RcLay.ly_k (CROW r)))) 0
        (RcLay.ly_ao (CROW r)) (RcLay.ly_al (CROW r)) gb)).

(* ---- facts the cut at 0x84cec uses ---- *)
Lemma gc_addr_rel : forall m m0 p n, mem_rel rsegs m m0 -> addressable m0 p n -> addressable m p n.
Proof.
  intros m m0 p n REL (H0 & H1 & H2 & H). split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hok). split; [exact Ha|].
  exists b. split; [|exact Hok]. rewrite (mrd_rel rsegs m m0 _ REL). exact Hb.
Qed.

Lemma gc_garr8_munch : forall (WR : list ivl) (H : word -> bool) (m m' : word -> option byte) a (l : list Z),
  munch WR m m' ->
  (forall j, (j < length l)%nat -> 0 <= a + Z.of_nat j < 2 ^ 64 /\ outside WR (a + Z.of_nat j)) ->
  garr8 SEGS (mrestrict H m) a l -> garr8 SEGS (mrestrict H m') a l.
Proof.
  intros WR H m m' a l MU G HG j Hj. destruct (HG j Hj) as [V R]. split; [|exact R].
  intros kk Hk. assert (kk = 0%nat) by lia. subst kk. pose proof (V 0%nat Hk) as V0.
  destruct (G j Hj) as [Rg Og]. replace (a + Z.of_nat j + Z.of_nat 0) with (a + Z.of_nat j) in * by lia.
  rewrite <- V0. unfold mbyte, mrestrict. destruct (H (Z_to_bv 64 (a + Z.of_nat j))); [reflexivity|].
  rewrite (MU (Z_to_bv 64 (a + Z.of_nat j))); [reflexivity|]. rewrite gc_u64 by lia. exact Og.
Qed.

Lemma gc_present_wmono : forall (H : word -> bool) (m m' : word -> option byte) a,
  wmono rsegs m m' -> 0 <= a < 2 ^ 64 -> ~ in_img SEGS a -> apresent H m a -> apresent H m' a.
Proof.
  intros H m m' a WM Ha Hni (Hh & b & Hb). split; [exact Hh|].
  assert (Hw : wview rsegs m (Z_to_bv 64 a) <> None) by (unfold wview; rewrite Hb; discriminate).
  pose proof (WM _ Hw) as Hw'. unfold wview in Hw'.
  destruct (m' (Z_to_bv 64 a)) as [b'|] eqn:E; [exists b'; reflexivity|]. exfalso. apply Hw'.
  rewrite gc_u64 by exact Ha. rewrite <- ge_segs. rewrite (find_segment_none SEGS a Hni). reflexivity.
Qed.

Lemma gc_div64 : forall x y, x <= y -> x / 64 * 64 <= y / 64 * 64.
Proof.
  intros x y H. pose proof (Z.div_le_mono x y 64 ltac:(lia) H). lia.
Qed.

(* Every byte of [IMG_LO, IMG_HI) lies in a segment (GE_pre.v ge_img_in, word for word). *)
Lemma gc_img_in : forall x, IMG_LO <= x < IMG_HI -> in_img SEGS x.
Proof.
  intros x Hx.
  assert (G : forall b sz, In (b, sz) (map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s))) rsegs) ->
    b <= x < b + sz -> in_img SEGS x).
  { intros b sz Hin Hb. apply in_map_iff in Hin as (sg & E & Hsg). injection E as <- <-.
    exists sg. split; [exact Hsg | exact Hb]. }
  rewrite rsegs_spans in G. unfold IMG_LO, IMG_HI in Hx.
  destruct (Z_lt_le_dec x 0x30000) as [h1 | h1].
  { apply (G 0x10000 0x20000); [left; reflexivity | lia]. }
  destruct (Z_lt_le_dec x 0x9e000) as [h2 | h2].
  { apply (G 0x30000 0x6e000); [right; left; reflexivity | lia]. }
  destruct (Z_lt_le_dec x 0xa1000) as [h3 | h3].
  { apply (G 0x9e000 0x3000); [right; right; left; reflexivity | lia]. }
  apply (G 0xa1000 0x55d000); [right; right; right; left; reflexivity | lia].
Qed.

Lemma gc_sh_out : forall x p len lo hi ceil,
  0 <= x -> x < ceil -> ceil <= 140737479966720 -> 140735332483072 <= ceil -> ceil <= lo -> lo <= hi ->
  0 <= len <= 1492 -> amem_range p 1492 -> 0 <= p ->
  0 <= 2147450880 + x / 8 < 2 ^ 64 /\ outside [(lo, hi); (p, p + len)] (2147450880 + x / 8).
Proof.
  intros x p len lo hi ceil H0 H1 H2 H3 H4 H5 H6 H7 H8. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in H7.
  cbn [outside]. split; [lia|]. split; [lia | split; [lia | exact I]].
Qed.

Local Ltac gc_ne1 := let E := fresh "E" in intro E; apply (f_equal bv_unsigned) in E; discriminate E.

(* A byte that is not outside the two-range window [lo, hi) U [q, q + l) is in one of them. *)
Lemma gc_not_out2 : forall lo hi q l a, ~ outside [(lo, hi); (q, q + l)] a -> (lo <= a < hi) \/ (q <= a < q + l).
Proof.
  intros lo hi q l a H.
  destruct (Z.le_gt_cases lo a) as [L1 | L1]; [destruct (Z.lt_ge_cases a hi) as [L2 | L2]|].
  - left. lia.
  - destruct (Z.le_gt_cases q a) as [L3 | L3]; [destruct (Z.lt_ge_cases a (q + l)) as [L4 | L4]|].
    + right. lia.
    + exfalso. apply H. cbn [outside]. split; [lia|]. split; [lia | exact I].
    + exfalso. apply H. cbn [outside]. split; [lia|]. split; [lia | exact I].
  - destruct (Z.le_gt_cases q a) as [L3 | L3]; [destruct (Z.lt_ge_cases a (q + l)) as [L4 | L4]|].
    + right. lia.
    + exfalso. apply H. cbn [outside]. split; [lia|]. split; [lia | exact I].
    + exfalso. apply H. cbn [outside]. split; [lia|]. split; [lia | exact I].
Qed.

(* awr_byte reads the layout only through ly_F (frame_addr), which a journal keeps. *)
Lemma gc_awr_ly : forall STK sp0 (FP bl0 bl : list (Z * Z)) (ly ly' : alayout) (own : list (Z * Z)) a,
  ly_F ly' = ly_F ly -> awr_byte STK sp0 FP bl0 bl ly own a -> awr_byte STK sp0 FP bl0 bl ly' own a.
Proof. intros STK sp0 FP bl0 bl ly ly' own a E H. unfold awr_byte, in_frames, frame_addr in *. rewrite E. exact H. Qed.


Section m.
Variable B : asyms.
Variable GLOBS : list (Z * Z).
Variables RLO RHI : Z.

(* The second stretch and the post at the return point. *)
Lemma gc_stretch2 : ge_stretch2 B GLOBS RLO RHI.
Proof.
  unfold ge_stretch2.
  intros HBRF HFNF LAWS HIMGSH HGM HFR_glob HFR_al HCAT_glob HCAT_al HBOX_glob HROWS HFR_rng HCAT_rng HBOX_rng
    RELRO_IMG STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p md d c16 n r i ns mb nb db sb
    mc W2 ly2 S2 regs2 mem2 md2 j0 P
    HJ HRO Hret Hra4 Hgp Htp Hr10 Hr11 Hr Hr12 Hmd Hi Hr13 Hr14 Hr15 Hc16 Hr16 Hn Hr17 Hr29 Hns
    Hsp16 Hslo Hshi HC1 HC0 Hp Hp8 Hpe Hpam Hpni Hptw Hpfo HPC HDC Hpfh Hdl HdG Hdsrc Hdni Hdp Hds Hd8
    Hsl HsG HmG Hml HNB RO AC SW AWIN FP0 TLS0 SHW HE MUr WMr Hle J2 FR BL KEPT
    E2 E3 E4 E18 E19 E20 E21 E22 E23 E24 E25 E26 E27 RET.
  pose proof (RcEmitLib.em_len_rng _ _ _ _ HE) as RLE.
  pose proof RET as RET'.
  destruct RET' as (AC5 & SW5 & AW5 & AO5 & FP5 & TL5 & ST5r0 & RO5 & Lj0 & FR5 & HR5 & Af5 & P15 & P25 & P35 & P45 &
                    P55 & P65 & VWIN & VWSH & VROW & VROWS & VMDS & VOB & VOBS).
  (* the re-based second stretch, from the return point 0x84cf0 on the memory ctrl_lay_block returns *)
  refine (ge_entry W2 0x84cf0 regs2 mem2 md2 _ _ ctrl_wx _ _).
  { rewrite E2, E3, E4, E18, E19, E20, E21, E22, E23, E24, E25, E26, E27.
    exact (GE_post2.ge_post2 B GLOBS RLO RHI HBRF HFNF LAWS HIMGSH HGM HFR_glob HFR_al HCAT_glob HFR_rng HCAT_rng
             HBOX_rng RELRO_IMG STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k W2 mem2 regs (ly_F lyc)
             p md d n r i ns mb nb db sb j0 P
             (getr regs2 1) (getr regs2 5) (getr regs2 6) (getr regs2 7) (getr regs2 8) (getr regs2 9)
             (getr regs2 10) (getr regs2 11) (getr regs2 12) (getr regs2 13) (getr regs2 14) (getr regs2 15)
             (getr regs2 16) (getr regs2 17) (getr regs2 28) (getr regs2 29) (getr regs2 30) (getr regs2 31)
             AC5 SW5 AW5 AO5 FP5 TL5 ST5r0 RO5 Lj0 FR5 HR5 Af5 P15 P25 P35 P45 P55 P65
             VWIN VWSH VROW VROWS VMDS VOB VOBS
             HE HJ Hr Hmd Hi Hn Hslo Hshi Hp Hpe Hpam Hpni Hptw Hpfo Hpfh Hdl Hdsrc Hdp Hd8 Hsl Hml HNB RO Hns Hle). }
  intros ms5 md5 (s5 & HQ5 & Hrel5 & Hros5) Hhid5 Hsame5.
  destruct HQ5 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
                   Es5 & MU5 & WM5 & MI5 & ST5 & AC5' & SW5' & AW5' & FP5' & RES).
  rewrite Es5 in Hrel5.
  destruct (ms_rel_MS _ _ _ _ _ _ _ _ Hrel5) as [Ems5 REL5].
  rewrite Ems5.
  pose proof (mem_rel_normalize rsegs mem2 RO5) as REL05.
  assert (MU5r : munch [(spZ regs - 4640, spZ regs); (p, p + LENr r n)] mem2 (ms_mem ms5))
    by exact (munch_rel rsegs _ _ _ _ _ REL05 REL5 Hros5 MU5).
  assert (WM5r : wmono rsegs mem2 (ms_mem ms5)) by exact (wmono_rel rsegs _ _ _ _ REL05 REL5 Hros5 WM5).
  assert (ST5r : stk rsegs (ms_mem ms5) (spZ regs - 4640) (spZ regs)) by exact (stk_of_rel _ _ _ _ REL5 ST5).
  (* the side stack's base is the same in the two layouts (layout_le of the two journals) *)
  assert (EF2 : ly_F ly2 = ly_F lyc).
  { pose proof HJ as (_ & HLE1 & _). pose proof J2 as (_ & HLE2 & _).
    destruct HLE1 as (_ & _ & _ & _ & _ & F1 & _). destruct HLE2 as (_ & _ & _ & _ & _ & F2 & _).
    rewrite F1, F2. reflexivity. }
  (* the caller's journal across the second stretch: it writes the window and the output only *)
  assert (HJ5 : ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 (ms_mem ms5) md5 (k + EV_LAY)).
  { apply (ge_jrnl B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + EV_LAY) md5
             [(spZ regs - 4640, spZ regs); (p, p + LENr r n)] (ms_mem ms5) LAWS J2 MU5r WM5r Hhid5 Hsame5).
    intros a Ha Ho. destruct (gc_not_out2 _ _ _ _ _ Ho) as [Hw | Ho2].
    - unfold awr_byte. left. assert (HT : TEMIT_STK = 4640) by reflexivity. lia.
    - destruct (Hptw a ltac:(lia)) as (Haw & _).
      rewrite BL. exact (gc_awr_ly _ _ _ _ _ lyc ly2 own a EF2 Haw). }
  assert (HE' : RcEmit.em_E (EM_L r) (EM_G r) n (RcEmit.em_hid mb) = true)
    by (rewrite <- (ge_row_E r n mb); exact HE).
  pose proof (GE_post.ge_keep_lay B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n r mb mc W2 mem2
                (ms_mem ms5) LAWS HJ Hslo Hshi Hpni HE MUr WMr Hle KEPT MU5r WM5r ST5r) as KEEP.
  apply (SRr_ret SEGS).
  apply (GE_post.ge_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p md c16 n r mb nb db sb [] []
           W2 ly2 S2 (ms_mem ms5) md5 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'
           Hret Hr15 Hc16 Hr Hptw Hml Hdl Hsl Hle).
  - intros HE0. destruct (RES HE0) as (RB & _). exact (proj2 (bytes_at_rel rsegs _ _ _ _ REL5) RB).
  - rewrite HE'. exact HJ5.
  - exact FR.
  - exact BL.
  - exact KEEP.
Qed.

Theorem pb_ctrl_emit_as :
  forall (HTS : A.AF0m.CtrlTSyms B)
    (VIS0 : A.ProgWorld.AR_states_vis0_shadow B)
    (HRLO : RLO = PA_RLO) (HRHI : RHI = PA_RHI),
  pb_ctrl_emit_as_stmt (SK := SK) B GLOBS RLO RHI.
Proof.
  intros HTS VIS0 HRLO HRHI.
  (* the owned read-only bytes of the bundle: a Theorem Labs lane's proved lemma, at CtrlTSyms B *)
  pose proof (A.ProgWorldOwnedRo.AR_states_owned_ro_of_AR B HTS) as OWNED_RO.
  (* a Theorem Labs lane's facts at CtrlTSyms B, in the forms the glue's parts state them *)
  assert (HRT' : ge_ctlrt_stmt B) by (intros L V O; exact (A.ProgWorldCtlRt.ctlrt_of_AR B HTS L V O)).
  (* VIS0 / OWNED_RO are used as they are: their types are a Theorem Labs lane's statements. *)
  assert (HSS' : ge_stack_shadow_stmt B) by exact (A.ProgWorldShadow.ctl_stack_shadow_of_AR B).
  assert (HFP : ge_fp_stmt B) by (intros L; exact (A.ProgWorld_Fs.ctl_fp_of_AR B HTS L)).
  pose proof (A.ProgWorld.as_tp_RT_TP B HTS) as HTP.
  assert (HTSD : as_tsd B = 0x5fcbb8) by (rewrite (A.AF0m.ts_tsd B HTS); vm_compute; reflexivity).
  unfold pb_ctrl_emit_as_stmt.
  intros TL LAWS ML HMSF HMCF HBRF HFNF TLAY HIMGSH HGM HFR_glob HFR_al HCAT_glob HCAT_al HBOX_glob HROWS
    HFR_rng HCAT_rng HBOX_rng RELRO_IMG.
  unfold tctrl_emit_as_spec.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p md d c16 n r i ns mb nb db sb
    HJ HRO Hret Hra4 Hgp Htp Hr10 Hr11 Hr Hr12 Hmd Hi Hr13 Hr14 Hr15 Hc16 Hr16 Hn Hr17 Hr29 Hns
    Hsp16 Hslo Hshi HC1 HC0 Hp Hp8 Hpe Hpam Hpni Hptw Hpfo HPC HDC Hpfh Hdl HdG Hdsrc Hdni Hdp Hds Hd8
    Hsl HsG HmG Hml HNB.
  (* ---- the run state at the call, from the caller's journal (its AR conjunct) and ProgWorld ---- *)
  pose proof HJ as HJ'.
  destruct HJ' as (HAR & HLE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRES & HSTK & _).
  destruct HSTK as (_ & _ & HCEIL & HSLO & HSHI & H47 & _).
  destruct HLE as (_ & _ & _ & _ & _ & EF & _ & _ & _ & Eslo & Eshi & _).
  assert (HT : TEMIT_STK = 4640) by reflexivity.
  assert (Wlo : ly_stk_lo lyc <= spZ regs - 4640) by lia.
  assert (Whi : spZ regs <= ly_stk_hi lyc) by lia.
  destruct (HRT' LAWS VIS0 OWNED_RO RLO RHI lyc Sc W memc mdc HAR (gc_ro_P B _ _ _ HRO)) as (RAC & RSW & RRO).
  assert (RO : ro_agree rsegs memc) by exact RRO.
  assert (AC : asan_cells memc) by exact RAC.
  assert (SW : shadow_rw memc) by exact RSW.
  assert (AWIN : addressable memc (spZ regs - 4640) 4640).
  { apply (HSS' LAWS lyc Sc W memc mdc); [exact HAR | lia | lia | lia]. }
  assert (Htp' : bv_unsigned (getr regs 4) = RT_TP).
  { change (bv_unsigned (lib.Reusable.YK11.getr regs 4) = RT_TP).
    rewrite Htp, HTP. unfold w64. apply gc_u64. unfold RT_TP. lia. }
  pose proof HPC as (cid & pos & HinP & Hc2 & HfaP & HfeP).
  pose proof HDC as (cid' & pos' & HinD & Hc2' & HfaD & HfeD).
  assert (RLN : 0 <= RRr r n mb <= 1492).
  { destruct (EEr r n mb) eqn:E; [pose proof (RcEmitLib.em_len_rng _ _ _ _ E); lia | lia]. }
  assert (FP0 : fp [0%nat; 1%nat] memc (bv_unsigned (getr regs 4)) (ly_F lyc) (spZ regs - 4640) (spZ regs)
    [(spZ regs - 4640, spZ regs); (p, p + RRr r n mb)]
    [(VAL (A_OBJ A_FRAMES) + ROW_BYTES * r, VAL (A_OBJ A_FRAMES) + ROW_BYTES * r + 24); (md, md + 296);
     (d, d + 6); (VAL (A_OBJ A_BOX), VAL (A_OBJ A_BOX) + 6); (p, p + RRr r n mb)]).
  { rewrite Htp'.
    apply (gc_fp_emit B lyc Sc W memc mdc (spZ regs - 4640) (spZ regs) _ md d _ p (RRr r n mb) cid pos cid' pos'
             LAWS (HFP LAWS) HAR); try lia.
    all: try (unfold ROW_BYTES, CAT_BYTES in *; lia).
    all: try assumption.
    all: rewrite HTSD; unfold IMG_LO, IMG_HI; lia. }
  assert (TLS0 : ctrl_emit_as_c.ctrl_emit_as_tls memc (bv_unsigned (getr regs 4)) (ly_F lyc)
                   (spZ regs - 4640) (spZ regs)).
  { rewrite Htp'. apply (gc_tls_AR' B lyc Sc W memc mdc); [exact HTS | exact LAWS | exact HAR | lia | lia | lia]. }
  assert (SHW : sh_cov_vis (w_H W) (spZ regs - 4640) (spZ regs - 1)).
  { destruct (A.ProgWorldVisWin.win_sh_vis B LAWS lyc Sc W memc mdc (spZ regs - 4640) 4640 HAR
               ltac:(lia) ltac:(lia) ltac:(lia)) as [E | V]; [lia |].
    replace (spZ regs - 1) with (spZ regs - 4640 + 4640 - 1) by lia.
    exact (gc_shcov_of_al8 _ (spZ regs - 4640) 4640 ltac:(lia) V). }
  (* ---- the first lifted stretch ---- *)
  apply (ge_entry W (BASE + AF_ctrl_emit_as) regs memc mdc _ _ ctrl_wx
           (GE_pre.ge_pre B GLOBS RLO RHI HMSF HMCF LAWS HIMGSH HGM HFR_glob HFR_al HCAT_glob HCAT_al HBOX_glob HROWS
              HFR_rng HCAT_rng
              HBOX_rng RELRO_IMG STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p md d n r i ns
              (ly_F lyc) mb nb db sb HJ HRO Hr10 Hr11 Hr Hr12 Hmd Hi Hr13 Hr14 Hr16 Hn Hr17 Hr29 Hslo Hshi Hp
              Hpe Hpam Hpni Hptw Hpfo Hpfh Hdl HdG Hdsrc Hdp Hds Hd8 Hsl HsG HmG Hml HNB RO AC SW AWIN FP0 TLS0
              SHW)).
  intros ms' mdc' (s0 & Hmid & Hrel & Hros) Hhid Hsame.
  pose proof (mem_rel_normalize rsegs memc RO) as REL0.
  unfold ctrl_emit_asF2.aMid in Hmid.
  destruct Hmid as [HQ | HAT].
  - (* ---- the early return (EE = false): the run's own window is the stack window alone ---- *)
    destruct HQ as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
                    Es0 & MU & WM & MI & ST & ACq & SWq & AWq & FPq & RES).
    rewrite Es0 in Hrel.
    destruct (ms_rel_MS _ _ _ _ _ _ _ _ Hrel) as [Ems REL].
    rewrite Ems.
    assert (MUs : munch [(spZ regs - 4640, spZ regs)] memc (ms_mem ms'))
      by exact (munch_rel rsegs _ _ _ _ _ REL0 REL Hros MU).
    assert (WMr : wmono rsegs memc (ms_mem ms')) by exact (wmono_rel rsegs _ _ _ _ REL0 REL Hros WM).
    assert (HJm : ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms') mdc' k).
    { apply (ge_jrnl_win B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k mdc' (ms_mem ms') (spZ regs) 4640
               p 1492 W memc (spZ regs) LAWS HJ); [| exact WMr | exact Hhid | exact Hsame | lia | lia | exact Hptw].
      apply (gc_munch_sub _ _ _ _ MUs). intros x Hx. cbn [outside] in Hx |- *.
      destruct Hx as (H1 & _ & _). split; [exact H1 | exact I]. }
    pose proof (GE_post.ge_keep_ret B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
                  (fun a => p <= a < p + RRr r n mb) (ms_mem ms') LAWS HJ Hslo Hshi MUs WMr
                  (stk_of_rel _ _ _ _ REL ST)) as KEEP.
    apply (SRr_ret SEGS).
    apply (GE_post.ge_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p md c16 n r mb nb db sb [] []
             W lyc Sc (ms_mem ms') mdc' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'
             Hret Hr15 Hc16 Hr Hptw Hml Hdl Hsl (wle_refl SEGS W)).
    + intros HE. destruct (RES HE) as (RB & _).
      exact (proj2 (bytes_at_rel rsegs _ _ _ _ REL) RB).
    + apply (ajournal_mono_k SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJm).
      assert (EV0 : EV_EMIT = 0) by reflexivity. rewrite EV0.
      destruct (RcEmit.em_E (EM_L r) (EM_G r) n (RcEmit.em_hid mb)); lia.
    + reflexivity.
    + reflexivity.
    + exact KEEP.
  - (* ---- the call site 0x84cec: the jal, a Theorem Labs lane's contract, then the second stretch ---- *)
    destruct HAT as (x1 & u0 & u1 & u2 & x8 & x9 & x14 & x15 & x16 & x17 & u3 & u4 & u5 & u6 & mc0 & j0 & P &
                     Es0 & HE & Lj0 & AJ & STc & MUc & WMc & MIc & FRc & P1 & P2 & P3 & P4 & P5 & P6).
    rewrite Es0 in Hrel.
    destruct (ms_rel_MS _ _ _ _ _ _ _ _ Hrel) as [Ems REL].
    rewrite Ems.
    pose proof (RcEmitLib.em_len_rng _ _ _ _ HE) as RLE.
    assert (MUr : munch [(spZ regs - 4640, spZ regs); (p, p + LENr r n)] memc (ms_mem ms'))
      by exact (munch_rel rsegs _ _ _ _ _ REL0 REL Hros MUc).
    assert (WMr : wmono rsegs memc (ms_mem ms')) by exact (wmono_rel rsegs _ _ _ _ REL0 REL Hros WMc).
    pose proof AJ as AJ'. destruct AJ' as (_ & _ & _ & AOc & _ & _).
    assert (AOr : addressable (ms_mem ms') p (LENr r n)) by exact (gc_addr_rel _ _ _ _ REL AOc).
    pose proof (rw_cells_of_rel _ _ _ _ REL FRc) as FRr.
    pose proof (rw_cells_of_rel _ _ _ _ REL P1) as P1r.
    pose proof (rw_cells_of_rel _ _ _ _ REL P2) as P2r.
    pose proof (rw_cells_of_rel _ _ _ _ REL P3) as P3r.
    pose proof (rw_cells_of_rel _ _ _ _ REL P5) as P5r.
    pose proof (rw_cells_of_rel _ _ _ _ REL P6) as P6r.
    (* the stack and the buffer: the window lies above alloc_ceiling, the buffer in a frame below it *)
    pose proof (frames_bounds SEGS B LAWS _ _ _ _ _ _ _ HAR HinP) as (_ & FBP & _).
    pose proof asan_consts as (CV & _).
    (* the journal at the call site *)
    assert (HJc : ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms') mdc' k).
    { apply (ge_jrnl_win B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k mdc' (ms_mem ms') (spZ regs) 4640
               p 1492 W memc (spZ regs) LAWS HJ); [| exact WMr | exact Hhid | exact Hsame | lia | lia | exact Hptw].
      apply (gc_munch_sub _ _ _ _ MUr). intros x Hx. cbn [outside] in Hx |- *.
      destruct Hx as (H1 & H2 & _). split; [exact H1 | split; [lia | exact I]]. }
    (* the image is outside the first stretch's writes *)
    assert (IMGO : forall a, in_img SEGS a -> outside [(spZ regs - 4640, spZ regs); (p, p + LENr r n)] a).
    { intros a Hia. pose proof (ctrl_segs_low a Hia) as Hlow. cbn [outside].
      split; [unfold kLowMemEnd in Hlow; lia | split; [intros Ha; apply (Hpni a); [lia | exact Hia] | exact I]]. }
    (* the jal *)
    match goal with |- SRr _ _ (mkCfg (MS ?R0 _ _ _ _ _ _) _) _ => set (RR := R0) end.
    apply (ge_steps W _ (MS (lib.Reusable.YK11.regupd RR 1 (Z_to_bv 64 0x84cf0)) lib.Reusable.YK11.fp_regs
                           (Z_to_bv 64 0x855f4) lib.Reusable.YK11.fp_csr None (ms_mem ms') (seg_rom SEGS)) mdc' _
             ctrl_wx (ge_jal_lay (RNG_W (w_H W)) RR lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr (ms_mem ms'))).
    intros md' Hsame'.
    apply (ge_at_cfg W _ 0x855f4 (ms_mem ms') md' _).
    assert (Elay : BASE + AF_ctrl_lay_block = 0x855f4) by (vm_compute; reflexivity).
    rewrite <- Elay.
    set (RC := lib.Reusable.YK11.regupd RR 1 (Z_to_bv 64 0x84cf0)).
    assert (GRC : forall x : bv 5, x <> (1%bv : bv 5) -> lib.Reusable.YK11.getr RC x = lib.Reusable.YK11.getr RR x).
    { intros x Hx. apply lib.Reusable.YK11.getr_other. exact Hx. }
    assert (Esp : spZ RC = spZ regs + -128).
    { unfold spZ. rewrite (GRC 2%bv ltac:(gc_ne1)).
      change (lib.Reusable.YK11.getr RR 2%bv) with (Z_to_bv 64 (bv_unsigned (getr regs 2) + -128)).
      apply gc_u64. unfold spZ in *. lia. }
    apply (SRr_bind SEGS W _
             (tctrl_lay_block_post (SK := SK) B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms') k RC p r md mb nb)).
    + apply (TLAY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms') md' k RC p r i md mb nb).
      * rewrite (same_but_materialized_wvb mdc' md' Hsame').
        exact (ajournal_materialize SEGS B LAWS ctrl_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc).
      * rewrite <- HRLO, <- HRHI.
        exact (ge_ro_keep B (w_H W) RLO RHI memc (ms_mem ms') _ RELRO_IMG HRO MUr IMGO).
      * unfold RC. rewrite lib.Reusable.YK11.getr_same by gc_ne1. vm_compute. reflexivity.
      * unfold raZ, RC. rewrite lib.Reusable.YK11.getr_same by gc_ne1. vm_compute. discriminate.
      * rewrite (GRC 3%bv ltac:(gc_ne1)). exact Hgp.
      * rewrite (GRC 4%bv ltac:(gc_ne1)). exact Htp.
      * rewrite (GRC 10%bv ltac:(gc_ne1)). reflexivity.
      * rewrite (GRC 11%bv ltac:(gc_ne1)). reflexivity.
      * exact Hr.
      * rewrite (GRC 12%bv ltac:(gc_ne1)). reflexivity.
      * exact Hmd.
      * exact Hi.
      * rewrite (GRC 13%bv ltac:(gc_ne1)). reflexivity.
      * rewrite Esp. replace (spZ regs + -128) with (spZ regs + (-8) * 16) by lia.
        rewrite Z.mod_add by lia. exact Hsp16.
      * rewrite Esp. change TLAY_STK with 4512. lia.
      * rewrite Esp. lia.
      * exact HC1.
      * exact HC0.
      * lia.
      * lia.
      * unfold amem_range in *. lia.
      * intros x Hx. apply Hpni. lia.
      * intros a Ha. destruct (Hptw a ltac:(lia)) as (Haw & Hpr & Hno & Hes).
        split; [exact Haw|]. split; [|split; [exact Hno|]].
        -- apply (gc_present_wmono _ memc); [exact WMr | lia | apply Hpni; lia | exact Hpr].
        -- rewrite Esp. unfold ESTACK. lia.
      * destruct Hpfo as ((cf & pf & Hinf & Hc0f & Hal & Hlo & Hhi) & H8 & HRA).
        split; [exists cf, pf; repeat split; (assumption || lia)|]. split; [exact H8|].
        intros x Hx. destruct (HRA x ltac:(lia)) as (sv & Hsv & Hok). exists sv. split; [|exact Hok].
        assert (Hxc : x < lib.Reusable.YM05.alloc_ceiling) by lia.
        assert (Hlw : lib.Reusable.YM05.alloc_ceiling <= spZ regs - 4640) by lia.
        destruct CV as [CV1 CV2].
        pose proof (gc_sh_out x p (LENr r n) (spZ regs - 4640) (spZ regs) lib.Reusable.YM05.alloc_ceiling
                      ltac:(lia) Hxc CV2 CV1 Hlw ltac:(lia) ltac:(lia) Hpam ltac:(lia)) as Hsh.
        unfold shadow_of_addr, SHADOW_OFF.
        rewrite (ge_view_of_munch (w_H W) memc (ms_mem ms') _ _ (proj1 Hsh) MUr (proj2 Hsh)). exact Hsv.
      * destruct Hpfh as (cf & pf & Hinf & Hcf & Hlo & Hhi). exists cf, pf. split; [exact Hinf|].
        split; [exact Hcf|].
        split; [pose proof (gc_div64 p (p + 18) ltac:(lia)); lia|].
        pose proof (gc_div64 (p + 18 + 32 - 1) (p + 1492 - 1) ltac:(lia)). lia.
      * apply (gc_garr8_munch _ _ memc (ms_mem ms') _ _ MUr); [| exact HmG].
        intros j Hj. unfold C_reac_box_model_block.bmb_z in Hj. rewrite length_map, Hml in Hj.
        unfold CAT_BYTES in Hmd. unfold IMG_LO, IMG_HI, CAT_BYTES in HCAT_rng.
        split; [unfold IMG_HI; lia|]. apply IMGO. apply gc_img_in. unfold IMG_LO, IMG_HI. lia.
      * exact Hml.
      * intros HB Hh Hn0. destruct (HNB HB Hh Hn0) as (Hok & HG & Hq & Hro).
        split; [exact Hok|]. split; [|split; [exact Hq|]].
        -- apply (gc_garr8_munch _ _ memc (ms_mem ms') _ _ MUr); [| exact HG].
           intros j Hj. unfold C_reac_box_model_block.bmb_z in Hj. rewrite length_map in Hj.
           assert (Hia : in_img SEGS (RcSynth.rname mb + Z.of_nat j)).
           { destruct (Hro (RcSynth.rname mb + Z.of_nat j) ltac:(lia)) as ([(sg & Hs & _ & Hsr) | Hsr] & _ & _).
             - exists sg. split; [exact Hs | exact Hsr].
             - exact (RELRO_IMG _ Hsr). }
           pose proof (ctrl_segs_low _ Hia) as Hlow. unfold kLowMemEnd in Hlow.
           split; [lia | exact (IMGO _ Hia)].
        -- intros x Hx. destruct (Hro x Hx) as (H1 & H2 & H3). rewrite <- HRLO, <- HRHI.
           exact (conj H1 (conj H2 H3)).
    + intros W2 c2 Hle (ly2 & S2 & regs2 & mem2 & md2 & Ec2 & J2 & PRE & FR & BL & GA & KEPT).
      subst c2.
      assert (Gra : lib.Reusable.YK11.getr RC 1 = Z_to_bv 64 0x84cf0).
      { unfold RC. apply lib.Reusable.YK11.getr_same. gc_ne1. }
      rewrite Gra. rewrite Esp in KEPT.
      apply (gc_stretch2 HBRF HFNF LAWS HIMGSH HGM HFR_glob HFR_al HCAT_glob HCAT_al HBOX_glob HROWS HFR_rng HCAT_rng
               HBOX_rng RELRO_IMG STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p md d c16 n r i ns
               mb nb db sb (ms_mem ms') W2 ly2 S2 regs2 mem2 md2 j0 P
               HJ HRO Hret Hra4 Hgp Htp Hr10 Hr11 Hr Hr12 Hmd Hi Hr13 Hr14 Hr15 Hc16 Hr16 Hn Hr17 Hr29 Hns
               Hsp16 Hslo Hshi HC1 HC0 Hp Hp8 Hpe Hpam Hpni Hptw Hpfo HPC HDC Hpfh Hdl HdG Hdsrc Hdni Hdp Hds Hd8
               Hsl HsG HmG Hml HNB RO AC SW AWIN FP0 TLS0 SHW HE MUr WMr Hle J2 FR BL KEPT).
      1-13: lazymatch goal with
            | |- getr _ ?x = _ =>
                let rr := eval vm_compute in (bv_unsigned x) in
                refine (eq_trans (PRE rr _) _); [unfold acallee_saved; lia | unfold RC, RR; reflexivity]
            end.
      exact (gc_ret B GLOBS RLO RHI HRT' VIS0 OWNED_RO HSS' HFP HTS HTP HTSD LAWS HIMGSH HGM HFR_glob HROWS HFR_rng HCAT_rng HBOX_rng
               RELRO_IMG STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p md d n r i ns mb nb db sb
               (ms_mem ms') W2 ly2 S2 mem2 md2 j0 P HJ HRO Htp Hr Hmd Hi Hslo Hshi Hsp16 Hp Hpe Hpam Hpni Hptw
               Hpfo HPC HDC Hpfh Hml HE MUr WMr Lj0 FRr P1r P2r P3r P5r P6r AOr Hle J2 FR GA KEPT).
Qed.

End m.
End b.

(* Rests on Rocq's primitive int / string / array declarations and the library's own axioms only (the compile
   log shows the list); no axiom of this project. *)
Print Assumptions pb_ctrl_emit_as.
