(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzR2Theory BzR5a.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR5cG.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR5cW.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR5cW.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR5cG.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR5cS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR4a.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR4a.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR2Theory OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5a OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cG.BzR5b OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cW OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cW.BzR5cLB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cG.BzR5cD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cS OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR4a.BzR4m OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR4a.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint ws_sym (sel : Z -> Z) (Lf : Z -> Z -> Z) (A : Z) (k : Z) (xs : list Z) : list (Z * Z) :=
  match xs with
  | [] => []
  | x :: xs' => (Lf (sel (k / 50)) x, ccode (Lf (sel (k / 50))) A x) :: ws_sym sel Lf A (k + 1) xs'
  end.
Lemma ws_sym_app : forall sel Lf A xs ys k,
  ws_sym sel Lf A k (xs ++ ys) = ws_sym sel Lf A k xs ++ ws_sym sel Lf A (k + Z.of_nat (length xs)) ys.
Proof.
  induction xs as [|x xs IH]; intros ys k; cbn [ws_sym app length].
  - rewrite Z.add_0_r. reflexivity.
  - rewrite IH. f_equal. f_equal. f_equal. lia.
Qed.

(* [comment removed for export] *)
Fixpoint zfillc (k : nat) (a : zarr) (i v : Z) : zarr :=
  match k with O => a | S k' => zfillc k' (zset a i v) (i + 1) v end.
Lemma zfillc_get : forall k a i v p, zget (zfillc k a i v) p = (if (i <=? p) && (p <? i + Z.of_nat k) then v else zget a p)%bool.
Proof.
  induction k as [|k IH]; intros a i v p; cbn [zfillc].
  - destruct (Z.leb_spec i p), (Z.ltb_spec p (i + Z.of_nat 0)); cbn; try reflexivity; lia.
  - rewrite IH, zget_zset.
    destruct (Z.leb_spec (i + 1) p), (Z.ltb_spec p (i + 1 + Z.of_nat k)), (Z.eqb_spec p i), (Z.leb_spec i p), (Z.ltb_spec p (i + Z.of_nat (S k)));
      cbn; try reflexivity; lia.
Qed.

Lemma run_write_spec : forall n sm uc nb es mx d, 0 <= es -> (Z.to_nat es <= n)%nat -> nb + es <= mx ->
  run_write n sm uc nb es mx d =
  (nb + es, 0, (if sm then d_set_ll16 d (zfillc (Z.to_nat es) (d_ll16 d) nb uc) else d_set_tt d (zfillc (Z.to_nat es) (d_tt d) nb uc)), false).
Proof.
  induction n as [|n IH]; intros sm uc nb es mx d Hes Hn Hmx; rewrite ?run_write_S.
  - cbn [run_write]. replace es with 0 by lia. cbn [zfillc Z.to_nat]. rewrite Z.add_0_r. destruct sm; destruct d; reflexivity.
  - destruct (Z.ltb_spec 0 es) as [P|NP].
    + replace (mx <=? nb) with false by (symmetry; apply Z.leb_gt; lia).
      rewrite IH by lia. replace (Z.to_nat es) with (S (Z.to_nat (es - 1))) by lia. cbn [zfillc].
      f_equal. f_equal; [f_equal; lia|]. destruct sm; destruct d; reflexivity.
    + replace es with 0 by lia. cbn [zfillc Z.to_nat]. rewrite Z.add_0_r. destruct sm; destruct d; reflexivity.
Qed.

(* [comment removed for export] *)
Definition hist (s2u : Z -> Z) (out : list Z) (c : Z) : nat := cnt (fun i => s2u (nth i out 0) =? c) (length out).
Lemma hist_snoc : forall s2u out u c, hist s2u (out ++ [u]) c = (hist s2u out c + (if (s2u u =? c)%Z then 1 else 0))%nat.
Proof.
  intros s2u out u c. unfold hist. rewrite length_app. cbn [length]. rewrite Nat.add_1_r, cnt_S.
  rewrite nth_middle. f_equal. apply cnt_ext. intros k Hk. rewrite app_nth1 by exact Hk. reflexivity.
Qed.
Lemma hist_app_repeat : forall k s2u out u c, hist s2u (out ++ repeat u k) c = (hist s2u out c + (if (s2u u =? c)%Z then k else 0))%nat.
Proof.
  induction k as [|k IH]; intros s2u out u c.
  - cbn [repeat]. rewrite app_nil_r. destruct (s2u u =? c); lia.
  - replace (repeat u (S k)) with (repeat u k ++ [u]) by (symmetry; apply repeat_cons).
    rewrite app_assoc, hist_snoc, IH. destruct (s2u u =? c); lia.
Qed.
Lemma hist_nil : forall s2u c, hist s2u [] c = 0%nat. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition LK (L0 : dsv) (gNo gPos ns nb es N zn zvec zj gSel gMinlen : Z) : dsv :=
  DSV (sv_i L0) (sv_j L0) (sv_t L0) (sv_alphaSize L0) (sv_nGroups L0) (sv_nSelectors L0) (sv_EOB L0) gNo gPos ns
      (sv_nblockMAX L0) nb es N (sv_curr L0) (sv_zt L0) zn zvec zj gSel gMinlen true.
(* [comment removed for export] *)
Definition symd_upd (d0 : dst) (tt l16 unz ma mb : zarr) (lbl B V : Z) : dst :=
  setLB (d_set_state (d_set_mtfbase (d_set_mtfa (d_set_unzftab (d_set_ll16 (d_set_tt d0 tt) l16) unz) ma) mb) lbl) B V.

Lemma symd_upd_fields : forall d0 tt l16 unz ma mb lbl B V, let d := symd_upd d0 tt l16 unz ma mb lbl B V in
  d_tt d = tt /\ d_ll16 d = l16 /\ d_unzftab d = unz /\ d_mtfa d = ma /\ d_mtfbase d = mb /\ d_state d = lbl /\
  d_bsBuff d = B /\ d_bsLive d = V /\
  d_out_ch d = d_out_ch d0 /\ d_out_len d = d_out_len d0 /\ d_rand d = d_rand d0 /\ d_rNToGo d = d_rNToGo d0 /\
  d_rTPos d = d_rTPos d0 /\ d_bs100k d = d_bs100k d0 /\ d_small d = d_small d0 /\ d_blockNo d = d_blockNo d0 /\
  d_verb d = d_verb d0 /\ d_origPtr d = d_origPtr d0 /\ d_tPos d = d_tPos d0 /\ d_k0 d = d_k0 d0 /\ d_nused d = d_nused d0 /\
  d_cftab d = d_cftab d0 /\ d_cftabCopy d = d_cftabCopy d0 /\ d_ll4 d = d_ll4 d0 /\ d_tt_al d = d_tt_al d0 /\ d_ll_al d = d_ll_al d0 /\
  d_sbcrc d = d_sbcrc d0 /\ d_sccrc d = d_sccrc d0 /\ d_cbcrc d = d_cbcrc d0 /\ d_cccrc d = d_cccrc d0 /\ d_nInUse d = d_nInUse d0 /\
  d_inUse d = d_inUse d0 /\ d_inUse16 d = d_inUse16 d0 /\ d_s2u d = d_s2u d0 /\ d_sel d = d_sel d0 /\ d_selMtf d = d_selMtf d0 /\
  d_len d = d_len d0 /\ d_limit d = d_limit d0 /\ d_base d = d_base d0 /\ d_perm d = d_perm d0 /\ d_minLens d = d_minLens d0 /\ d_sv d = d_sv d0.
Proof. intros. subst d. unfold symd_upd. rewrite setLB_eq. repeat split; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition sym_hyps (L0 : dsv) (d0 : dst) : Prop :=
  let nI := d_nInUse d0 in
  1 <= nI <= 256 /\ sv_alphaSize L0 = nI + 2 /\ sv_EOB L0 = nI + 1 /\ 1 <= sv_nSelectors L0 /\
  (forall g, 0 <= g < sv_nSelectors L0 -> 0 <= zget (d_sel d0) g < sv_nGroups L0) /\
  (forall t, 0 <= t < sv_nGroups L0 -> exists mn mx, grp_ok (sv_alphaSize L0) (d_len d0) (d_limit d0) (d_base d0) (d_perm d0) (d_minLens d0) t mn mx) /\
  (forall t n, 0 <= t < sv_nGroups L0 -> 1 <= n -> wsum (Lrow (d_len d0) (258 * t)) (sv_alphaSize L0) n <= 2 ^ n) /\
  (MINV (d_mtfbase d0) /\ (forall k, 0 <= k < 256 -> MV (d_mtfa d0) (d_mtfbase d0) k = k)) /\
  (forall c, 0 <= c < 256 -> zget (d_unzftab d0) c = 0) /\
  (forall v, 0 <= v < nI -> 0 <= zget (d_s2u d0) v < 256) /\
  (sv_groupNo L0 = 0 /\ sv_groupPos L0 = BZ_G_SIZE - 1 /\ sv_gSel L0 = zget (d_sel d0) 0 /\
   sv_gMinlen L0 = zget (d_minLens d0) (zget (d_sel d0) 0) /\ sv_zn L0 = zget (d_minLens d0) (zget (d_sel d0) 0) /\
   sv_nblock L0 = 0 /\ sv_gPtr L0 = true /\ 0 <= sv_nblockMAX L0).

(* [comment removed for export] *)
Definition ast0 : ast := AST (fun k => k) [] None.

(* [comment removed for export] *)
Definition FINAL (L0 : dsv) (d0 : dst) (st : ast) (L : dsv) (d : dst) : Prop :=
  exists ns es N zvec zj gNo gPos gSel gMinlen zn tt l16 unz ma mb lbl B V,
    L = LK L0 gNo gPos ns (Z.of_nat (length (a_out st))) es N zn zvec zj gSel gMinlen /\ ns = sv_EOB L0 /\
    d = symd_upd d0 tt l16 unz ma mb lbl B V /\
    Forall (fun u => 0 <= u < d_nInUse d0) (a_out st) /\
    (forall i, (i < length (a_out st))%nat -> zget (if smallb d0 then l16 else tt) (Z.of_nat i) = zget (d_s2u d0) (nth i (a_out st) 0)) /\
    (if smallb d0 then tt = d_tt d0 else l16 = d_ll16 d0) /\
    (forall c0, 0 <= c0 <= 255 -> zget unz c0 = Z.of_nat (hist (zget (d_s2u d0)) (a_out st) c0)) /\
    (forall c0, (c0 < 0 \/ 255 < c0) -> zget unz c0 = zget (d_unzftab d0) c0).

(* [comment removed for export] *)
Ltac dsn := cbv beta iota delta [sv_i sv_j sv_t sv_alphaSize sv_nGroups sv_nSelectors sv_EOB sv_groupNo sv_groupPos sv_nextSym sv_nblockMAX sv_nblock sv_es sv_N sv_curr sv_zt sv_zn sv_zvec sv_zj sv_gSel sv_gMinlen sv_gPtr d_state d_out_ch d_out_len d_rand d_rNToGo d_rTPos d_bsBuff d_bsLive d_bs100k d_small d_blockNo d_verb d_origPtr d_tPos d_k0 d_unzftab d_nused d_cftab d_cftabCopy d_tt d_ll16 d_ll4 d_tt_al d_ll_al d_sbcrc d_sccrc d_cbcrc d_cccrc d_nInUse d_inUse d_inUse16 d_s2u d_mtfa d_mtfbase d_sel d_selMtf d_len d_limit d_base d_perm d_minLens d_sv
    sv_set_i sv_set_j sv_set_t sv_set_alphaSize sv_set_nGroups sv_set_nSelectors sv_set_EOB sv_set_groupNo sv_set_groupPos sv_set_nextSym sv_set_nblockMAX sv_set_nblock sv_set_es sv_set_N sv_set_curr sv_set_zt sv_set_zn sv_set_zvec sv_set_zj sv_set_gSel sv_set_gMinlen sv_set_gPtr d_set_state d_set_out_ch d_set_out_len d_set_rand d_set_rNToGo d_set_rTPos d_set_bsBuff d_set_bsLive d_set_bs100k d_set_small d_set_blockNo d_set_verb d_set_origPtr d_set_tPos d_set_k0 d_set_unzftab d_set_nused d_set_cftab d_set_cftabCopy d_set_tt d_set_ll16 d_set_ll4 d_set_tt_al d_set_ll_al d_set_sbcrc d_set_sccrc d_set_cbcrc d_set_cccrc d_set_nInUse d_set_inUse d_set_inUse16 d_set_s2u d_set_mtfa d_set_mtfbase d_set_sel d_set_selMtf d_set_len d_set_limit d_set_base d_set_perm d_set_minLens d_set_sv].
Ltac dsnin H := cbv beta iota delta [sv_i sv_j sv_t sv_alphaSize sv_nGroups sv_nSelectors sv_EOB sv_groupNo sv_groupPos sv_nextSym sv_nblockMAX sv_nblock sv_es sv_N sv_curr sv_zt sv_zn sv_zvec sv_zj sv_gSel sv_gMinlen sv_gPtr d_state d_out_ch d_out_len d_rand d_rNToGo d_rTPos d_bsBuff d_bsLive d_bs100k d_small d_blockNo d_verb d_origPtr d_tPos d_k0 d_unzftab d_nused d_cftab d_cftabCopy d_tt d_ll16 d_ll4 d_tt_al d_ll_al d_sbcrc d_sccrc d_cbcrc d_cccrc d_nInUse d_inUse d_inUse16 d_s2u d_mtfa d_mtfbase d_sel d_selMtf d_len d_limit d_base d_perm d_minLens d_sv
    sv_set_i sv_set_j sv_set_t sv_set_alphaSize sv_set_nGroups sv_set_nSelectors sv_set_EOB sv_set_groupNo sv_set_groupPos sv_set_nextSym sv_set_nblockMAX sv_set_nblock sv_set_es sv_set_N sv_set_curr sv_set_zt sv_set_zn sv_set_zvec sv_set_zj sv_set_gSel sv_set_gMinlen sv_set_gPtr d_set_state d_set_out_ch d_set_out_len d_set_rand d_set_rNToGo d_set_rTPos d_set_bsBuff d_set_bsLive d_set_bs100k d_set_small d_set_blockNo d_set_verb d_set_origPtr d_set_tPos d_set_k0 d_set_unzftab d_set_nused d_set_cftab d_set_cftabCopy d_set_tt d_set_ll16 d_set_ll4 d_set_tt_al d_set_ll_al d_set_sbcrc d_set_sccrc d_set_cbcrc d_set_cccrc d_set_nInUse d_set_inUse d_set_inUse16 d_set_s2u d_set_mtfa d_set_mtfbase d_set_sel d_set_selMtf d_set_len d_set_limit d_set_base d_set_perm d_set_minLens d_set_sv] in H.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section SymPhase.
  Variables (i0 j0 t0 alphaSize0 nGroups0 nSelectors0 EOB0 groupNo0 groupPos0 nextSym0 nblockMAX0 nblock0 es0 N0 curr0 zt0 zn0 zvec0 zj0 gSel0 gMinlen0 : Z) (gPtr0 : bool).
  Variables (q_state q_out_ch q_out_len q_rand q_rNToGo q_rTPos q_bsBuff q_bsLive q_bs100k q_small q_blockNo q_verb q_origPtr q_tPos q_k0 : Z)
            (q_unzftab : zarr) (q_nused : Z) (q_cftab q_cftabCopy q_tt q_ll16 q_ll4 : zarr) (q_tt_al q_ll_al : bool)
            (q_sbcrc q_sccrc q_cbcrc q_cccrc q_nInUse : Z) (q_inUse q_inUse16 q_s2u q_mtfa q_mtfbase q_sel q_selMtf q_len q_limit q_base q_perm q_minLens : zarr)
            (q_sv : dsv).
  Let L0 : dsv := DSV i0 j0 t0 alphaSize0 nGroups0 nSelectors0 EOB0 groupNo0 groupPos0 nextSym0 nblockMAX0 nblock0 es0 N0 curr0 zt0 zn0 zvec0 zj0 gSel0 gMinlen0 gPtr0.
  Let d0 : dst := DST q_state q_out_ch q_out_len q_rand q_rNToGo q_rTPos q_bsBuff q_bsLive q_bs100k q_small q_blockNo q_verb q_origPtr q_tPos q_k0 q_unzftab q_nused q_cftab q_cftabCopy q_tt q_ll16 q_ll4 q_tt_al q_ll_al q_sbcrc q_sccrc q_cbcrc q_cccrc q_nInUse q_inUse q_inUse16 q_s2u q_mtfa q_mtfbase q_sel q_selMtf q_len q_limit q_base q_perm q_minLens q_sv.
  (* [comment removed for export] *)
  Let nI : Z := q_nInUse.
  Let aS : Z := alphaSize0.
  Let EOB : Z := EOB0.
  Let nG : Z := nGroups0.
  Let nS : Z := nSelectors0.
  Let nbMAX : Z := nblockMAX0.
  Let sel (g : Z) : Z := zget q_sel g.
  Let Lf (t : Z) : Z -> Z := Lrow q_len (258 * t).
  Let mn (t : Z) : Z := zget q_minLens t.
  Let s2u (v : Z) : Z := zget q_s2u v.
  Let sm : bool := smallb d0.
  #[local] Notation "'LL' gNo gPos ns nb es N zn zvec zj gSel gMinlen" :=
    (DSV i0 j0 t0 alphaSize0 nGroups0 nSelectors0 EOB0 gNo gPos ns nblockMAX0 nb es N curr0 zt0 zn zvec zj gSel gMinlen true) (at level 10, gNo at level 9, gPos at level 9,
       ns at level 9, nb at level 9, es at level 9, N at level 9, zn at level 9, zvec at level 9, zj at level 9, gSel at level 9, gMinlen at level 9).
  #[local] Notation "'DD' tt l16 unz ma mb lbl B V" :=
    (DST lbl q_out_ch q_out_len q_rand q_rNToGo q_rTPos B V q_bs100k q_small q_blockNo q_verb q_origPtr q_tPos q_k0 unz q_nused q_cftab q_cftabCopy tt l16 q_ll4 q_tt_al q_ll_al q_sbcrc q_sccrc q_cbcrc q_cccrc q_nInUse q_inUse q_inUse16 q_s2u ma mb q_sel q_selMtf q_len q_limit q_base q_perm q_minLens q_sv) (at level 10, tt at level 9, l16 at level 9, unz at level 9,
       ma at level 9, mb at level 9, lbl at level 9, B at level 9, V at level 9).

  Lemma LK_LL : forall gNo gPos ns nb es N zn zvec zj gSel gMinlen,
    LK L0 gNo gPos ns nb es N zn zvec zj gSel gMinlen = LL gNo gPos ns nb es N zn zvec zj gSel gMinlen.
  Proof. reflexivity. Qed.
  Lemma SD_DD : forall tt l16 unz ma mb lbl B V, symd_upd d0 tt l16 unz ma mb lbl B V = DD tt l16 unz ma mb lbl B V.
  Proof. intros. unfold symd_upd. rewrite setLB_eq. reflexivity. Qed.
  Lemma smallb_DD : forall tt l16 unz ma mb lbl B V, smallb (DD tt l16 unz ma mb lbl B V) = sm.
  Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Hypothesis HnI : 1 <= nI <= 256.
  Hypothesis HaS : aS = nI + 2.
  Hypothesis HEOB : EOB = nI + 1.
  Hypothesis HnS : 1 <= nS.
  Hypothesis Hsel : forall g, 0 <= g < nS -> 0 <= sel g < nG.
  Hypothesis Htab : forall t, 0 <= t < nG -> exists mnx mx, grp_ok aS q_len q_limit q_base q_perm q_minLens t mnx mx.
  Hypothesis Hkraft : forall t n, 0 <= t < nG -> 1 <= n -> wsum (Lf t) aS n <= 2 ^ n.
  Hypothesis Hmtf : MINV q_mtfbase /\ (forall k, 0 <= k < 256 -> MV q_mtfa q_mtfbase k = k).
  Hypothesis Hunz : forall c, 0 <= c < 256 -> zget q_unzftab c = 0.
  Hypothesis Hs2u : forall v, 0 <= v < nI -> 0 <= s2u v < 256.
  Hypothesis HL0 : groupNo0 = 0 /\ groupPos0 = BZ_G_SIZE - 1 /\ gSel0 = sel 0 /\ gMinlen0 = mn (sel 0) /\
                   zn0 = mn (sel 0) /\ nblock0 = 0 /\ gPtr0 = true /\ 0 <= nbMAX.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition which_of (m : Z) (st : ast) : Z :=
    match a_run st with Some _ => 3 | None => if m =? 0 then 1 else 5 end.

  (* [comment removed for export] *)
  Definition DINV (st : ast) (tt l16 unz ma mb : zarr) : Prop :=
    MINV mb /\ MPERM nI (a_M st) /\ (forall k, 0 <= k < 256 -> MV ma mb k = (if k <? nI then a_M st k else MV q_mtfa q_mtfbase k)) /\
    Forall (fun u => 0 <= u < nI) (a_out st) /\
    (forall i, (i < length (a_out st))%nat -> zget (if sm then l16 else tt) (Z.of_nat i) = s2u (nth i (a_out st) 0)) /\
    (if sm then tt = q_tt else l16 = q_ll16) /\
    (forall c0, 0 <= c0 <= 255 -> zget unz c0 = Z.of_nat (hist s2u (a_out st) c0)) /\
    (forall c0, (c0 < 0 \/ 255 < c0) -> zget unz c0 = zget q_unzftab c0).
  (* [comment removed for export] *)
  Definition RUNINV (c : nat) (st : ast) (es N : Z) : Prop :=
    match a_run st with
    | Some (es', N') => es = es' /\ N = N' /\ N = 2 ^ Z.of_nat c /\ 0 <= es /\ (1 <= c)%nat
    | None => c = 0%nat
    end.
  (* [comment removed for export] *)
  Definition REL (m : Z) (c : nat) (st : ast) (L : dsv) (d : dst) : Prop :=
    exists ns es N zvec zj tt l16 unz ma mb lbl B V,
      L = LL (m / 50) (BZ_G_SIZE - 1 - m mod 50) ns (Z.of_nat (length (a_out st))) es N (mn (sel (m / 50))) zvec zj (sel (m / 50)) (mn (sel (m / 50))) /\
      d = DD tt l16 unz ma mb lbl B V /\ 0 <= m /\ RUNINV c st es N /\ DINV st tt l16 unz ma mb.
  #[local] Notation "'FINP'" := (FINAL L0 d0) (at level 0, only parsing).

  Lemma REL_init : REL 0 0 ast0 L0 d0.
  Proof.
    cps_destruct HL0 as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8). destruct Hmtf as [M1 M2].
    exists nextSym0, es0, N0, zvec0, zj0, q_tt, q_ll16, q_unzftab, q_mtfa, q_mtfbase, q_state, q_bsBuff, q_bsLive.
    split. { change (0 / 50) with 0. change (0 mod 50) with 0. rewrite Z.sub_0_r. cbn [a_out ast0 length Z.of_nat]. subst L0.
             f_equal; first [assumption | symmetry; assumption]. }
    split. { reflexivity. }
    split; [lia|]. split; [reflexivity|]. split; [exact M1|]. split; [apply MPERM_id|]. split.
    { intros k Hk. cbn [a_M ast0]. destruct (Z.ltb_spec k nI); [apply M2; lia| reflexivity]. }
    split; [constructor|]. split; [intros i Hi; cbn in Hi; lia|]. split; [unfold sm; destruct (smallb d0); reflexivity|].
    split; [| intros; reflexivity]. intros c0 Hc0. cbn [a_out ast0]. rewrite hist_nil. apply Hunz. lia.
  Qed.

  Lemma REL_intro : forall m c st ns es N zvec zj tt l16 unz ma mb lbl B V,
    0 <= m -> RUNINV c st es N -> DINV st tt l16 unz ma mb ->
    REL m c st (LL (m / 50) (BZ_G_SIZE - 1 - m mod 50) ns (Z.of_nat (length (a_out st))) es N (mn (sel (m / 50))) zvec zj (sel (m / 50)) (mn (sel (m / 50))))
        (DD tt l16 unz ma mb lbl B V).
  Proof.
    intros. exists ns, es, N, zvec, zj, tt, l16, unz, ma, mb, lbl, B, V. repeat (split; [first [reflexivity | assumption] |]). assumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma zlen_app1 : forall (l : list Z) u, Z.of_nat (length (l ++ [u])) = Z.of_nat (length l) + 1.
  Proof. intros. rewrite length_app. cbn [length]. lia. Qed.
  Lemma zlen_app_repeat : forall (l : list Z) u k, Z.of_nat (length (l ++ repeat u k)) = Z.of_nat (length l) + Z.of_nat k.
  Proof. intros. rewrite length_app, repeat_length. lia. Qed.
  Lemma isrun_spec : forall x, isrun x = ((x =? BZ_RUNA) || (x =? BZ_RUNB))%bool.
  Proof. intros x. reflexivity. Qed.
  Lemma not_run : forall x, isrun x = false -> x <> 0 /\ x <> 1.
  Proof. intros x H. unfold isrun in H. apply Bool.orb_false_iff in H as [A B]. apply Z.eqb_neq in A. apply Z.eqb_neq in B. lia. Qed.
  Lemma is_run : forall x, isrun x = true -> x = 0 \/ x = 1.
  Proof. intros x H. unfold isrun in H. apply Bool.orb_true_iff in H as [A|B]; [apply Z.eqb_eq in A| apply Z.eqb_eq in B]; lia. Qed.
  Lemma astep_flush : forall st r x, a_run st = Some r -> isrun x = false ->
    astep EOB st x = astep EOB (AST (a_M st) (a_out st ++ run_out (a_M st) (Some r)) None) x.
  Proof. intros st r x H1 H2. unfold astep. rewrite H1, H2. cbn [a_run a_M a_out run_out]. rewrite app_nil_r. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma MV_mtf1 : forall (M : Z -> Z) ma mb ma' mb' j,
    0 <= j < nI ->
    (forall k, 0 <= k < 256 -> MV ma mb k = (if k <? nI then M k else MV q_mtfa q_mtfbase k)) ->
    (forall k, 0 <= k < 256 -> MV ma' mb' k = mtf1 (MV ma mb) j k) ->
    forall k, 0 <= k < 256 -> MV ma' mb' k = (if k <? nI then mtf1 M j k else MV q_mtfa q_mtfbase k).
  Proof.
    intros M ma mb ma' mb' j Hj R1 R2 k Hk. rewrite R2 by lia.
    destruct (Z.eq_dec k 0) as [->|NZ].
    - rewrite !mtf1_0. rewrite R1 by lia. replace (0 <? nI) with true by (symmetry; apply Z.ltb_lt; lia).
      replace (j <? nI) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
    - destruct (Z.le_gt_cases k j) as [LE|GT].
      + rewrite !mtf1_low by lia. rewrite R1 by lia.
        replace (k - 1 <? nI) with true by (symmetry; apply Z.ltb_lt; lia). replace (k <? nI) with true by (symmetry; apply Z.ltb_lt; lia).
        reflexivity.
      + rewrite mtf1_high by lia. rewrite R1 by lia. destruct (Z.ltb_spec k nI); [| reflexivity]. rewrite mtf1_high by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma DINV_write : forall st tt l16 unz ma mb u k,
    DINV st tt l16 unz ma mb -> 0 <= u < nI ->
    let nb := Z.of_nat (length (a_out st)) in
    let uc := s2u u in
    DINV (AST (a_M st) (a_out st ++ repeat u (S k)) (a_run st))
         (if sm then tt else zfillc (S k) tt nb uc) (if sm then zfillc (S k) l16 nb uc else l16) (zset unz uc (zget unz uc + (Z.of_nat k + 1))) ma mb.
  Proof.
    (intros st tt l16 unz ma mb u k; cps_intros (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8); intros Hu). cbv zeta. pose proof (Hs2u u Hu) as U8.
    unfold DINV; cbn [a_M a_out a_run]. split; [exact D1|]. split; [exact D2|]. split; [exact D3|]. split.
    { apply Forall_app. split; [exact D4|]. apply Forall_forall. intros x Hx. apply repeat_spec in Hx. lia. }
    split.
    { intros i Hi. rewrite length_app, repeat_length in Hi.
      replace (if sm then (if sm then zfillc (S k) l16 (Z.of_nat (length (a_out st))) (s2u u) else l16) else (if sm then tt else zfillc (S k) tt (Z.of_nat (length (a_out st))) (s2u u)))
        with (zfillc (S k) (if sm then l16 else tt) (Z.of_nat (length (a_out st))) (s2u u)) by (unfold sm; destruct (smallb d0); reflexivity).
      rewrite zfillc_get. destruct (Nat.lt_ge_cases i (length (a_out st))) as [LT|GE].
      - replace ((Z.of_nat (length (a_out st)) <=? Z.of_nat i) && (Z.of_nat i <? Z.of_nat (length (a_out st)) + Z.of_nat (S k)))%bool with false
          by (symmetry; apply Bool.andb_false_iff; left; apply Z.leb_gt; lia).
        rewrite app_nth1 by exact LT. apply D5. exact LT.
      - replace ((Z.of_nat (length (a_out st)) <=? Z.of_nat i) && (Z.of_nat i <? Z.of_nat (length (a_out st)) + Z.of_nat (S k)))%bool with true
          by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
        rewrite app_nth2 by exact GE. rewrite nth_repeat_lt by lia. reflexivity. }
    split; [unfold sm in *; destruct (smallb d0); exact D6|]. split.
    { intros c0 Hc0. rewrite hist_app_repeat. rewrite zget_zset. destruct (Z.eqb_spec c0 (s2u u)) as [->|NE].
      - rewrite Z.eqb_refl. rewrite D7 by lia. lia.
      - replace (s2u u =? c0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite D7 by lia. lia. }
    intros c0 Hc0. rewrite zget_zset_other by lia. apply D8. exact Hc0.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma val_start : forall lbl1 m ns nb es N zn zvec zj tt l16 unz ma mb lbl B V s,
    0 <= m -> m + 1 < BZ_G_SIZE * nS ->
    mtf_val_start lbl1 (LL (m / 50) (BZ_G_SIZE - 1 - m mod 50) ns nb es N zn zvec zj (sel (m / 50)) (mn (sel (m / 50)))) (DD tt l16 unz ma mb lbl B V) s
    = DGo lbl1 (LL ((m + 1) / 50) (BZ_G_SIZE - 1 - (m + 1) mod 50) ns nb es N (mn (sel ((m + 1) / 50))) zvec zj
                     (sel ((m + 1) / 50)) (mn (sel ((m + 1) / 50)))) (DD tt l16 unz ma mb lbl B V) s.
  Proof.
    intros. unfold mtf_val_start. dsn.
    pose proof (Z.div_mod m 50 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound m 50 ltac:(lia)) as MB. unfold BZ_G_SIZE in *.
    destruct (Z.eqb_spec (50 - 1 - m mod 50) 0) as [E|NE].
    - assert (E1 : (m + 1) / 50 = m / 50 + 1) by (symmetry; apply (Z.div_unique _ 50 _ 0); lia).
      assert (E2 : (m + 1) mod 50 = 0) by (symmetry; apply (Z.mod_unique _ 50 (m / 50 + 1)); lia).
      rewrite E1, E2. replace (nSelectors0 <=? m / 50 + 1) with false.
      2:{ symmetry. apply Z.leb_gt. assert ((m + 1) / 50 < nS) by (apply Z.div_lt_upper_bound; lia). subst nS. lia. }
      reflexivity.
    - assert (E1 : (m + 1) / 50 = m / 50) by (symmetry; apply (Z.div_unique _ 50 _ (m mod 50 + 1)); lia).
      assert (E2 : (m + 1) mod 50 = m mod 50 + 1) by (symmetry; apply (Z.mod_unique _ 50 (m / 50)); lia).
      rewrite E1, E2. f_equal. f_equal. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma ldone_LL : forall A mn0 gNo gPos ns nb es N zn zvec zj g gm i,
    exists zn' zvec' zj', ldone (Lf g) A mn0 (LL gNo gPos ns nb es N zn zvec zj g gm) i = LL gNo gPos ns nb es N zn' zvec' zj' g gm.
  Proof. intros. unfold ldone. destruct (mn0 <? Lf g i); dsn; eauto. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma mtf_fin_15 : forall m st L x d s, a_run st = None ->
    mtf_fin (which_of m st) L x d s = sym_dispatch (sv_set_nextSym L x) d s.
  Proof. intros m st L x d s H. unfold mtf_fin, which_of. rewrite H. destruct (m =? 0); reflexivity. Qed.
  Lemma mtf_fin_3 : forall m st r L x d s, a_run st = Some r ->
    mtf_fin (which_of m st) L x d s = (if isrun x then run_body (sv_set_nextSym L x) d s else run_exit (sv_set_nextSym L x) d s).
  Proof. intros m st r L x d s H. unfold mtf_fin, which_of. rewrite H. rewrite isrun_spec. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma disp_eob : forall m st es N zn zvec zj tt l16 unz ma mb lbl B V s,
    a_run st = None -> DINV st tt l16 unz ma mb ->
    let L := LL (m / 50) (BZ_G_SIZE - 1 - m mod 50) EOB (Z.of_nat (length (a_out st))) es N zn zvec zj (sel (m / 50)) (mn (sel (m / 50))) in
    let d := DD tt l16 unz ma mb lbl B V in
    sym_dispatch L d s = block_end L d s /\ FINP (astep EOB st EOB) L d.
  Proof.
    (intros m st es N zn zvec zj tt l16 unz ma mb lbl B V s RN; cps_intros (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8)). cbv zeta.
    unfold sym_dispatch. dsn. fold EOB. rewrite Z.eqb_refl. split; [reflexivity|].
    unfold astep. rewrite RN. replace (isrun EOB) with false by (symmetry; unfold isrun; apply Bool.orb_false_iff; split; apply Z.eqb_neq; lia).
    rewrite Z.eqb_refl. cbn [a_M a_out run_out]. rewrite app_nil_r.
    exists EOB, es, N, zvec, zj, (m / 50), (BZ_G_SIZE - 1 - m mod 50), (sel (m / 50)), (mn (sel (m / 50))), zn,
      tt, l16, unz, ma, mb, lbl, B, V.
    rewrite LK_LL, SD_DD. repeat (split; [first [reflexivity | assumption] |]). assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma disp_run : forall m st x es N zn zvec zj tt l16 unz ma mb lbl B V s,
    0 <= m -> m + 1 < BZ_G_SIZE * nS -> a_run st = None -> DINV st tt l16 unz ma mb -> isrun x = true ->
    let L := LL (m / 50) (BZ_G_SIZE - 1 - m mod 50) x (Z.of_nat (length (a_out st))) es N zn zvec zj (sel (m / 50)) (mn (sel (m / 50))) in
    let d := DD tt l16 unz ma mb lbl B V in
    exists L', sym_dispatch L d s = DGo 38 L' d s /\ REL (m + 1) 1 (astep EOB st x) L' d.
  Proof.
    intros m st x es N zn zvec zj tt l16 unz ma mb lbl B V s Hm HS RN DI RX. cbv zeta.
    pose proof (is_run x RX) as X01.
    unfold sym_dispatch. dsn. fold EOB. replace (x =? EOB) with false by (symmetry; apply Z.eqb_neq; lia).
    rewrite <- isrun_spec, RX. unfold run_body. dsn. change (2097152 <=? 1) with false. cbv iota.
    rewrite val_start by assumption.
    eexists. split; [reflexivity|].
    replace (if x =? BZ_RUNA then -1 + 1 else if x =? BZ_RUNB then -1 + 2 * 1 else -1) with (-1 + (x + 1) * 1)
      by (unfold BZ_RUNA, BZ_RUNB; destruct X01 as [-> | ->]; reflexivity).
    assert (AS : astep EOB st x = AST (a_M st) (a_out st) (Some (-1 + (x + 1) * 1, 2 * 1))) by (unfold astep; rewrite RX, RN; reflexivity).
    rewrite AS. apply (REL_intro (m + 1) 1 (AST (a_M st) (a_out st) (Some (-1 + (x + 1) * 1, 2 * 1)))); [lia| | exact DI].
    unfold RUNINV. cbn [a_run]. change (2 ^ Z.of_nat 1) with 2. repeat split; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma disp_lit : forall m st x es N zn zvec zj tt l16 unz ma mb lbl B V s,
    0 <= m -> m + 1 < BZ_G_SIZE * nS -> a_run st = None -> DINV st tt l16 unz ma mb -> isrun x = false -> 0 <= x < EOB ->
    Z.of_nat (length (a_out st)) + 1 <= nbMAX ->
    let L := LL (m / 50) (BZ_G_SIZE - 1 - m mod 50) x (Z.of_nat (length (a_out st))) es N zn zvec zj (sel (m / 50)) (mn (sel (m / 50))) in
    let d := DD tt l16 unz ma mb lbl B V in
    exists L' tt' l16' unz' ma' mb', sym_dispatch L d s = DGo 40 L' (DD tt' l16' unz' ma' mb' lbl B V) s /\ REL (m + 1) 0 (astep EOB st x) L' (DD tt' l16' unz' ma' mb' lbl B V).
  Proof.
    intros m st x es N zn zvec zj tt l16 unz ma mb lbl B V s Hm HS RN DI RX Hx HB. cbv zeta.
    pose proof (not_run x RX) as X01. cps_pose DI as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8).
    unfold sym_dispatch. dsn. fold EOB. replace (x =? EOB) with false by (symmetry; apply Z.eqb_neq; lia).
    rewrite <- isrun_spec, RX. replace (nblockMAX0 <=? Z.of_nat (length (a_out st))) with false by (symmetry; apply Z.leb_gt; subst nbMAX; lia).
    set (X := DD tt l16 unz ma mb lbl B V).
    pose proof (mtf_decode_spec X (x - 1) ltac:(subst X; exact D1) ltac:(lia)) as MD.
    destruct (mtf_decode X (x - 1)) as [uc d']. cps_destruct MD as (U1 & U2 & U3 & U4).
    assert (XA : d_mtfa X = ma) by reflexivity. assert (XB : d_mtfbase X = mb) by reflexivity. rewrite XA, XB in U1, U3. clear XA XB.
    set (ma' := d_mtfa d') in *. set (mb' := d_mtfbase d') in *. clearbody ma' mb'. subst d' X. dsn. rewrite smallb_DD.
    assert (UC : uc = a_M st (x - 1)).
    { rewrite U1, D3 by lia. replace (x - 1 <? nI) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
    assert (Hu : 0 <= a_M st (x - 1) < nI) by (apply (proj1 D2); lia).
    assert (DI' : DINV (AST (mtf1 (a_M st) (x - 1)) (a_out st) None) tt l16 unz ma' mb').
    { unfold DINV; cbn [a_M a_out]. split; [exact U2|]. split; [apply mtf1_MPERM; [exact D2| lia]|]. split; [| repeat (split; [assumption|]); assumption].
      apply (MV_mtf1 (a_M st) ma mb); [lia| exact D3| exact U3]. }
    pose proof (DINV_write _ tt l16 unz ma' mb' (a_M st (x - 1)) 0 DI' Hu) as DW. cbv zeta in DW. cbn [repeat Z.of_nat a_M a_out a_run] in DW.
    rewrite Z.add_0_l in DW.
    assert (AS : astep EOB st x = AST (mtf1 (a_M st) (x - 1)) (a_out st ++ [a_M st (x - 1)]) None).
    { unfold astep. rewrite RX, RN. replace (x =? EOB) with false by (symmetry; apply Z.eqb_neq; lia). cbn [run_out]. rewrite app_nil_r. reflexivity. }
    rewrite AS. rewrite <- UC in DW |- *. fold s2u. unfold zincr. change (zget unz (s2u uc) + 1) with (zget unz (s2u uc) + (0 + 1)).
    replace (Z.of_nat (length (a_out st)) + 1) with (Z.of_nat (length (a_out st ++ [uc]))) by (rewrite zlen_app1; reflexivity).
    unfold sm in DW |- *. destruct (Bool.bool_dec (smallb d0) true) as [SM|SM]; [| apply Bool.not_true_is_false in SM]; rewrite ?SM in DW; rewrite ?SM; dsn;
      (rewrite val_start by assumption); do 6 eexists; (split; [reflexivity|]); (apply (REL_intro (m + 1) 0); [lia| reflexivity| exact DW]).
  Qed.

  (* [comment removed for export] *)
  Lemma body_run : forall m c st es N x zn zvec zj tt l16 unz ma mb lbl B V s,
    0 <= m -> m + 1 < BZ_G_SIZE * nS -> a_run st = Some (es, N) -> RUNINV c st es N -> (c <= 19)%nat -> DINV st tt l16 unz ma mb -> isrun x = true ->
    let L := LL (m / 50) (BZ_G_SIZE - 1 - m mod 50) x (Z.of_nat (length (a_out st))) es N zn zvec zj (sel (m / 50)) (mn (sel (m / 50))) in
    let d := DD tt l16 unz ma mb lbl B V in
    exists L', run_body L d s = DGo 38 L' d s /\ REL (m + 1) (S c) (astep EOB st x) L' d.
  Proof.
    intros m c st es N x zn zvec zj tt l16 unz ma mb lbl B V s Hm HS RS RI Hc DI RX. cbv zeta.
    pose proof (is_run x RX) as X01. unfold RUNINV in RI. rewrite RS in RI. cps_destruct RI as (_ & _ & HN & Hes & Hc1).
    assert (N2 : N < 2097152).
    { rewrite HN. change 2097152 with (2 ^ 21). apply Z.pow_lt_mono_r; lia. }
    unfold run_body. dsn. replace (2097152 <=? N) with false by (symmetry; apply Z.leb_gt; lia).
    rewrite val_start by assumption. eexists. split; [reflexivity|].
    replace (if x =? BZ_RUNA then es + N else if x =? BZ_RUNB then es + 2 * N else es) with (es + (x + 1) * N)
      by (unfold BZ_RUNA, BZ_RUNB; destruct X01 as [-> | ->]; cbn -[Z.add Z.mul]; lia).
    assert (AS : astep EOB st x = AST (a_M st) (a_out st) (Some (es + (x + 1) * N, 2 * N))) by (unfold astep; rewrite RX, RS; reflexivity).
    rewrite AS. apply (REL_intro (m + 1) (S c) (AST (a_M st) (a_out st) (Some (es + (x + 1) * N, 2 * N)))); [lia| | exact DI].
    unfold RUNINV. cbn [a_run]. assert (0 <= N) by (rewrite HN; apply Z.pow_nonneg; lia).
    replace (Z.of_nat (S c)) with (Z.succ (Z.of_nat c)) by lia. rewrite Z.pow_succ_r by lia. repeat split; try lia.
  Qed.

  (* [comment removed for export] *)
  Lemma exit_run : forall m c st es N x zn zvec zj tt l16 unz ma mb lbl B V s,
    a_run st = Some (es, N) -> RUNINV c st es N -> DINV st tt l16 unz ma mb -> isrun x = false ->
    Z.of_nat (length (a_out st)) + es + 1 <= nbMAX ->
    let L := LL (m / 50) (BZ_G_SIZE - 1 - m mod 50) x (Z.of_nat (length (a_out st))) es N zn zvec zj (sel (m / 50)) (mn (sel (m / 50))) in
    let d := DD tt l16 unz ma mb lbl B V in
    let st2 := AST (a_M st) (a_out st ++ run_out (a_M st) (Some (es, N))) None in
    exists tt' l16' unz',
      run_exit L d s = sym_dispatch (LL (m / 50) (BZ_G_SIZE - 1 - m mod 50) x (Z.of_nat (length (a_out st2))) 0 N zn zvec zj (sel (m / 50)) (mn (sel (m / 50))))
                                    (DD tt' l16' unz' ma mb lbl B V) s /\
      DINV st2 tt' l16' unz' ma mb.
  Proof.
    intros m c st es N x zn zvec zj tt l16 unz ma mb lbl B V s RS RI DI RX HB. cbv zeta.
    unfold RUNINV in RI. rewrite RS in RI. cps_destruct RI as (_ & _ & HN & Hes & Hc1). cps_pose DI as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8).
    unfold run_exit. dsn. rewrite smallb_DD.
    replace (zget ma (zget mb 0)) with (a_M st 0).
    2:{ rewrite <- (Z.add_0_r (zget mb 0)). change (zget ma (zget mb 0 + 0)) with (MV ma mb 0). rewrite D3 by lia.
        replace (0 <? nI) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
    assert (Hu : 0 <= a_M st 0 < nI) by (apply (proj1 D2); lia).
    rewrite run_write_spec by (try lia; subst nbMAX; lia). dsn.
    pose proof (DINV_write _ tt l16 unz ma mb (a_M st 0) (Z.to_nat es) DI Hu) as DW. cbv zeta in DW. cbn [a_M a_out a_run] in DW.
    replace (Z.of_nat (Z.to_nat es) + 1) with (es + 1) in DW by lia. replace (S (Z.to_nat es)) with (Z.to_nat (es + 1)) in DW by lia.
    fold s2u. cbn [a_M a_out a_run run_out]. rewrite zlen_app_repeat. replace (Z.of_nat (Z.to_nat (es + 1))) with (es + 1) by lia.
    replace (Z.of_nat (length (a_out st)) + (es + 1)) with (Z.of_nat (length (a_out st)) + es + 1) by lia.
    unfold sm in DW |- *. destruct (Bool.bool_dec (smallb d0) true) as [SM|SM]; [| apply Bool.not_true_is_false in SM]; rewrite ?SM in DW; rewrite ?SM; dsn;
      do 3 eexists; (split; [reflexivity| exact DW]).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma tab_at : forall m, 0 <= m -> m < BZ_G_SIZE * nS ->
    let t := sel (m / 50) in
    0 <= t < nG /\ exists mnx mx, grp_ok aS q_len q_limit q_base q_perm q_minLens t mnx mx.
  Proof.
    intros m Hm HM. cbv zeta.
    assert (HmS : 0 <= m / 50 < nS) by (unfold BZ_G_SIZE in HM; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
    pose proof (Hsel (m / 50) HmS) as HT. split; [exact HT| apply Htab; exact HT].
  Qed.

  Lemma ws_sym_legal : forall xs m, 0 <= m -> m + Z.of_nat (length xs) <= BZ_G_SIZE * nS ->
    Forall (fun x => 0 <= x < aS) xs -> wlegal (ws_sym sel Lf aS m xs).
  Proof.
    induction xs as [|x xs IH]; intros m Hm HM F; cbn [ws_sym length] in *; [apply wlegal_nil|].
    apply Forall_cons_iff in F as [Fx F]. apply wlegal_cons. split; [| apply IH; [lia| lia| exact F]].
    cps_destruct (tab_at m Hm ltac:(lia)) as (HT & mnx & mx & G1 & G2 & G3 & G4 & _). cbv zeta in *.
    pose proof (G3 x Fx) as L3. split; [unfold Lf; lia|].
    apply (ccode_lt (Lf (sel (m / 50))) aS); [intros j Hj; pose proof (G3 j Hj); unfold Lf; lia| intros n Hn; apply Hkraft; [exact HT| exact Hn]| exact Fx].
  Qed.

  Lemma rd_abs_DD : forall tt l16 unz ma mb lbl tt' l16' unz' ma' mb' lbl' B V s,
    rd_abs (DD tt l16 unz ma mb lbl B V) s = rd_abs (DD tt' l16' unz' ma' mb' lbl' B V) s /\
    (rd_ok (DD tt l16 unz ma mb lbl B V) s <-> rd_ok (DD tt' l16' unz' ma' mb' lbl' B V) s) /\
    (forall d s0, dcost d s0 (DD tt l16 unz ma mb lbl B V) s = dcost d s0 (DD tt' l16' unz' ma' mb' lbl' B V) s) /\
    (forall d s0, dcost (DD tt l16 unz ma mb lbl B V) s d s0 = dcost (DD tt' l16' unz' ma' mb' lbl' B V) s d s0).
  Proof. intros. split; [reflexivity|]. split; [unfold rd_ok; cbn [d_bsLive d_bsBuff]; tauto|]. split; intros; reflexivity. Qed.

  Lemma which_run : forall m st x, isrun x = true -> which_of m (astep EOB st x) = 3.
  Proof. intros m st x RX. unfold which_of, astep. rewrite RX. destruct (run_acc (a_run st)); reflexivity. Qed.
  Lemma which_lit : forall m st x, 0 <= m -> isrun x = false -> x <> EOB -> which_of (m + 1) (astep EOB st x) = 5.
  Proof.
    intros m st x Hm RX NE. unfold which_of, astep. rewrite RX. replace (x =? EOB) with false by (symmetry; apply Z.eqb_neq; exact NE).
    cbn [a_run]. replace (m + 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
  Qed.

  Lemma astep_len_lit : forall st x, isrun x = false -> x <> EOB ->
    length (a_out (astep EOB st x)) = (length (a_out st) + length (run_out (a_M st) (a_run st)) + 1)%nat.
  Proof.
    intros st x RX NE. unfold astep. rewrite RX. replace (x =? EOB) with false by (symmetry; apply Z.eqb_neq; exact NE).
    cbn [a_out]. rewrite !length_app. cbn [length]. lia.
  Qed.
  Lemma astep_len_eob : forall st, length (a_out (astep EOB st EOB)) = (length (a_out st) + length (run_out (a_M st) (a_run st)))%nat.
  Proof.
    intros st. unfold astep. replace (isrun EOB) with false by (symmetry; unfold isrun; apply Bool.orb_false_iff; split; apply Z.eqb_neq; lia).
    rewrite Z.eqb_refl. cbn [a_out]. apply length_app.
  Qed.
  Lemma run_out_len : forall M es N, length (run_out M (Some (es, N))) = Z.to_nat (es + 1).
  Proof. intros. cbn [run_out]. apply repeat_length. Qed.

  Lemma phase : forall xs m c st L d s rest,
    REL m c st L d ->
    (exists body, xs = body ++ [EOB] /\ Forall (fun x => 0 <= x < EOB) body) ->
    runs_ok 20 c xs ->
    m + Z.of_nat (length xs) <= BZ_G_SIZE * nS ->
    Z.of_nat (length (a_out (asteps EOB st xs))) <= nbMAX ->
    rd_ok d s -> bits_ok rest -> rd_abs d s = bapp (wbits (ws_sym sel Lf aS m xs)) rest ->
    exists k L' d' s1 kb,
      (forall f, drun (k + f) (which_of m st + 35) L d s = dgo f (block_end L' d' s1)) /\
      FINP (asteps EOB st xs) L' d' /\ rd_abs d' s1 = rest /\ rd_ok d' s1 /\ Z.of_nat k <= dcost d s d' s1 /\ consumed_from kb s s1.
  Proof.
    induction xs as [|x xs IH]; (intros m c st L d s rest R; cps_intros (body & HB & FB); intros RO HM HLEN RD BO AB).
    { exfalso. destruct body; discriminate. }
    cps_destruct R as (ns & es & N & zvec & zj & tt & l16 & unz & ma & mb & lbl & B & V & HL & HD & Hm & RI & DI).
    cbn [length] in HM.
    (* [comment removed for export] *)
    assert (HX : 0 <= x <= EOB /\ ((x = EOB /\ xs = []) \/ (x < EOB /\ exists body', xs = body' ++ [EOB] /\ Forall (fun x => 0 <= x < EOB) body'))).
    { destruct body as [|b body']; cbn [app] in HB.
      - injection HB as E1 E2. subst. split; [lia| left; auto].
      - injection HB as E1 E2. subst b. apply Forall_cons_iff in FB as [Fx FB]. split; [lia|]. right. split; [lia|]. exists body'. auto. }
    destruct HX as [HxE HX].
    cps_destruct (tab_at m Hm ltac:(lia)) as (HT & mnx & mx & G). cbv zeta in HT, G. cps_destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
    set (t := sel (m / 50)) in *.
    (* [comment removed for export] *)
    cbn [ws_sym] in AB. fold t in AB. rewrite wbits_cons in AB.
    assert (WL : wlegal (ws_sym sel Lf aS (m + 1) xs)).
    { apply ws_sym_legal; [lia| lia|]. destruct HX as [[-> ->]|(LT & body' & -> & FB')]; [constructor|].
      apply Forall_app. split; [eapply Forall_impl; [| exact FB']; cbv beta; intros; lia| constructor; [lia| constructor]]. }
    rewrite bapp_assoc in AB by (first [apply wbits_len; exact WL | exact (proj1 BO)]).
    set (rest' := bapp (wbits (ws_sym sel Lf aS (m + 1) xs)) rest) in AB.
    assert (BO' : bits_ok rest') by (apply bapp_ok; [apply wbits_ok; exact WL| exact BO]).
    assert (W135 : which_of m st = 1 \/ which_of m st = 3 \/ which_of m st = 5).
    { unfold which_of. destruct (a_run st); [lia|]. destruct (m =? 0); lia. }
    cps_destruct (huff_decode (Lf t) aS mnx mx t q_limit q_base q_perm ltac:(lia) G1 G2 G3 ltac:(intros n Hn; apply Hkraft; [exact HT| exact Hn]) G5 G6 G7
                (which_of m st) L d s rest' x W135 ltac:(lia) ltac:(subst L; reflexivity) ltac:(subst d; reflexivity) ltac:(subst d; reflexivity)
                ltac:(subst d; reflexivity) ltac:(subst L; unfold mn in G4; exact G4) RD BO' AB)
      as (k1 & d1 & s1 & kb1 & RUN1 & AB1 & RO1 & CO1 & SB1 & CF1).
    (* [comment removed for export] *)
    unfold same_but_bits in SB1. set (B1 := d_bsBuff d1) in SB1. set (V1 := d_bsLive d1) in SB1. clearbody B1 V1.
    set (lbl' := if mnx <? Lf t x then which_of m st + 36 else which_of m st + 35) in SB1. clearbody lbl'.
    subst d1. subst d. subst L. dsnin RUN1. dsnin AB1. dsnin RO1. dsnin CO1. dsn.
    cps_destruct (ldone_LL aS mnx (m / 50) (BZ_G_SIZE - 1 - m mod 50) ns (Z.of_nat (length (a_out st))) es N (mn t) zvec zj t (mn t) x) as (zn' & zvec' & zj' & LD).
    rewrite LD in RUN1. clear LD.
    rewrite asteps_cons in HLEN |- *.
    pose proof (asteps_out_mono EOB xs (astep EOB st x)) as MONO.
    destruct (a_run st) as [[es' N']|] eqn:AR.
    - (* [comment removed for export] *)
      pose proof RI as RI'. unfold RUNINV in RI'. rewrite AR in RI'. cps_destruct RI' as (<- & <- & HN & Hes & Hc1).
      rewrite (mtf_fin_3 m st (es, N)) in RUN1 by exact AR. dsnin RUN1.
      destruct (isrun x) eqn:RX.
      + (* [comment removed for export] *)
        destruct HX as [[-> ->]|(LT & body' & -> & FB')].
        { exfalso. unfold isrun in RX. apply Bool.orb_true_iff in RX as [RX|RX]; apply Z.eqb_eq in RX; lia. }
        cbn [runs_ok] in RO. rewrite RX in RO. destruct RO as [RC RO].
        rewrite length_app in HM. cbn [length] in HM.
        cps_destruct (body_run m c st es N x zn' zvec' zj' tt l16 unz ma mb lbl' B1 V1 s1 Hm ltac:(lia) AR RI ltac:(lia) DI RX) as (L' & E & R').
        cbv zeta in E. fold t in E. rewrite E in RUN1. clear E.
        cps_destruct (IH (m + 1) (S c) (astep EOB st x) L' _ s1 rest R' ltac:(exists body'; auto) RO ltac:(rewrite length_app; cbn [length]; lia) HLEN RO1 BO AB1)
          as (k2 & L'' & d'' & s2 & kb2 & RUN2 & FIN & AB2 & RO2 & CO2 & CF2).
        rewrite (which_run (m + 1) st x RX) in RUN2.
        exists (k1 + k2)%nat, L'', d'', s2, (kb1 + kb2)%nat. split; [| split; [exact FIN| split; [exact AB2| split; [exact RO2| split]]]].
        * intros f. replace (k1 + k2 + f)%nat with (k1 + (k2 + f))%nat by lia. rewrite RUN1. cbn [dgo]. apply RUN2.
        * rewrite (dcost_trans _ s (DD tt l16 unz ma mb lbl' B1 V1) s1 d'' s2). pose proof CO1. lia.
        * eapply consumed_from_trans; [exact CF1| exact CF2].
      + (* [comment removed for export] *)
        pose proof (run_out_len (a_M st) es N) as ROL.
        assert (LENx : (length (a_out st) + Z.to_nat (es + 1) <= length (a_out (astep EOB st x)))%nat).
        { destruct HX as [[-> _]|(LT & _)]; [rewrite astep_len_eob| rewrite astep_len_lit by (try exact RX; lia)]; rewrite AR, ROL; lia. }
        cps_destruct (exit_run m c st es N x zn' zvec' zj' tt l16 unz ma mb lbl' B1 V1 s1 AR RI DI RX ltac:(lia)) as (tt' & l16' & unz' & E & DI2).
        cbv zeta in E. fold t in E. rewrite E in RUN1. clear E.
        set (st2 := AST (a_M st) (a_out st ++ run_out (a_M st) (Some (es, N))) None) in *.
        assert (L2 : length (a_out st2) = (length (a_out st) + Z.to_nat (es + 1))%nat) by (subst st2; cbn [a_out]; rewrite length_app, ROL; reflexivity).
        rewrite (astep_flush st (es, N) x AR RX) in HLEN, MONO, LENx |- *. fold st2 in HLEN, MONO, LENx |- *.
        cps_destruct (rd_abs_DD tt' l16' unz' ma mb lbl' tt l16 unz ma mb lbl' B1 V1 s1) as (RA & RK & RC & RC').
        destruct HX as [[-> ->]|(LT & body' & -> & FB')].
        * (* [comment removed for export] *)
          destruct (disp_eob m st2 0 N zn' zvec' zj' tt' l16' unz' ma mb lbl' B1 V1 s1 eq_refl DI2) as [E FIN]. cbv zeta in E. fold t in E.
          rewrite E in RUN1. clear E.
          exists k1. eexists. eexists. exists s1, kb1. split; [exact RUN1|]. split; [exact FIN|].
          rewrite RA, RC. split; [rewrite AB1; subst rest'; cbn [ws_sym wbits]; apply bapp_bnil_l|]. split; [apply RK; exact RO1|]. split; [exact CO1| exact CF1].
        * (* [comment removed for export] *)
          cbn [runs_ok] in RO. rewrite RX in RO. rewrite length_app in HM. cbn [length] in HM.
          assert (LEN2 : Z.of_nat (length (a_out st2)) + 1 <= nbMAX).
          { rewrite (astep_len_lit st2 x RX ltac:(lia)) in MONO. replace (length (run_out (a_M st2) (a_run st2))) with 0%nat in MONO by reflexivity.
            rewrite L2 in MONO |- *. lia. }
          cps_destruct (disp_lit m st2 x 0 N zn' zvec' zj' tt' l16' unz' ma mb lbl' B1 V1 s1 Hm ltac:(lia) eq_refl DI2 RX ltac:(lia) LEN2) as (L' & tt2 & l162 & unz2 & ma2 & mb2 & E & R').
          cbv zeta in E. fold t in E. rewrite E in RUN1. clear E.
          cps_destruct (rd_abs_DD tt2 l162 unz2 ma2 mb2 lbl' tt l16 unz ma mb lbl' B1 V1 s1) as (RA2 & RK2 & RC2 & RC2').
          cps_destruct (IH (m + 1) 0%nat (astep EOB st2 x) L' _ s1 rest R' ltac:(exists body'; auto) RO ltac:(rewrite length_app; cbn [length]; lia) HLEN
                       ltac:(apply RK2; exact RO1) BO ltac:(rewrite RA2; exact AB1))
            as (k2 & L'' & d'' & s2 & kb2 & RUN2 & FIN & AB2 & RO2 & CO2 & CF2).
          rewrite (which_lit m st2 x Hm RX ltac:(lia)) in RUN2.
          exists (k1 + k2)%nat, L'', d'', s2, (kb1 + kb2)%nat. split; [| split; [exact FIN| split; [exact AB2| split; [exact RO2| split]]]].
          -- intros f. replace (k1 + k2 + f)%nat with (k1 + (k2 + f))%nat by lia. rewrite RUN1. cbn [dgo]. apply RUN2.
          -- rewrite (dcost_trans _ s (DD tt l16 unz ma mb lbl' B1 V1) s1 d'' s2). rewrite RC2' in CO2. pose proof CO1. lia.
          -- eapply consumed_from_trans; [exact CF1| exact CF2].
    - (* [comment removed for export] *)
      pose proof RI as RI'. unfold RUNINV in RI'. rewrite AR in RI'. subst c.
      rewrite (mtf_fin_15 m st) in RUN1 by exact AR. dsnin RUN1.
      destruct (isrun x) eqn:RX.
      + (* [comment removed for export] *)
        destruct HX as [[-> ->]|(LT & body' & -> & FB')].
        { exfalso. unfold isrun in RX. apply Bool.orb_true_iff in RX as [RX|RX]; apply Z.eqb_eq in RX; lia. }
        cbn [runs_ok] in RO. rewrite RX in RO. destruct RO as [RC RO].
        rewrite length_app in HM. cbn [length] in HM.
        cps_destruct (disp_run m st x es N zn' zvec' zj' tt l16 unz ma mb lbl' B1 V1 s1 Hm ltac:(lia) AR DI RX) as (L' & E & R').
        cbv zeta in E. fold t in E. rewrite E in RUN1. clear E.
        cps_destruct (IH (m + 1) 1%nat (astep EOB st x) L' _ s1 rest R' ltac:(exists body'; auto) RO ltac:(rewrite length_app; cbn [length]; lia) HLEN RO1 BO AB1)
          as (k2 & L'' & d'' & s2 & kb2 & RUN2 & FIN & AB2 & RO2 & CO2 & CF2).
        rewrite (which_run (m + 1) st x RX) in RUN2.
        exists (k1 + k2)%nat, L'', d'', s2, (kb1 + kb2)%nat. split; [| split; [exact FIN| split; [exact AB2| split; [exact RO2| split]]]].
        * intros f. replace (k1 + k2 + f)%nat with (k1 + (k2 + f))%nat by lia. rewrite RUN1. cbn [dgo]. apply RUN2.
        * rewrite (dcost_trans _ s (DD tt l16 unz ma mb lbl' B1 V1) s1 d'' s2). pose proof CO1. lia.
        * eapply consumed_from_trans; [exact CF1| exact CF2].
      + destruct HX as [[-> ->]|(LT & body' & -> & FB')].
        * (* [comment removed for export] *)
          destruct (disp_eob m st es N zn' zvec' zj' tt l16 unz ma mb lbl' B1 V1 s1 AR DI) as [E FIN]. cbv zeta in E. fold t in E.
          rewrite E in RUN1. clear E.
          exists k1. eexists. eexists. exists s1, kb1. split; [exact RUN1|]. split; [exact FIN|].
          split; [rewrite AB1; subst rest'; cbn [ws_sym wbits]; apply bapp_bnil_l|]. split; [exact RO1|]. split; [exact CO1| exact CF1].
        * (* [comment removed for export] *)
          cbn [runs_ok] in RO. rewrite RX in RO. rewrite length_app in HM. cbn [length] in HM.
          assert (LEN2 : Z.of_nat (length (a_out st)) + 1 <= nbMAX).
          { rewrite (astep_len_lit st x RX ltac:(lia)), AR in MONO. cbn [run_out length] in MONO. lia. }
          cps_destruct (disp_lit m st x es N zn' zvec' zj' tt l16 unz ma mb lbl' B1 V1 s1 Hm ltac:(lia) AR DI RX ltac:(lia) LEN2) as (L' & tt2 & l162 & unz2 & ma2 & mb2 & E & R').
          cbv zeta in E. fold t in E. rewrite E in RUN1. clear E.
          cps_destruct (rd_abs_DD tt2 l162 unz2 ma2 mb2 lbl' tt l16 unz ma mb lbl' B1 V1 s1) as (RA2 & RK2 & RC2 & RC2').
          cps_destruct (IH (m + 1) 0%nat (astep EOB st x) L' _ s1 rest R' ltac:(exists body'; auto) RO ltac:(rewrite length_app; cbn [length]; lia) HLEN
                       ltac:(apply RK2; exact RO1) BO ltac:(rewrite RA2; exact AB1))
            as (k2 & L'' & d'' & s2 & kb2 & RUN2 & FIN & AB2 & RO2 & CO2 & CF2).
          rewrite (which_lit m st x Hm RX ltac:(lia)) in RUN2.
          exists (k1 + k2)%nat, L'', d'', s2, (kb1 + kb2)%nat. split; [| split; [exact FIN| split; [exact AB2| split; [exact RO2| split]]]].
          -- intros f. replace (k1 + k2 + f)%nat with (k1 + (k2 + f))%nat by lia. rewrite RUN1. cbn [dgo]. apply RUN2.
          -- rewrite (dcost_trans _ s (DD tt l16 unz ma mb lbl' B1 V1) s1 d'' s2). rewrite RC2' in CO2. pose proof CO1. lia.
          -- eapply consumed_from_trans; [exact CF1| exact CF2].
  Qed.

  Theorem sym_phase_sec : forall xs body s rest,
    xs = body ++ [EOB] -> Forall (fun x => 0 <= x < EOB) body -> runs_ok 20 0 xs ->
    Z.of_nat (length xs) <= BZ_G_SIZE * nS ->
    Z.of_nat (length (a_out (asteps EOB ast0 xs))) <= nbMAX ->
    rd_ok d0 s -> bits_ok rest -> rd_abs d0 s = bapp (wbits (ws_sym sel Lf aS 0 xs)) rest ->
    exists k L' d' s1 kb,
      (forall f, drun (k + f) 36 L0 d0 s = dgo f (block_end L' d' s1)) /\
      FINP (asteps EOB ast0 xs) L' d' /\ rd_abs d' s1 = rest /\ rd_ok d' s1 /\ Z.of_nat k <= dcost d0 s d' s1 /\ consumed_from kb s s1.
  Proof.
    intros xs body s rest HB FB RO HM HLEN RD BO AB.
    cps_destruct (phase xs 0 0 ast0 L0 d0 s rest REL_init ltac:(exists body; auto) RO ltac:(lia) HLEN RD BO AB) as (k & L' & d' & s1 & kb & RUN & REST).
    exists k, L', d', s1, kb. split; [exact RUN| exact REST].
  Qed.
End SymPhase.

(* [comment removed for export] *)
Theorem sym_phase : forall L0 d0 xs body s rest,
  sym_hyps L0 d0 ->
  xs = body ++ [sv_EOB L0] -> Forall (fun x => 0 <= x < sv_EOB L0) body -> runs_ok 20 0 xs ->
  Z.of_nat (length xs) <= BZ_G_SIZE * sv_nSelectors L0 ->
  Z.of_nat (length (a_out (asteps (sv_EOB L0) ast0 xs))) <= sv_nblockMAX L0 ->
  rd_ok d0 s -> bits_ok rest ->
  rd_abs d0 s = bapp (wbits (ws_sym (fun g => zget (d_sel d0) g) (fun t => Lrow (d_len d0) (258 * t)) (sv_alphaSize L0) 0 xs)) rest ->
  exists k L' d' s1 kb,
    (forall f, drun (k + f) 36 L0 d0 s = dgo f (block_end L' d' s1)) /\
    FINAL L0 d0 (asteps (sv_EOB L0) ast0 xs) L' d' /\ rd_abs d' s1 = rest /\ rd_ok d' s1 /\ Z.of_nat k <= dcost d0 s d' s1 /\ consumed_from kb s s1.
Proof.
  intros L0 d0 xs body s rest SH. destruct L0 as [i0 j0 t0 alphaSize0 nGroups0 nSelectors0 EOB0 groupNo0 groupPos0 nextSym0 nblockMAX0 nblock0 es0 N0 curr0 zt0 zn0 zvec0 zj0 gSel0 gMinlen0 gPtr0], d0 as [q_state q_out_ch q_out_len q_rand q_rNToGo q_rTPos q_bsBuff q_bsLive q_bs100k q_small q_blockNo q_verb q_origPtr q_tPos q_k0 q_unzftab q_nused q_cftab q_cftabCopy q_tt q_ll16 q_ll4 q_tt_al q_ll_al q_sbcrc q_sccrc q_cbcrc q_cccrc q_nInUse q_inUse q_inUse16 q_s2u q_mtfa q_mtfbase q_sel q_selMtf q_len q_limit q_base q_perm q_minLens q_sv].
  unfold sym_hyps in SH.
  cbn [sv_i sv_j sv_t sv_alphaSize sv_nGroups sv_nSelectors sv_EOB sv_groupNo sv_groupPos sv_nextSym sv_nblockMAX sv_nblock sv_es sv_N sv_curr
    sv_zt sv_zn sv_zvec sv_zj sv_gSel sv_gMinlen sv_gPtr
    d_state d_out_ch d_out_len d_rand d_rNToGo d_rTPos d_bsBuff d_bsLive d_bs100k d_small d_blockNo d_verb d_origPtr d_tPos d_k0
    d_unzftab d_nused d_cftab d_cftabCopy d_tt d_ll16 d_ll4 d_tt_al d_ll_al d_sbcrc d_sccrc d_cbcrc d_cccrc d_nInUse d_inUse d_inUse16
    d_s2u d_mtfa d_mtfbase d_sel d_selMtf d_len d_limit d_base d_perm d_minLens d_sv] in SH |- *.
  cps_destruct SH as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
  intros HB FB RO HM HLEN RD BO AB. eapply sym_phase_sec; eassumption.
Qed.
