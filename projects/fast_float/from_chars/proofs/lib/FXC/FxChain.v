(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Run Specs.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg SysNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop FxPlan FxFrame FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.FxAcct.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChLib FxChSep.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChFix.

Module FxChNorepB.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Run Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg SysNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxRgs FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop FxPlan FxFrame FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.FxAcct.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChFix.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChSeg OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChNode OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFix.FxChNorep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Lemma u_scale8_sub : forall E pb sp, 8 * bv_unsigned (lden E pb) < two64 ->
  bv_unsigned (lden E (lsub (lscale 8 pb) sp)) = (8 * bv_unsigned (lden E pb) - bv_unsigned (lden E sp)) mod two64.
Proof.
  intros E pb sp H. rewrite lden_lsub, lscale_mul by (unfold two64; lia).
  rewrite bv_sub_unsigned, bv_mul_unsigned, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
  rewrite (Z.mod_small 8) by (unfold two64; lia). rewrite Z.mul_comm.
  pose proof (bv_unsigned_in_range _ (lden E pb)) as R. rewrite (Z.mod_small (8 * _)) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Definition bandp_ok (fs : list fact) (n : positive) (sp : lin) (b k : Z) (pb ps : lin) (ub : Z) : bool :=
  let ia := irange fs pb in let is := irange fs ps in let id := irange fs (lsub (lscale 8 pb) sp) in
  let it := irange fs (ladd pb ps) in
  (lwf n pb && lwf n ps && Z.leb b (fst ia) && Z.leb SH_OFF (fst ia) && Z.leb 1 (fst is) && Z.leb (snd is) ub &&
   Z.ltb (snd ia + snd is) 4611686018427387904 && Z.leb (snd it) (b + k) && Z.leb (8 * (snd it - SH_OFF)) 0x800000000000 &&
   Z.leb (8 * SH_OFF - 8388608 - 4095) (fst id) && Z.ltb (snd id) 9223372036854775808 && Z.leb 9 (lalign fs pb))%bool.

Lemma bandp_spec : forall E fs n (model : Model) sp b k pb ps ub,
  Forall (fact_ok E) fs -> vm_init_sp (m_vmmaps model) = lden E sp -> bv_unsigned (vm_init_sp (m_vmmaps model)) <= sp_window_hi ->
  init_sp_ok (m_vmmaps model) -> 0 <= b -> bandp_ok fs n sp b k pb ps ub = true ->
  piece_ok E model b k (pb, ps, ub) /\ (lwf n pb && lwf n ps)%bool = true /\ 0 <= ub.
Proof.
  intros E fs n model sp b k pb ps ub HF Hsp Hhi Hok Hb0 H. unfold bandp_ok in H.
  pose proof (irange_sound E fs pb HF) as Ra. pose proof (irange_sound E fs ps HF) as Rs.
  pose proof (irange_sound E fs (lsub (lscale 8 pb) sp) HF) as Rd.
  pose proof (irange_sound E fs (ladd pb ps) HF) as Rt.
  repeat match type of H with ((_ && _)%bool = true) => apply andb_prop in H as [H ?H] end.
  rename H into Hw1.
  repeat match goal with
         | Hx : Z.leb _ _ = true |- _ => apply Z.leb_le in Hx
         | Hx : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in Hx
         end.
  rewrite ladd_u in Rt by (unfold two64; lia).
  remember (bv_unsigned (lden E pb)) as A eqn:HAe. remember (bv_unsigned (lden E ps)) as s eqn:HSe.
  pose proof (alloc_top_lo _ Hok) as Hat.
  assert (Hspu : bv_unsigned (lden E sp) <= sp_window_hi) by (rewrite <- Hsp; exact Hhi).
  unfold sp_window_hi in Hspu.
  (* [comment removed for export] *)
  assert (Hrel : 8 * A - bv_unsigned (lden E sp) >= 8 * SH_OFF - 8388608 - 4095).
  { assert (HA64 : 8 * A < two64) by (unfold two64, SH_OFF in *; lia).
    rewrite (u_scale8_sub E pb sp) in Rd by (rewrite <- HAe; exact HA64). rewrite <- HAe in Rd.
    pose proof (bv_unsigned_in_range _ (lden E sp)) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with two64 in Rsp.
    destruct (Z_le_gt_dec (bv_unsigned (lden E sp)) (8 * A)) as [Hle|Hgt].
    - rewrite Z.mod_small in Rd by lia. lia.
    - replace (8 * A - bv_unsigned (lden E sp)) with ((8 * A - bv_unsigned (lden E sp) + two64) + (-1) * two64) in Rd by lia.
      rewrite Z.mod_add in Rd by (unfold two64; lia). rewrite Z.mod_small in Rd by lia.
      unfold two64 in *. lia. }
  split; [|split; [rewrite ?Hw1; unfold is_true in *; repeat (apply andb_true_intro; split); first [reflexivity | assumption] | lia]].
  unfold piece_ok. cbn [fst snd]. unfold uE. rewrite <- HAe, <- HSe.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  (* [comment removed for export] *)
  pose proof (lalign_sound E fs pb HF) as [Hal0 Hal]. rewrite <- HAe in Hal.
  assert (H512 : (512 | A)).
  { apply (Z.divide_trans _ (2 ^ lalign fs pb)); [|exact Hal].
    replace (2 ^ lalign fs pb) with (2 ^ 9 * 2 ^ (lalign fs pb - 9)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    exists (2 ^ (lalign fs pb - 9)). ring. }
  destruct H512 as [q Hq].
  assert (Hpg : atop_pg (m_vmmaps model) <= 8 * (A - SH_OFF)).
  { unfold atop_pg, alloc_top, stack_max_size. rewrite Hsp.
    replace (8 * (A - SH_OFF)) with (4096 * (q - 0x3fffc0)) by (unfold SH_OFF; lia).
    apply Z.mul_le_mono_nonneg_l; [lia|]. apply Z.lt_succ_r. apply Z.div_lt_upper_bound; [lia|]. unfold SH_OFF in *. lia. }
  intros x Hx. unfold app_pt. split; [right|split].
  - lia.
  - unfold in_shadow, SH_LO, SH_HI. apply andb_false_iff. right. apply Z.ltb_ge.
    unfold alloc_top, stack_max_size in Hat. rewrite Hsp in Hat. unfold SH_OFF in *. lia.
  - unfold SH_OFF in *. lia.
Qed.

Definition band_budget (fs : list fact) (M : smodel) (b k : Z) (kd : gkind) (pb : lin) (ub : Z) : Z :=
  eager_sum fs ((lconst b, lconst k, kd) :: sm_maps M) + allow_bound (piece_allow [(pb, lconst 0, ub)] ++ sm_allow M).

Definition norepb_ok (res : list (word * word)) (LIMIT : Z) (L : sst) (M : smodel) (b k : Z) (kd : gkind)
    (pb ps : lin) (ub : Z) (zr : bool) : bool :=
  (norep_ok res LIMIT L M b k kd false [] zr SH_HI SH_HI && bandp_ok (s_facts L) (s_next L) (sm_sp M) b k pb ps ub &&
   Z.leb (band_budget (s_facts L) M b k kd pb ub) LIMIT)%bool.

Section NorepBNode.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.
Hypothesis Hsegb : segs_below_b segs 0x800000000000 = true.
Hypothesis Hoff : sc_alloc cfg = false.

#[using="Hsegb Hoff"] Theorem den_norepb : forall E L M ms model T b k kd pb ps ub zr,
  DEN segs LIMIT model0 mem0 E L M ms model -> sm_own M = [] -> nomark (sm_maps M) = true ->
  norepb_ok (segments_reserved segs) LIMIT L M b k kd pb ps ub zr = true ->
  (forall ms' model', DEN segs LIMIT model0 mem0 E (norep_post L b [(pb, ps, ub)]) (norep_M M b k kd [(pb, ps, ub)] zr) ms' model' ->
      realizes_cfg segs cfg (mkCfg ms' model') T) ->
  realizes_cfg segs cfg (mkCfg (svc_set ms) model) T.
Proof. LiaFast.lf_pins (fun (Hsegb Hoff : LiaFast.U) => LiaFast.u0).
  intros E L M ms model T b k kd pb ps ub zr Hd Hon Hnm Hokb Hk.
  unfold norepb_ok in Hokb. apply andb_prop in Hokb as [Hokb Hbud]. apply Z.leb_le in Hbud.
  apply andb_prop in Hokb as [Hok Hband].
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  den_noblob Hnm.
  unfold norep_ok in Hok. cbn [pieces_of] in Hok.
  destruct (a7c L) as [c7|] eqn:H7; [|discriminate]. destruct (arg L 0) as [c0|] eqn:H0; [|discriminate].
  destruct (arg L 1) as [len|] eqn:H1; [|discriminate]. destruct (arg L 2) as [prot|] eqn:H2; [|discriminate].
  destruct (arg L 3) as [flags|] eqn:H3; [|discriminate]. destruct (arg L 5) as [off|] eqn:H5; [|discriminate].
  apply andb_prop in Hok as [Hok _].
  apply andb_prop in Hok as [Hok Hwk]. apply Z.leb_le in Hwk. apply andb_prop in Hok as [Hok Hwb]. apply Z.leb_le in Hwb.
  apply andb_prop in Hok as [Hok Hwlo]. apply Z.leb_le in Hwlo. apply andb_prop in Hok as [Hok Hwin].
  apply andb_prop in Hok as [Hok Hinc]. apply andb_prop in Hok as [Hok Hsrcs]. apply andb_prop in Hok as [Hok Hnaz].
  apply andb_prop in Hok as [Hok Hkd]. apply andb_prop in Hok as [Hok Hnr]. apply andb_prop in Hok as [Hok Hshi].
  apply Z.leb_le in Hshi. apply andb_prop in Hok as [Hok Hslo]. apply Z.leb_le in Hslo. apply andb_prop in Hok as [Hok Hfree].
  apply andb_prop in Hok as [Hok Htopc]. apply Z.leb_le in Htopc. apply andb_prop in Hok as [Hok Hal]. apply Z.eqb_eq in Hal.
  apply andb_prop in Hok as [Hok Hlen]. apply Z.eqb_eq in Hlen. apply andb_prop in Hok as [Hok Hsel].
  apply andb_prop in Hok as [Hok Hfrw]. apply andb_prop in Hok as [Hok Hfna]. apply andb_prop in Hok as [Hok Hnac].
  apply andb_prop in Hok as [Hok Hmod]. apply andb_prop in Hok as [Hok Hnz0]. apply andb_prop in Hok as [Hok Hanon].
  apply andb_prop in Hok as [Hok Hoffa]. apply andb_prop in Hok as [Hok Hb64]. apply Z.ltb_lt in Hb64.
  apply andb_prop in Hok as [Hok Hbpos]. apply Z.ltb_lt in Hbpos. apply andb_prop in Hok as [Hok Hc0]. apply Z.eqb_eq in Hok, Hc0.
  subst c7 c0. apply negb_true_iff in Hnz0, Hmod, Hnac, Hfna, Hfrw.
  set (H := Hof E M model) in *.
  set (ms1 := svc_set ms).
  assert (Hx8 : ms_reg ms 17 = Z_to_bv 64 222) by exact (a7_const segs E L (restrict H ms) ms 222 Hsd eq_refl H7).
  assert (Hg0 : ms_gpr ms1 0 = Z_to_bv 64 b) by exact (gpr_const segs E L (restrict H ms) ms 0 b Hsd eq_refl ltac:(lia) H0).
  assert (Hg1 : ms_gpr ms1 1 = Z_to_bv 64 len) by exact (gpr_const segs E L (restrict H ms) ms 1 len Hsd eq_refl ltac:(lia) H1).
  assert (Hg2 : ms_gpr ms1 2 = Z_to_bv 64 prot) by exact (gpr_const segs E L (restrict H ms) ms 2 prot Hsd eq_refl ltac:(lia) H2).
  assert (Hg3 : ms_gpr ms1 3 = Z_to_bv 64 flags) by exact (gpr_const segs E L (restrict H ms) ms 3 flags Hsd eq_refl ltac:(lia) H3).
  assert (Hg5 : ms_gpr ms1 5 = Z_to_bv 64 off) by exact (gpr_const segs E L (restrict H ms) ms 5 off Hsd eq_refl ltac:(lia) H5).
  destruct (is_const_sound E _ len H1) as [_ Hlen64].
  assert (HnZ : page_round_up_Z (bv_unsigned (Z_to_bv 64 len)) = k) by (rewrite fg64 by exact Hlen64; symmetry; exact Hlen).
  assert (HnZpos : 0 < k) by (rewrite <- HnZ; exact (len_nZ_pos _ Hnz0)).
  assert (HnZal : k mod 4096 = 0) by (rewrite <- HnZ; exact (page_round_up_Z_aligned' _)).
  assert (Hub : bv_unsigned (Z_to_bv 64 b) = b) by (apply fg64; lia).
  assert (HTOP : b + k <= alloc_top (m_vmmaps model)).
  { destruct Hspok as [Hsp1 _]. unfold init_sp_ok, sp_window_lo in Hsp1. unfold alloc_top, stack_max_size. lia. }
  assert (Hrf : region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) (Z_to_bv 64 b) (Z_to_bv 64 k) = true).
  { rewrite Hres, Hmaps. apply norep_free_sound; [exact Hgsh | lia | unfold SH_HI, two64 in *; lia | exact Hfree]. }
  assert (Hplace : place_ok model k (Z_to_bv 64 b)).
  { unfold place_ok, page_size. rewrite Hub. repeat split; try lia. exact Hrf. }
  assert (Hgate : fixed_gate model (Z_to_bv 64 b) (Z_to_bv 64 len)).
  { unfold fixed_gate, page_size. rewrite Hub, HnZ. repeat split; lia. }
  assert (Hsh : forall w, b <= w < b + k -> in_shadow w = true).
  { intros w Hw. unfold in_shadow. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  assert (Hkk : kd = GL) by (destruct kd; cbn in Hkd; try discriminate; reflexivity).
  destruct (sden_0 _ _ _ _ Hsd) as (_ & _ & _ & _ & HG0 & HD0 & HF0 & _).
  destruct (bandp_spec E (s_facts L) (s_next L) model (sm_sp M) b k pb ps ub HF0 Hsp (proj2 Hspok) (proj1 Hspok) ltac:(lia) Hband)
    as (P1 & P2 & P3).
  assert (P4 : rgs_disj E (piece_rgs [(pb, ps, ub)])) by (cbn; split; [constructor | exact I]).
  assert (Hbud' : eager_sum (s_facts L) ((lconst b, lconst k, kd) :: sm_maps M) + allow_bound (piece_allow [(pb, ps, ub)] ++ sm_allow M) <= LIMIT)
    by exact Hbud.
  pose proof (norep_den segs LIMIT model0 mem0 Hsegb E L M ms model b k kd (Z_to_bv 64 flags) false [(pb, ps, ub)] zr Hd ltac:(unfold two64 in *; lia) Hplace
                HnZpos HnZal Hsh Hnr Hkk ltac:(discriminate) ltac:(constructor; [exact P1 | constructor]) ltac:(cbn; rewrite P2; reflexivity) P4 Hbud'
                ltac:(constructor; [exact P3 | constructor]) Hon Hnm) as HD'.
  assert (Hsvc : ms_svc_pending ms1 = Some (ms_reg ms 17)) by reflexivity.
  assert (Hno : bv_unsigned (ms_reg ms 17) = 222) by (rewrite Hx8; reflexivity).
  assert (Hbr := branch_noreplace_rw_free segs ms1 (ms_reg ms 17) model Hno).
  rewrite ?Hg0, ?Hg1, ?Hg2, ?Hg3, ?Hg5 in Hbr. rewrite HnZ in Hbr.
  apply andb_prop in Hsel as [Hsel1 Hsel2]. apply negb_true_iff in Hsel1.
  specialize (Hbr Hoffa Hanon Hnz0 Hmod Hnac Hfna Hfrw Hsel1 Hsel2 Hgate Hrf).
  eapply rzc_silent1; [|exact (Hk _ _ HD')].
  apply (node_mmap_alt_choose_at segs cfg Hoff ms1 model (ms_reg ms 17) (Z_to_bv 64 b)
           (fun a => a = Z_to_bv 64 b /\ mmap_noreserve_backed_ok (Z_to_bv 64 flags) model k = true)
           (fun a => fresh_rw_next (Z_to_bv 64 flags) a (Z_to_bv 64 k) model)
           (fun a => mkEffect a [] [(a, Z_to_bv 64 k)]) Hh Hsvc Hno Hbr).
  - intros a [Ha _]. exact Ha.
  - split; [reflexivity|]. unfold mmap_noreserve_backed_ok. rewrite Hnr. reflexivity.
  - cbn [eff_ret]. apply (below_top_not_errno (m_vmmaps model) _ ENOMEM ENOMEM_range). rewrite Hub. lia.
  - intros a. apply vm_only_fresh_rw_next.
  - reflexivity.
Qed.
End NorepBNode.
End FxChNorepB.

From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChFix FxChAdd FxChFixNew FxChUnmap.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChMprot.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChMprot.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChStart.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChStart.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChSep OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChSeg OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChNode OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFix.FxChNorep OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain.FxChNorepB OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFix OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChAdd OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFixNew OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChUnmap OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMprot.FxChBrk OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMprot OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChStart.FxChLoop OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChStart.

Module FxChSys.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Run Specs Fs.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi Syscall.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Open.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg SysNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop FxPlan FxFrame FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.FxAcct.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChMprot.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChFix FxChStart.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChSeg OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChNode OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMprot.FxChBrk OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFix OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChStart.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Instance chs_fx : FPState := fx0.

Section Sys.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.

(* [comment removed for export] *)
#[using="Type"] Lemma rzc_sys_acc : forall H A ms model x8 (I : Type) (EF : I -> SyscallEffect) (MD : I -> Model) (EV : I -> list event)
    (T : I -> TSet) (i0 : I),
  A_wf A -> m_halted model = None -> ms_svc_pending ms = Some x8 ->
  (forall j, syscall_spec (sys_input segs ms x8) model (Ok (EF j) (MD j) (EV j))) ->
  (forall eff m' evs, syscall_spec (sys_input segs ms x8) model (Ok eff m' evs) -> exists j, eff = EF j /\ m' = MD j /\ evs = EV j) ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled ->
  (forall eff, ~ spurious_refusal_cfg cfg (sys_input segs ms x8) model eff) ->
  (forall j, m_halted (MD j) = None) ->
  (forall j, lazy_cover H (m_vm_lazy (MD j)) A) -> (forall j, MInv A (MD j)) ->
  (forall j, ranges_avoid H (syscall_effect_accesses (EF j))) ->
  (forall j m'', MInv A m'' -> same_but_materialized (MD j) m'' ->
     realizes_cfg segs cfg (mkCfg (advance_past_svc (apply_effect ms (EF j))) m'') (T j)) ->
  realizes_cfg segs cfg (mkCfg ms model) (t_alt (fun j => t_emit (EV j) (T j))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros H A ms model x8 I EF MD EV T i0 Hwf Hh Hsvc Hcomp Hsound Hnu Hns HhM Hcov Hinv Hav HK.
  assert (Hmat : forall j, exists mat',
            materialize_model_accesses (MD j) (syscall_effect_accesses (EF j))
              = Some (with_vm_backing (m_vm_lazy (MD j)) mat' (MD j))
            /\ MInv A (with_vm_backing (m_vm_lazy (MD j)) mat' (MD j))).
  { intros j. exact (materialize_restricted H A (MD j) _ (Hcov j) Hwf (Hinv j) (Hav j)). }
  apply (rzc_node segs cfg (mkCfg ms model) I EV
           (fun j => mkCfg (advance_past_svc (apply_effect ms (EF j))) (materialized_succ (MD j) (syscall_effect_accesses (EF j)))) T i0).
  - apply (node_sys_cfg segs cfg ms model x8 I EF MD (fun j => materialized_succ (MD j) (syscall_effect_accesses (EF j))) EV Hh Hsvc Hcomp).
    + intros j. apply Hns.
    + intros eff m' evs Hs _. exact (Hsound eff m' evs Hs).
    + exact Hnu.
    + intros eff m' evs Hs. destruct (Hsound eff m' evs Hs) as (j & _ & -> & _). apply HhM.
    + intros j. destruct (Hmat j) as (mat' & Hm & _). unfold materialized_succ. rewrite Hm. reflexivity.
  - intros j. destruct (Hmat j) as (mat' & Hm & Hinv'). apply HK.
    + unfold materialized_succ. rewrite Hm. exact Hinv'.
    + unfold materialized_succ. rewrite Hm. apply with_vm_backing_same.
Qed.


Variable LIMIT : Z.
Variable mem0 : word -> option byte.

#[using="Type"] Lemma with_fds_vmmaps' : forall f m, m_vmmaps (with_fds f m) = m_vmmaps m. Proof. LiaFast.lf_pins LiaFast.u0. intros f m; destruct m; reflexivity. Qed.
#[using="Type"] Lemma with_fds_mat' : forall f m, m_vm_materialized (with_fds f m) = m_vm_materialized m. Proof. LiaFast.lf_pins LiaFast.u0. intros f m; destruct m; reflexivity. Qed.
#[using="Type"] Lemma with_fds_tid' : forall f m, m_tid (with_fds f m) = m_tid m. Proof. LiaFast.lf_pins LiaFast.u0. intros f m; destruct m; reflexivity. Qed.
#[using="Type"] Lemma with_fds_proc' : forall f m, m_proc (with_fds f m) = m_proc m. Proof. LiaFast.lf_pins LiaFast.u0. intros f m; destruct m; reflexivity. Qed.
#[using="Type"] Lemma eager_used_with_fds : forall f m, eager_used (with_fds f m) = eager_used m. Proof. LiaFast.lf_pins LiaFast.u0. intros f m; destruct m; reflexivity. Qed.
#[using="Type"] Lemma MInv_with_fds : forall A f m, MInv A m -> MInv A (with_fds f m).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros A f m [H1 H2 H3 H4 H5]. constructor; rewrite ?with_fds_mat', ?with_fds_lazy, ?with_fds_vmmaps', ?eager_used_with_fds; assumption.
Qed.
#[using="Type"] Lemma with_tid_fds' : forall t f m, with_tid t (with_fds f m) = with_fds f (with_tid t m). Proof. LiaFast.lf_pins LiaFast.u0. intros t f m; destruct m; reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma den_fds : forall model0 E L M ms model f,
  DEN segs LIMIT model0 mem0 E L M ms model ->
  DEN segs LIMIT (with_fds f model0) mem0 E L M ms (with_fds f model).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros model0 E L M ms model f Hd.
  destruct Hd as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  assert (HH : Hof E M (with_fds f model) = Hof E M model) by (unfold Hof; rewrite with_fds_lazy; reflexivity).
  constructor; rewrite ?HH, ?with_fds_vmmaps', ?with_fds_lazy, ?with_fds_halted, ?with_fds_tid'; try assumption.
  all: try exact (MInv_with_fds _ f model Hminv).
  all: try (unfold kind_ok in *; rewrite Forall_forall in *; intros g Hg; rewrite with_fds_vmmaps', with_fds_lazy; exact (Hkind g Hg)).
  all: try (unfold rl_ok, app_pt in *; rewrite Forall_forall in *; intros R HR; rewrite with_fds_vmmaps'; exact (Hrl R HR)).
  all: try (destruct Hvmo as (H1 & H2 & H3 & H4 & H5); destruct model, model0; cbn in *; rewrite H1; repeat split; assumption).
  all: try (rewrite with_fds_proc'; rewrite Hproc; destruct (m_tid model) as [t|];
            [rewrite with_tid_fds', with_fds_proc'; reflexivity | rewrite with_fds_proc'; reflexivity]).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma den_ret_ci : forall model0 E L M ms model (v : lin) f ci m'',
  DEN segs LIMIT model0 mem0 E L M ms model -> lwf (s_next L) v = true ->
  MInv (AM model0 E M) m'' -> same_but_materialized (with_fds f model) m'' ->
  DEN segs LIMIT (with_fds f model0) mem0 E (ret_post L v) M
      (advance_past_svc (apply_effect (svc_set ms) (mkEffectU (lden E v) [] [] [] [] ci))) m''.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros model0 E L M ms model v f ci m'' Hd Hwv Hinv Hsb.
  pose proof (den_fds _ E _ M _ model f (den_ret segs LIMIT model0 mem0 E L M ms model v Hd Hwv)) as H2.
  exact (den_sbm segs LIMIT (with_fds f model0) mem0 E (ret_post L v) M _ (with_fds f model) m'' H2 Hsb Hinv).
Qed.

(* [comment removed for export] *)
#[using="mem0"] Lemma in_arg_svc : forall ms x8 k, (k <= 5)%nat -> in_arg (sys_input segs (svc_set ms) x8) k = ms_gpr (svc_set ms) k.
Proof. LiaFast.lf_pins (fun (mem0 : LiaFast.U) => LiaFast.u0). intros ms x8 k Hk. unfold in_arg, sys_input. cbn [in_args]. unfold syscall_args. do 6 (destruct k as [|k]; [reflexivity|]). lia. Qed.
#[using="Type"] Lemma in_sysno_svc : forall ms x8, in_sysno (sys_input segs (svc_set ms) x8) = x8. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma svc_set_pending : forall ms, ms_svc_pending (svc_set ms) = Some (ms_reg ms 17). Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
(* [comment removed for export] *)
Definition argl (L : sst) (k : Z) : lin := rget (s_regs L) (rkey (Z_to_bv 5 (10 + k))).
#[using="Type"] Lemma gpr_lin_k : forall E L (msr ms : machine_state) (k : nat), sden segs E L msr -> ms_regs msr = ms_regs ms -> (k <= 5)%nat ->
  ms_gpr (svc_set ms) k = lden E (argl L (Z.of_nat k)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E L msr ms k Hd Hr Hk. destruct (sden_0 _ _ _ _ Hd) as (_ & _ & _ & HR & _).
  specialize (HR (Z_to_bv 5 (10 + Z.of_nat k))). unfold ms_gpr. cbn [svc_set ms_regs]. rewrite <- Hr. unfold getr in HR.
  assert (Hne : bv_eqb (Z_to_bv 5 (10 + Z.of_nat k)) 0 = false).
  { destruct k as [|[|[|[|[|[|k]]]]]]; try lia; reflexivity. }
  rewrite Hne in HR. exact HR.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem den_close : forall model0 E L M ms model T (fd : Z) ent,
  DEN segs LIMIT model0 mem0 E L M ms model ->
  a7c L = Some 57 -> arg L 0 = Some fd ->
  fd_lookup (m_fds model0) (fd32 (Z_to_bv 64 fd)) = Some ent ->
  (forall ms' m'', DEN segs LIMIT (with_fds (fd_remove (m_fds model0) (fd32 (Z_to_bv 64 fd))) model0) mem0 E (ret_post L (lconst 0)) M ms' m'' ->
      realizes_cfg segs cfg (mkCfg ms' m'') T) ->
  realizes_cfg segs cfg (mkCfg (svc_set ms) model) T.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros model0 E L M ms model T fd ent Hd H7 H0 Hfd Hk. pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  set (H := Hof E M model) in *.
  set (ms1 := svc_set ms).
  set (x8 := ms_reg ms 17).
  assert (Hx8 : x8 = Z_to_bv 64 57) by exact (a7_const segs E L (restrict H ms) ms 57 Hsd eq_refl H7).
  assert (Hg0 : ms_gpr ms1 0 = Z_to_bv 64 fd) by exact (gpr_const segs E L (restrict H ms) ms 0 fd Hsd eq_refl ltac:(lia) H0).
  set (i := sys_input segs ms1 x8).
  assert (Hno : bv_unsigned (in_sysno i) = 57%Z) by (unfold i; cbn [in_sysno sys_input]; rewrite Hx8; reflexivity).
  assert (A0 : in_arg i 0 = Z_to_bv 64 fd) by (unfold i, ms1; rewrite in_arg_svc by lia; exact Hg0).
  assert (Hfm : m_fds model = m_fds model0) by (destruct Hvmo as (H1 & _); unfold m_fds; rewrite H1; reflexivity).
  set (f := fd_remove (m_fds model0) (fd32 (Z_to_bv 64 fd))).
  assert (Hspc : forall o, syscall_spec i model o <-> (set_fds f ;; ret_only (Z_to_bv 64 0)) i model o).
  { intro o. rewrite (syscall_spec_57 i model o Hno). rewrite A0. unfold close_spec. rewrite bind_get_model.
    rewrite Hfm, Hfd. reflexivity. }
  eapply rzc_conseq.
  - apply (rzc_sys_acc H (AM model0 E M) ms1 model x8 unit (fun _ => mkEffect (Z_to_bv 64 0) [] []) (fun _ => with_fds f model)
             (fun _ => []) (fun _ => T) tt (A_wf_app _ _ Hawf (A_wf_blobA _)) Hh (svc_set_pending ms)).
    + intros []. apply Hspc. unfold set_fds, modify, ret_only, bind, pure. exists tt, (with_fds f model), [], []. auto.
    + intros eff m' evs Hs. apply Hspc in Hs. unfold set_fds, modify, ret_only, bind, pure in Hs. sys_destruct. exists tt. auto.
    + intros Hs. apply Hspc in Hs. unfold set_fds, modify, ret_only, bind, pure in Hs. sys_destruct.
    + intros eff. apply not_spurious_uninjected. fold i. rewrite Hno. reflexivity.
    + intros _. rewrite with_fds_halted. exact Hh.
    + intros _. rewrite with_fds_lazy. apply lazy_cover_mkH_app. intros x Hx'. exact Hx'.
    + intros _. exact (MInv_with_fds _ f model Hminv).
    + intros _. apply ranges_avoid_nil.
    + intros _ m'' Hinv'' Hsb''. apply Hk.
      exact (den_ret_ci model0 E L M ms model (lconst 0) f [] m'' Hd eq_refl Hinv'' Hsb'').
  - apply t_alt_const_nil; [exact tt|].
    assert (HR : realizes_cfg segs cfg (mkCfg (advance_past_svc (apply_effect ms1 (mkEffect (Z_to_bv 64 0) [] []))) (with_fds f model)) T).
    { apply Hk. exact (den_ret_ci model0 E L M ms model (lconst 0) f [] (with_fds f model) Hd eq_refl (MInv_with_fds _ f model Hminv)
                         (same_but_materialized_refl _)). }
    exact (realizes_cfg_nonempty segs cfg _ _ HR).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma den_ret_ci0 : forall model0 E L M ms model (v : lin) ci m'',
  DEN segs LIMIT model0 mem0 E L M ms model -> lwf (s_next L) v = true ->
  MInv (AM model0 E M) m'' -> same_but_materialized model m'' ->
  DEN segs LIMIT model0 mem0 E (ret_post L v) M (advance_past_svc (apply_effect (svc_set ms) (mkEffectU (lden E v) [] [] [] [] ci))) m''.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros model0 E L M ms model v ci m'' Hd Hwv Hinv Hsb.
  exact (den_sbm segs LIMIT model0 mem0 E (ret_post L v) M _ model m'' (den_ret segs LIMIT model0 mem0 E L M ms model v Hd Hwv) Hsb Hinv).
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem den_ioctl_notty : forall model0 E L M ms model T (fd cmd : Z) ch,
  DEN segs LIMIT model0 mem0 E L M ms model ->
  a7c L = Some 29 -> arg L 0 = Some fd -> arg L 1 = Some cmd ->
  fd_lookup (m_fds model0) (fd32 (Z_to_bv 64 fd)) = Some (FdChannel ch) ->
  tty_only_request (cmd32 (Z_to_bv 64 cmd)) = true ->
  (forall ms' m'', DEN segs LIMIT model0 mem0 E (ret_post L (lconst (bv_unsigned (errno_ret ENOTTY)))) M ms' m'' ->
      realizes_cfg segs cfg (mkCfg ms' m'') T) ->
  realizes_cfg segs cfg (mkCfg (svc_set ms) model) T.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros model0 E L M ms model T fd cmd ch Hd H7 H0 H1 Hfd Htty Hk. pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  set (H := Hof E M model) in *.
  set (ms1 := svc_set ms).
  set (x8 := ms_reg ms 17).
  assert (Hx8 : x8 = Z_to_bv 64 29) by exact (a7_const segs E L (restrict H ms) ms 29 Hsd eq_refl H7).
  assert (Hg0 : ms_gpr ms1 0 = Z_to_bv 64 fd) by exact (gpr_const segs E L (restrict H ms) ms 0 fd Hsd eq_refl ltac:(lia) H0).
  assert (Hg1 : ms_gpr ms1 1 = Z_to_bv 64 cmd) by exact (gpr_const segs E L (restrict H ms) ms 1 cmd Hsd eq_refl ltac:(lia) H1).
  set (i := sys_input segs ms1 x8).
  assert (Hno : bv_unsigned (in_sysno i) = 29%Z) by (unfold i; cbn [in_sysno sys_input]; rewrite Hx8; reflexivity).
  assert (A0 : in_arg i 0 = Z_to_bv 64 fd) by (unfold i, ms1; rewrite in_arg_svc by lia; exact Hg0).
  assert (A1 : in_arg i 1 = Z_to_bv 64 cmd) by (unfold i, ms1; rewrite in_arg_svc by lia; exact Hg1).
  assert (Hfm : m_fds model = m_fds model0) by (destruct Hvmo as (H1' & _); unfold m_fds; rewrite H1'; reflexivity).
  assert (Hspi : forall o, syscall_spec i model o <-> err_ret ENOTTY i model o).
  { intro o. rewrite (syscall_spec_29 i model o Hno). rewrite A0, A1. unfold ioctl_spec. rewrite bind_get_model.
    rewrite Hfm, Hfd, Htty. reflexivity. }
  assert (Hwv : lwf (s_next L) (lconst (bv_unsigned (errno_ret ENOTTY))) = true) by reflexivity.
  assert (Hcont : forall m'', MInv (AM model0 E M) m'' -> same_but_materialized model m'' ->
     realizes_cfg segs cfg (mkCfg (advance_past_svc (apply_effect ms1 (mkEffect (errno_ret ENOTTY) [] []))) m'') T).
  { intros m'' Hinv'' Hsb''. apply Hk.
    pose proof (den_ret_ci0 model0 E L M ms model (lconst (bv_unsigned (errno_ret ENOTTY))) [] m'' Hd Hwv Hinv'' Hsb'') as HD.
    rewrite lden_lconst, u64_roundtrip in HD. exact HD. }
  eapply rzc_conseq.
  - apply (rzc_sys_acc H (AM model0 E M) ms1 model x8 unit (fun _ => mkEffect (errno_ret ENOTTY) [] []) (fun _ => model)
             (fun _ => []) (fun _ => T) tt (A_wf_app _ _ Hawf (A_wf_blobA _)) Hh (svc_set_pending ms)).
    + intros []. apply Hspi. apply err_ret_ok_iff. auto.
    + intros eff m' evs Hs. apply Hspi, err_ret_ok_iff in Hs as (-> & -> & ->). exists tt. auto.
    + intros Hs. apply Hspi in Hs. exact (err_ret_unmodeled _ _ _ Hs).
    + intros eff. apply not_spurious_uninjected. fold i. rewrite Hno. reflexivity.
    + intros _. exact Hh.
    + intros _. apply lazy_cover_mkH_app. intros x Hx'. exact Hx'.
    + intros _. exact Hminv.
    + intros _. apply ranges_avoid_nil.
    + intros _ m'' Hinv'' Hsb''. exact (Hcont m'' Hinv'' Hsb'').
  - apply t_alt_const_nil; [exact tt|].
    exact (realizes_cfg_nonempty segs cfg _ _ (Hcont model Hminv (same_but_materialized_refl _))).
Qed.

(* [comment removed for export] *)
Section Open.
Hypothesis Hfs : sc_fs cfg = true.

#[using="Hfs"] Theorem den_openat_file : forall model0 E L M ms model (A B : TSet) (c0 flags : Z) p data (fd3 : word),
  DEN segs LIMIT model0 mem0 E L M ms model ->
  a7c L = Some 56 -> arg L 0 = Some c0 -> fd32 (Z_to_bv 64 c0) = AT_FDCWD32 ->
  arg L 2 = Some flags -> Z.ldiff (bv_unsigned (Z_to_bv 64 flags)) open_ignored_flags = 0 ->
  read_cstr (in_mem (sys_input segs (svc_set ms) (ms_reg ms 17))) (lden E (rget (s_regs L) (rkey a1r))) = CstrOk p ->
  path_eqb p [] = false -> path_has_slash p = false -> path_is_dirref p = false ->
  fs_lookup (m_fs model0) p = Some data ->
  alloc_fd (m_fds model0) = fd3 -> fd_lookup (m_fds model0) fd3 = None -> (bv_unsigned fd3 < 2 ^ 63) ->
  ranges_avoid (Hof E M model) [(lden E (rget (s_regs L) (rkey a1r)),
                                 cstr_access_len_aux (in_mem (sys_input segs (svc_set ms) (ms_reg ms 17))) (lden E (rget (s_regs L) (rkey a1r))) path_max)] ->
  (forall e, In e openat_errnos -> forall ms' m'', DEN segs LIMIT model0 mem0 E (ret_post L (lconst (bv_unsigned (errno_ret e)))) M ms' m'' ->
      realizes_cfg segs cfg (mkCfg ms' m'') A) ->
  (forall ms' m'', DEN segs LIMIT (with_fds (fd_insert (m_fds model0) fd3 (FdFile p (Z_to_bv 64 0))) model0) mem0 E
                      (ret_post L (lconst (bv_unsigned fd3))) M ms' m'' -> realizes_cfg segs cfg (mkCfg ms' m'') B) ->
  realizes_cfg segs cfg (mkCfg (svc_set ms) model) (t_alt2 A B).
Proof. LiaFast.lf_pins (fun (Hfs : LiaFast.U) => LiaFast.u0).
  intros model0 E L M ms model A B c0 flags p data fd3 Hd H7 H0 Hdfd H2 Hfl Hc Hne Hsl Hdr Hlk Hal Hfree Hfd64 Hav HA HB.
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  set (H := Hof E M model) in *.
  set (ms1 := svc_set ms).
  set (x8 := ms_reg ms 17) in *.
  assert (Hx8 : x8 = Z_to_bv 64 56) by exact (a7_const segs E L (restrict H ms) ms 56 Hsd eq_refl H7).
  assert (Hg0 : ms_gpr ms1 0 = Z_to_bv 64 c0) by exact (gpr_const segs E L (restrict H ms) ms 0 c0 Hsd eq_refl ltac:(lia) H0).
  assert (Hg1 : ms_gpr ms1 1 = lden E (rget (s_regs L) (rkey a1r))) by exact (gpr_lin1 segs E L (restrict H ms) ms Hsd eq_refl).
  assert (Hg2 : ms_gpr ms1 2 = Z_to_bv 64 flags) by exact (gpr_const segs E L (restrict H ms) ms 2 flags Hsd eq_refl ltac:(lia) H2).
  set (i := sys_input segs ms1 x8) in *.
  assert (Hno : bv_unsigned (in_sysno i) = 56%Z) by (unfold i; cbn [in_sysno sys_input]; rewrite Hx8; reflexivity).
  assert (A0 : in_arg i 0 = Z_to_bv 64 c0) by (unfold i, ms1; rewrite in_arg_svc by lia; exact Hg0).
  assert (A1 : in_arg i 1 = lden E (rget (s_regs L) (rkey a1r))) by (unfold i, ms1; rewrite in_arg_svc by lia; exact Hg1).
  assert (A2 : in_arg i 2 = Z_to_bv 64 flags) by (unfold i, ms1; rewrite in_arg_svc by lia; exact Hg2).
  assert (Hfm : m_fds model = m_fds model0) by (destruct Hvmo as (H1' & _); unfold m_fds; rewrite H1'; reflexivity).
  assert (Hfsm : m_fs model = m_fs model0) by (destruct Hvmo as (_ & _ & H3' & _); unfold m_fs; rewrite H3'; reflexivity).
  set (pl := lden E (rget (s_regs L) (rkey a1r))) in *.
  set (ci := [(pl, cstr_access_len_aux (in_mem i) pl path_max)]) in *.
  set (ent := FdFile p (Z_to_bv 64 0)).
  set (f := fd_insert (m_fds model0) fd3 ent).
  assert (Hspo : forall o, syscall_spec i model o <-> record_copyins ci (open_result_spec model (fun fd => with_fds (fd_insert (m_fds model) fd ent))) i model o).
  { intro o. rewrite (syscall_spec_56 i model o Hno). rewrite A0, A1, A2, Hdfd.
    rewrite (openat_rd_reduce AT_FDCWD32 pl (Z_to_bv 64 flags) p i model o eq_refl Hfl Hc Hne Hsl).
    fold ci. destruct o as [eff m' evs|].
    - rewrite !record_copyins_ok_iff. split; intros (eff0 & Ho & ->); exists eff0; split; try reflexivity;
        unfold openat_read_spec in *; rewrite Hdr, Hfsm, Hlk in *; exact Ho.
    - rewrite !record_copyins_unmodeled_iff. unfold openat_read_spec. rewrite Hdr, Hfsm, Hlk. reflexivity. }
  set (I := ({e : Z | In e openat_errnos} + unit)%type).
  assert (ia : {e : Z | In e openat_errnos}) by (exists ENOMEM; left; reflexivity).
  assert (Hw0 : forall z, lwf (s_next L) (lconst z) = true) by reflexivity.
  assert (HcA : forall e, In e openat_errnos -> forall m'', MInv (AM model0 E M) m'' -> same_but_materialized model m'' ->
     realizes_cfg segs cfg (mkCfg (advance_past_svc (apply_effect ms1 (ret_ci (errno_ret e) ci))) m'') A).
  { intros e He m'' Hinv'' Hsb''. apply (HA e He).
    pose proof (den_ret_ci0 model0 E L M ms model (lconst (bv_unsigned (errno_ret e))) ci m'' Hd (Hw0 _) Hinv'' Hsb'') as HD.
    rewrite lden_lconst, u64_roundtrip in HD. exact HD. }
  assert (HcB : forall m'', MInv (AM model0 E M) m'' -> same_but_materialized (with_fds f model) m'' ->
     realizes_cfg segs cfg (mkCfg (advance_past_svc (apply_effect ms1 (ret_ci fd3 ci))) m'') B).
  { intros m'' Hinv'' Hsb''. apply HB.
    pose proof (den_ret_ci model0 E L M ms model (lconst (bv_unsigned fd3)) f ci m'' Hd (Hw0 _) Hinv'' Hsb'') as HD.
    rewrite lden_lconst, u64_roundtrip in HD. exact HD. }
  eapply rzc_conseq.
  - apply (rzc_sys_acc H (AM model0 E M) ms1 model x8 I
             (fun j => match j with inl e => ret_ci (errno_ret (proj1_sig e)) ci | inr _ => ret_ci fd3 ci end)
             (fun j => match j with inl _ => model | inr _ => with_fds f model end)
             (fun _ => [])
             (fun j => match j with inl _ => A | inr _ => B end) (inl ia) (A_wf_app _ _ Hawf (A_wf_blobA _)) Hh (svc_set_pending ms)).
    + intros [[e He]|[]]; apply Hspo; apply record_copyins_ok_iff; cbn [proj1_sig].
      * exists (mkEffect (errno_ret e) [] []). split.
        2:{ unfold with_copyins, ret_ci. cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies eff_copyins].
            rewrite app_nil_r. reflexivity. }
        apply open_result_ok_iff. left. exists e. auto.
      * exists (mkEffect fd3 [] []). split.
        2:{ unfold with_copyins, ret_ci. cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies eff_copyins].
            rewrite app_nil_r. reflexivity. }
        apply open_result_ok_iff. right. rewrite Hfm, Hal. split; [exact Hfree|]. unfold f. rewrite <- Hfm. auto.
    + intros eff m' evs Hs. apply Hspo, record_copyins_ok_iff in Hs as (eff0 & Hs & ->).
      apply open_result_ok_iff in Hs as [(e & He & -> & -> & ->) | (_ & -> & -> & ->)].
      * exists (inl (exist _ e He)). cbn [proj1_sig]. auto.
      * exists (inr tt). rewrite Hfm, Hal. unfold f. rewrite <- Hfm. auto.
    + intros Hs. apply Hspo, record_copyins_unmodeled_iff in Hs. exact (open_result_unmodeled _ _ _ Hs).
    + intros eff. apply not_spurious_fs; [exact Hfs | exact Hno].
    + intros [_|_]; [exact Hh | rewrite with_fds_halted; exact Hh].
    + intros [_|_]; [| rewrite with_fds_lazy]; apply lazy_cover_mkH_app; intros x Hx'; exact Hx'.
    + intros [_|_]; [exact Hminv | exact (MInv_with_fds _ f model Hminv)].
    + intros [e|[]]; unfold ret_ci, syscall_effect_accesses; cbn [eff_copyins eff_writes write_accesses]; rewrite app_nil_r; exact Hav.
    + intros [[e He]|[]] m'' Hinv'' Hsb''; cbn [proj1_sig]; [exact (HcA e He m'' Hinv'' Hsb'') | exact (HcB m'' Hinv'' Hsb'')].
  - apply t_alt_sum_nil; [exact ia | |].
    + exact (realizes_cfg_nonempty segs cfg _ _ (HcA ENOMEM ltac:(left; reflexivity) model Hminv (same_but_materialized_refl _))).
    + exact (realizes_cfg_nonempty segs cfg _ _ (HcB (with_fds f model) (MInv_with_fds _ f model Hminv) (same_but_materialized_refl _))).
Qed.
End Open.

(* [comment removed for export] *)
Definition read_post (L : sst) (i : nat) (lo hi : Z) (v : lin) : sst :=
  match nth_error (s_rgs L) i with
  | Some R => SST (s_pc L + 4) (rset (s_regs L) (rkey a0r) v)
                  (upd_nth (s_rgs L) i (RG (rg_base R) (rg_size R) RW (havoc_range (rg_cont R) lo hi))) (s_facts L) (s_next L) (s_resv L)
  | None => L
  end.

#[using="Type"] Lemma rg_ok_rz_rw : forall E m R, rg_kind R = RZ -> rg_ok segs E m R -> rg_ok segs E m (RG (rg_base R) (rg_size R) RW (rg_cont R)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m R Hk (H1 & H2 & H3 & H4). unfold rg_ok, rsz in *. cbn [rg_base rg_size rg_kind rg_cont] in *.
  split; [exact H1|]. split; [exact H2|]. split; [|exact H4].
  intros i Hi. specialize (H3 i Hi). rewrite Hk in H3. exact (proj1 H3).
Qed.
#[using="Type"] Lemma rg_ok_rw_rw : forall E m R, rg_kind R = RW -> rg_ok segs E m R -> rg_ok segs E m (RG (rg_base R) (rg_size R) RW (rg_cont R)).
Proof. LiaFast.lf_pins LiaFast.u0. intros E m [b sz k c] Hk HR. cbn in Hk. subst k. exact HR. Qed.

#[using="Type"] Lemma sden_read_post : forall E L msr i R o lo hi bs (v : lin) (w : word),
  sden segs E L msr -> bases_wf (s_next L) (s_rgs L) = true ->
  nth_error (s_rgs L) i = Some R -> (rg_kind R = RW \/ rg_kind R = RZ) ->
  0 <= o -> (forall E', agree (s_next L) E E' -> o + Z.of_nat (length bs) <= rsz E' R) -> lo <= o -> o + Z.of_nat (length bs) <= hi ->
  (forall E', agree (s_next L) E E' -> lden E' v = w) ->
  sden segs E (read_post L i lo hi v)
       (mks (ms_fregs msr) (ms_fcsr msr) (rupd (ms_regs msr) a0r w) (Z_to_bv 64 (s_pc L + 4)) (ms_resv msr)
            (write_to_mem (ms_mem msr) (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + o)) bs) (ms_rom msr)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E L msr i R o lo hi bs v w Hsd Hbw Hi Hk Ho Hsz Hlo Hhi Hv.
  unfold read_post. rewrite Hi. intros E' Ha. cbn [s_next] in Ha.
  destruct (Hsd E' Ha) as (Hpc & Hsv & Hrv & HR & HG & HD & HF & Hfrm).
  assert (HbR : lwf (s_next L) (rg_base R) = true).
  { unfold bases_wf in Hbw. rewrite forallb_forall in Hbw. pose proof (Hbw R (nth_error_In _ _ Hi)) as X. apply andb_prop in X as [X _]. exact X. }
  assert (Hbase : lden E' (rg_base R) = lden E (rg_base R)) by exact (lden_agree_wf _ E E' _ HbR Ha).
  rewrite <- Hbase.
  unfold sden0. cbn [s_pc s_regs s_rgs s_facts s_resv mks ms_pc_val ms_svc_pending ms_resv ms_regs ms_mem ms_fcsr].
  split; [reflexivity|]. split; [reflexivity|]. split; [exact Hrv|]. split.
  - pose proof (regs_ok_upd E' (s_regs L) (ms_regs msr) a0r v w HR (Hv E' Ha)) as X.
    assert (E10 : bv_eqb a0r 0 = false) by reflexivity. rewrite E10 in X. unfold rupd. rewrite E10. exact X.
  - split; [|split; [|split; [exact HF | exact Hfrm]]].
    + apply Forall_nth'. intros j Rj Hj. destruct (Nat.eq_dec j i) as [->|Hne].
      * rewrite (nth_upd_same _ _ _ _ Hi) in Hj. injection Hj as <-.
        pose proof (proj1 (Forall_nth' _ _) HG i R Hi) as HR0.
        assert (HRW : rg_ok segs E' (ms_mem msr) (RG (rg_base R) (rg_size R) RW (rg_cont R))).
        { destruct Hk as [Hk|Hk]; [exact (rg_ok_rw_rw E' _ R Hk HR0) | exact (rg_ok_rz_rw E' _ R Hk HR0)]. }
        pose proof (rg_havoc_ok segs E' (RG (rg_base R) (rg_size R) RW (rg_cont R)) (ms_mem msr) o lo hi bs eq_refl HRW Ho) as X.
        cbn [rg_base rg_size rg_cont] in X. apply X; [unfold rsz in *; cbn [rg_size] in *; exact (Hsz E' Ha) | exact Hlo | exact Hhi].
      * rewrite (nth_upd_other _ _ _ _ (not_eq_sym Hne)) in Hj.
        exact (rgs_frame_write segs E' (ms_mem msr) (s_rgs L) i R o bs HG HD Hi Ho (Hsz E' Ha) j Rj Hne Hj).
    + exact (rgs_disj_upd E' (s_rgs L) i (RG (rg_base R) (rg_size R) RW (havoc_range (rg_cont R) lo hi)) R Hi eq_refl eq_refl HD).
Qed.

#[using="Type"] Lemma apply_writes_delivered : forall m buf bs, apply_writes m (delivered_writes buf bs) = write_to_mem m buf bs.
Proof. LiaFast.lf_pins LiaFast.u0. intros m buf [|b bs]; reflexivity. Qed.

#[using="Type"] Lemma restrict_adv_write : forall H ms v buf bs pcz, ms_pc_val ms = Z_to_bv 64 pcz ->
  restrict H (advance_past_svc (apply_effect (svc_set ms) (mkEffect v (delivered_writes buf bs) []))) =
  mks (ms_fregs ms) (ms_fcsr ms) (rupd (ms_regs ms) a0r v) (Z_to_bv 64 (pcz + 4)) (ms_resv ms)
      (mrestrict H (write_to_mem (ms_mem ms) buf bs)) (ms_rom ms).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros H ms v buf bs pcz Hpc. destruct ms as [rg fr pcv sv rv fc mem rom]. cbn in Hpc. subst pcv.
  unfold restrict, advance_past_svc, apply_effect, svc_set, set_reg, mks, rupd, regupd, a0r, ms_pc.
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom eff_ret eff_writes eff_zeros eff_unmaps eff_copies apply_copies].
  assert (E10 : @bv_eqb 5 10 0 = false) by reflexivity. rewrite E10.
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom].
  rewrite pc_plus4, apply_writes_delivered. reflexivity.
Qed.

#[using="Type"] Lemma adv_write_mem : forall ms v buf bs,
  ms_mem (advance_past_svc (apply_effect (svc_set ms) (mkEffect v (delivered_writes buf bs) []))) = write_to_mem (ms_mem ms) buf bs.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ms v buf bs. destruct ms as [rg fr pcv sv rv fc mem rom].
  unfold advance_past_svc, apply_effect, svc_set, set_reg.
  assert (E10 : @bv_eqb 5 10 0 = false) by reflexivity. rewrite E10. cbn. apply apply_writes_delivered.
Qed.

(* [comment removed for export] *)
#[using="mem0"] Lemma write_outside : forall E rgs i R o bs m x,
  nth_error rgs i = Some R -> 0 <= o -> o + Z.of_nat (length bs) <= rsz E R -> bv_unsigned (lden E (rg_base R)) + rsz E R <= two64 ->
  outside E rgs x -> write_to_mem m (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + o)) bs x = m x.
Proof. LiaFast.lf_pins (fun (mem0 : LiaFast.U) => LiaFast.u0).
  intros E rgs i R o bs m x Hi Ho Hn Hfl Hout. unfold outside in Hout. rewrite Forall_forall in Hout.
  pose proof (Hout R (nth_error_In _ _ Hi)) as HoR.
  pose proof (bv_unsigned_in_range _ (lden E (rg_base R))) as RA. unfold bv_modulus in RA. change (2 ^ Z.of_N 64) with two64 in RA.
  pose proof (bv_unsigned_in_range _ x) as RX. unfold bv_modulus in RX. change (2 ^ Z.of_N 64) with two64 in RX.
  rewrite write_to_mem_spec by (unfold rsz in *; lia).
  replace (Z.leb (bv_unsigned (lden E (rg_base R)) + o) (bv_unsigned x) && Z.ltb (bv_unsigned x) (bv_unsigned (lden E (rg_base R)) + o + Z.of_nat (length bs)))%bool with false; [reflexivity|].
  symmetry. apply andb_false_iff. unfold uE in HoR. destruct HoR as [H1|H1]; [left; apply Z.leb_gt; lia | right; apply Z.ltb_ge; unfold rsz in *; lia].
Qed.

#[using="Type"] Lemma den_read_post : forall model0 E L M ms model i R o lo hi bs (v : lin),
  DEN segs LIMIT model0 mem0 E L M ms model -> lwf (s_next L) v = true ->
  nth_error (s_rgs L) i = Some R -> (rg_kind R = RW \/ rg_kind R = RZ) -> 0 <= o ->
  (forall E', agree (s_next L) E E' -> o + Z.of_nat (length bs) <= rsz E' R) -> lo <= o -> o + Z.of_nat (length bs) <= hi ->
  range_avoids (Hof E M model) (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + o)) (length bs) ->
  DEN segs LIMIT model0 mem0 E (read_post L i lo hi v) M
      (advance_past_svc (apply_effect (svc_set ms) (mkEffect (lden E v) (delivered_writes (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + o)) bs) []))) model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros model0 E L M ms model i R o lo hi bs v Hd Hwv Hi Hk Ho Hsz Hlo Hhi Hav.
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  destruct (sden_0 _ _ _ _ Hsd) as (Hpc0 & _ & _ & _ & HG0 & _).
  set (H := Hof E M model) in *.
  set (buf := Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + o)) in *.
  assert (Hshape : shape (s_rgs (read_post L i lo hi v)) = shape (s_rgs L)).
  { unfold read_post. rewrite Hi. cbn [s_rgs]. exact (shape_upd (s_rgs L) i (RG (rg_base R) (rg_size R) RW (havoc_range (rg_cont R) lo hi)) R Hi eq_refl eq_refl). }
  assert (Hnext : s_next (read_post L i lo hi v) = s_next L) by (unfold read_post; rewrite Hi; reflexivity).
  assert (HR0 : rg_ok segs E (mrestrict H (ms_mem ms)) R) by exact (proj1 (Forall_nth' _ _) HG0 i R Hi).
  assert (Hfl : bv_unsigned (lden E (rg_base R)) + rsz E R <= two64) by exact (proj1 (proj2 HR0)).
  assert (Hout : forall x, outside E (s_rgs L) x -> write_to_mem (ms_mem ms) buf bs x = ms_mem ms x)
    by (intros x Hx; exact (write_outside E (s_rgs L) i R o bs (ms_mem ms) x Hi Ho (Hsz E (agree_refl _ _)) Hfl Hx)).
  constructor; rewrite ?Hnext; try assumption.
  - fold H. fold buf. rewrite (restrict_adv_write H ms (lden E v) buf bs (s_pc L) Hpc0). rewrite <- (write_to_mem_restrict H bs (ms_mem ms) buf Hav).
    assert (Hpc' : s_pc (read_post L i lo hi v) = s_pc L + 4) by (unfold read_post; rewrite Hi; reflexivity).
    pose proof (sden_read_post E L (restrict H ms) i R o lo hi bs v (lden E v) Hsd Hbw Hi Hk Ho Hsz Hlo Hhi
                  (fun E' Ha => lden_agree_wf _ E E' v Hwv Ha)) as X.
    cbn [restrict ms_fregs ms_fcsr ms_regs ms_resv ms_mem ms_rom] in X |- *. exact X.
  - eapply bases_wf_shape; [|exact Hshape|exact Hbw]. lia.
  - intros w Hw Hout'. rewrite adv_write_mem.
    assert (Ho' : outside E (s_rgs L) (Z_to_bv 64 w)) by exact (outside_agree_shape (s_next L) E E (s_rgs L) _ _ Hbw (agree_refl _ _) Hshape Hout').
    rewrite (Hout _ Ho'). exact (Hzr w Hw Ho').
  - exact (rl_ok_agree_shape (s_next L) E E model model (s_rgs L) _ Hbw (agree_refl _ _) Hshape eq_refl Hrl).
  - apply (frz_keep mem0 E E L (read_post L i lo hi v) M M ms _ model model Hwf (agree_refl _ _) eq_refl eq_refl); [| | exact Hfrz].
    + intros w _ Ho'. unfold outside in *. rewrite Forall_forall in *. intros R' HR'.
      destruct (In_nth_error _ _ HR') as (j & Hj). unfold read_post in Hj. rewrite Hi in Hj. cbn [s_rgs] in Hj.
      destruct (Nat.eq_dec j i) as [->|Hne].
      * rewrite (nth_upd_same _ _ _ _ Hi) in Hj. injection Hj as <-. exact (Ho' R (nth_error_In _ _ Hi)).
      * rewrite (nth_upd_other _ _ _ _ (not_eq_sym Hne)) in Hj. exact (Ho' R' (nth_error_In _ _ Hj)).
    + intros w _ Ho'. rewrite adv_write_mem. exact (Hout _ Ho').
  - apply (own_keep mem0 E E L (read_post L i lo hi v) M M ms _ model model Hwf (agree_refl _ _) eq_refl); [| | | exact Hown].
    + intros w Ho'. exact (outside_agree_shape (s_next L) E E (s_rgs L) _ _ Hbw (agree_refl _ _) Hshape Ho').
    + intros w Ho'. rewrite adv_write_mem. exact (Hout _ Ho').
    + intros x Hx. exact Hx.
Qed.

(* [comment removed for export] *)
Definition put_rg (S : sst) (i : nat) (o : Z) (bvs : list bval) : sst :=
  match nth_error (s_rgs S) i with
  | Some R => SST (s_pc S) (s_regs S) (upd_nth (s_rgs S) i (RG (rg_base R) (rg_size R) (rg_kind R) (put_bytes (rg_cont R) o bvs)))
                  (s_facts S) (s_next S) (s_resv S)
  | None => S
  end.
#[using="Type"] Theorem den_put : forall model0 E S M ms model i R o bvs,
  DEN segs LIMIT model0 mem0 E S M ms model ->
  nth_error (s_rgs S) i = Some R -> rg_kind R <> RO -> 0 <= o ->
  (forall E', agree (s_next S) E E' -> o + Z.of_nat (length bvs) <= rsz E' R) ->
  (forall E', agree (s_next S) E E' -> forall j x, nth_error bvs j = Some x ->
     rd1 segs (mrestrict (Hof E M model) (ms_mem ms)) (Z_to_bv 64 (uE E' (rg_base R) + o + Z.of_nat j)) = Some (bden E' x)) ->
  DEN segs LIMIT model0 mem0 E (put_rg S i o bvs) M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros model0 E S M ms model i R o bvs Hd Hi Hk Ho Hsz Hb.
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  set (R' := RG (rg_base R) (rg_size R) (rg_kind R) (put_bytes (rg_cont R) o bvs)).
  assert (Hshape : shape (s_rgs (put_rg S i o bvs)) = shape (s_rgs S)).
  { unfold put_rg. rewrite Hi. cbn [s_rgs]. exact (shape_upd (s_rgs S) i R' R Hi eq_refl eq_refl). }
  assert (Hnext : s_next (put_rg S i o bvs) = s_next S) by (unfold put_rg; rewrite Hi; reflexivity).
  constructor; rewrite ?Hnext; try assumption.
  - intros E'' Ha''. rewrite Hnext in Ha''. destruct (Hsd E'' Ha'') as (H1 & H2 & H3 & H4 & HG & HD & HF & H8).
    unfold put_rg. rewrite Hi. unfold sden0. cbn [s_pc s_regs s_rgs s_facts s_resv].
    split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [|split; [|split; [exact HF | exact H8]]].
    + apply Forall_forall. intros R0 HR0. destruct (In_nth_error _ _ HR0) as (j & Hj).
      destruct (Nat.eq_dec j i) as [->|Hne].
      * rewrite (nth_upd_same _ _ _ _ Hi) in Hj. injection Hj as <-.
        apply rg_ok_put_same; [exact (proj1 (Forall_nth' _ _) HG i R Hi) | exact Hk | exact Ho | exact (Hsz E'' Ha'') |].
        intros jj x Hx. exact (Hb E'' Ha'' jj x Hx).
      * rewrite (nth_upd_other _ _ _ _ (not_eq_sym Hne)) in Hj. rewrite Forall_forall in HG. exact (HG R0 (nth_error_In _ _ Hj)).
    + eapply rgs_disj_upd; [exact Hi | reflexivity | reflexivity | exact HD].
  - eapply bases_wf_shape; [|exact Hshape|exact Hbw]. lia.
  - intros w Hw Hout' Hnow Hnb. apply (Hzr w Hw); [|exact Hnow | exact Hnb].
    exact (outside_agree_shape (s_next S) E E (s_rgs S) _ _ Hbw (agree_refl _ _) Hshape Hout').
  - exact (rl_ok_agree_shape (s_next S) E E model model (s_rgs S) _ Hbw (agree_refl _ _) Hshape eq_refl Hrl).
  - apply (frz_keep mem0 E E S (put_rg S i o bvs) M M ms ms model model Hwf (agree_refl _ _) eq_refl eq_refl); [| | exact Hfrz].
    + intros w _ Ho'. unfold outside in *. rewrite Forall_forall in *. intros R0 HR0.
      destruct (In_nth_error _ _ HR0) as (j & Hj). unfold put_rg in Hj. rewrite Hi in Hj. cbn [s_rgs] in Hj.
      destruct (Nat.eq_dec j i) as [->|Hne].
      * rewrite (nth_upd_same _ _ _ _ Hi) in Hj. injection Hj as <-. exact (Ho' R (nth_error_In _ _ Hi)).
      * rewrite (nth_upd_other _ _ _ _ (not_eq_sym Hne)) in Hj. exact (Ho' R0 (nth_error_In _ _ Hj)).
    + intros w _ _. reflexivity.
  - apply (own_keep mem0 E E S (put_rg S i o bvs) M M ms ms model model Hwf (agree_refl _ _) eq_refl); [| | | exact Hown].
    + intros w Ho'. exact (outside_agree_shape (s_next S) E E (s_rgs S) _ _ Hbw (agree_refl _ _) Hshape Ho').
    + intros w _. reflexivity.
    + intros x Hx. exact Hx.
Qed.

#[using="mem0"] Lemma read_bytes_aux_some : forall mp k a, (forall j, (j < k)%nat -> mp (woff a j) <> None) -> read_bytes_aux mp a k <> None.
Proof. LiaFast.lf_pins (fun (mem0 : LiaFast.U) => LiaFast.u0).
  intros mp k. induction k as [|k IH]; intros a Hall; cbn [read_bytes_aux]; [discriminate|].
  destruct (mp a) as [b|] eqn:Ha; [|exfalso; apply (Hall O ltac:(lia)); rewrite woff_0; exact Ha].
  destruct (read_bytes_aux mp (a + 1)%bv k) as [r|] eqn:Hr; [discriminate|].
  exfalso. apply (IH (a + 1)%bv); [|exact Hr]. intros j Hj. rewrite woff_succ. apply Hall. lia.
Qed.

#[using="mem0"] Lemma length_file_read_le : forall data off count, (length (file_read data off count) <= word_to_nat count)%nat.
Proof. LiaFast.lf_pins (fun (mem0 : LiaFast.U) => LiaFast.u0).
  intros data off count. unfold file_read. rewrite length_firstn.
  unfold word_to_nat_bounded. destruct (bv_unsigned count <=? Z.of_nat (length (file_from data (bv_unsigned off))))%Z eqn:E.
  - lia.
  - apply Z.leb_gt in E. unfold word_to_nat. lia.
Qed.

#[using="Type"] Lemma ranges_avoid_delivered : forall H buf bs, range_avoids H buf (length bs) -> ranges_avoid H (write_accesses (delivered_writes buf bs)).
Proof. LiaFast.lf_pins LiaFast.u0. intros H buf [|b bs] Hav; cbn [delivered_writes write_accesses]; [apply ranges_avoid_nil|]. apply ranges_avoid_cons; [exact Hav | apply ranges_avoid_nil]. Qed.

#[using="mem0"] Lemma range_avoids_le : forall H a n n', (n' <= n)%nat -> range_avoids H a n -> range_avoids H a n'.
Proof. LiaFast.lf_pins (fun (mem0 : LiaFast.U) => LiaFast.u0). intros H a n n' Hle Hav k Hk. apply Hav. lia. Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem den_read_file : forall model0 E L M ms model T (fd cnt : Z) p off data (i : nat) R o (v : lin),
  DEN segs LIMIT model0 mem0 E L M ms model ->
  a7c L = Some 63 -> arg L 0 = Some fd -> arg L 2 = Some cnt -> 0 < cnt <= 65536 ->
  nth_error (s_rgs L) i = Some R -> (rg_kind R = RW \/ rg_kind R = RZ) -> 0 <= o ->
  lden E (rget (s_regs L) (rkey a1r)) = Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + o) ->
  (forall E', agree (s_next L) E E' -> o + cnt <= rsz E' R) ->
  fd_lookup (m_fds model0) (fd32 (Z_to_bv 64 fd)) = Some (FdFile p off) ->
  fs_lookup (m_fs model0) p = Some data ->
  lwf (s_next L) v = true -> lden E v = len_word (file_read data off (Z_to_bv 64 cnt)) ->
  access_okb (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + o)) cnt = true ->
  range_avoids (Hof E M model) (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + o)) (Z.to_nat cnt) ->
  (forall ms' m'', DEN segs LIMIT (with_fds (fd_insert (m_fds model0) (fd32 (Z_to_bv 64 fd)) (FdFile p (off + lden E v))) model0) mem0 E
                      (read_post L i o (o + cnt) v) M ms' m'' -> realizes_cfg segs cfg (mkCfg ms' m'') T) ->
  realizes_cfg segs cfg (mkCfg (svc_set ms) model) T.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros model0 E L M ms model T fd cnt p off data i R o v Hd H7 H0 H2 Hcnt Hi Hk Ho Hbuf Hsz Hfd Hlk Hwv Hv Hok Hav Hk'.
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  destruct (sden_0 _ _ _ _ Hsd) as (_ & _ & _ & _ & HG0 & _).
  set (H := Hof E M model) in *.
  set (ms1 := svc_set ms).
  set (x8 := ms_reg ms 17).
  set (buf := Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + o)) in *.
  assert (Hx8 : x8 = Z_to_bv 64 63) by exact (a7_const segs E L (restrict H ms) ms 63 Hsd eq_refl H7).
  assert (Hg0 : ms_gpr ms1 0 = Z_to_bv 64 fd) by exact (gpr_const segs E L (restrict H ms) ms 0 fd Hsd eq_refl ltac:(lia) H0).
  assert (Hg1 : ms_gpr ms1 1 = buf) by (rewrite <- Hbuf; exact (gpr_lin1 segs E L (restrict H ms) ms Hsd eq_refl)).
  assert (Hg2 : ms_gpr ms1 2 = Z_to_bv 64 cnt) by exact (gpr_const segs E L (restrict H ms) ms 2 cnt Hsd eq_refl ltac:(lia) H2).
  set (i0 := sys_input segs ms1 x8).
  assert (Hno : bv_unsigned (in_sysno i0) = 63%Z) by (unfold i0; cbn [in_sysno sys_input]; rewrite Hx8; reflexivity).
  assert (A0 : in_arg i0 0 = Z_to_bv 64 fd) by (unfold i0, ms1; rewrite in_arg_svc by lia; exact Hg0).
  assert (A1 : in_arg i0 1 = buf) by (unfold i0, ms1; rewrite in_arg_svc by lia; exact Hg1).
  assert (A2 : in_arg i0 2 = Z_to_bv 64 cnt) by (unfold i0, ms1; rewrite in_arg_svc by lia; exact Hg2).
  assert (Hfm : m_fds model = m_fds model0) by (destruct Hvmo as (H1' & _); unfold m_fds; rewrite H1'; reflexivity).
  assert (Hfsm : m_fs model = m_fs model0) by (destruct Hvmo as (_ & _ & H3' & _); unfold m_fs; rewrite H3'; reflexivity).
  assert (Hcl : rw_count_clamp (Z_to_bv 64 cnt) = cnt).
  { unfold rw_count_clamp. rewrite u_small64 by (unfold two64; lia). unfold MAX_RW_COUNT. lia. }
  set (bs := file_read data off (Z_to_bv 64 cnt)) in *.
  assert (Hlb : (length bs <= Z.to_nat cnt)%nat).
  { pose proof (length_file_read_le data off (Z_to_bv 64 cnt)) as X. fold bs in X. unfold word_to_nat in X.
    rewrite u_small64 in X by (unfold two64; lia). exact X. }
  set (fent := FdFile p (off + len_word bs)).
  set (m' := with_fds (fd_insert (m_fds model0) (fd32 (Z_to_bv 64 fd)) fent) model).
  set (eff := mkEffect (len_word bs) (delivered_writes buf bs) []).
  assert (HR0 : rg_ok segs E (mrestrict H (ms_mem ms)) R) by exact (proj1 (Forall_nth' _ _) HG0 i R Hi).
  assert (Hwr : read_bytes_map (in_wmem i0) buf (len_word bs) <> None).
  { rewrite read_bytes_map_eq. unfold len_word, word_to_nat. rewrite u_small64 by (unfold two64; lia). rewrite Nat2Z.id.
    apply read_bytes_aux_some. intros j Hj. unfold i0. cbn [in_wmem sys_input]. unfold ms_writable_byte.
    cbn [svc_set ms_mem]. fold (wview segs (ms_mem ms)).
    destruct HR0 as (_ & Hfl & Hall & _).
    pose proof (Hsz E (agree_refl _ _)) as Hsz0.
    assert (Hj' : 0 <= o + Z.of_nat j < rsz E R) by lia.
    specialize (Hall (o + Z.of_nat j) Hj').
    assert (Hwo : woff buf j = Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + (o + Z.of_nat j))).
    { unfold woff, buf. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite Zplus_mod_idemp_l. f_equal. lia. }
    rewrite Hwo. rewrite <- (wview_mrestrict_eq segs H (ms_mem ms)).
    - destruct Hk as [Hk|Hk]; rewrite Hk in Hall; [exact (proj2 Hall) | exact (proj2 (proj1 Hall))].
    - rewrite <- Hwo. exact (Hav j ltac:(lia)). }
  assert (Hok' : access_okb buf (bv_unsigned (Z_to_bv 64 cnt)) = true) by (rewrite u_small64 by (unfold two64; lia); exact Hok).
  assert (Hspr : forall eff1 m1 evs1, syscall_spec i0 model (Ok eff1 m1 evs1) <-> eff1 = eff /\ m1 = m' /\ evs1 = []).
  { intros eff1 m1 evs1. rewrite (syscall_spec_63 i0 model _ Hno). rewrite A0, A1, A2.
    unfold read_spec. rewrite bind_input, bind_get_model. rewrite Hfm, Hfd, Hok'. cbn [negb]. rewrite Hfsm, Hlk. rewrite Hcl. fold bs.
    destruct (read_bytes_map (in_wmem i0) buf (len_word bs)) as [w|] eqn:Ew; [|exfalso; apply Hwr; reflexivity].
    unfold set_fds, modify, bind, pure. split.
    - intros X. sys_destruct. all: rewrite ?app_nil_l; repeat split; reflexivity.
    - intros (-> & -> & ->). exists tt, m', [], []. repeat split; reflexivity. }
  assert (Hnur : ~ syscall_spec i0 model Unmodeled).
  { intros Hs. rewrite (syscall_spec_63 i0 model _ Hno) in Hs. rewrite A0, A1, A2 in Hs.
    unfold read_spec in Hs. rewrite bind_input, bind_get_model in Hs. rewrite Hfm, Hfd, Hok' in Hs. cbn [negb] in Hs.
    rewrite Hfsm, Hlk, Hcl in Hs. fold bs in Hs.
    destruct (read_bytes_map (in_wmem i0) buf (len_word bs)) as [w|] eqn:Ew; [|apply Hwr; reflexivity].
    unfold set_fds, modify, bind, pure in Hs. sys_destruct. }
  assert (Havb : range_avoids H buf (length bs)) by exact (range_avoids_le H buf _ _ Hlb Hav).
  assert (Hcont : forall m'', MInv (AM model0 E M) m'' -> same_but_materialized m' m'' ->
     realizes_cfg segs cfg (mkCfg (advance_past_svc (apply_effect ms1 eff)) m'') T).
  { intros m'' Hinv'' Hsb''. apply Hk'.
    pose proof (den_read_post model0 E L M ms model i R o o (o + cnt) bs v Hd Hwv Hi Hk Ho
                  (fun E' Ha => Z.le_trans (o + Z.of_nat (length bs)) (o + cnt) (rsz E' R) ltac:(lia) (Hsz E' Ha)) ltac:(lia) ltac:(lia) Havb) as HD1.
    rewrite Hv in HD1. fold buf in HD1. fold eff in HD1.
    pose proof (den_fds _ E _ M _ model (fd_insert (m_fds model0) (fd32 (Z_to_bv 64 fd)) (FdFile p (off + lden E v))) HD1) as HD2.
    assert (Hm' : with_fds (fd_insert (m_fds model0) (fd32 (Z_to_bv 64 fd)) (FdFile p (off + lden E v))) model = m').
    { unfold m', fent. rewrite Hv. reflexivity. }
    rewrite Hm' in HD2.
    exact (den_sbm segs LIMIT _ mem0 E _ M _ m' m'' HD2 Hsb'' Hinv''). }
  eapply rzc_conseq.
  - apply (rzc_sys_acc H (AM model0 E M) ms1 model x8 unit (fun _ => eff) (fun _ => m') (fun _ => []) (fun _ => T) tt (A_wf_app _ _ Hawf (A_wf_blobA _)) Hh (svc_set_pending ms)).
    + intros []. apply Hspr. auto.
    + intros eff1 m1 evs1 Hs. apply Hspr in Hs as (-> & -> & ->). exists tt. auto.
    + exact Hnur.
    + intros eff1. apply not_spurious_uninjected. fold i0. rewrite Hno. reflexivity.
    + intros _. unfold m'. rewrite with_fds_halted. exact Hh.
    + intros _. unfold m'. rewrite with_fds_lazy. apply lazy_cover_mkH_app. intros x Hx'. exact Hx'.
    + intros _. exact (MInv_with_fds _ _ model Hminv).
    + intros _. unfold eff, syscall_effect_accesses. cbn [eff_copyins eff_writes]. rewrite app_nil_l.
      exact (ranges_avoid_delivered H buf bs Havb).
    + intros _ m'' Hinv'' Hsb''. exact (Hcont m'' Hinv'' Hsb'').
  - apply t_alt_const_nil; [exact tt|].
    exact (realizes_cfg_nonempty segs cfg _ _ (Hcont m' (MInv_with_fds _ _ model Hminv) (same_but_materialized_refl _))).
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem den_read_file2 : forall model0 E L M ms model T (fd cnt : Z) p off data (i : nat) R o (v : lin),
  DEN segs LIMIT model0 mem0 E L M ms model ->
  a7c L = Some 63 -> arg L 0 = Some fd -> lden E (argl L 2) = Z_to_bv 64 cnt -> 0 < cnt <= 65536 -> forall hi, cnt <= hi ->
  nth_error (s_rgs L) i = Some R -> (rg_kind R = RW \/ rg_kind R = RZ) -> 0 <= o ->
  lden E (rget (s_regs L) (rkey a1r)) = Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + o) ->
  (forall E', agree (s_next L) E E' -> o + hi <= rsz E' R) ->
  fd_lookup (m_fds model0) (fd32 (Z_to_bv 64 fd)) = Some (FdFile p off) ->
  fs_lookup (m_fs model0) p = Some data ->
  lwf (s_next L) v = true -> lden E v = len_word (file_read data off (Z_to_bv 64 cnt)) ->
  access_okb (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + o)) cnt = true ->
  range_avoids (Hof E M model) (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + o)) (Z.to_nat cnt) ->
  (forall ms' m'', DEN segs LIMIT (with_fds (fd_insert (m_fds model0) (fd32 (Z_to_bv 64 fd)) (FdFile p (off + lden E v))) model0) mem0 E
                      (read_post L i o (o + hi) v) M ms' m'' ->
     ms_mem ms' = write_to_mem (ms_mem ms) (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + o)) (file_read data off (Z_to_bv 64 cnt)) ->
     realizes_cfg segs cfg (mkCfg ms' m'') T) ->
  realizes_cfg segs cfg (mkCfg (svc_set ms) model) T.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros model0 E L M ms model T fd cnt p off data i R o v Hd H7 H0 H2 Hcnt hi Hhi Hi Hk Ho Hbuf Hsz Hfd Hlk Hwv Hv Hok Hav Hk'.
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  destruct (sden_0 _ _ _ _ Hsd) as (_ & _ & _ & _ & HG0 & _).
  set (H := Hof E M model) in *.
  set (ms1 := svc_set ms).
  set (x8 := ms_reg ms 17).
  set (buf := Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + o)) in *.
  assert (Hx8 : x8 = Z_to_bv 64 63) by exact (a7_const segs E L (restrict H ms) ms 63 Hsd eq_refl H7).
  assert (Hg0 : ms_gpr ms1 0 = Z_to_bv 64 fd) by exact (gpr_const segs E L (restrict H ms) ms 0 fd Hsd eq_refl ltac:(lia) H0).
  assert (Hg1 : ms_gpr ms1 1 = buf) by (rewrite <- Hbuf; exact (gpr_lin1 segs E L (restrict H ms) ms Hsd eq_refl)).
  assert (Hg2 : ms_gpr ms1 2 = Z_to_bv 64 cnt) by (rewrite <- H2; exact (gpr_lin_k E L (restrict H ms) ms 2 Hsd eq_refl ltac:(lia))).
  set (i0 := sys_input segs ms1 x8).
  assert (Hno : bv_unsigned (in_sysno i0) = 63%Z) by (unfold i0; cbn [in_sysno sys_input]; rewrite Hx8; reflexivity).
  assert (A0 : in_arg i0 0 = Z_to_bv 64 fd) by (unfold i0, ms1; rewrite in_arg_svc by lia; exact Hg0).
  assert (A1 : in_arg i0 1 = buf) by (unfold i0, ms1; rewrite in_arg_svc by lia; exact Hg1).
  assert (A2 : in_arg i0 2 = Z_to_bv 64 cnt) by (unfold i0, ms1; rewrite in_arg_svc by lia; exact Hg2).
  assert (Hfm : m_fds model = m_fds model0) by (destruct Hvmo as (H1' & _); unfold m_fds; rewrite H1'; reflexivity).
  assert (Hfsm : m_fs model = m_fs model0) by (destruct Hvmo as (_ & _ & H3' & _); unfold m_fs; rewrite H3'; reflexivity).
  assert (Hcl : rw_count_clamp (Z_to_bv 64 cnt) = cnt).
  { unfold rw_count_clamp. rewrite u_small64 by (unfold two64; lia). unfold MAX_RW_COUNT. lia. }
  set (bs := file_read data off (Z_to_bv 64 cnt)) in *.
  assert (Hlb : (length bs <= Z.to_nat cnt)%nat).
  { pose proof (length_file_read_le data off (Z_to_bv 64 cnt)) as X. fold bs in X. unfold word_to_nat in X.
    rewrite u_small64 in X by (unfold two64; lia). exact X. }
  set (fent := FdFile p (off + len_word bs)).
  set (m' := with_fds (fd_insert (m_fds model0) (fd32 (Z_to_bv 64 fd)) fent) model).
  set (eff := mkEffect (len_word bs) (delivered_writes buf bs) []).
  assert (HR0 : rg_ok segs E (mrestrict H (ms_mem ms)) R) by exact (proj1 (Forall_nth' _ _) HG0 i R Hi).
  assert (Hwr : read_bytes_map (in_wmem i0) buf (len_word bs) <> None).
  { rewrite read_bytes_map_eq. unfold len_word, word_to_nat. rewrite u_small64 by (unfold two64; lia). rewrite Nat2Z.id.
    apply read_bytes_aux_some. intros j Hj. unfold i0. cbn [in_wmem sys_input]. unfold ms_writable_byte.
    cbn [svc_set ms_mem]. fold (wview segs (ms_mem ms)).
    destruct HR0 as (_ & Hfl & Hall & _).
    pose proof (Hsz E (agree_refl _ _)) as Hsz0.
    assert (Hj' : 0 <= o + Z.of_nat j < rsz E R) by lia.
    specialize (Hall (o + Z.of_nat j) Hj').
    assert (Hwo : woff buf j = Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + (o + Z.of_nat j))).
    { unfold woff, buf. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite Zplus_mod_idemp_l. f_equal. lia. }
    rewrite Hwo. rewrite <- (wview_mrestrict_eq segs H (ms_mem ms)).
    - destruct Hk as [Hk|Hk]; rewrite Hk in Hall; [exact (proj2 Hall) | exact (proj2 (proj1 Hall))].
    - rewrite <- Hwo. exact (Hav j ltac:(lia)). }
  assert (Hok' : access_okb buf (bv_unsigned (Z_to_bv 64 cnt)) = true) by (rewrite u_small64 by (unfold two64; lia); exact Hok).
  assert (Hspr : forall eff1 m1 evs1, syscall_spec i0 model (Ok eff1 m1 evs1) <-> eff1 = eff /\ m1 = m' /\ evs1 = []).
  { intros eff1 m1 evs1. rewrite (syscall_spec_63 i0 model _ Hno). rewrite A0, A1, A2.
    unfold read_spec. rewrite bind_input, bind_get_model. rewrite Hfm, Hfd, Hok'. cbn [negb]. rewrite Hfsm, Hlk. rewrite Hcl. fold bs.
    destruct (read_bytes_map (in_wmem i0) buf (len_word bs)) as [w|] eqn:Ew; [|exfalso; apply Hwr; reflexivity].
    unfold set_fds, modify, bind, pure. split.
    - intros X. sys_destruct. all: rewrite ?app_nil_l; repeat split; reflexivity.
    - intros (-> & -> & ->). exists tt, m', [], []. repeat split; reflexivity. }
  assert (Hnur : ~ syscall_spec i0 model Unmodeled).
  { intros Hs. rewrite (syscall_spec_63 i0 model _ Hno) in Hs. rewrite A0, A1, A2 in Hs.
    unfold read_spec in Hs. rewrite bind_input, bind_get_model in Hs. rewrite Hfm, Hfd, Hok' in Hs. cbn [negb] in Hs.
    rewrite Hfsm, Hlk, Hcl in Hs. fold bs in Hs.
    destruct (read_bytes_map (in_wmem i0) buf (len_word bs)) as [w|] eqn:Ew; [|apply Hwr; reflexivity].
    unfold set_fds, modify, bind, pure in Hs. sys_destruct. }
  assert (Havb : range_avoids H buf (length bs)) by exact (range_avoids_le H buf _ _ Hlb Hav).
  assert (Hcont : forall m'', MInv (AM model0 E M) m'' -> same_but_materialized m' m'' ->
     realizes_cfg segs cfg (mkCfg (advance_past_svc (apply_effect ms1 eff)) m'') T).
  { intros m'' Hinv'' Hsb''. apply Hk'; [|exact (adv_write_mem ms _ buf bs)].
    pose proof (den_read_post model0 E L M ms model i R o o (o + hi) bs v Hd Hwv Hi Hk Ho
                  (fun E' Ha => Z.le_trans (o + Z.of_nat (length bs)) (o + hi) (rsz E' R) ltac:(lia) (Hsz E' Ha)) ltac:(lia) ltac:(lia) Havb) as HD1.
    rewrite Hv in HD1. fold buf in HD1. fold eff in HD1.
    pose proof (den_fds _ E _ M _ model (fd_insert (m_fds model0) (fd32 (Z_to_bv 64 fd)) (FdFile p (off + lden E v))) HD1) as HD2.
    assert (Hm' : with_fds (fd_insert (m_fds model0) (fd32 (Z_to_bv 64 fd)) (FdFile p (off + lden E v))) model = m').
    { unfold m', fent. rewrite Hv. reflexivity. }
    rewrite Hm' in HD2.
    exact (den_sbm segs LIMIT _ mem0 E _ M _ m' m'' HD2 Hsb'' Hinv''). }
  eapply rzc_conseq.
  - apply (rzc_sys_acc H (AM model0 E M) ms1 model x8 unit (fun _ => eff) (fun _ => m') (fun _ => []) (fun _ => T) tt (A_wf_app _ _ Hawf (A_wf_blobA _)) Hh (svc_set_pending ms)).
    + intros []. apply Hspr. auto.
    + intros eff1 m1 evs1 Hs. apply Hspr in Hs as (-> & -> & ->). exists tt. auto.
    + exact Hnur.
    + intros eff1. apply not_spurious_uninjected. fold i0. rewrite Hno. reflexivity.
    + intros _. unfold m'. rewrite with_fds_halted. exact Hh.
    + intros _. unfold m'. rewrite with_fds_lazy. apply lazy_cover_mkH_app. intros x Hx'. exact Hx'.
    + intros _. exact (MInv_with_fds _ _ model Hminv).
    + intros _. unfold eff, syscall_effect_accesses. cbn [eff_copyins eff_writes]. rewrite app_nil_l.
      exact (ranges_avoid_delivered H buf bs Havb).
    + intros _ m'' Hinv'' Hsb''. exact (Hcont m'' Hinv'' Hsb'').
  - apply t_alt_const_nil; [exact tt|].
    exact (realizes_cfg_nonempty segs cfg _ _ (Hcont m' (MInv_with_fds _ _ model Hminv) (same_but_materialized_refl _))).
Qed.

End Sys.
End FxChSys.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Inductive nodek : Type :=
| NTid
| NNull (nZ : Z) (k : gkind) (vis piece na : bool)
| NNorep (b k : Z) (kd : gkind) (na : bool) (idxs : list (nat * Z)) (zr : bool) (wlo whi : Z)
| NNorepB (b k : Z) (kd : gkind) (pb ps : lin) (ub : Z) (zr : bool)
| NFixKeep (n : Z) (na : bool) (j : nat) (kd' : gkind)
| NFixNew (n : Z) (j : nat)
| NUnmap (j : nat)
| NBrkQ
| NMprot (n : Z) (j : nat).

Inductive templop : Type :=
| TDrop (bases : list lin)
| TDropA0
| TAllowA0 (n : Z)
| TForget (a : lin)
| TSepG (i j : nat)
| TSepW (i j : nat)     (* [comment removed for export] *)
| TSepR (j : nat) (lo hi : Z)   (* [comment removed for export] *)
| TSepS (j : nat).   (* [comment removed for export] *)

Inductive chain : Type :=
| CEnd
| CSeg (depth : nat) (p : plan) (k : chain)
| CNode (nk : nodek) (k : chain)
| CGrow (k o s : Z) (kok kfail : chain)
| COp (op : templop) (k : chain).

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint pos_below_go (n : nat) (q : positive) (acc : list positive) : list positive :=
  match n with O => acc | Datatypes.S n' => pos_below_go n' (Pos.pred q) (q :: acc) end.
Definition pos_below (p : positive) : list positive := pos_below_go (Pos.to_nat p - 1) (Pos.pred p) [].

Lemma pos_below_go_In : forall n q acc x, (Pos.to_nat q = n \/ n = O) ->
  In x (pos_below_go n q acc) <-> In x acc \/ (Pos.to_nat x <= n)%nat.
Proof.
  induction n as [|n IH]; intros q acc x Hq; cbn [pos_below_go].
  - pose proof (Pos2Nat.is_pos x) as Hx. split; [intros H; left; exact H | intros [H|H]; [exact H | lia]].
  - destruct Hq as [Hq|Hq]; [|discriminate].
    rewrite IH.
    + cbn [In]. split.
      * intros [[<-|H]|H]; [right; lia | left; exact H | right; lia].
      * intros [H|H]; [left; right; exact H|]. destruct (Nat.eq_dec (Pos.to_nat x) (Datatypes.S n)) as [He|Hne].
        -- left. left. apply Pos2Nat.inj. lia.
        -- right. lia.
    + destruct n as [|n]; [right; reflexivity|]. left.
      rewrite Pos2Nat.inj_pred; [lia|]. apply Pos2Nat.inj_lt. cbn. lia.
Qed.

Lemma pos_below_In : forall p x, (x < p)%positive -> In x (pos_below p).
Proof.
  intros p x H. unfold pos_below. apply pos_below_go_In.
  - destruct (Pos.eq_dec p 1) as [->|Hp]; [right; reflexivity|]. left.
    rewrite Pos2Nat.inj_pred; [lia|]. pose proof (Pos2Nat.is_pos p). apply Pos2Nat.inj_lt. cbn.
    assert (Pos.to_nat p <> 1)%nat by (intros He; apply Hp; apply Pos2Nat.inj; exact He). lia.
  - right. apply Pos2Nat.inj_lt in H. lia.
Qed.
(* [comment removed for export] *)
Definition bases_below (n : positive) (rgs : list region) : bool :=
  forallb (fun R => forallb (fun '(y, _) => Pos.ltb y n) (l_t (rg_base R) ++ l_t (rg_size R))) rgs.
Lemma pos_below_In_iff : forall p x, In x (pos_below p) <-> (x < p)%positive.
Proof.
  intros p x. split; [|apply pos_below_In]. unfold pos_below. intros H.
  assert (Hq : Pos.to_nat (Pos.pred p) = (Pos.to_nat p - 1)%nat \/ (Pos.to_nat p - 1)%nat = O).
  { destruct (Pos.eq_dec p 1) as [->|Hp]; [right; reflexivity|]. left.
    rewrite Pos2Nat.inj_pred; [lia|]. pose proof (Pos2Nat.is_pos p). apply Pos2Nat.inj_lt. cbn.
    assert (Pos.to_nat p <> 1)%nat by (intros He; apply Hp; apply Pos2Nat.inj; exact He). lia. }
  apply (pos_below_go_In _ _ [] x Hq) in H. destruct H as [H|H]; [destruct H|]. apply Pos2Nat.inj_lt. pose proof (Pos2Nat.is_pos x). lia.
Qed.
Lemma bases_below_eq : forall n rgs, bases_below n rgs = bases_ins (pos_below n) rgs.
Proof.
  intros n rgs. unfold bases_below, bases_ins. induction rgs as [|R rs IH]; [reflexivity|]. cbn [forallb]. rewrite IH. f_equal.
  induction (l_t (rg_base R) ++ l_t (rg_size R)) as [|[y k] t IHt]; [reflexivity|]. cbn [forallb]. rewrite IHt. f_equal.
  apply eq_true_iff_eq. rewrite Pos.ltb_lt, existsb_exists. split.
  - intros H. exists y. split; [apply pos_below_In; exact H | apply Pos.eqb_refl].
  - intros (x & Hin & He). apply Pos.eqb_eq in He. subst x. apply pos_below_In_iff. exact Hin.
Qed.
(* [comment removed for export] *)
Lemma fixed_below_eq : forall n0 s, fixed_below s n0 = params_fixed s (pos_below n0).
Proof. intros n0 s. symmetry. exact (params_fixed_eq n0 (pos_below n0) (pos_below_In_iff n0) s). Qed.
Lemma checkB_pos_below : forall t img n0 depth p s, checkB t img n0 depth p s = check t img (pos_below n0) depth p s.
Proof. intros t img n0 depth p s. exact (checkB_eq t img n0 (pos_below n0) (pos_below_In_iff n0) depth p s). Qed.



Definition drop_f (bases : list lin) (R : region) : bool := existsb (lin_eqb (rg_base R)) bases.
(* [comment removed for export] *)
Definition a0_bases (S : sst) : list lin :=
  let a := rget (s_regs S) (rkey a0r) in a :: match srl_lin (s_facts S) 3 a with Some pb => [laddc pb SH_OFF] | None => [] end.
(* [comment removed for export] *)
Definition drop_ok (fs : list fact) (zr : list (Z * Z)) (R : region) : bool :=
  (match rg_kind R with RZ => tall is_bk0 (rg_cont R) | _ => false end || sep_noshadow_b fs R ||
   forallb (fun p => (Z.leb (snd (irange fs (rg_base R)) + snd (irange fs (rg_size R))) (fst p) || Z.leb (snd p) (fst (irange fs (rg_base R))))%bool) zr)%bool.

(* [comment removed for export] *)
Definition sepg_post (S : sst) (M : smodel) (i j : nat) : option sst :=
  match nth_error (sm_maps M) i, nth_error (sm_maps M) j with
  | Some gi, Some gj =>
      if (is_mark gi || is_mark gj)%bool then None else       (* [comment removed for export] *)
      match is_const (fst (fst gj)) with
      | Some gb => if (negb (Nat.eqb i j) && Z.ltb (snd (irange (s_facts S) (fst (fst gi)))) (gb + gsz_lo (s_facts S) gj) &&
                       Z.leb (gsz_lo (s_facts S) gi) gb && lwf (s_next S) (fst (fst gi)))%bool
                   then Some (add_fact S (FRange (fst (fst gi)) 0 (gb - gsz_lo (s_facts S) gi))) else None
      | None => None
      end
  | _, _ => None
  end.

(* [comment removed for export] *)
Definition sepw_fact (fs : list fact) (gi gj : lin * lin * gkind) : fact :=
  FRange (lsub (fst (fst gi)) (laddc (fst (fst gj)) (gsz_lo fs gj))) 0 (two64 - gsz_lo fs gj - gsz_lo fs gi).
Definition sepw_post (S : sst) (M : smodel) (i j : nat) : option sst :=
  match nth_error (sm_maps M) i, nth_error (sm_maps M) j with
  | Some gi, Some gj =>
      if (is_mark gi || is_mark gj)%bool then None else       (* [comment removed for export] *)
      if (negb (Nat.eqb i j) && lwf (s_next S) (fst (fst gi)) && lwf (s_next S) (fst (fst gj)))%bool
      then Some (add_fact S (sepw_fact (s_facts S) gi gj)) else None
  | _, _ => None
  end.

(* [comment removed for export] *)
Fixpoint res_chain (rs : list (word * word)) (cur hi : Z) (fuel : nat) : bool :=
  match fuel with
  | O => false
  | Datatypes.S f =>
      if Z.leb hi cur then true else
      match List.find (fun p => Z.eqb (bv_unsigned (fst p)) cur) rs with
      | Some p => (Z.ltb 0 (bv_unsigned (snd p)) && res_chain rs (cur + bv_unsigned (snd p)) hi f)%bool
      | None => false
      end
  end.
Lemma res_chain_cov : forall rs f cur hi, res_chain rs cur hi f = true -> forall x, cur <= x < hi ->
  exists p, In p rs /\ bv_unsigned (fst p) <= x < bv_unsigned (fst p) + bv_unsigned (snd p).
Proof.
  intros rs f. induction f as [|f IH]; intros cur hi H x Hx; cbn [res_chain] in H; [discriminate|].
  destruct (Z.leb_spec hi cur) as [Hle|Hlt]; [lia|].
  destruct (List.find (fun p => Z.eqb (bv_unsigned (fst p)) cur) rs) as [p|] eqn:Hf; [|discriminate].
  apply andb_prop in H as [Hpos H]. apply Z.ltb_lt in Hpos.
  apply find_some in Hf as [Hin Heq]. apply Z.eqb_eq in Heq.
  destruct (Z_lt_le_dec x (cur + bv_unsigned (snd p))) as [Hx1|Hx1].
  - exists p. split; [exact Hin|]. lia.
  - exact (IH _ _ H x ltac:(lia)).
Qed.

(* [comment removed for export] *)
Definition own_nilb (M : smodel) : bool := match sm_own M with [] => true | _ => false end.
Lemma own_nilb_eq : forall M, own_nilb M = true -> sm_own M = [].
Proof. intros M H. unfold own_nilb in H. destruct (sm_own M); [reflexivity | discriminate]. Qed.

(* [comment removed for export] *)
Section Check.
Variable segs : list Segment.
Variable LIMIT : Z.
Variable t : tree xi.
Variable img : tree Z.

Definition node_post (nk : nodek) (L : sst) (M : smodel) : option (sst * smodel) :=
  if (own_nilb M &&& nomark (sm_maps M)) then      (* [comment removed for export] *)
  match nk with
  | NTid => match sm_tid M with
            | None => match a7c L with
                      | Some c => if Z.eqb c 96 then Some (post_fresh L TID_FACTS, sm_with_tid M (lvar (s_next L))) else None
                      | None => None
                      end
            | Some _ => None
            end
  | NNull nZ k vis piece na =>
      if null_ok (segments_reserved segs) LIMIT L M nZ k vis piece na
      then Some (null_post L nZ vis piece, null_M M (s_next L) nZ k vis piece) else None
  | NNorep b k kd na idxs zr wlo whi =>
      match pieces_of (s_facts L) (s_rgs L) idxs with
      | Some pcs => if norep_ok (segments_reserved segs) LIMIT L M b k kd na idxs zr wlo whi
                    then Some (norep_post L b pcs, norep_M M b k kd pcs zr) else None
      | None => None
      end
  | NNorepB b k kd pb ps ub zr =>
      if norepb_ok (segments_reserved segs) LIMIT L M b k kd pb ps ub zr
      then Some (norep_post L b [(pb, ps, ub)], norep_M M b k kd [(pb, ps, ub)] zr) else None
  | NFixKeep n na j kd' =>
      if fixkeep_ok LIMIT (segments_reserved segs) L M n na j kd' then Some (fix_post L (rget (s_regs L) (rkey a0r)), fix_M M j kd') else None
  | NFixNew n j =>
      if fixnew_ok LIMIT (segments_reserved segs) L M n j
      then Some (add_post (fix_post L (rget (s_regs L) (rkey a0r))) (rget (s_regs L) (rkey a0r)) n (Some (fixnew_piece L)),
                 add_M (fix_M M j GE) n (Some (fixnew_piece L))) else None
  | NUnmap j => if munmap_ok (segments_reserved segs) LIMIT L M j then Some (munmap_post L, munmap_M M j) else None
  | NBrkQ => if brkq_ok L M then Some (ret_post L (sm_brk M), M) else None
  | NMprot n j => if mprot_ok (segments_reserved segs) LIMIT L M n j
                  then Some (add_post (mprot_post L) (rget (s_regs L) (rkey a0r)) n None, add_M (fix_M M j GE) n None) else None
  end
  else None.

(* [comment removed for export] *)
Definition sepr_post (S : sst) (M : smodel) (j : nat) (lo hi : Z) : option sst :=
  match nth_error (sm_maps M) j with
  | Some gj =>
      if is_mark gj then None else                             (* [comment removed for export] *)
      if (lwf (s_next S) (fst (fst gj)) && Z.ltb lo hi && Z.ltb lo (fst (irange (s_facts S) (fst (fst gj))) + gsz_lo (s_facts S) gj) &&
          res_chain (segments_reserved segs) lo hi (Datatypes.S (List.length (segments_reserved segs))))%bool
      then Some (add_fact S (FRange (fst (fst gj)) hi M64)) else None
  | None => None
  end.

(* [comment removed for export] *)
Definition seps_fact (fs : list fact) (M : smodel) (gj : lin * lin * gkind) : fact :=
  FRange (lsub (laddc (sm_sp M) (- (stack_max_size + gsz_lo fs gj))) (fst (fst gj))) 0 (sp_window_hi - stack_max_size - gsz_lo fs gj).

Definition seps_post (S : sst) (M : smodel) (j : nat) : option sst :=
  match nth_error (sm_maps M) j with
  | Some gj => if lwf (s_next S) (fst (fst gj)) then Some (add_fact S (seps_fact (s_facts S) M gj)) else None
  | None => None
  end.

Definition op_post (op : templop) (S : sst) (M : smodel) : option (sst * smodel) :=
  match op with
  | TDrop bases => if (own_nilb M && forallb (fun R => negb (drop_f bases R) || drop_ok (s_facts S) (sm_zr M) R) (s_rgs S))%bool
                   then Some (drop_post S (drop_f bases), M) else None
  | TDropA0 => if (own_nilb M && forallb (fun R => negb (drop_f (a0_bases S) R) || drop_ok (s_facts S) (sm_zr M) R) (s_rgs S))%bool
               then Some (drop_post S (drop_f (a0_bases S)), M) else None
  | TAllowA0 n => let b := rget (s_regs S) (rkey a0r) in
                  if (lwf (s_next S) b && Z.leb 0 n && Z.leb (eager_sum (s_facts S) (sm_maps M) + allow_bound ((b, n) :: sm_allow M)) LIMIT)%bool
                  then Some (S, allow_M M b n) else None
  | TForget a => match forget_post S a with
                 | Some S' => if sm_wf (s_next S') M then Some (S', M) else None
                 | None => None
                 end
  | TSepG i j => match sepg_post S M i j with Some S' => Some (S', M) | None => None end
  | TSepW i j => match sepw_post S M i j with Some S' => Some (S', M) | None => None end
  | TSepR j lo hi => match sepr_post S M j lo hi with Some S' => Some (S', M) | None => None end
  | TSepS j => match seps_post S M j with Some S' => Some (S', M) | None => None end
  end.

Fixpoint check_chain (ch : chain) (S : sst) (M : smodel) : option (list (sst * smodel)) :=
  match ch with
  | CEnd => Some [(S, M)]
  | CSeg depth p k =>
      if bases_below (s_next S) (s_rgs S) then
        match checkB t img (s_next S) depth p S with
        | Some [L] => if (sm_wf (s_next L) M && Pos.leb (s_next S) (s_next L))%bool then check_chain k L M else None
        | _ => None
        end
      else None
  | CNode nk k =>
      match tlookup t (s_pc S) with
      | XEcall => match node_post nk S M with Some (S', M') => if Pos.leb (s_next S) (s_next S') then check_chain k S' M' else None | None => None end
      | _ => None
      end
  | CGrow k o s kok kfail =>
      match tlookup t (s_pc S) with
      | XEcall =>
          if own_nilb M then
          if brkgrow_ok LIMIT S M k o s then
            if (Pos.leb (s_next S) (s_next (grow_post S (rget (s_regs S) (rkey a0r)) (sm_brk M) o s)) &&
                Pos.leb (s_next S) (s_next (ret_post S (sm_brk M))))%bool then
            match check_chain kok (grow_post S (rget (s_regs S) (rkey a0r)) (sm_brk M) o s) (grow_M M (rget (s_regs S) (rkey a0r)) k),
                  check_chain kfail (ret_post S (sm_brk M)) M with
            | Some f1, Some f2 => Some (f1 ++ f2)
            | _, _ => None
            end
            else None
          else None
          else None
      | _ => None
      end
  | COp op k => match op_post op S M with Some (S', M') => if Pos.leb (s_next S) (s_next S') then check_chain k S' M' else None | None => None end
  end.
End Check.

(* [comment removed for export] *)
Section Sound.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.
Variable t : tree xi.
Variable img : tree Z.
Hypothesis Hwx : wx_segs_nowrap segs.
Hypothesis Hsegb : segs_below_b segs 0x800000000000 = true.
Hypothesis Hoff : sc_alloc cfg = false.
Hypothesis Hrespos : Forall (fun p => 0 < bv_unsigned (snd p)) (segments_reserved segs).
Hypothesis Hreswf : ivs_wf (segments_reserved segs).
Hypothesis Ht : tbl_ok segs t.
Hypothesis Himg : img_ok segs img.
Hypothesis Hect : ecall_ok segs t.

#[using="Hsegb"] Lemma drop_ok_sound : forall E S M ms model bases,
  DEN segs LIMIT model0 mem0 E S M ms model ->
  forallb (fun R => negb (drop_f bases R) || drop_ok (s_facts S) (sm_zr M) R) (s_rgs S) = true ->
  forall R, In R (s_rgs S) -> drop_f bases R = true -> forall w, uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R ->
     in_zr (sm_zr M) w = true -> ms_mem ms (Z_to_bv 64 w) = Some (Z_to_bv 8 0).
Proof. LiaFast.lf_pins (fun (Hsegb : LiaFast.U) => LiaFast.u0).
  intros E S M ms model bases Hd Hok R HR Hf w Hw Hz.
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  rewrite forallb_forall in Hok. specialize (Hok R HR). rewrite Hf in Hok. cbn [negb orb] in Hok.
  destruct (sden_0 _ _ _ _ Hsd) as (_ & _ & _ & _ & HG & _ & HF & _). rewrite Forall_forall in HG.
  unfold drop_ok in Hok. apply orb_prop in Hok as [Hok|Hok]; [apply orb_prop in Hok as [Hok|Hok]|].
  - destruct (rg_kind R) eqn:Hk; try discriminate.
    pose proof (HG R HR) as HR'. rewrite restrict_mem in HR'. set (i := w - uE E (rg_base R)).
    assert (Hi : 0 <= i < rsz E R) by (unfold i; lia).
    pose proof (rg_ok_visible segs (Hof E M model) (ms_mem ms) E R Hhoff HR' i Hi) as Hv.
    destruct HR' as (_ & _ & Hall & Hcont). specialize (Hall i Hi). rewrite Hk in Hall. destruct Hall as [_ Hzz].
    assert (Hrd : rd1 segs (mrestrict (Hof E M model) (ms_mem ms)) (Z_to_bv 64 (uE E (rg_base R) + i)) = Some (Z_to_bv 8 0)).
    { destruct (tget (okey i) (rg_cont R)) as [v|] eqn:Ht0; [|exact (Hzz eq_refl)].
      destruct (Hcont _ _ Ht0) as [_ Hrd]. rewrite okey_pos in Hrd by lia. unfold uE. rewrite Hrd. f_equal.
      pose proof (tall_spec _ _ _ _ Hok Ht0) as Hb0. destruct v as [[|b0|b0]|l j]; cbn in Hb0; try discriminate. reflexivity. }
    replace (uE E (rg_base R) + i) with w in Hrd, Hv by (unfold i; lia).
    unfold rd1, mrestrict in Hrd. rewrite Hv in Hrd. destruct (ms_mem ms (Z_to_bv 64 w)) as [b0|] eqn:Hm; [exact Hrd|].
    exfalso. assert (Hcm : covered (vm_maps (m_vmmaps model)) w = true) by exact (Hzrm w Hz).
    pose proof (Hmres w Hcm) as Hnr. rewrite Hres in Hnr.
    assert (Hw64 : bv_unsigned (Z_to_bv 64 w) = w).
    { apply fg64. pose proof (Hzrsh w Hz) as Hs. unfold in_shadow, SH_LO, SH_HI in Hs. apply andb_prop in Hs as [S1 S2].
      apply Z.leb_le in S1. apply Z.ltb_lt in S2. unfold two64. lia. }
    assert (Hfs : find_segment segs (bv_unsigned (Z_to_bv 64 w)) 1 = None).
    { destruct (find_segment segs (bv_unsigned (Z_to_bv 64 w)) 1) eqn:Hf0; [|reflexivity]. exfalso.
      rewrite Hw64 in Hf0. pose proof (seg_covered segs w Hsegb ltac:(rewrite <- Hw64; apply bv_unsigned_in_range) ltac:(rewrite Hf0; discriminate)) as Hc'.
      rewrite Hnr in Hc'. discriminate. }
    rewrite (seg_rom_none segs _ Hfs) in Hrd. discriminate.
  - exfalso. pose proof (Hzrsh w Hz) as Hs. rewrite (noshadow_sound E (s_facts S) R HF Hok w Hw) in Hs. discriminate.
  - exfalso. rewrite forallb_forall in Hok. unfold in_zr in Hz. apply existsb_exists in Hz as (p & Hp & Hc).
    specialize (Hok p Hp). apply andb_prop in Hc as [C1 C2]. apply Z.leb_le in C1. apply Z.ltb_lt in C2.
    pose proof (irange_sound E (s_facts S) (rg_base R) HF). pose proof (irange_sound E (s_facts S) (rg_size R) HF).
    unfold uE, rsz in *. apply orb_prop in Hok as [Hok|Hok]; apply Z.leb_le in Hok; lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma den_addfact : forall E S M ms model f, DEN segs LIMIT model0 mem0 E S M ms model ->
  (forall E', agree (s_next S) E E' -> fact_ok E' f) -> DEN segs LIMIT model0 mem0 E (add_fact S f) M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model f Hd Hf. destruct Hd as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  constructor; try assumption.
  intros E' Ha'. destruct (Hsd E' Ha') as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
  unfold sden0; cbn [s_pc s_regs s_rgs s_facts s_resv add_fact]. split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  split; [exact H4|]. split; [exact H5|]. split; [exact H6|]. split; [|exact H8]. constructor; [exact (Hf E' Ha') | exact H7].
Qed.

#[using="Type"] Lemma den_sepg : forall E S M ms model i j S', DEN segs LIMIT model0 mem0 E S M ms model -> sepg_post S M i j = Some S' ->
  DEN segs LIMIT model0 mem0 E S' M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model i j S' Hd Hs. unfold sepg_post in Hs.
  destruct (nth_error (sm_maps M) i) as [gi|] eqn:Hi; [|discriminate]. destruct (nth_error (sm_maps M) j) as [gj|] eqn:Hj; [|discriminate].
  destruct (is_mark gi || is_mark gj)%bool eqn:Hmk; [discriminate|]. apply orb_false_iff in Hmk as [Hmi Hmj].
  destruct (is_const (fst (fst gj))) as [gb|] eqn:Hb; [|discriminate].
  destruct (negb (Nat.eqb i j) && Z.ltb (snd (irange (s_facts S) (fst (fst gi)))) (gb + gsz_lo (s_facts S) gj) &&
            Z.leb (gsz_lo (s_facts S) gi) gb && lwf (s_next S) (fst (fst gi)))%bool eqn:Hc; [|discriminate]. injection Hs as <-.
  apply andb_prop in Hc as [Hc Hwl]. apply andb_prop in Hc as [Hc Hsz]. apply andb_prop in Hc as [Hij Hlt].
  apply negb_true_iff, Nat.eqb_neq in Hij. apply Z.ltb_lt in Hlt. apply Z.leb_le in Hsz.
  apply den_addfact; [exact Hd|]. intros E' Ha'. cbn [fact_ok].
  pose proof (dn_sden segs LIMIT model0 mem0 E S M ms model Hd) as Hsd. destruct (sden_0 _ _ _ _ Hsd) as (_ & _ & _ & _ & _ & _ & HF & _).
  pose proof (irange_sound E (s_facts S) (fst (fst gi)) HF) as Ir.
  pose proof (dn_pd segs LIMIT model0 mem0 E S M ms model Hd) as Hpd. rewrite (dn_maps segs LIMIT model0 mem0 E S M ms model Hd) in Hpd.
  pose proof (pdisj_lden_nth E _ _ i j gi gj Hpd Hi Hj Hij Hmi Hmj) as Hdj.
  pose proof (dn_gsh segs LIMIT model0 mem0 E S M ms model Hd) as Hgsh. rewrite Forall_forall in Hgsh.
  destruct (Hgsh gi (nth_error_In _ _ Hi)) as (S1 & _ & _ & S4 & _). destruct (Hgsh gj (nth_error_In _ _ Hj)) as (T1 & _ & _ & T4 & _).
  destruct (is_const_sound E _ gb Hb) as [Hbv Hbr].
  unfold iv_disj, FxBacking.B, FxBacking.S, gden in Hdj. cbn [fst snd] in Hdj. rewrite Hbv in Hdj.
  unfold uE in T4. rewrite Hbv in T4. rewrite (fg64' gb Hbr) in Hdj, T4.
  pose proof (gsz_bounds E (s_facts S) gi HF) as Bi. pose proof (gsz_bounds E (s_facts S) gj HF) as Bj.
  unfold gsz, uE in Bi, Bj.
  rewrite <- (lden_agree (s_next S) E E' (fst (fst gi)) Hwl Ha'). pose proof (u_range E (fst (fst gi))). lia.
Qed.



#[using="Type"] Lemma den_sepw : forall E S M ms model i j S', DEN segs LIMIT model0 mem0 E S M ms model -> sepw_post S M i j = Some S' ->
  DEN segs LIMIT model0 mem0 E S' M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model i j S' Hd Hs. unfold sepw_post in Hs.
  destruct (nth_error (sm_maps M) i) as [gi|] eqn:Hi; [|discriminate]. destruct (nth_error (sm_maps M) j) as [gj|] eqn:Hj; [|discriminate].
  destruct (is_mark gi || is_mark gj)%bool eqn:Hmk; [discriminate|]. apply orb_false_iff in Hmk as [Hmi Hmj].
  destruct (negb (Nat.eqb i j) && lwf (s_next S) (fst (fst gi)) && lwf (s_next S) (fst (fst gj)))%bool eqn:Hc; [|discriminate].
  injection Hs as <-.
  apply andb_prop in Hc as [Hc Hwj]. apply andb_prop in Hc as [Hij Hwi]. apply negb_true_iff, Nat.eqb_neq in Hij.
  pose proof (dn_sden segs LIMIT model0 mem0 E S M ms model Hd) as Hsd. destruct (sden_0 _ _ _ _ Hsd) as (_ & _ & _ & _ & _ & _ & HF & _).
  apply den_addfact; [exact Hd|]. intros E' Ha'. unfold sepw_fact. cbn [fact_ok].
  pose proof (dn_pd segs LIMIT model0 mem0 E S M ms model Hd) as Hpd. rewrite (dn_maps segs LIMIT model0 mem0 E S M ms model Hd) in Hpd.
  pose proof (pdisj_lden_nth E _ _ i j gi gj Hpd Hi Hj Hij Hmi Hmj) as Hdj.
  pose proof (dn_gsh segs LIMIT model0 mem0 E S M ms model Hd) as Hgsh. rewrite Forall_forall in Hgsh.
  destruct (Hgsh gi (nth_error_In _ _ Hi)) as (S1 & _ & _ & S4 & _). destruct (Hgsh gj (nth_error_In _ _ Hj)) as (T1 & _ & _ & T4 & _).
  unfold iv_disj, FxBacking.B, FxBacking.S, gden in Hdj. cbn [fst snd] in Hdj.
  pose proof (u_range E (fst (fst gi))) as Ri. pose proof (u_range E (fst (fst gj))) as Rj. unfold uE in S4, T4.
  pose proof (gsz_bounds E (s_facts S) gi HF) as Bi. pose proof (gsz_bounds E (s_facts S) gj HF) as Bj.
  pose proof (gsz_lo_nonneg (s_facts S) gi) as Bi0. pose proof (gsz_lo_nonneg (s_facts S) gj) as Bj0.
  unfold gsz, uE in Bi, Bj, S1, S4, T1, T4.
  assert (Hl : lwf (s_next S) (lsub (fst (fst gi)) (laddc (fst (fst gj)) (gsz_lo (s_facts S) gj))) = true).
  { unfold lsub. rewrite lneg_eq. apply lwf_ladd; [exact Hwi | apply lwf_lscale; apply lwf_laddc; exact Hwj]. }
  rewrite <- (lden_agree (s_next S) E E' _ Hl Ha').
  rewrite lden_lsub, bv_sub_unsigned, lden_laddc, (fg64' (bv_unsigned (lden E (fst (fst gj))) + gsz_lo (s_facts S) gj)) by (unfold two64 in *; lia).
  unfold bv_wrap. change (bv_modulus 64) with two64.
  set (bi := bv_unsigned (lden E (fst (fst gi)))) in *. set (bj := bv_unsigned (lden E (fst (fst gj)))) in *.
  set (si := gsz_lo (s_facts S) gi) in *. set (sj := gsz_lo (s_facts S) gj) in *.
  set (Si := bv_unsigned (lden E (snd (fst gi)))) in *. set (Sj := bv_unsigned (lden E (snd (fst gj)))) in *.
  destruct Hdj as [Hd1|Hd1].
  - replace (bi - (bj + sj)) with ((two64 + bi - bj - sj) + (-1) * two64) by lia.
    rewrite Z.mod_add by (unfold two64; lia). rewrite Z.mod_small by (unfold two64 in *; lia). unfold two64 in *. lia.
  - rewrite Z.mod_small by (unfold two64 in *; lia). unfold two64 in *. lia.
Qed.

#[using="Type"] Lemma den_sepr : forall E S M ms model j lo hi S', DEN segs LIMIT model0 mem0 E S M ms model -> sepr_post segs S M j lo hi = Some S' ->
  DEN segs LIMIT model0 mem0 E S' M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model j lo hi S' Hd Hs. unfold sepr_post in Hs.
  destruct (nth_error (sm_maps M) j) as [gj|] eqn:Hj; [|discriminate].
  destruct (is_mark gj) eqn:Hmj; [discriminate|].
  destruct (lwf (s_next S) (fst (fst gj)) && Z.ltb lo hi && Z.ltb lo (fst (irange (s_facts S) (fst (fst gj))) + gsz_lo (s_facts S) gj) &&
            res_chain (segments_reserved segs) lo hi (Datatypes.S (List.length (segments_reserved segs))))%bool eqn:Hc; [|discriminate].
  injection Hs as <-.
  apply andb_prop in Hc as [Hc Hch]. apply andb_prop in Hc as [Hc Hlb]. apply andb_prop in Hc as [Hwj Hlh].
  apply Z.ltb_lt in Hlb, Hlh.
  apply den_addfact; [exact Hd|]. intros E' Ha'. cbn [fact_ok].
  rewrite <- (lden_agree (s_next S) E E' _ Hwj Ha').
  destruct (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd)) as (_ & _ & _ & _ & _ & _ & HF0 & _).
  pose proof (irange_sound E _ (fst (fst gj)) HF0) as R.
  pose proof (u_range E (fst (fst gj))) as Ru.
  pose proof (dn_gsh segs LIMIT model0 mem0 E S M ms model Hd) as Hgsh. rewrite Forall_forall in Hgsh.
  destruct (Hgsh gj (nth_error_In _ _ Hj)) as (G1 & _ & _ & G4 & _). unfold uE in G4.
  pose proof (gsz_bounds E (s_facts S) gj HF0) as Bj. unfold gsz, uE in Bj, G1, G4.
  set (b := bv_unsigned (lden E (fst (fst gj)))) in *. set (s := bv_unsigned (lden E (snd (fst gj)))) in *.
  split; [|unfold M64, two64 in *; lia].
  destruct (Z_lt_le_dec b hi) as [Hbh|Hbh]; [|exact Hbh]. exfalso.
  set (x := Z.max b lo).
  assert (Hx1 : lo <= x < hi) by (unfold x; lia).
  assert (Hx2 : b <= x < b + s) by (unfold x; lia).
  destruct (res_chain_cov _ _ _ _ Hch x Hx1) as (p & Hp & Hpx).
  assert (Hcm : covered (vm_maps (m_vmmaps model)) x = true).
  { rewrite (dn_maps segs LIMIT model0 mem0 E S M ms model Hd). unfold covered. apply existsb_exists.
    exists (gden E gj). split; [exact (lden_maps_in E _ _ gj (nth_error_In _ _ Hj) Hmj)|].
    unfold in_iv, in_rng, gden, FxBacking.B, FxBacking.S. cbn [fst snd]. change (bv_unsigned (lden E (fst (fst gj)))) with b.
    change (bv_unsigned (lden E (snd (fst gj)))) with s. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  pose proof (dn_mres segs LIMIT model0 mem0 E S M ms model Hd x Hcm) as Hr.
  rewrite (dn_res segs LIMIT model0 mem0 E S M ms model Hd) in Hr.
  assert (Hcr : covered (segments_reserved segs) x = true).
  { unfold covered. apply existsb_exists. exists p. split; [exact Hp|].
    unfold in_iv, in_rng, FxBacking.B, FxBacking.S. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  rewrite Hcr in Hr. discriminate.
Qed.
#[using="Type"] Lemma den_seps : forall E S M ms model j S', DEN segs LIMIT model0 mem0 E S M ms model -> seps_post S M j = Some S' ->
  DEN segs LIMIT model0 mem0 E S' M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model j S' Hd Hs. unfold seps_post in Hs.
  destruct (nth_error (sm_maps M) j) as [gj|] eqn:Hj; [|discriminate].
  destruct (lwf (s_next S) (fst (fst gj))) eqn:Hwj; [|discriminate]. injection Hs as <-.
  pose proof (dn_sden segs LIMIT model0 mem0 E S M ms model Hd) as Hsd. destruct (sden_0 _ _ _ _ Hsd) as (_ & _ & _ & _ & _ & _ & HF & _).
  destruct (sm_wf_parts _ _ (dn_wf segs LIMIT model0 mem0 E S M ms model Hd)) as (_ & _ & _ & _ & _ & Hwsp).
  apply den_addfact; [exact Hd|]. intros E' Ha'. unfold seps_fact. cbn [fact_ok].
  assert (Hl : lwf (s_next S) (lsub (laddc (sm_sp M) (- (stack_max_size + gsz_lo (s_facts S) gj))) (fst (fst gj))) = true).
  { unfold lsub. rewrite lneg_eq. apply lwf_ladd; [apply lwf_laddc; exact Hwsp | apply lwf_lscale; exact Hwj]. }
  rewrite <- (lden_agree (s_next S) E E' _ Hl Ha').
  pose proof (dn_sp segs LIMIT model0 mem0 E S M ms model Hd) as Hsp.
  destruct (dn_spok segs LIMIT model0 mem0 E S M ms model Hd) as [_ Hsphi].
  pose proof (dn_gtop segs LIMIT model0 mem0 E S M ms model Hd) as Hgt. rewrite Forall_forall in Hgt.
  pose proof (Hgt gj (nth_error_In _ _ Hj)) as Gt. unfold alloc_top in Gt. rewrite Hsp in Gt, Hsphi.
  pose proof (dn_gsh segs LIMIT model0 mem0 E S M ms model Hd) as Hgsh. rewrite Forall_forall in Hgsh.
  destruct (Hgsh gj (nth_error_In _ _ Hj)) as (G1 & _ & _ & G4 & G5).
  pose proof (gsz_bounds E (s_facts S) gj HF) as Bj. pose proof (gsz_lo_nonneg (s_facts S) gj) as Bj0.
  unfold gsz, uE in Bj, G1, G4, G5, Gt.
  rewrite lden_lsub, bv_sub_unsigned, lden_laddc.
  set (sp := bv_unsigned (lden E (sm_sp M))) in *. set (b := bv_unsigned (lden E (fst (fst gj)))) in *.
  set (lo := gsz_lo (s_facts S) gj) in *. set (s := bv_unsigned (lden E (snd (fst gj)))) in *.
  unfold stack_max_size, sp_window_hi in *.
  pose proof (u_range E (sm_sp M)) as Rsp. fold sp in Rsp. unfold two64 in Rsp.
  rewrite (fg64' (sp + - (8 * 1024 * 1024 + lo))) by (unfold two64; lia).
  unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Z.mod_small by lia. lia.
Qed.


#[using="Hwx Hsegb Hoff Hrespos Hreswf Ht Himg Hect"] Theorem chain_sound_ag : forall ch S M finals, check_chain segs LIMIT t img ch S M = Some finals ->
  forall E ms model T, DEN segs LIMIT model0 mem0 E S M ms model ->
  (forall S' M' E' ms' model', In (S', M') finals -> DEN segs LIMIT model0 mem0 E' S' M' ms' model' -> agree (s_next S) E E' ->
     realizes_cfg segs cfg (mkCfg ms' model') T) ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx Hsegb Hoff Hrespos Hreswf Ht Himg Hect : LiaFast.U) => LiaFast.u0).
  induction ch as [| depth p k IH | nk k IH | k o s kok IHok kfail IHfail | op k IH]; intros S M finals Hck E ms model T Hd Hk; cbn [check_chain] in Hck.
  - injection Hck as <-. exact (Hk S M E ms model (or_introl eq_refl) Hd (agree_refl _ _)).
  - destruct (bases_below (s_next S) (s_rgs S)) eqn:Hbi; [|discriminate]. rewrite bases_below_eq in Hbi.
    rewrite checkB_pos_below in Hck.
    destruct (check t img (pos_below (s_next S)) depth p S) as [[|L [|L' Ls]]|] eqn:Hc; try discriminate.
    destruct (sm_wf (s_next L) M && Pos.leb (s_next S) (s_next L))%bool eqn:Hwl; [|discriminate].
    apply andb_prop in Hwl as [Hwl Hle]. apply Pos.leb_le in Hle.
    apply (den_seg segs cfg LIMIT model0 mem0 Hwx t img (pos_below (s_next S)) depth p S [L] E M ms model T Ht Himg Hc Hd Hbi
             (pos_below_In (s_next S))).
    intros L0 E' ms' model' HL0 Hd' Ha'. destruct HL0 as [<-|[]]. apply (IH L M finals Hck E' ms' model' T Hd').
    intros S'' M'' E'' ms'' model'' Hin Hd'' Ha''. exact (Hk S'' M'' E'' ms'' model'' Hin Hd'' (agree_trans _ E E' E'' Ha' (agree_mono _ _ E' E'' Hle Ha''))).
  - destruct (tlookup t (s_pc S)) eqn:Hx; try discriminate.
    destruct (node_post segs LIMIT nk S M) as [[S' M']|] eqn:Hn; [|discriminate].
    destruct (Pos.leb (s_next S) (s_next S')) eqn:Hle; [|discriminate]. apply Pos.leb_le in Hle.
    unfold node_post in Hn. destruct (own_nilb M) eqn:Hon0; [|discriminate]. pose proof (own_nilb_eq M Hon0) as Hon.
    destruct (nomark (sm_maps M)) eqn:Hnm; [|discriminate].
    apply (den_ecall segs cfg LIMIT model0 mem0 Hwx t E S M ms model T Hect Hx Hd). intros model1 Hd1.
    destruct nk as [ | nZ kd vis piece na | b kk kd na idxs zr wlo whi | b kk kd pb ps ub zr | n na j kd' | n j | j | | n j]; cbn [node_post] in Hn.
    + destruct (sm_tid M) eqn:Htid; [discriminate|]. destruct (a7c S) as [c|] eqn:H7; [|discriminate].
      destruct (Z.eqb c 96) eqn:Hc96; [|discriminate]. apply Z.eqb_eq in Hc96. subst c.
      injection Hn as <- <-.
      apply (den_set_tid segs cfg LIMIT model0 mem0 E S M ms model1 T Hd1 Htid H7).
      intros E' ms' model' Hd' Ha'. apply (IH _ _ finals Hck E' ms' model' T Hd').
      intros S'' M'' E'' ms'' model'' Hin Hd'' Ha''. exact (Hk S'' M'' E'' ms'' model'' Hin Hd'' (agree_trans _ E E' E'' Ha' (agree_mono _ _ E' E'' Hle Ha''))).
    + destruct (null_ok (segments_reserved segs) LIMIT S M nZ kd vis piece na) eqn:Hok; [|discriminate].
      injection Hn as <- <-.
      apply (den_null segs cfg LIMIT model0 mem0 Hsegb Hoff E S M ms model1 T nZ kd vis piece na Hd1 Hok
               (fun a _ => conj (own_avoid_nil E M _ _ Hon) (fun _ => own_avoid_nil E M _ _ Hon))).
      intros E' ms' model' Hd' Ha'. apply (IH _ _ finals Hck E' ms' model' T Hd').
      intros S'' M'' E'' ms'' model'' Hin Hd'' Ha''. exact (Hk S'' M'' E'' ms'' model'' Hin Hd'' (agree_trans _ E E' E'' Ha' (agree_mono _ _ E' E'' Hle Ha''))).
    + destruct (pieces_of (s_facts S) (s_rgs S) idxs) as [pcs|] eqn:Hpcs; [|discriminate].
      destruct (norep_ok (segments_reserved segs) LIMIT S M b kk kd na idxs zr wlo whi) eqn:Hok; [|discriminate].
      injection Hn as <- <-.
      apply (den_norep segs cfg LIMIT model0 mem0 Hsegb Hoff E S M ms model1 T b kk kd na idxs zr wlo whi pcs Hd1 Hon Hnm Hok Hpcs).
      intros ms' model' Hd'. apply (IH _ _ finals Hck E ms' model' T Hd').
      intros S'' M'' E'' ms'' model'' Hin Hd'' Ha''. exact (Hk S'' M'' E'' ms'' model'' Hin Hd'' (agree_mono _ _ E E'' Hle Ha'')).
    + destruct (norepb_ok (segments_reserved segs) LIMIT S M b kk kd pb ps ub zr) eqn:Hok; [|discriminate].
      injection Hn as <- <-.
      apply (den_norepb segs cfg LIMIT model0 mem0 Hsegb Hoff E S M ms model1 T b kk kd pb ps ub zr Hd1 Hon Hnm Hok).
      intros ms' model' Hd'. apply (IH _ _ finals Hck E ms' model' T Hd').
      intros S'' M'' E'' ms'' model'' Hin Hd'' Ha''. exact (Hk S'' M'' E'' ms'' model'' Hin Hd'' (agree_mono _ _ E E'' Hle Ha'')).
    + destruct (fixkeep_ok LIMIT (segments_reserved segs) S M n na j kd') eqn:Hok; [|discriminate].
      injection Hn as <- <-.
      apply (den_fixkeep segs cfg LIMIT model0 mem0 Hsegb Hoff Hrespos Hreswf E S M ms model1 T n na j kd' Hd1 Hon Hok).
      intros ms' model' Hd'. apply (IH _ _ finals Hck E ms' model' T Hd').
      intros S'' M'' E'' ms'' model'' Hin Hd'' Ha''. exact (Hk S'' M'' E'' ms'' model'' Hin Hd'' (agree_mono _ _ E E'' Hle Ha'')).
    + destruct (fixnew_ok LIMIT (segments_reserved segs) S M n j) eqn:Hok; [|discriminate].
      injection Hn as <- <-.
      apply (den_fixnew segs cfg LIMIT model0 mem0 Hsegb Hoff Hrespos Hreswf E S M ms model1 T n j Hd1 Hon Hok).
      intros ms' model' Hd'. apply (IH _ _ finals Hck E ms' model' T Hd').
      intros S'' M'' E'' ms'' model'' Hin Hd'' Ha''. exact (Hk S'' M'' E'' ms'' model'' Hin Hd'' (agree_mono _ _ E E'' Hle Ha'')).
    + destruct (munmap_ok (segments_reserved segs) LIMIT S M j) eqn:Hok; [|discriminate].
      injection Hn as <- <-.
      apply (den_munmap segs cfg LIMIT model0 mem0 Hsegb E S M ms model1 T j Hd1 Hon Hnm Hok).
      intros ms' model' Hd'. apply (IH _ _ finals Hck E ms' model' T Hd').
      intros S'' M'' E'' ms'' model'' Hin Hd'' Ha''. exact (Hk S'' M'' E'' ms'' model'' Hin Hd'' (agree_mono _ _ E E'' Hle Ha'')).
    + destruct (brkq_ok S M) eqn:Hok; [|discriminate].
      injection Hn as <- <-.
      apply (den_brkq segs cfg LIMIT model0 mem0 E S M ms model1 T Hd1 Hok).
      intros ms' model' Hd'. apply (IH _ _ finals Hck E ms' model' T Hd').
      intros S'' M'' E'' ms'' model'' Hin Hd'' Ha''. exact (Hk S'' M'' E'' ms'' model'' Hin Hd'' (agree_mono _ _ E E'' Hle Ha'')).
    + destruct (mprot_ok (segments_reserved segs) LIMIT S M n j) eqn:Hok; [|discriminate].
      injection Hn as <- <-.
      apply (den_mprotect segs cfg LIMIT model0 mem0 Hoff E S M ms model1 T n j Hd1 Hon Hnm Hok).
      intros ms' model' Hd'. apply (IH _ _ finals Hck E ms' model' T Hd').
      intros S'' M'' E'' ms'' model'' Hin Hd'' Ha''. exact (Hk S'' M'' E'' ms'' model'' Hin Hd'' (agree_mono _ _ E E'' Hle Ha'')).
  - destruct (tlookup t (s_pc S)) eqn:Hx; try discriminate.
    destruct (own_nilb M) eqn:Hon0; [|discriminate]. pose proof (own_nilb_eq M Hon0) as Hon.
    destruct (brkgrow_ok LIMIT S M k o s) eqn:Hok; [|discriminate].
    destruct (Pos.leb (s_next S) (s_next (grow_post S (rget (s_regs S) (rkey a0r)) (sm_brk M) o s)) &&
              Pos.leb (s_next S) (s_next (ret_post S (sm_brk M))))%bool eqn:Hle; [|discriminate].
    apply andb_prop in Hle as [Hle1 Hle2]. apply Pos.leb_le in Hle1, Hle2.
    destruct (check_chain segs LIMIT t img kok (grow_post S (rget (s_regs S) (rkey a0r)) (sm_brk M) o s) (grow_M M (rget (s_regs S) (rkey a0r)) k)) as [f1|] eqn:H1; [|discriminate].
    destruct (check_chain segs LIMIT t img kfail (ret_post S (sm_brk M)) M) as [f2|] eqn:H2; [|discriminate].
    injection Hck as <-.
    apply (den_ecall segs cfg LIMIT model0 mem0 Hwx t E S M ms model T Hect Hx Hd). intros model1 Hd1.
    apply (den_brkgrow segs cfg LIMIT model0 mem0 Hoff E S M ms model1 T k o s Hd1 Hon Hok).
    + intros ms' model' Hd'. apply (IHok _ _ f1 H1 E ms' model' T Hd').
      intros S' M' E' ms'' model'' Hin Hd'' Ha''. exact (Hk S' M' E' ms'' model'' (in_or_app _ _ _ (or_introl Hin)) Hd'' (agree_mono _ _ E E' Hle1 Ha'')).
    + intros ms' model' Hd'. apply (IHfail _ _ f2 H2 E ms' model' T Hd').
      intros S' M' E' ms'' model'' Hin Hd'' Ha''. exact (Hk S' M' E' ms'' model'' (in_or_app _ _ _ (or_intror Hin)) Hd'' (agree_mono _ _ E E' Hle2 Ha'')).
  - destruct (op_post segs LIMIT op S M) as [[S1 M1]|] eqn:Hop; [|discriminate].
    destruct (Pos.leb (s_next S) (s_next S1)) eqn:Hle; [|discriminate]. apply Pos.leb_le in Hle.
    destruct op as [bases| |n|a|i j|i j|j lo hi|j]; cbn [op_post] in Hop.
    + destruct (own_nilb M && forallb (fun R => negb (drop_f bases R) || drop_ok (s_facts S) (sm_zr M) R) (s_rgs S))%bool eqn:Hok; [|discriminate].
      injection Hop as <- <-. apply andb_prop in Hok as [Hon Hok].
      apply (IH _ _ finals Hck E ms model T).
      * apply (den_drop segs LIMIT model0 mem0 E S M ms model (drop_f bases) Hd (own_nilb_eq M Hon)).
        exact (drop_ok_sound E S M ms model bases Hd Hok).
      * intros S'' M'' E'' ms'' model'' Hin Hd'' Ha''. exact (Hk S'' M'' E'' ms'' model'' Hin Hd'' (agree_mono _ _ E E'' Hle Ha'')).
    + destruct (own_nilb M && forallb (fun R => negb (drop_f (a0_bases S) R) || drop_ok (s_facts S) (sm_zr M) R) (s_rgs S))%bool eqn:Hok; [|discriminate].
      injection Hop as <- <-. apply andb_prop in Hok as [Hon Hok].
      apply (IH _ _ finals Hck E ms model T).
      * apply (den_drop segs LIMIT model0 mem0 E S M ms model (drop_f (a0_bases S)) Hd (own_nilb_eq M Hon)).
        exact (drop_ok_sound E S M ms model (a0_bases S) Hd Hok).
      * intros S'' M'' E'' ms'' model'' Hin Hd'' Ha''. exact (Hk S'' M'' E'' ms'' model'' Hin Hd'' (agree_mono _ _ E E'' Hle Ha'')).
    + destruct (lwf (s_next S) (rget (s_regs S) (rkey a0r)) && Z.leb 0 n &&
                Z.leb (eager_sum (s_facts S) (sm_maps M) + allow_bound ((rget (s_regs S) (rkey a0r), n) :: sm_allow M)) LIMIT)%bool eqn:Hok; [|discriminate].
      injection Hop as <- <-.
      apply andb_prop in Hok as [Hok Hbud]. apply andb_prop in Hok as [Hwb Hn0]. apply Z.leb_le in Hbud, Hn0.
      apply (IH _ _ finals Hck E ms model T).
      * exact (den_allow segs LIMIT model0 mem0 E S M ms model (rget (s_regs S) (rkey a0r)) n Hd Hwb Hn0 Hbud).
      * intros S'' M'' E'' ms'' model'' Hin Hd'' Ha''. exact (Hk S'' M'' E'' ms'' model'' Hin Hd'' (agree_mono _ _ E E'' Hle Ha'')).
    + destruct (forget_post S a) as [S'|] eqn:Hf; [|discriminate].
      destruct (sm_wf (s_next S') M) eqn:Hw; [|discriminate].
      injection Hop as <- <-.
      apply (den_forget segs cfg LIMIT model0 mem0 Hwx E S M ms model T a S' Hd Hf).
      intros E' ms' model' Hd' Ha'. apply (IH _ _ finals Hck E' ms' model' T Hd').
      intros S'' M'' E'' ms'' model'' Hin Hd'' Ha''. exact (Hk S'' M'' E'' ms'' model'' Hin Hd'' (agree_trans _ E E' E'' Ha' (agree_mono _ _ E' E'' Hle Ha''))).
    + destruct (sepg_post S M i j) as [S'|] eqn:Hs; [|discriminate].
      injection Hop as <- <-.
      apply (IH _ _ finals Hck E ms model T (den_sepg E S M ms model i j S' Hd Hs)).
      intros S'' M'' E'' ms'' model'' Hin Hd'' Ha''. exact (Hk S'' M'' E'' ms'' model'' Hin Hd'' (agree_mono _ _ E E'' Hle Ha'')).
    + destruct (sepw_post S M i j) as [S'|] eqn:Hs; [|discriminate].
      injection Hop as <- <-.
      apply (IH _ _ finals Hck E ms model T (den_sepw E S M ms model i j S' Hd Hs)).
      intros S'' M'' E'' ms'' model'' Hin Hd'' Ha''. exact (Hk S'' M'' E'' ms'' model'' Hin Hd'' (agree_mono _ _ E E'' Hle Ha'')).
    + destruct (sepr_post segs S M j lo hi) as [S'|] eqn:Hs; [|discriminate].
      injection Hop as <- <-.
      apply (IH _ _ finals Hck E ms model T (den_sepr E S M ms model j lo hi S' Hd Hs)).
      intros S'' M'' E'' ms'' model'' Hin Hd'' Ha''. exact (Hk S'' M'' E'' ms'' model'' Hin Hd'' (agree_mono _ _ E E'' Hle Ha'')).
    + destruct (seps_post S M j) as [S'|] eqn:Hs; [|discriminate].
      injection Hop as <- <-.
      apply (IH _ _ finals Hck E ms model T (den_seps E S M ms model j S' Hd Hs)).
      intros S'' M'' E'' ms'' model'' Hin Hd'' Ha''. exact (Hk S'' M'' E'' ms'' model'' Hin Hd'' (agree_mono _ _ E E'' Hle Ha'')).
Qed.

#[using="Hwx Hsegb Hoff Hrespos Hreswf Ht Himg Hect"] Theorem chain_sound : forall ch S M finals, check_chain segs LIMIT t img ch S M = Some finals ->
  forall E ms model T, DEN segs LIMIT model0 mem0 E S M ms model ->
  (forall S' M' E' ms' model', In (S', M') finals -> DEN segs LIMIT model0 mem0 E' S' M' ms' model' -> realizes_cfg segs cfg (mkCfg ms' model') T) ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx Hsegb Hoff Hrespos Hreswf Ht Himg Hect : LiaFast.U) => LiaFast.u0).
  intros ch S M finals Hck E ms model T Hd Hk. apply (chain_sound_ag ch S M finals Hck E ms model T Hd).
  intros S' M' E' ms' model' Hin Hd' _. exact (Hk S' M' E' ms' model' Hin Hd').
Qed.
End Sound.
