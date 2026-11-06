(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Run Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
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
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChFix FxChAdd.

Module FxChBrk.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Run Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg SysNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop FxPlan FxFrame FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.FxAcct.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChFix.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChFix FxChAdd FxChUnmap.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChSeg OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChNode OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFix.FxChNorep OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFix OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChAdd OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChUnmap.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition ret_post (L : sst) (v : lin) : sst :=
  SST (s_pc L + 4) (rset (s_regs L) (rkey a0r) v) (s_rgs L) (s_facts L) (s_next L) (s_resv L).

Section Ret.
Variable segs : list Segment.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.

(* [comment removed for export] *)
#[using="Type"] Theorem den_ret : forall E L M ms model (v : lin),
  DEN segs LIMIT model0 mem0 E L M ms model -> lwf (s_next L) v = true ->
  DEN segs LIMIT model0 mem0 E (ret_post L v) M (advance_past_svc (apply_effect (svc_set ms) (mkEffect (lden E v) [] []))) model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E L M ms model v Hd Hwv.
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  destruct (sden_0 _ _ _ _ Hsd) as (Hpc0 & _).
  constructor; try assumption.
  - rewrite (restrict_adv_eff (Hof E M model) ms (lden E v) [] [] [] (s_pc L) Hpc0). cbn [apply_zeros apply_unmaps].
    intros E'' Ha''. cbn [ret_post s_next] in Ha''. destruct (Hsd E'' Ha'') as (_ & _ & Hrv & HR & HG & HD & HF & Hfrm).
    unfold sden0, ret_post. cbn [s_pc s_regs s_rgs s_facts s_resv mks ms_pc_val ms_svc_pending ms_resv ms_regs ms_mem ms_fcsr].
    split; [reflexivity|]. split; [reflexivity|]. split; [exact Hrv|].
    split; [apply regs_ok_upd; [exact HR | exact (lden_agree_wf _ E E'' v Hwv Ha'')]|]. auto.
Qed.
End Ret.

Section BrkQ.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.

Definition brkq_ok (L : sst) (M : smodel) : bool :=
  match a7c L, arg L 0 with Some c7, Some c0 => (Z.eqb c7 214 && Z.eqb c0 0 && lwf (s_next L) (sm_brk M))%bool | _, _ => false end.

#[using="Type"] Theorem den_brkq : forall E L M ms model T,
  DEN segs LIMIT model0 mem0 E L M ms model -> brkq_ok L M = true ->
  (forall ms' model', DEN segs LIMIT model0 mem0 E (ret_post L (sm_brk M)) M ms' model' -> realizes_cfg segs cfg (mkCfg ms' model') T) ->
  realizes_cfg segs cfg (mkCfg (svc_set ms) model) T.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E L M ms model T Hd Hok Hk. unfold brkq_ok in Hok.
  destruct (a7c L) as [c7|] eqn:H7; [|discriminate]. destruct (arg L 0) as [c0|] eqn:H0; [|discriminate].
  apply andb_prop in Hok as [Hok Hwb]. apply andb_prop in Hok as [Hc7 Hc0]. apply Z.eqb_eq in Hc7, Hc0. subst c7 c0.
  pose proof Hd as Hd0. destruct Hd0 as [Hsd _ _ Hh _ _ _ _ _ _ _ _ Hbrk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _].
  set (H := Hof E M model) in *.
  assert (Hx8 : ms_reg ms 17 = Z_to_bv 64 214) by exact (a7_const segs E L (restrict H ms) ms 214 Hsd eq_refl H7).
  assert (Hg0 : ms_gpr (svc_set ms) 0 = Z_to_bv 64 0) by exact (gpr_const segs E L (restrict H ms) ms 0 0 Hsd eq_refl ltac:(lia) H0).
  pose proof (den_ret segs LIMIT model0 mem0 E L M ms model (sm_brk M) Hd Hwb) as HD'. rewrite <- Hbrk in HD'.
  eapply rzc_silent1; [|exact (Hk _ _ HD')].
  apply (node_brk_query segs cfg (svc_set ms) model (ms_reg ms 17) (Z_to_bv 64 0) Hh eq_refl ltac:(rewrite Hx8; reflexivity) Hg0).
  left. reflexivity.
Qed.
End BrkQ.

(* [comment removed for export] *)
Lemma brk_grow_shape : forall (m : Model) (req : word) (k : Z),
  let b := vm_brk (m_vmmaps m) in
  0 < bv_unsigned b -> bv_unsigned b mod 4096 = 0 -> 0 < k -> k mod 4096 = 0 -> bv_unsigned req = bv_unsigned b + k ->
  bv_unsigned b + k < two64 ->
  brk_eff req req b = mkEffectU req [] [(b, Z_to_bv 64 k)] [] [] [] /\
  with_brk_next m req req = with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m)) ((b, Z_to_bv 64 k) :: vm_maps (m_vmmaps m))
     (vm_noaccess (m_vmmaps m)) (vm_start_brk (m_vmmaps m)) req (vm_limit (m_vmmaps m)) (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m.
Proof.
  intros m req k b Hb0 Hbal Hk Hkal Hreq Hw.
  assert (Hpb : page_round_up_Z (bv_unsigned b) = bv_unsigned b).
  { unfold page_round_up_Z, page_size. pose proof (Z.div_mod (bv_unsigned b) 4096 ltac:(lia)). rewrite Hbal in H.
    replace (bv_unsigned b + 4096 - 1) with (bv_unsigned b / 4096 * 4096 + 4095) by lia.
    rewrite Z.div_add_l by lia. change (4095 / 4096) with 0. lia. }
  assert (Hpr : page_round_up_Z (bv_unsigned req) = bv_unsigned req).
  { unfold page_round_up_Z, page_size. rewrite Hreq. pose proof (Z.div_mod (bv_unsigned b + k) 4096 ltac:(lia)).
    assert ((bv_unsigned b + k) mod 4096 = 0) by (rewrite Z.add_mod, Hbal, Hkal by lia; reflexivity). rewrite H0 in H.
    replace (bv_unsigned b + k + 4096 - 1) with ((bv_unsigned b + k) / 4096 * 4096 + 4095) by lia.
    rewrite Z.div_add_l by lia. change (4095 / 4096) with 0. lia. }
  assert (Hgrow : brk_is_grow req req b = true).
  { unfold brk_is_grow. rewrite <- (Z_to_bv_bv_unsigned _ req) at 1. unfold w_is0. rewrite Hreq.
    apply andb_true_intro. split; [apply andb_true_intro; split|].
    - apply negb_true_iff. unfold bv_eqb. rewrite fg_lit by (unfold two64 in Hw; change (2 ^ 64) with 18446744073709551616; pose proof (bv_unsigned_in_range _ b); lia).
      apply Z.eqb_neq. rewrite fg_lit by (change (2 ^ 64) with 18446744073709551616; lia). lia.
    - apply Z.ltb_lt. exact Hb0.
    - apply Z.ltb_lt. lia. }
  assert (Hun : brk_unmaps req b = []).
  { unfold brk_unmaps, brk_page_range. rewrite Hpb, Hpr. replace (0 <? bv_unsigned b) with true by (symmetry; apply Z.ltb_lt; lia).
    replace (bv_unsigned req <? bv_unsigned b) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
  split.
  - unfold brk_eff, brk_zeros, brk_page_range. rewrite Hgrow, Hun, Hpb, Hpr.
    replace (bv_unsigned b <? bv_unsigned req) with true by (symmetry; apply Z.ltb_lt; lia).
    rewrite Z_to_bv_bv_unsigned. replace (bv_unsigned req - bv_unsigned b) with k by lia. reflexivity.
  - unfold with_brk_next. fold b. rewrite Hun. cbn [forget_vm_ranges]. unfold brk_model_next, brk_maps_next. fold b.
    replace (0 <? bv_unsigned b) with true by (symmetry; apply Z.ltb_lt; lia).
    replace (bv_unsigned req <? bv_unsigned b) with false by (symmetry; apply Z.ltb_ge; lia). cbn [andb].
    unfold brk_grants. rewrite Hgrow. rewrite Hun. cbn [maps_subtract_ranges fold_left app].
    replace (req - b)%bv with (Z_to_bv 64 k); [reflexivity|].
    apply bv_eq. rewrite bv_sub_unsigned, Hreq. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
    rewrite fg_lit by (change (2 ^ 64) with 18446744073709551616; unfold two64 in Hw; lia).
    replace (bv_unsigned b + k - bv_unsigned b) with k by lia. symmetry. apply Z.mod_small. unfold two64 in *; lia.
Qed.

Definition grow_post (L : sst) (a b : lin) (o s : Z) : sst :=
  SST (s_pc L + 4) (rset (s_regs L) (rkey a0r) a) (RGz (laddc b o) s RZ TEmpty :: s_rgs L) (s_facts L) (s_next L) (s_resv L).
Definition grow_M (M : smodel) (a : lin) (k : Z) : smodel :=
  SM ((sm_brk M, lconst k, GE) :: sm_maps M) (sm_allow M) (sm_zr M) (sm_tid M) a (sm_sbrk M) (sm_sp M) (sm_frz M) [].

Lemma region_free_mono : forall l (lo n n' : word), region_free l lo n = true -> bv_unsigned n' <= bv_unsigned n -> region_free l lo n' = true.
Proof.
  induction l as [|[b s] l IH]; intros lo n n' H Hn; [reflexivity|]. cbn [region_free] in *. apply andb_prop in H as [H1 H2].
  apply andb_true_intro. split; [|exact (IH lo n n' H2 Hn)]. apply negb_true_iff in H1. apply negb_true_iff.
  unfold iv_overlap in *. apply andb_false_iff in H1 as [H1|H1]; apply andb_false_iff; [left|right]; apply Z.ltb_ge in H1; apply Z.ltb_ge; lia.
Qed.

Lemma gsz_lconst_b : forall E b k kd, 0 <= k < two64 -> gsz E (b, lconst k, kd) = k.
Proof. intros E b k kd Hk. unfold gsz, uE. cbn [fst snd]. rewrite lden_lconst. apply fg64. exact Hk. Qed.

Section Grow.
Variable segs : list Segment.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.
Hypothesis Hsegb : segs_below_b segs 0x800000000000 = true.

#[using="Type"] Theorem grow_den : forall E L M ms model (a : lin) (k o s : Z),
  DEN segs LIMIT model0 mem0 E L M ms model ->
  lwf (s_next L) a = true -> shadow_ok M = true ->
  uE E a = uE E (sm_brk M) + k -> 0 < uE E (sm_brk M) -> uE E (sm_brk M) mod 4096 = 0 -> 0 < k -> k mod 4096 = 0 ->
  0 <= o -> 0 < s -> o + s <= k ->
  brk_grow_ok model (lden E a) (lden E a) = true ->
  eager_sum (s_facts L) ((sm_brk M, lconst k, GE) :: sm_maps M) + allow_bound (sm_allow M) <= LIMIT -> sm_own M = [] ->
  nomark ((sm_brk M, lconst k, GE) :: sm_maps M) = true ->
  DEN segs LIMIT model0 mem0 E (grow_post L a (sm_brk M) o s) (grow_M M a k)
      (advance_past_svc (apply_effect (svc_set ms) (mkEffectU (lden E a) [] [(lden E (sm_brk M), Z_to_bv 64 k)] [] [] [])))
      (with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps model)) ((lden E (sm_brk M), Z_to_bv 64 k) :: vm_maps (m_vmmaps model))
         (vm_noaccess (m_vmmaps model)) (vm_start_brk (m_vmmaps model)) (lden E a) (vm_limit (m_vmmaps model))
         (vm_mmap_base (m_vmmaps model)) (vm_init_sp (m_vmmaps model))) model).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E L M ms model a k o s Hd Hwa Hsh Hua Hb0 Hbal HnZ Hnal Ho Hs Hos Hgrow Hbud Hon Hnm'.
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  assert (Hnm : nomark (sm_maps M) = true) by (cbn [nomark forallb] in Hnm'; apply andb_prop in Hnm' as [_ X]; exact X).
  pose proof (eq_sym Hmaps) as HmapsL. den_noblob Hnm. apply eq_sym in HmapsL.
  set (bw := lden E (sm_brk M)) in *. set (u := uE E (sm_brk M)) in *.
  assert (Hub : bv_unsigned bw = u) by reflexivity.
  (* [comment removed for export] *)
  unfold brk_grow_ok in Hgrow. rewrite Hbrk in Hgrow. fold bw in Hgrow.
  replace (0 <? bv_unsigned bw) with true in Hgrow by (symmetry; apply Z.ltb_lt; lia).
  change (bv_unsigned (lden E a)) with (uE E a) in Hgrow. rewrite Hua in Hgrow.
  replace (bv_unsigned bw <? u + k) with true in Hgrow by (symmetry; apply Z.ltb_lt; lia). cbn [andb] in Hgrow.
  assert (Hpb : page_round_up_Z u = u).
  { unfold page_round_up_Z, page_size. pose proof (Z.div_mod u 4096 ltac:(lia)). rewrite Hbal in H.
    replace (u + 4096 - 1) with (u / 4096 * 4096 + 4095) by lia. rewrite Z.div_add_l by lia. change (4095 / 4096) with 0. lia. }
  assert (Hpr : page_round_up_Z (u + k) = u + k).
  { unfold page_round_up_Z, page_size. pose proof (Z.div_mod (u + k) 4096 ltac:(lia)).
    assert ((u + k) mod 4096 = 0) by (rewrite Z.add_mod, Hbal, Hnal by lia; reflexivity). rewrite H0 in H.
    replace (u + k + 4096 - 1) with ((u + k) / 4096 * 4096 + 4095) by lia. rewrite Z.div_add_l by lia. change (4095 / 4096) with 0. lia. }
  rewrite Hub, Hpb, Hpr in Hgrow. replace (u <? u + k) with true in Hgrow by (symmetry; apply Z.ltb_lt; lia).
  apply andb_prop in Hgrow as [Hgrow _]. apply andb_prop in Hgrow as [Htop Hfree0]. apply Z.leb_le in Htop.
  assert (HnZw : bv_unsigned (Z_to_bv 64 k) = k).
  { apply fg64. destruct Hspok as [_ Hsp2]. pose proof (u_lt bw). unfold alloc_top, stack_max_size, sp_window_hi, two64 in *. lia. }
  assert (Hfree : region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) bw (Z_to_bv 64 k) = true).
  { rewrite <- (Z_to_bv_bv_unsigned _ bw). rewrite Hub. apply (region_free_mono _ _ (Z_to_bv 64 (u + k + 4096 - u))); [exact Hfree0|].
    rewrite HnZw. rewrite fg64 by (destruct Hspok as [_ Hsp2]; pose proof (u_lt bw); unfold alloc_top, stack_max_size, sp_window_hi, two64 in *; lia). lia. }
  assert (Hplace : place_ok model k bw) by (unfold place_ok, page_size; rewrite Hub; repeat split; try lia; exact Hfree).
  pose proof (place_facts_of E M model _ k bw HmapsL Hsh (proj2 Hspok) HnZ Hplace) as PF.
  pose proof PF as PF0. destruct PF0 as [Hal' Hlo Hhi Hshd]. rewrite Hub in Hal', Hlo, Hhi, Hshd.
  assert (Hnc : forall x, u <= x < u + k -> covered (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) x = false).
  { intros x Hx. apply (region_free_pt _ bw (Z_to_bv 64 k)); [exact Hfree | rewrite HnZw, Hub; exact Hx]. }
  set (model' := with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps model)) ((bw, Z_to_bv 64 k) :: vm_maps (m_vmmaps model))
         (vm_noaccess (m_vmmaps model)) (vm_start_brk (m_vmmaps model)) (lden E a) (vm_limit (m_vmmaps model))
         (vm_mmap_base (m_vmmaps model)) (vm_init_sp (m_vmmaps model))) model).
  set (M' := grow_M M a k).
  set (H := Hof E M model) in *.
  assert (HH : Hof E M' model' = H) by reflexivity.
  assert (Hsd0 := sden_0 _ _ _ _ Hsd). destruct Hsd0 as (Hpc0 & Hsv0 & Hrv0 & HR0 & HG0 & HD0 & HF0 & Hfrm0).
  assert (Hrgw : forall R, In R (s_rgs L) -> uE E (rg_base R) + rsz E R <= two64 /\ 0 <= rsz E R).
  { intros R HR. rewrite Forall_forall in HG0. destruct (HG0 R HR) as (Hs' & Hw & _). unfold uE. lia. }
  assert (Hold : forall R, In R (s_rgs L) -> forall w, uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R -> ~ (u <= w < u + k)).
  { intros R HR w Hw. rewrite Forall_forall in Hrl.
    destruct (old_pts E model bw k R w PF HnZ Hnal ltac:(rewrite Hub; exact Hnc) ltac:(rewrite Hub; lia) (Hrl R HR) Hw) as [H1 _].
    rewrite Hub in H1. exact H1. }
  set (mem' := apply_zeros (apply_unmaps (ms_mem ms) []) [(bw, Z_to_bv 64 k)]).
  assert (Hmout : forall w, ~ (u <= bv_unsigned w < u + k) -> mem' w = ms_mem ms w).
  { intros w Hw. unfold mem'. cbn [apply_unmaps]. apply apply_zeros_out. rewrite zeros_cover_one, Hub, HnZw.
    apply not_true_iff_false. intros Hb'. apply andb_prop in Hb' as [B1 B2]. apply Z.leb_le in B1. apply Z.ltb_lt in B2. lia. }
  assert (Hmin : forall w, u <= bv_unsigned w < u + k -> mem' w = Some (Z_to_bv 8 0)).
  { intros w Hw. unfold mem'. apply apply_zeros_in. rewrite zeros_cover_one, Hub, HnZw.
    apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  assert (Hvis : forall w, u <= bv_unsigned w < u + k -> H w = false).
  { intros w Hw. unfold H, Hof. apply mkH_notlazy. apply not_true_iff_false. intros Hp.
    destruct (pb_bounds w) as [Hb' _]. pose proof (Hlzm _ (page_in_covered _ _ _ Hp Hb')) as Hc.
    pose proof (Hnc (bv_unsigned w) Hw) as Hf. rewrite covered_app, Hc, orb_true_r in Hf. discriminate. }
  assert (Hsden : sden segs E (grow_post L a (sm_brk M) o s)
                    (restrict H (advance_past_svc (apply_effect (svc_set ms) (mkEffectU (lden E a) [] [(bw, Z_to_bv 64 k)] [] [] []))))).
  { rewrite (restrict_adv_eff H ms (lden E a) [(bw, Z_to_bv 64 k)] [] [] (s_pc L) Hpc0). fold mem'.
    intros E'' Ha''. cbn [grow_post s_next] in Ha''.
    destruct (Hsd E'' Ha'') as (_ & _ & Hrv & HR & HG & HD & HF & Hfrm).
    assert (HbE : forall R, In R (s_rgs L) -> uE E'' (rg_base R) = uE E (rg_base R) /\ rsz E'' R = rsz E R).
    { intros R HR'. unfold uE, rsz. unfold bases_wf in Hbw. rewrite forallb_forall in Hbw. destruct (andb_prop _ _ (Hbw R HR')) as [Hb1 Hb2].
      rewrite (lden_agree_wf _ E E'' _ Hb1 Ha''), (lden_agree_wf _ E E'' _ Hb2 Ha''). split; reflexivity. }
    destruct (sm_wf_parts _ M Hwf) as (_ & _ & _ & Hwb & _ & _).
    assert (HbE' : uE E'' (laddc (sm_brk M) o) = u + o).
    { unfold uE. rewrite lden_laddc, (lden_agree_wf _ E E'' _ Hwb Ha''). fold bw. rewrite Hub. apply fg64. unfold TOPW, two64 in *. lia. }
    assert (Hs64 : 0 <= s < two64) by (unfold TOPW, two64 in *; lia).
    unfold sden0, grow_post. cbn [s_pc s_regs s_rgs s_facts s_resv mks ms_pc_val ms_svc_pending ms_resv ms_regs ms_mem ms_fcsr].
    split; [reflexivity|]. split; [reflexivity|]. split; [exact Hrv|].
    split; [apply regs_ok_upd; [exact HR | exact (lden_agree_wf _ E E'' a Hwa Ha'')]|].
    split; [|split; [|split; [exact HF | exact Hfrm]]].
    - constructor.
      + apply rg_ok_fresh_rz; [exact Hs64 | rewrite HbE'; unfold TOPW, two64 in *; lia|]. intros i Hi. rewrite HbE'.
        assert (Hw64 : bv_unsigned (Z_to_bv 64 (u + o + i)) = u + o + i) by (apply fg64; unfold TOPW, two64 in *; lia).
        unfold mrestrict. rewrite (Hvis _ ltac:(rewrite Hw64; lia)). apply Hmin. rewrite Hw64. lia.
      + apply Forall_forall. intros R HR'. rewrite Forall_forall in HG. apply (rg_ok_mem_eq segs E'' (ms_mem (restrict H ms))); [exact (HG R HR')|].
        intros i Hi. rewrite (proj2 (HbE R HR')) in Hi. rewrite (proj1 (HbE R HR')). cbn [ms_mem restrict]. unfold mrestrict.
        destruct (H (Z_to_bv 64 (uE E (rg_base R) + i))); [reflexivity|].
        destruct (Hrgw R HR') as [Hw1 Hw2]. pose proof (u_lt (lden E (rg_base R))).
        apply Hmout. rewrite fg64 by (unfold uE in *; lia). exact (Hold R HR' (uE E (rg_base R) + i) ltac:(lia)).
    - cbn [rgs_disj]. split; [|exact HD]. apply Forall_forall. intros R2 H2. unfold rg_disj. cbv zeta.
      rewrite (rsz_RGz E'' (laddc (sm_brk M) o) s RZ TEmpty Hs64). unfold RGz. cbn [rg_base].
      change (bv_unsigned (lden E'' (laddc (sm_brk M) o))) with (uE E'' (laddc (sm_brk M) o)). rewrite HbE'.
      change (bv_unsigned (lden E'' (rg_base R2))) with (uE E'' (rg_base R2)). rewrite (proj1 (HbE R2 H2)), (proj2 (HbE R2 H2)).
      pose proof Hrl as Hrl2. rewrite Forall_forall in Hrl2. destruct (Hrl2 R2 H2) as [Hpos2 _].
      apply iv_pts_disj; [lia | exact Hpos2|]. intros w Hw1 Hw2. exact (Hold R2 H2 w Hw2 ltac:(lia)). }
  assert (Hvm' : m_vmmaps model' = mkVmMapsFull (vm_reserved (m_vmmaps model)) ((bw, Z_to_bv 64 k) :: vm_maps (m_vmmaps model))
         (vm_noaccess (m_vmmaps model)) (vm_start_brk (m_vmmaps model)) (lden E a) (vm_limit (m_vmmaps model))
         (vm_mmap_base (m_vmmaps model)) (vm_init_sp (m_vmmaps model))) by reflexivity.
  assert (Hlz' : m_vm_lazy model' = m_vm_lazy model) by reflexivity.
  assert (Hmat' : m_vm_materialized model' = m_vm_materialized model) by reflexivity.
  assert (Hmaps' : vm_maps (m_vmmaps model') = List.map (gden E) (sm_maps M')).
  { rewrite Hvm'. cbn [vm_maps sm_maps M' grow_M List.map]. unfold gden at 1. cbn [fst snd]. fold bw. rewrite lden_lconst, Hmaps. reflexivity. }
  assert (Hgsh' : Forall (gshape_ok E) (sm_maps M')).
  { cbn [sm_maps M' grow_M]. constructor; [|exact Hgsh]. unfold gshape_ok. rewrite gsz_lconst_b by (unfold two64, TOPW in *; lia). cbn [fst snd]. fold u. unfold TOPW in Hhi. lia. }
  assert (Hcovm : forall x, covered (vm_maps (m_vmmaps model')) x = (in_iv (bw, Z_to_bv 64 k) x || covered (vm_maps (m_vmmaps model)) x)%bool)
    by (intros x; rewrite Hvm'; reflexivity).
  assert (Hinv : forall x, in_iv (bw, Z_to_bv 64 k) x = true -> u <= x < u + k).
  { intros x Hx. rewrite in_iv_word, HnZw, Hub in Hx. apply andb_prop in Hx as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia. }
  assert (Hinv' : forall x, u <= x < u + k -> in_iv (bw, Z_to_bv 64 k) x = true).
  { intros x Hx. rewrite in_iv_word, HnZw, Hub. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  assert (Hlzm' : forall x, covered (m_vm_lazy model') x = true -> covered (vm_maps (m_vmmaps model')) x = true).
  { intros x Hx. rewrite Hcovm, (Hlzm x Hx), orb_true_r. reflexivity. }
  assert (Hmres' : forall x, covered (vm_maps (m_vmmaps model')) x = true -> covered (vm_reserved (m_vmmaps model')) x = false).
  { intros x Hx. rewrite Hvm'. cbn [vm_reserved]. rewrite Hcovm in Hx. apply orb_prop in Hx as [Hx|Hx]; [|exact (Hmres x Hx)].
    pose proof (Hnc x (Hinv x Hx)) as Hf. rewrite covered_app in Hf. apply orb_false_iff in Hf. exact (proj1 Hf). }
  assert (Hkind' : Forall (kind_ok E model') (sm_maps M')).
  { cbn [sm_maps M' grow_M]. constructor; [unfold kind_ok; cbn [snd]; split; [intros Hne; exfalso; exact (Hne eq_refl) | discriminate]|].
    rewrite Forall_forall in Hkind |- *. intros g Hg. split; [intros Hne x Hx; exact (proj1 (Hkind g Hg) Hne x Hx)|].
    intros Hgn. rewrite Hvm'. cbn [vm_noaccess]. exact (proj2 (Hkind g Hg) Hgn). }
  assert (Hbud' : eager_used model' + A_bytes (allowA E M') <= LIMIT).
  { assert (HFL : Forall (fact_ok E) (s_facts L)) by (destruct (sden_0 _ _ _ _ Hsd) as (_ & _ & _ & _ & _ & _ & X & _); exact X).
    pose proof (eager_le_old E model' (s_facts L) (sm_maps M') HFL Hmaps' Hgsh' Hkind') as He.
    pose proof (A_bytes_allowA E M' Hanz) as Hb. cbn [sm_maps sm_allow M' grow_M] in He, Hb. lia. }
  assert (Hcovrm : forall x, covered (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) x = true ->
                     covered (vm_reserved (m_vmmaps model') ++ vm_maps (m_vmmaps model')) x = true).
  { intros x Hx. rewrite Hvm'. cbn [vm_reserved vm_maps]. rewrite covered_app in *. apply orb_prop in Hx as [Hx|Hx];
      [rewrite Hx; reflexivity | rewrite covered_cons, Hx, !orb_true_r; reflexivity]. }
  assert (Hcovm' : forall x, covered (vm_maps (m_vmmaps model)) x = true -> covered (vm_maps (m_vmmaps model')) x = true)
    by (intros x Hx; rewrite Hcovm, Hx, orb_true_r; reflexivity).
  assert (Htop' : alloc_top (m_vmmaps model') = alloc_top (m_vmmaps model)) by (rewrite Hvm'; reflexivity).
  destruct (sm_wf_parts _ M Hwf) as (Hwg & Hwal & Hwt & Hwb & Hwsb & Hwsp).
  constructor.
  - rewrite HH. exact Hsden.
  - cbn [grow_post s_next]. pose proof (sm_wf_frz _ M Hwf) as Hwz. unfold M', grow_M.
    apply sm_wf_intro; cbn [sm_maps sm_allow sm_tid sm_brk sm_sbrk sm_sp sm_frz sm_own]; try assumption; try apply Forall_nil.
    constructor; [split; [exact Hwb | apply lwf_lconst] |]. pose proof (sm_wf_sizes _ M Hwf) as Hws.
    rewrite Forall_forall in Hwg, Hws |- *. intros q Hq. exact (conj (Hwg q Hq) (Hws q Hq)).
  - cbn [grow_post s_next s_rgs]. unfold bases_wf, RGz in *. cbn [forallb rg_base rg_size]. rewrite lwf_laddc, lwf_lconst by exact Hwb.
    cbn [andb]. exact Hbw.
  - exact Hh.
  - exact Hawf.
  - exact Hanz.
  - rewrite (AM_nil model0 _ _ Hblob0). destruct Hminv as [N1 N2 N3 N4 N5]. constructor; try assumption. rewrite Hvm'. cbn [vm_limit]. rewrite Hlim. exact Hbud'.
  - rewrite HH. exact Hhoff.
  - rewrite Hvm'. exact Hres.
  - rewrite Hvm'. exact Hlim.
  - rewrite Hvm'. exact Hsp.
  - rewrite Hvm'. exact Hspok.
  - rewrite Hvm'. reflexivity.
  - rewrite Hvm'. exact Hsbrk.
  - exact Htid.
  - rewrite (lden_maps_nomark _ _ _ Hnm'). exact Hmaps'.
  - exact Hgsh'.
  - cbn [sm_maps M' grow_M]. constructor; [rewrite gsz_lconst_b by (unfold two64, TOPW in *; lia); cbn [fst snd]; fold u; rewrite Htop'; lia | rewrite Htop'; exact Hgtop].
  - rewrite Hvm', Hlz'. cbn [vm_noaccess]. exact Hivwf.
  - rewrite Hvm'. cbn [vm_maps pdisj]. split; [|exact Hpd]. apply Forall_forall. intros q Hq. destruct q as [bb sz].
    assert (Hq' : In (bb, sz) (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model))) by (apply in_or_app; right; exact Hq).
    destruct (region_free_avoid _ _ _ _ _ Hfree Hq') as [H1|H1]; unfold iv_disj, B, S; cbn [fst snd]; lia.
  - exact Hmres'.
  - exact Hkind'.
  - exact Hlzm'.
  - exact Hzrsh.
  - intros w Hw. exact (Hcovm' w (Hzrm w Hw)).
  - intros w Hw Hout. rewrite adv_eff_mem. fold mem'. unfold outside in Hout. cbn [grow_post s_rgs] in Hout.
    apply Forall_inv_tail in Hout. pose proof (Hzrsh w Hw) as Hws.
    assert (Hw64 : 0 <= w < two64) by (unfold in_shadow, SH_LO, SH_HI in Hws; apply andb_prop in Hws as [H1 H2];
                                        apply Z.leb_le in H1; apply Z.ltb_lt in H2; unfold two64; lia).
    rewrite Hmout by (rewrite fg64 by exact Hw64; unfold in_shadow in Hws; apply andb_prop in Hws as [H1 H2];
                      apply Z.leb_le in H1; apply Z.ltb_lt in H2; unfold SH_LO, SH_HI in *; lia).
    exact (fun _ _ => Hzr w Hw Hout (own_pt_nil E M w Hon)).
  - cbn [grow_post s_rgs]. constructor.
    + assert (Hs64 : 0 <= s < two64) by (unfold TOPW, two64 in *; lia).
      unfold rl_ok. rewrite (rsz_RGz E (laddc (sm_brk M) o) s RZ TEmpty Hs64). unfold RGz. cbn [rg_base].
      assert (HbE0 : uE E (laddc (sm_brk M) o) = u + o) by (unfold uE; rewrite lden_laddc; fold bw; rewrite Hub; apply fg64; unfold TOPW, two64 in *; lia).
      rewrite HbE0. split; [exact Hs|]. left. intros w Hw. split; [left|split].
      * rewrite Hvm'. cbn [vm_reserved vm_maps]. rewrite covered_app, covered_cons, (Hinv' w ltac:(lia)), orb_true_r. reflexivity.
      * apply not_true_iff_false. intros Hsw. unfold in_shadow in Hsw. apply andb_prop in Hsw as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
        unfold SH_LO, SH_HI in *. lia.
      * unfold TOPW in Hhi. lia.
    + rewrite Forall_forall in Hrl |- *. intros R HR. exact (rl_ok_mono E model model' R Hcovrm Hcovm' Htop' (Hrl R HR)).
  - exact Hvmo.
  - exact Hproc.
  - assert (Hgt : u + k <= alloc_top (m_vmmaps model)) by lia.
    apply (frz_keep mem0 E E L (grow_post L a (sm_brk M) o s) M M' ms _ model model' Hwf (agree_refl _ _) eq_refl Htop'); [| | exact Hfrz].
    + intros w Hw Hou. unfold outside in *. cbn [grow_post s_rgs]. constructor; [|exact Hou].
      assert (Hs64 : 0 <= s < two64) by (unfold TOPW, two64 in *; lia).
      right. rewrite (rsz_RGz E (laddc (sm_brk M) o) s RZ TEmpty Hs64). unfold RGz. cbn [rg_base].
      assert (HbE0 : bv_unsigned (lden E (laddc (sm_brk M) o)) = u + o) by (rewrite lden_laddc; fold bw; rewrite Hub; apply fg64; unfold TOPW, two64 in *; lia).
      rewrite HbE0, fg64 by (unfold two64; lia). lia.
    + intros w Hw Hou. rewrite adv_eff_mem. fold mem'. rewrite Hmout; [reflexivity|]. rewrite fg64 by (unfold two64; lia). lia.
  - rom_tac.
  - apply own_nil. reflexivity.
  - rewrite Hblob0. apply blob_ok_nil. exact Hnm'.
Qed.
End Grow.

Definition div4096_lin (l : lin) : bool := (Z.eqb (l_c l mod 4096) 0 && forallb (fun '(_, c) => Z.eqb (c mod 4096) 0) (l_t l))%bool.

Lemma tsum_div4096 : forall E t, forallb (fun '(_, c) => Z.eqb (c mod 4096) 0) t = true -> tsum E t mod 4096 = 0.
Proof.
  intros E t. induction t as [|[x c] t IH]; intros H; [reflexivity|]. cbn [forallb] in H. apply andb_prop in H as [H1 H2].
  apply Z.eqb_eq in H1. cbn [tsum]. rewrite Z.add_mod by lia. rewrite (IH H2), Z.add_0_r. rewrite Z.mul_mod by lia. rewrite H1. reflexivity.
Qed.
Lemma div4096_sound : forall E l, div4096_lin l = true -> bv_unsigned (lden E l) mod 4096 = 0.
Proof.
  intros E l H. unfold div4096_lin in H. apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1.
  rewrite u_lden_mod. rewrite Z.mod_mod_divide by (unfold two64; exists 4503599627370496; lia).
  unfold lz. rewrite Z.add_mod, H1, (tsum_div4096 E _ H2) by lia. reflexivity.
Qed.

Definition brkgrow_ok (LIMIT : Z) (L : sst) (M : smodel) (k o s : Z) : bool :=
  let fs := s_facts L in let a := rget (s_regs L) (rkey a0r) in
  match a7c L, lin_off a (sm_brk M), lin_off (sm_brk M) (sm_sbrk M) with
  | Some c7, Some k', Some d =>
      (Z.eqb c7 214 && Z.eqb k' k && Z.ltb 0 k && Z.eqb (k mod 4096) 0 && div4096_lin (sm_brk M) &&
       Z.ltb 0 (fst (irange fs (sm_brk M))) && Z.leb 0 d && Z.ltb (snd (irange fs (sm_sbrk M)) + d + k) 0x800000000000 &&
       Z.leb 0 o && Z.ltb 0 s && Z.leb (o + s) k && shadow_ok M && lwf (s_next L) a &&
       Z.leb (eager_sum fs ((sm_brk M, lconst k, GE) :: sm_maps M) + allow_bound (sm_allow M)) LIMIT &&
       nomark ((sm_brk M, lconst k, GE) :: sm_maps M))%bool      (* [comment removed for export] *)
  | _, _, _ => false
  end.

Section GrowNode.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.
Hypothesis Hsegb : segs_below_b segs 0x800000000000 = true.
Hypothesis Hoff : sc_alloc cfg = false.

#[using="Hoff"] Theorem den_brkgrow : forall E L M ms model T k o s,
  DEN segs LIMIT model0 mem0 E L M ms model -> sm_own M = [] -> brkgrow_ok LIMIT L M k o s = true ->
  (forall ms' model', DEN segs LIMIT model0 mem0 E (grow_post L (rget (s_regs L) (rkey a0r)) (sm_brk M) o s)
                        (grow_M M (rget (s_regs L) (rkey a0r)) k) ms' model' -> realizes_cfg segs cfg (mkCfg ms' model') T) ->
  (forall ms' model', DEN segs LIMIT model0 mem0 E (ret_post L (sm_brk M)) M ms' model' -> realizes_cfg segs cfg (mkCfg ms' model') T) ->
  realizes_cfg segs cfg (mkCfg (svc_set ms) model) T.
Proof. LiaFast.lf_pins (fun (Hoff : LiaFast.U) => LiaFast.u0).
  intros E L M ms model T k o s Hd Hon Hok Kok Kfail. unfold brkgrow_ok in Hok. set (a := rget (s_regs L) (rkey a0r)) in *.
  destruct (a7c L) as [c7|] eqn:H7; [|discriminate]. destruct (lin_off a (sm_brk M)) as [k'|] eqn:Hk'; [|discriminate].
  destruct (lin_off (sm_brk M) (sm_sbrk M)) as [d|] eqn:Hdd; [|discriminate].
  apply andb_prop in Hok as [Hok Hnm'].
  apply andb_prop in Hok as [Hok Hbud]. apply Z.leb_le in Hbud. apply andb_prop in Hok as [Hok Hwa].
  apply andb_prop in Hok as [Hok Hsh]. apply andb_prop in Hok as [Hok Hos]. apply Z.leb_le in Hos.
  apply andb_prop in Hok as [Hok Hs]. apply Z.ltb_lt in Hs. apply andb_prop in Hok as [Hok Ho]. apply Z.leb_le in Ho.
  apply andb_prop in Hok as [Hok Hnw]. apply Z.ltb_lt in Hnw. apply andb_prop in Hok as [Hok Hd0]. apply Z.leb_le in Hd0.
  apply andb_prop in Hok as [Hok Hbpos]. apply Z.ltb_lt in Hbpos. apply andb_prop in Hok as [Hok Hbal].
  apply andb_prop in Hok as [Hok Hkal]. apply Z.eqb_eq in Hkal. apply andb_prop in Hok as [Hok Hk0]. apply Z.ltb_lt in Hk0.
  apply andb_prop in Hok as [Hc7 Hkk]. apply Z.eqb_eq in Hc7, Hkk. subst c7 k'.
  pose proof Hd as Hd0'. destruct Hd0' as [Hsd _ _ Hh _ _ _ _ _ _ _ Hspok Hbrk Hsbrk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _].
  destruct (sden_0 _ _ _ _ Hsd) as (_ & _ & _ & _ & _ & _ & HF0 & _).
  set (H := Hof E M model) in *.
  pose proof (irange_sound E (s_facts L) (sm_brk M) HF0) as Ib. pose proof (irange_sound E (s_facts L) (sm_sbrk M) HF0) as Isb.
  pose proof (div4096_sound E _ Hbal) as Hal.
  assert (Hbs : uE E (sm_brk M) = uE E (sm_sbrk M) + d) by (unfold uE; apply (lin_off_u E _ _ d Hdd); unfold two64; lia).
  assert (Hua : uE E a = uE E (sm_brk M) + k) by (unfold uE; apply (lin_off_u E _ _ k Hk'); unfold uE in *; unfold two64; lia).
  assert (Hx8 : ms_reg ms 17 = Z_to_bv 64 214) by exact (a7_const segs E L (restrict H ms) ms 214 Hsd eq_refl H7).
  assert (Hg0 : ms_gpr (svc_set ms) 0 = lden E a) by exact (gpr_lin segs E L (restrict H ms) ms Hsd eq_refl).
  assert (Hnz : w_is0 (lden E a) = false).
  { unfold w_is0, bv_eqb. apply Z.eqb_neq. rewrite fg64 by (unfold two64; lia). change (bv_unsigned (lden E a)) with (uE E a). unfold uE in *. lia. }
  assert (Hmin : bv_unsigned (min_brk (m_vmmaps model)) <= bv_unsigned (lden E a)).
  { unfold min_brk. rewrite Hsbrk. change (bv_unsigned (lden E a)) with (uE E a). change (bv_unsigned (lden E (sm_sbrk M))) with (uE E (sm_sbrk M)). lia. }
  assert (Hgt : bv_unsigned (vm_brk (m_vmmaps model)) < bv_unsigned (lden E a)).
  { rewrite Hbrk. change (bv_unsigned (lden E a)) with (uE E a). change (bv_unsigned (lden E (sm_brk M))) with (uE E (sm_brk M)). lia. }
  destruct (brk_grow_ok model (lden E a) (lden E a)) eqn:Hgrow.
  - destruct (brk_grow_shape model (lden E a) k ltac:(rewrite Hbrk; unfold uE in *; lia) ltac:(rewrite Hbrk; exact Hal) Hk0 Hkal
                ltac:(rewrite Hbrk; change (bv_unsigned (lden E a)) with (uE E a); unfold uE in *; lia)
                ltac:(rewrite Hbrk; unfold uE, two64 in *; lia)) as [Heff Hnext].
    pose proof (grow_den segs LIMIT model0 mem0 E L M ms model a k o s Hd Hwa Hsh Hua ltac:(unfold uE in *; lia) Hal Hk0 Hkal Ho Hs Hos Hgrow Hbud Hon Hnm') as HD'.
    eapply rzc_silent1; [|exact (Kok _ _ HD')].
    pose proof (node_brk_grow segs cfg Hoff (svc_set ms) model (ms_reg ms 17) (lden E a) Hh eq_refl ltac:(rewrite Hx8; reflexivity) Hg0 Hnz Hmin Hgt Hgrow) as Hn.
    rewrite Heff, Hnext, Hbrk in Hn. exact Hn.
  - pose proof (den_ret segs LIMIT model0 mem0 E L M ms model (sm_brk M) Hd ltac:(destruct (sm_wf_parts _ M (dn_wf _ _ _ _ _ _ _ _ _ Hd)) as (_ & _ & _ & Hwb & _); exact Hwb)) as HD'.
    rewrite <- Hbrk in HD'.
    eapply rzc_silent1; [|exact (Kfail _ _ HD')].
    exact (node_brk_grow_forced_fail segs cfg (svc_set ms) model (ms_reg ms 17) (lden E a) Hh eq_refl ltac:(rewrite Hx8; reflexivity) Hg0 Hnz Hmin Hgt Hgrow).
Qed.
End GrowNode.
End FxChBrk.

Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChSep OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChSeg OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChNode OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFix.FxChNorep OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFix OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChAdd OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMprot.FxChBrk.

Module AcAddOwn.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Run Specs.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg SysNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop FxPlan FxFrame FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.FxAcct.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChFix.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChFix.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChSeg OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChNode OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFix.FxChNorep OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFix.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition addo_post (S : sst) (R : region) : sst := SST (s_pc S) (s_regs S) (R :: s_rgs S) (s_facts S) (s_next S) (s_resv S).
(* [comment removed for export] *)
Definition cont_bk (c : tree bval) : Prop := forall p v, tget p c = Some v -> exists b, v = BK b.

Fixpoint remove_nth {A} (i : nat) (l : list A) : list A :=
  match l, i with [] , _ => [] | _ :: r, O => r | x :: r, Datatypes.S i' => x :: remove_nth i' r end.
Lemma In_remove_nth : forall {A} i (l : list A) x, In x (remove_nth i l) -> In x l.
Proof. intros A i. induction i as [|i IH]; intros [|y r] x H; cbn in H; try (destruct H); [right; exact H | left; exact H | right; exact (IH r x H)]. Qed.
Lemma nth_remove_cases : forall {A} i (l : list A) R x, nth_error l i = Some R -> In x l -> x = R \/ In x (remove_nth i l).
Proof.
  intros A i. induction i as [|i IH]; intros [|y r] R x HR Hx; cbn in HR; try discriminate.
  - injection HR as <-. destruct Hx as [<-|Hx]; [left; reflexivity | right; exact Hx].
  - destruct Hx as [<-|Hx]; [right; left; reflexivity|]. destruct (IH r R x HR Hx) as [->|H]; [left; reflexivity | right; right; exact H].
Qed.
Lemma rgs_disj_remove : forall E i rgs, rgs_disj E rgs -> rgs_disj E (remove_nth i rgs).
Proof.
  intros E i. induction i as [|i IH]; intros [|R rs] H; cbn [remove_nth]; try exact I.
  - exact (proj2 H).
  - destruct H as [H1 H2]. split; [|exact (IH rs H2)]. apply Forall_forall. intros x Hx. rewrite Forall_forall in H1. exact (H1 x (In_remove_nth i rs x Hx)).
Qed.
Definition dropo_post (S : sst) (i : nat) : sst := SST (s_pc S) (s_regs S) (remove_nth i (s_rgs S)) (s_facts S) (s_next S) (s_resv S).

Section AddOwn.
Variable segs : list Segment.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.

(* [comment removed for export] *)
#[using="Type"] Theorem den_add_own_v0 : forall E S M ms model (R : region),
  DEN segs LIMIT model0 mem0 E S M ms model ->
  lwf (s_next S) (rg_base R) = true -> lwf (s_next S) (rg_size R) = true ->
  (rg_kind R = RW \/ (rg_kind R = RZ /\ forall x, uE E (rg_base R) <= x < uE E (rg_base R) + rsz E R ->
                                          tget (okey (x - uE E (rg_base R))) (rg_cont R) = None -> ms_mem ms (Z_to_bv 64 x) = Some (Z_to_bv 8 0))) ->
  0 < rsz E R -> uE E (rg_base R) + rsz E R <= 0x800000000000 ->
  (forall x, uE E (rg_base R) <= x < uE E (rg_base R) + rsz E R -> own_pt E M x /\ ms_mem ms (Z_to_bv 64 x) <> None /\ x < alloc_top (m_vmmaps model)) ->
  (forall p v, tget p (rg_cont R) = Some v -> bwf (s_next S) v = true /\ Zpos p - 1 < rsz E R /\
               ms_mem ms (Z_to_bv 64 (uE E (rg_base R) + (Zpos p - 1))) = Some (bden E v)) ->
  (forall R', In R' (s_rgs S) -> forall w, uE E (rg_base R') <= w < uE E (rg_base R') + rsz E R' -> ~ (uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R)) ->
  rl_ok E model R ->
  DEN segs LIMIT model0 mem0 E (addo_post S R) M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model R Hd Hwb Hwz Hk Hpos Htop Hpts Hcont Hsep Hrl0.
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  set (H := Hof E M model) in *.
  pose proof (u_lt (lden E (rg_base R))) as Ra.
  assert (Hvis : forall x, uE E (rg_base R) <= x < uE E (rg_base R) + rsz E R -> H (Z_to_bv 64 x) = false).
  { intros x Hx. destruct (Hpts x Hx) as ((q & Hq & Hqw) & _). exact (proj1 (Hown q Hq x Hqw)). }
  assert (Hsden : sden segs E (addo_post S R) (restrict H ms)).
  { intros E'' Ha''. cbn [addo_post s_next] in Ha''.
    destruct (Hsd E'' Ha'') as (Hpc1 & Hsv1 & Hrv & HR & HG & HD & HF & Hfrm).
    assert (HbE : forall R', In R' (s_rgs S) -> uE E'' (rg_base R') = uE E (rg_base R') /\ rsz E'' R' = rsz E R').
    { intros R' HR'. unfold uE, rsz. unfold bases_wf in Hbw. rewrite forallb_forall in Hbw. destruct (andb_prop _ _ (Hbw R' HR')) as [Hb1 Hb2].
      rewrite (lden_agree_wf _ E E'' _ Hb1 Ha''), (lden_agree_wf _ E E'' _ Hb2 Ha''). split; reflexivity. }
    assert (HaE : uE E'' (rg_base R) = uE E (rg_base R)) by (unfold uE; rewrite (lden_agree_wf _ E E'' _ Hwb Ha''); reflexivity).
    assert (HzE : rsz E'' R = rsz E R) by (unfold rsz; rewrite (lden_agree_wf _ E E'' _ Hwz Ha''); reflexivity).
    unfold sden0, addo_post. cbn [s_pc s_regs s_rgs s_facts s_resv].
    split; [exact Hpc1|]. split; [exact Hsv1|]. split; [exact Hrv|]. split; [exact HR|].
    split; [|split; [|split; [exact HF | exact Hfrm]]].
    - constructor; [|exact HG].
      unfold rg_ok. cbv zeta. change (bv_unsigned (lden E'' (rg_base R))) with (uE E'' (rg_base R)). rewrite HaE, HzE.
      split; [lia|]. split; [unfold two64; lia|]. split.
      + intros i Hi. destruct (Hpts (uE E (rg_base R) + i) ltac:(lia)) as (_ & Hm & _).
        assert (Hr : ms_mem (restrict H ms) (Z_to_bv 64 (uE E (rg_base R) + i)) = ms_mem ms (Z_to_bv 64 (uE E (rg_base R) + i))).
        { cbn [restrict ms_mem]. unfold mrestrict. rewrite (Hvis (uE E (rg_base R) + i) ltac:(lia)). reflexivity. }
        assert (Hrw : rd1 segs (ms_mem (restrict H ms)) (Z_to_bv 64 (uE E (rg_base R) + i)) <> None /\
                      wview segs (ms_mem (restrict H ms)) (Z_to_bv 64 (uE E (rg_base R) + i)) <> None).
        { unfold rd1, wview. rewrite Hr. destruct (ms_mem ms (Z_to_bv 64 (uE E (rg_base R) + i))); [split; discriminate | contradiction]. }
        destruct Hk as [Hk|[Hk Hzero]]; rewrite Hk; [exact Hrw|]. split; [exact Hrw|]. intros Ht. unfold rd1. rewrite Hr.
        rewrite (Hzero (uE E (rg_base R) + i) ltac:(lia) ltac:(replace (uE E (rg_base R) + i - uE E (rg_base R)) with i by ring; exact Ht)). reflexivity.
      + intros p v Hp. destruct (Hcont p v Hp) as (C0 & C1 & C2). split; [exact C1|]. rewrite <- (bden_agree _ E E'' v C0 Ha'').
        assert (Hr : ms_mem (restrict H ms) (Z_to_bv 64 (uE E (rg_base R) + (Z.pos p - 1))) = ms_mem ms (Z_to_bv 64 (uE E (rg_base R) + (Z.pos p - 1)))).
        { cbn [restrict ms_mem]. unfold mrestrict. rewrite (Hvis (uE E (rg_base R) + (Z.pos p - 1)) ltac:(lia)). reflexivity. }
        unfold rd1. rewrite Hr, C2. reflexivity.
    - cbn [rgs_disj]. split; [|exact HD]. apply Forall_forall. intros R2 H2. unfold rg_disj. cbv zeta.
      change (bv_unsigned (lden E'' (rg_base R))) with (uE E'' (rg_base R)). change (bv_unsigned (lden E'' (rg_base R2))) with (uE E'' (rg_base R2)).
      rewrite HaE, HzE, (proj1 (HbE R2 H2)), (proj2 (HbE R2 H2)).
      pose proof Hrl as Hrl2. rewrite Forall_forall in Hrl2. destruct (Hrl2 R2 H2) as [Hpos2 _].
      apply iv_pts_disj; [lia | lia|]. intros w Hw1 Hw2. exact (Hsep R2 H2 w Hw2 Hw1). }
  constructor.
  - exact Hsden.
  - exact Hwf.
  - cbn [addo_post s_next s_rgs]. unfold bases_wf. cbn [forallb]. rewrite Hwb, Hwz. exact Hbw.
  - exact Hh.
  - exact Hawf.
  - exact Hanz.
  - exact Hminv.
  - exact Hhoff.
  - exact Hres.
  - exact Hlim.
  - exact Hsp.
  - exact Hspok.
  - exact Hbrk.
  - exact Hsbrk.
  - exact Htid.
  - exact Hmaps.
  - exact Hgsh.
  - exact Hgtop.
  - exact Hivwf.
  - exact Hpd.
  - exact Hmres.
  - exact Hkind.
  - exact Hlzm.
  - exact Hzrsh.
  - exact Hzrm.
  - intros w Hw Hout Hnow Hnb. cbn [addo_post s_rgs] in Hout. unfold outside in Hout. apply Forall_inv_tail in Hout. exact (Hzr w Hw Hout Hnow Hnb).
  - cbn [addo_post s_rgs]. constructor; [exact Hrl0 | exact Hrl].
  - exact Hvmo.
  - exact Hproc.
  - pose proof (alloc_top_lo _ (proj1 Hspok)) as Hatl.
    apply (frz_keep mem0 E E S (addo_post S R) M M ms ms model model Hwf (agree_refl _ _) eq_refl eq_refl); [| | exact Hfrz].
    + intros w Hw Ho. unfold outside in *. cbn [addo_post s_rgs]. constructor; [|exact Ho].
      assert (Hw64 : bv_unsigned (Z_to_bv 64 w) = w) by (apply fg64; unfold two64; lia). rewrite Hw64.
      right. fold (uE E (rg_base R)). destruct (Hpts (uE E (rg_base R) + rsz E R - 1) ltac:(lia)) as (_ & _ & Hlt). lia.
    + intros w _ _. reflexivity.
  - rom_tac.
  - apply (own_keep mem0 E E S (addo_post S R) M M ms ms model model Hwf (agree_refl _ _) eq_refl); [| | | exact Hown].
    + intros w Ho. unfold outside in Ho. cbn [addo_post s_rgs] in Ho. exact (Forall_inv_tail Ho).
    + intros w _. reflexivity.
    + intros x Hx. exact Hx.
  - exact Hblob.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem den_add_own_v : forall E S M ms model (R : region),
  DEN segs LIMIT model0 mem0 E S M ms model ->
  lwf (s_next S) (rg_base R) = true -> lwf (s_next S) (rg_size R) = true ->
  (rg_kind R = RW \/ (rg_kind R = RZ /\ forall x, uE E (rg_base R) <= x < uE E (rg_base R) + rsz E R ->
                                          tget (okey (x - uE E (rg_base R))) (rg_cont R) = None -> ms_mem ms (Z_to_bv 64 x) = Some (Z_to_bv 8 0))) ->
  (forall p v, tget p (rg_cont R) = Some v -> bwf (s_next S) v = true) ->
  0 < rsz E R -> uE E (rg_base R) + rsz E R <= 0x800000000000 ->
  (forall x, uE E (rg_base R) <= x < uE E (rg_base R) + rsz E R -> own_pt E M x /\ ms_mem ms (Z_to_bv 64 x) <> None /\ x < alloc_top (m_vmmaps model)) ->
  (forall p v, tget p (rg_cont R) = Some v -> Zpos p - 1 < rsz E R /\ ms_mem ms (Z_to_bv 64 (uE E (rg_base R) + (Zpos p - 1))) = Some (bden E v)) ->
  (forall R', In R' (s_rgs S) -> forall w, uE E (rg_base R') <= w < uE E (rg_base R') + rsz E R' -> ~ (uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R)) ->
  rl_ok E model R ->
  DEN segs LIMIT model0 mem0 E (addo_post S R) M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model R Hd Hwb Hwz Hk Hbw Hpos Htop Hpts Hcont Hsep Hrl0.
  apply (den_add_own_v0 E S M ms model R Hd Hwb Hwz Hk Hpos Htop Hpts); [|exact Hsep | exact Hrl0].
  intros p v Hp. destruct (Hcont p v Hp) as [C1 C2]. split; [exact (Hbw p v Hp)|]. split; [exact C1 | exact C2].
Qed.
#[using="Type"] Theorem den_add_own_g : forall E S M ms model (R : region),
  DEN segs LIMIT model0 mem0 E S M ms model ->
  lwf (s_next S) (rg_base R) = true -> lwf (s_next S) (rg_size R) = true ->
  (rg_kind R = RW \/ (rg_kind R = RZ /\ forall x, uE E (rg_base R) <= x < uE E (rg_base R) + rsz E R ->
                                          tget (okey (x - uE E (rg_base R))) (rg_cont R) = None -> ms_mem ms (Z_to_bv 64 x) = Some (Z_to_bv 8 0))) ->
  cont_bk (rg_cont R) ->
  0 < rsz E R -> uE E (rg_base R) + rsz E R <= 0x800000000000 ->
  (forall x, uE E (rg_base R) <= x < uE E (rg_base R) + rsz E R -> own_pt E M x /\ ms_mem ms (Z_to_bv 64 x) <> None /\ x < alloc_top (m_vmmaps model)) ->
  (forall p b, tget p (rg_cont R) = Some (BK b) -> Zpos p - 1 < rsz E R /\ ms_mem ms (Z_to_bv 64 (uE E (rg_base R) + (Zpos p - 1))) = Some (Z_to_bv 8 b)) ->
  (forall R', In R' (s_rgs S) -> forall w, uE E (rg_base R') <= w < uE E (rg_base R') + rsz E R' -> ~ (uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R)) ->
  rl_ok E model R ->
  DEN segs LIMIT model0 mem0 E (addo_post S R) M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model R Hd Hwb Hwz Hk Hbk Hpos Htop Hpts Hcont Hsep Hrl0.
  apply (den_add_own_v0 E S M ms model R Hd Hwb Hwz Hk Hpos Htop Hpts); [|exact Hsep | exact Hrl0].
  intros p v Hp. destruct (Hbk p v Hp) as (b & ->). destruct (Hcont p b Hp) as [C1 C2]. split; [reflexivity|]. split; [exact C1 | exact C2].
Qed.
#[using="Type"] Theorem den_add_own : forall E S M ms model (R : region),
  DEN segs LIMIT model0 mem0 E S M ms model ->
  lwf (s_next S) (rg_base R) = true -> lwf (s_next S) (rg_size R) = true -> rg_kind R = RW -> cont_bk (rg_cont R) ->
  0 < rsz E R -> uE E (rg_base R) + rsz E R <= 0x800000000000 ->
  (forall x, uE E (rg_base R) <= x < uE E (rg_base R) + rsz E R -> own_pt E M x /\ ms_mem ms (Z_to_bv 64 x) <> None /\ x < alloc_top (m_vmmaps model)) ->
  (forall p b, tget p (rg_cont R) = Some (BK b) -> Zpos p - 1 < rsz E R /\ ms_mem ms (Z_to_bv 64 (uE E (rg_base R) + (Zpos p - 1))) = Some (Z_to_bv 8 b)) ->
  (forall R', In R' (s_rgs S) -> forall w, uE E (rg_base R') <= w < uE E (rg_base R') + rsz E R' -> ~ (uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R)) ->
  rl_ok E model R ->
  DEN segs LIMIT model0 mem0 E (addo_post S R) M ms model.
Proof. LiaFast.lf_pins LiaFast.u0. intros E S M ms model R Hd Hwb Hwz Hk. exact (den_add_own_g E S M ms model R Hd Hwb Hwz (or_introl Hk)). Qed.
(* [comment removed for export] *)
#[using="Type"] Theorem den_add_own_z : forall E S M ms model (R : region),
  DEN segs LIMIT model0 mem0 E S M ms model ->
  lwf (s_next S) (rg_base R) = true -> lwf (s_next S) (rg_size R) = true -> rg_kind R = RZ -> rg_cont R = TEmpty ->
  0 < rsz E R -> uE E (rg_base R) + rsz E R <= 0x800000000000 ->
  (forall x, uE E (rg_base R) <= x < uE E (rg_base R) + rsz E R -> own_pt E M x /\ ms_mem ms (Z_to_bv 64 x) = Some (Z_to_bv 8 0) /\ x < alloc_top (m_vmmaps model)) ->
  (forall R', In R' (s_rgs S) -> forall w, uE E (rg_base R') <= w < uE E (rg_base R') + rsz E R' -> ~ (uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R)) ->
  rl_ok E model R ->
  DEN segs LIMIT model0 mem0 E (addo_post S R) M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model R Hd Hwb Hwz Hk Hc Hpos Htop Hpts Hsep Hrl0.
  apply (den_add_own_g E S M ms model R Hd Hwb Hwz); [| | exact Hpos | exact Htop | | | exact Hsep | exact Hrl0].
  - right. split; [exact Hk|]. intros x Hx _. exact (proj1 (proj2 (Hpts x Hx))).
  - rewrite Hc. intros p v Hp. rewrite tget_empty in Hp. discriminate.
  - intros x Hx. destruct (Hpts x Hx) as (P1 & P2 & P3). split; [exact P1|]. split; [rewrite P2; discriminate | exact P3].
  - rewrite Hc. intros p b Hp. rewrite tget_empty in Hp. discriminate.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem den_drop_own : forall E S M ms model i R,
  DEN segs LIMIT model0 mem0 E S M ms model -> nth_error (s_rgs S) i = Some R ->
  (forall w, uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R -> own_pt E M w /\ ms_mem ms (Z_to_bv 64 w) = mem0 (Z_to_bv 64 w)) ->
  DEN segs LIMIT model0 mem0 E (dropo_post S i) M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model i R Hd HR Hpts.
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  pose proof (sden_0 _ _ _ _ Hsd) as (_ & _ & _ & _ & HG0 & _).
  assert (HRw : 0 <= rsz E R /\ uE E (rg_base R) + rsz E R <= two64).
  { rewrite Forall_forall in HG0. destruct (HG0 R (nth_error_In _ _ HR)) as (Hs & Hw & _). unfold uE. lia. }
  (* [comment removed for export] *)
  assert (Hcase : forall x : word, outside E (remove_nth i (s_rgs S)) x ->
            outside E (s_rgs S) x \/ uE E (rg_base R) <= bv_unsigned x < uE E (rg_base R) + rsz E R).
  { intros x Hout. destruct (Z_lt_le_dec (bv_unsigned x) (uE E (rg_base R))) as [H1|H1];
      [left | destruct (Z_lt_le_dec (bv_unsigned x) (uE E (rg_base R) + rsz E R)) as [H2|H2]; [right; lia | left]].
    all: unfold outside in *; apply Forall_forall; intros y Hy; rewrite Forall_forall in Hout.
    all: destruct (nth_remove_cases i (s_rgs S) R y HR Hy) as [->|Hy']; [unfold uE in *; lia | exact (Hout y Hy')]. }
  constructor; try assumption.
  - intros E'' Ha''. cbn [dropo_post s_next] in Ha''. destruct (Hsd E'' Ha'') as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
    unfold sden0, dropo_post. cbn [s_pc s_regs s_rgs s_facts s_resv]. repeat split; try assumption.
    + apply Forall_forall. intros x Hx. rewrite Forall_forall in H5. exact (H5 x (In_remove_nth i _ x Hx)).
    + exact (rgs_disj_remove E'' i _ H6).
  - unfold bases_wf in *. cbn [dropo_post s_rgs s_next]. rewrite forallb_forall in *. intros x Hx. exact (Hbw x (In_remove_nth i _ x Hx)).
  - intros w Hw Hout Hnow Hnb. cbn [dropo_post s_rgs] in Hout.
    pose proof (Hzrsh w Hw) as Hs. unfold in_shadow, SH_LO, SH_HI in Hs. apply andb_prop in Hs as [Hs1 Hs2]. apply Z.leb_le in Hs1. apply Z.ltb_lt in Hs2.
    destruct (Hcase _ Hout) as [Ho|Hin]; [exact (Hzr w Hw Ho Hnow Hnb)|]. rewrite fg64 in Hin by (unfold two64; lia). exfalso. exact (Hnow (proj1 (Hpts w Hin))).
  - rewrite Forall_forall in *. intros x Hx. exact (Hrl x (In_remove_nth i _ x Hx)).
  - apply (frz_keep mem0 E E S (dropo_post S i) M M ms ms model model Hwf (agree_refl _ _) eq_refl eq_refl); [| | exact Hfrz].
    + intros w _ Ho. unfold outside in *. cbn [dropo_post s_rgs]. apply Forall_forall. intros x Hx. rewrite Forall_forall in Ho. exact (Ho x (In_remove_nth i _ x Hx)).
    + intros w _ _. reflexivity.
  - intros q Hq w Hw. destruct (Hown q Hq w Hw) as [Hv Hm]. split; [exact Hv|]. intros Hout. cbn [dropo_post s_rgs] in Hout.
    destruct (Hcase _ Hout) as [Ho|Hin]; [exact (Hm Ho)|].
    pose proof (proj2 (Hpts _ Hin)) as X. rewrite Z_to_bv_bv_unsigned in X. exact X.
Qed.
End AddOwn.
(* [comment removed for export] *)
End AcAddOwn.

Module FxChAllow.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Run Specs.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg SysNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop FxPlan FxFrame FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.FxAcct.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChFix.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChFix FxChAdd.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChSeg OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChNode OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFix.FxChNorep OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFix OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChAdd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition allow_ins (M : smodel) (k : nat) (p : lin * Z) : smodel :=
  SM (sm_maps M) (firstn k (sm_allow M) ++ p :: skipn k (sm_allow M)) (sm_zr M) (sm_tid M) (sm_brk M) (sm_sbrk M) (sm_sp M) (sm_frz M) (sm_own M).
Definition allow_ins_ok (LIMIT : Z) (n : positive) (M : smodel) (k : nat) (p : lin * Z) : bool :=
  (Z.leb 0 (snd p) && lwf n (fst p) && Z.leb (eager_sum [] (sm_maps M) + allow_bound (sm_allow (allow_ins M k p))) LIMIT)%bool.

Lemma page_allowedb_ins : forall (A : list (Z * Z)) k x p, page_allowedb A p = true -> page_allowedb (firstn k A ++ x :: skipn k A) p = true.
Proof.
  intros A k x p H. unfold page_allowedb in *. rewrite existsb_app. cbn [existsb].
  rewrite <- (firstn_skipn k A) in H. rewrite existsb_app in H. apply orb_prop in H as [H|H]; rewrite H; [reflexivity|].
  rewrite !orb_true_r. reflexivity.
Qed.
Lemma allowA_ins : forall E M k p, allowA E (allow_ins M k p) = firstn k (allowA E M) ++ allow1 E p :: skipn k (allowA E M).
Proof. intros E M k p. unfold allowA, allow_ins. cbn [sm_allow]. rewrite map_app, firstn_map, skipn_map. reflexivity. Qed.
Lemma Forall_ins : forall {X} (P : X -> Prop) (l : list X) k x, Forall P l -> P x -> Forall P (firstn k l ++ x :: skipn k l).
Proof.
  intros X P l k x H Hx. rewrite <- (firstn_skipn k l) in H. apply Forall_app in H as [H1 H2].
  apply Forall_app. split; [exact H1 | constructor; [exact Hx | exact H2]].
Qed.
Lemma forallb_ins : forall {X} (f : X -> bool) (l : list X) k x, forallb f l = true -> f x = true -> forallb f (firstn k l ++ x :: skipn k l) = true.
Proof.
  intros X f l k x H Hx. rewrite <- (firstn_skipn k l) in H. rewrite forallb_app in H |- *. apply andb_prop in H as [H1 H2].
  cbn [forallb]. rewrite H1, Hx, H2. reflexivity.
Qed.

Section Allow.
Variable segs : list Segment.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.

#[using="Type"] Theorem den_allow_ins : forall E S M ms model k p,
  DEN segs LIMIT model0 mem0 E S M ms model -> allow_ins_ok LIMIT (s_next S) M k p = true ->
  DEN segs LIMIT model0 mem0 E S (allow_ins M k p) ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model k p Hd Hok. unfold allow_ins_ok in Hok.
  apply andb_prop in Hok as [Hok Hbud]. apply andb_prop in Hok as [Hz0 Hwp]. apply Z.leb_le in Hz0, Hbud.
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  set (M' := allow_ins M k p).
  set (H := Hof E M model) in *.
  set (H' := Hof E M' model).
  assert (HH' : forall w, H w = false -> H' w = false).
  { intros w Hw. unfold H', Hof. unfold M'. rewrite allowA_ins. unfold H, Hof in Hw. unfold mkH in *.
    destruct (page_in_ranges (page_base w) (m_vm_lazy model)); [|reflexivity]. cbn [andb] in *.
    apply negb_false_iff in Hw. apply negb_false_iff. apply page_allowedb_ins. exact Hw. }
  assert (Hsd0 := sden_0 _ _ _ _ Hsd). destruct Hsd0 as (Hpc0 & Hsv0 & Hrv0 & HR0 & HG0 & HD0 & HF0 & Hfrm0).
  assert (Hpt : forall R, In R (s_rgs S) -> forall i, 0 <= i < rsz E R ->
             mrestrict H' (ms_mem ms) (Z_to_bv 64 (uE E (rg_base R) + i)) = mrestrict H (ms_mem ms) (Z_to_bv 64 (uE E (rg_base R) + i))).
  { intros R HR i Hi. rewrite Forall_forall in HG0. pose proof (rg_ok_visible segs H (ms_mem ms) E R Hhoff (HG0 R HR) i Hi) as Hv.
    unfold mrestrict. rewrite Hv, (HH' _ Hv). reflexivity. }
  assert (Hanz' : Forall (fun q => 0 <= snd q) (sm_allow M')) by (unfold M', allow_ins; cbn [sm_allow]; apply Forall_ins; [exact Hanz | exact Hz0]).
  constructor.
  - intros E'' Ha''. destruct (Hsd E'' Ha'') as (Hpc1 & Hsv1 & Hrv & HR & HG & HD & HF & Hfrm).
    assert (HbE : forall R, In R (s_rgs S) -> uE E'' (rg_base R) = uE E (rg_base R) /\ rsz E'' R = rsz E R).
    { intros R HR'. unfold uE, rsz. unfold bases_wf in Hbw. rewrite forallb_forall in Hbw. destruct (andb_prop _ _ (Hbw R HR')) as [Hb1 Hb2].
      rewrite (lden_agree_wf _ E E'' _ Hb1 Ha''), (lden_agree_wf _ E E'' _ Hb2 Ha''). split; reflexivity. }
    unfold sden0. split; [exact Hpc1|]. split; [exact Hsv1|]. split; [exact Hrv|]. split; [exact HR|].
    split; [|split; [exact HD | split; [exact HF | exact Hfrm]]].
    apply Forall_forall. intros R HR'. rewrite Forall_forall in HG. apply (rg_ok_mem_eq segs E'' (ms_mem (restrict H ms))); [exact (HG R HR')|].
    intros i Hi. rewrite (proj2 (HbE R HR')) in Hi. rewrite (proj1 (HbE R HR')). cbn [ms_mem restrict]. exact (Hpt R HR' i Hi).
  - destruct (sm_wf_parts _ M Hwf) as (Hwg & Hwa & Hwt & Hwb & Hwsb & Hwsp).
    unfold sm_wf in Hwf |- *. unfold M', allow_ins. cbn [sm_maps sm_allow sm_tid sm_brk sm_sbrk sm_sp sm_frz sm_own] in *.
    repeat match type of Hwf with ((_ && _)%bool = true) => apply andb_prop in Hwf as [Hwf ?Hx] end.
    repeat match goal with Hx : (_ && _)%bool = true |- _ => apply andb_prop in Hx as [? ?] end.
    rewrite (forallb_ins (fun g => lwf (s_next S) (fst g)) (sm_allow M) k p) by assumption.
    repeat match goal with Hx : ?e = true |- context [?e] => rewrite Hx end. reflexivity.
  - exact Hbw.
  - exact Hh.
  - unfold M'. rewrite allowA_ins. unfold A_wf in *. apply Forall_ins; [exact Hawf|].
    destruct (allow1_wf E p Hz0) as (W1 & W2 & W3). unfold page_size. split; [exact W1|]. split; [exact W2 | exact W3].
  - exact Hanz'.
  - destruct Hminv as [Mn Ma Mal Mlz Mb]. constructor.
    + exact Mn.
    + exact Ma.
    + intros q Hq. specialize (Mal q Hq). unfold AM in *. unfold M'. rewrite allowA_ins. unfold page_allowedb in *. rewrite existsb_app in *.
      apply orb_prop in Mal as [Mal|Mal]; [|rewrite Mal, orb_true_r; reflexivity].
      apply orb_true_iff. left. pose proof (page_allowedb_ins (allowA E M) k (allow1 E p) q) as X. unfold page_allowedb in X. exact (X Mal).
    + exact Mlz.
    + pose proof (eager_le E M model [] _ (Forall_nil _) Hmaps Hgsh Hkind Hblob) as He. pose proof (A_bytes_allowA E M' Hanz') as Hb.
      rewrite Hlim. unfold AM. rewrite A_bytes_app. unfold M' in Hb |- *. cbn [sm_allow allow_ins] in Hb, Hbud. lia.
  - intros w Hw. apply Hhoff. change (Hof E M' model w = true) in Hw. fold H' in Hw. destruct (H w) eqn:Hh0; [reflexivity|]. rewrite (HH' w Hh0) in Hw. discriminate.
  - exact Hres.
  - exact Hlim.
  - exact Hsp.
  - exact Hspok.
  - exact Hbrk.
  - exact Hsbrk.
  - exact Htid.
  - exact Hmaps.
  - exact Hgsh.
  - exact Hgtop.
  - exact Hivwf.
  - exact Hpd.
  - exact Hmres.
  - exact Hkind.
  - exact Hlzm.
  - exact Hzrsh.
  - exact Hzrm.
  - intros w Hw Hout Hnow Hnb. exact (Hzr w Hw Hout Hnow Hnb).
  - exact Hrl.
  - exact Hvmo.
  - exact Hproc.
  - exact Hfrz.
  - rom_tac.
  - intros q Hq w Hw. destruct (Hown q Hq w Hw) as [Hv Hm]. split; [|exact Hm]. exact (HH' _ Hv).
  - exact (blob_ok_same E M M' model model _ eq_refl eq_refl Hblob).
Qed.
End Allow.
End FxChAllow.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma mp_vmmaps : forall a n m, m_vmmaps (mprotect_model_next m a n) =
  mkVmMapsFull (vm_reserved (m_vmmaps m)) (vm_maps (m_vmmaps m))
    (maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
    (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m)) (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m)).
Proof. intros a n m. destruct m; reflexivity. Qed.
Lemma mp_lazy : forall a n m, m_vm_lazy (mprotect_model_next m a n) = m_vm_lazy m.
Proof. intros a n m. destruct m; reflexivity. Qed.
Lemma mp_mat : forall a n m, m_vm_materialized (mprotect_model_next m a n) = m_vm_materialized m.
Proof. intros a n m. destruct m; reflexivity. Qed.
Lemma mp_other : forall a n m, let m' := mprotect_model_next m a n in
  m_proc m' = m_proc m /\ m_fd m' = m_fd m /\ m_io m' = m_io m /\ m_fsys m' = m_fsys m /\ m_lim m' = m_lim m /\ m_time m' = m_time m.
Proof. intros a n m. destruct m; cbn; repeat split; reflexivity. Qed.

Definition mprot_post (L : sst) : sst := ret_post L (lconst 0).
Definition mprot_eff (a n : word) : SyscallEffect := mkEffect (Z_to_bv 64 0) [] [(a, n)].

Section MprotPost.
Variable segs : list Segment.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.
Hypothesis Hsegb : segs_below_b segs 0x800000000000 = true.

#[using="Type"] Theorem mprot_den : forall E L M ms model (a : lin) (n : Z) (j : nat) (g : lin * lin * gkind),
  DEN segs LIMIT model0 mem0 E L M ms model ->
  nth_error (sm_maps M) j = Some g -> snd g = GN ->
  uE E (fst (fst g)) <= uE E a -> uE E a + n <= uE E (fst (fst g)) + gsz E g ->
  0 < n -> n mod 4096 = 0 -> uE E a mod 4096 = 0 ->
  (forall R, In R (s_rgs L) -> forall w, uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R -> ~ (uE E a <= w < uE E a + n)) ->
  eager_sum (s_facts L) (set_kind j GE (sm_maps M)) + allow_bound (sm_allow M) <= LIMIT -> sm_own M = [] -> nomark (sm_maps M) = true ->
  DEN segs LIMIT model0 mem0 E (mprot_post L) (fix_M M j GE)
      (advance_past_svc (apply_effect (svc_set ms) (mprot_eff (lden E a) (Z_to_bv 64 n))))
      (mprotect_model_next model (lden E a) (Z_to_bv 64 n)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E L M ms model a n j g Hd Hj Hgn Hlo Hhi HnZ Hnal Hal Hsep Hbud Hon Hnm.
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  den_noblob Hnm.
  assert (Hnm' : nomark (sm_maps (fix_M M j GE)) = true) by (cbn [sm_maps fix_M]; rewrite set_kind_nomark; exact Hnm).
  set (av := lden E a) in *.
  set (u := uE E a) in *.
  assert (Hgj : In g (sm_maps M)) by exact (nth_error_In _ _ Hj).
  assert (Hgsh_j : gshape_ok E g) by (rewrite Forall_forall in Hgsh; exact (Hgsh g Hgj)).
  destruct Hgsh_j as (Hgs1 & Hgs2 & Hgs3 & Hgs4).
  assert (Hu64 : u + n <= 0x800000000000) by lia.
  assert (Hua : bv_unsigned av = u) by reflexivity.
  assert (Hu0 : 0 <= u) by (rewrite <- Hua; exact (proj1 (u_lt av))).
  assert (HnZw : bv_unsigned (Z_to_bv 64 n) = n) by (apply fg64; unfold two64; lia).
  set (model' := mprotect_model_next model av (Z_to_bv 64 n)).
  set (M' := fix_M M j GE).
  set (H := Hof E M model) in *.
  set (H' := Hof E M' model').
  assert (HH' : H' = H) by (unfold H', H, Hof, model'; rewrite mp_lazy; reflexivity).
  assert (Hvm' : m_vmmaps model' = _) by exact (mp_vmmaps av (Z_to_bv 64 n) model).
  assert (Hlz' : m_vm_lazy model' = m_vm_lazy model) by exact (mp_lazy av (Z_to_bv 64 n) model).
  assert (Hmat' : m_vm_materialized model' = m_vm_materialized model) by exact (mp_mat av (Z_to_bv 64 n) model).
  assert (Hoth' := mp_other av (Z_to_bv 64 n) model). cbv zeta in Hoth'.
  rewrite Hua, HnZw in Hvm'.
  destruct Hivwf as [Hwna Hwlz].
  (* [comment removed for export] *)
  assert (Hrg : forall x, u <= x < u + n -> covered (vm_maps (m_vmmaps model)) x = true).
  { intros x Hx. rewrite Hmaps. apply (covered_In _ (gden E g)); [apply in_map; exact Hgj|]. unfold gden. rewrite in_iv_word.
    pose proof (u_lt (lden E (fst (fst g)))). unfold gsz, uE in *.
    apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  assert (Hsd0 := sden_0 _ _ _ _ Hsd). destruct Hsd0 as (Hpc0 & Hsv0 & Hrv0 & HR0 & HG0 & HD0 & HF0 & Hfrm0).
  assert (Hrgw : forall R, In R (s_rgs L) -> uE E (rg_base R) + rsz E R <= two64 /\ 0 <= rsz E R).
  { intros R HR. rewrite Forall_forall in HG0. destruct (HG0 R HR) as (Hs & Hw & _). unfold uE. lia. }
  set (mem' := fresh_mem false (ms_mem ms) av (Z_to_bv 64 n)).
  assert (Hmem' : ms_mem (advance_past_svc (apply_effect (svc_set ms) (mprot_eff av (Z_to_bv 64 n)))) = mem').
  { unfold mprot_eff, mem', fresh_mem. exact (adv_eff_mem ms (Z_to_bv 64 0) [(av, Z_to_bv 64 n)] [] []). }
  (* [comment removed for export] *)
  assert (Hpt : forall R, In R (s_rgs L) -> forall i, 0 <= i < rsz E R ->
             mrestrict H mem' (Z_to_bv 64 (uE E (rg_base R) + i)) = mrestrict H (ms_mem ms) (Z_to_bv 64 (uE E (rg_base R) + i))).
  { intros R HR i Hi. destruct (Hrgw R HR) as [Hw1 Hw2]. pose proof (u_lt (lden E (rg_base R))) as HuR.
    set (w := uE E (rg_base R) + i) in *.
    assert (Hw64 : bv_unsigned (Z_to_bv 64 w) = w) by (apply fg64; unfold uE in *; lia).
    unfold mrestrict. unfold mem'. rewrite fresh_mem_out; [reflexivity|]. rewrite Hua, HnZw, Hw64.
    exact (Hsep R HR w ltac:(unfold w; lia)). }
  (* [comment removed for export] *)
  assert (Hsden : sden segs E (mprot_post L) (restrict H' (advance_past_svc (apply_effect (svc_set ms) (mprot_eff av (Z_to_bv 64 n)))))).
  { rewrite HH'. unfold mprot_eff. rewrite (restrict_adv_eff H ms (Z_to_bv 64 0) [(av, Z_to_bv 64 n)] [] [] (s_pc L) Hpc0).
    intros E'' Ha''. cbn [mprot_post ret_post s_next] in Ha''.
    destruct (Hsd E'' Ha'') as (_ & _ & Hrv & HR & HG & HD & HF & Hfrm).
    assert (HbE : forall R, In R (s_rgs L) -> uE E'' (rg_base R) = uE E (rg_base R) /\ rsz E'' R = rsz E R).
    { intros R HR'. unfold uE, rsz. unfold bases_wf in Hbw. rewrite forallb_forall in Hbw. destruct (andb_prop _ _ (Hbw R HR')) as [Hb1 Hb2].
      rewrite (lden_agree_wf _ E E'' _ Hb1 Ha''), (lden_agree_wf _ E E'' _ Hb2 Ha''). split; reflexivity. }
    unfold sden0, mprot_post, ret_post. cbn [s_pc s_regs s_rgs s_facts s_resv mks ms_pc_val ms_svc_pending ms_resv ms_regs ms_mem ms_fcsr].
    split; [reflexivity|]. split; [reflexivity|]. split; [exact Hrv|].
    split; [apply regs_ok_upd; [exact HR | apply lden_lconst]|].
    split; [|split; [exact HD | split; [exact HF | exact Hfrm]]].
    apply Forall_forall. intros R HR'. rewrite Forall_forall in HG. apply (rg_ok_mem_eq segs E'' (ms_mem (restrict H ms))); [exact (HG R HR')|].
    intros i Hi. rewrite (proj2 (HbE R HR')) in Hi. rewrite (proj1 (HbE R HR')). cbn [ms_mem restrict].
    unfold fresh_mem in Hpt. exact (Hpt R HR' i Hi). }
  (* [comment removed for export] *)
  assert (Hhl' : m_halted model' = m_halted model) by (unfold model', m_halted; rewrite (proj1 Hoth'); reflexivity).
  assert (Htd' : m_tid model' = m_tid model) by (unfold model', m_tid; rewrite (proj1 Hoth'); reflexivity).
  assert (Hmaps' : vm_maps (m_vmmaps model') = List.map (gden E) (sm_maps M')).
  { rewrite Hvm'. cbn [vm_maps sm_maps M' fix_M]. rewrite set_kind_gden. exact Hmaps. }
  assert (Hgsh' : Forall (gshape_ok E) (sm_maps M')).
  { cbn [sm_maps M' fix_M]. apply set_kind_Forall; [exact Hgsh|]. intros g0 Hg0. rewrite Forall_forall in Hgsh.
    exact (Hgsh g0 (nth_error_In _ _ Hg0)). }
  assert (Hrng : forall x, in_rng u (u + n) x = true <-> u <= x < u + n).
  { intros x. unfold in_rng. split; intros Hx; [apply andb_prop in Hx as [H1 H2]; apply Z.leb_le in H1; apply Z.ltb_lt in H2; lia|].
    apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  assert (Hcovna : forall x, covered (vm_noaccess (m_vmmaps model')) x =
                     (covered (vm_noaccess (m_vmmaps model)) x && negb (in_rng u (u + n) x))%bool).
  { intros x. rewrite Hvm'. cbn [vm_noaccess].
    destruct (maps_subtract_sem (vm_noaccess (m_vmmaps model)) u (u + n) Hwna ltac:(lia)) as (_ & _ & Hc). exact (Hc x). }
  assert (Hkind' : Forall (kind_ok E model') (sm_maps M')).
  { cbn [sm_maps M' fix_M]. apply set_kind_Forall'.
    - intros i g0 Hg0 Hij. rewrite Forall_forall in Hkind. rewrite Hmaps in Hpd.
      assert (Hi' : nth_error (List.map (gden E) (sm_maps M)) i = Some (gden E g0)) by (rewrite nth_error_map, Hg0; reflexivity).
      assert (Hj' : nth_error (List.map (gden E) (sm_maps M)) j = Some (gden E g)) by (rewrite nth_error_map, Hj; reflexivity).
      pose proof (pdisj_nth _ _ _ _ _ Hpd Hi' Hj' Hij) as Hdis. unfold iv_disj, B, S in Hdis. unfold gden in Hdis. cbn [fst snd] in Hdis.
      rewrite Forall_forall in Hgsh. destruct (Hgsh g0 (nth_error_In _ _ Hg0)) as (G1 & _ & _ & G4).
      pose proof (u_lt (lden E (fst (fst g0)))). pose proof (u_lt (lden E (fst (fst g)))). unfold uE in *.
      assert (E1 : bv_unsigned (lden E (snd (fst g0))) = gsz E g0) by reflexivity.
      assert (E2 : bv_unsigned (lden E (snd (fst g))) = gsz E g) by reflexivity.
      rewrite E1, E2 in Hdis. split.
      + intros Hne x Hx. pose proof (proj1 (Hkind g0 (nth_error_In _ _ Hg0)) Hne x Hx) as Hc.
        rewrite covered_app, Hcovna, Hlz'. rewrite covered_app in Hc.
        unfold gden in Hx. rewrite in_iv_word, E1 in Hx. apply andb_prop in Hx as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2.
        destruct (in_rng u (u + n) x) eqn:Hr; [exfalso; apply Hrng in Hr; lia|].
        cbn [negb]. rewrite !andb_true_r. exact Hc.
      + intros Hgn0. pose proof (proj2 (Hkind g0 (nth_error_In _ _ Hg0)) Hgn0) as Hin0. rewrite Hvm'. cbn [vm_noaccess].
        unfold gden in Hin0 |- *. cbn [fst snd] in Hin0 |- *.
        apply In_maps_subtract_disj; [exact Hin0 | lia | rewrite E1; lia | rewrite E1; lia].
    - intros g0 Hg0. rewrite Hj in Hg0. injection Hg0 as <-. unfold kind_ok. cbn [snd]. split; [intros Hne; exfalso; exact (Hne eq_refl) | discriminate]. }
  assert (Hbud' : eager_used model' + A_bytes (allowA E M') <= LIMIT).
  { pose proof (eager_le_old E model' (s_facts L) (sm_maps M') HF0 Hmaps' Hgsh' Hkind') as He.
    pose proof (A_bytes_allowA E M' Hanz) as Hb. cbn [sm_maps sm_allow M' fix_M] in He, Hb. lia. }
  assert (Hmres' : forall x, covered (vm_maps (m_vmmaps model')) x = true -> covered (vm_reserved (m_vmmaps model')) x = false)
    by (rewrite Hvm'; exact Hmres).
  constructor.
  - exact Hsden.
  - cbn [mprot_post ret_post s_next]. unfold M', fix_M, sm_wf in *. cbn [sm_maps sm_allow sm_tid sm_brk sm_sbrk sm_sp sm_own] in *.
    replace (forallb (fun g0 => (lwf (s_next L) (fst (fst g0)) && lwf (s_next L) (snd (fst g0)))%bool) (set_kind j GE (sm_maps M))) with
            (forallb (fun g0 => (lwf (s_next L) (fst (fst g0)) && lwf (s_next L) (snd (fst g0)))%bool) (sm_maps M)); [exact Hwf|].
    clear -Hj. revert j Hj. induction (sm_maps M) as [|g0 r IH]; intros [|j'] Hj; cbn [set_kind forallb]; try reflexivity.
    f_equal. cbn in Hj. exact (IH j' Hj).
  - exact Hbw.
  - rewrite Hhl'. exact Hh.
  - exact Hawf.
  - exact Hanz.
  - rewrite (AM_nil model0 _ _ Hblob0). destruct Hminv as [N1 N2 N3 N4 N5]. constructor; rewrite ?Hmat', ?Hlz'.
    + exact N1.
    + exact N2.
    + exact N3.
    + exact N4.
    + rewrite Hvm'. cbn [vm_limit]. rewrite Hlim. exact Hbud'.
  - change (H_off_segments segs H'). rewrite HH'. exact Hhoff.
  - rewrite Hvm'. exact Hres.
  - rewrite Hvm'. exact Hlim.
  - rewrite Hvm'. exact Hsp.
  - rewrite Hvm'. exact Hspok.
  - rewrite Hvm'. exact Hbrk.
  - rewrite Hvm'. exact Hsbrk.
  - rewrite Htd'. exact Htid.
  - rewrite (lden_maps_nomark _ _ _ Hnm'). exact Hmaps'.
  - exact Hgsh'.
  - cbn [sm_maps M' fix_M]. apply set_kind_Forall; [rewrite Hvm'; exact Hgtop|]. intros g0 Hg0. rewrite Forall_forall in Hgtop.
    rewrite Hvm'. exact (Hgtop g0 (nth_error_In _ _ Hg0)).
  - rewrite Hvm', Hlz'. cbn [vm_noaccess]. split; [exact (proj1 (maps_subtract_sem _ u (u + n) Hwna ltac:(lia))) | exact Hwlz].
  - rewrite Hvm'. exact Hpd.
  - exact Hmres'.
  - exact Hkind'.
  - rewrite Hlz', Hvm'. exact Hlzm.
  - exact Hzrsh.
  - rewrite Hvm'. exact Hzrm.
  - intros w Hw Hout. rewrite Hmem'. cbn [mprot_post ret_post s_rgs] in Hout. cbn [sm_zr M' fix_M] in Hw.
    pose proof (Hzrsh w Hw) as Hws.
    assert (Hw64 : 0 <= w < two64) by (unfold in_shadow, SH_LO, SH_HI in Hws; apply andb_prop in Hws as [H1 H2];
                                        apply Z.leb_le in H1; apply Z.ltb_lt in H2; unfold two64; lia).
    destruct (Z_lt_le_dec w u) as [Hlt|Hge]; [|destruct (Z_lt_le_dec w (u + n)) as [Hlt2|Hge2]].
    + unfold mem'. rewrite fresh_mem_out by (rewrite Hua, HnZw, fg64 by exact Hw64; lia). exact (fun _ _ => Hzr w Hw Hout (own_pt_nil E M w Hon)).
    + unfold mem'. intros _ _. apply fresh_mem_in. rewrite Hua, HnZw, fg64 by exact Hw64. lia.
    + unfold mem'. rewrite fresh_mem_out by (rewrite Hua, HnZw, fg64 by exact Hw64; lia). exact (fun _ _ => Hzr w Hw Hout (own_pt_nil E M w Hon)).
  - rewrite Forall_forall in Hrl |- *. intros R HR. unfold rl_ok, app_pt in *. rewrite Hvm'. exact (Hrl R HR).
  - destruct Hvmo as (H1 & H2 & H3 & H4 & H5). destruct Hoth' as (Hp & Hf & Hi & Hs & Hl & Ht).
    unfold model'. rewrite Hf, Hi, Hs, Hl, Ht. repeat split; assumption.
  - rewrite Htd'. destruct Hoth' as (Hp & _). unfold model'. rewrite Hp. exact Hproc.
  - assert (Hgt : uE E (fst (fst g)) + gsz E g <= alloc_top (m_vmmaps model)) by (rewrite Forall_forall in Hgtop; exact (Hgtop g Hgj)).
    apply (frz_keep mem0 E E L (mprot_post L) M M' ms _ model model' Hwf (agree_refl _ _) eq_refl); [unfold alloc_top; rewrite Hvm'; reflexivity | | | exact Hfrz].
    + intros w _ Ho. exact Ho.
    + intros w Hw Ho. rewrite Hmem'. unfold mem'. rewrite fresh_mem_out; [reflexivity|].
      rewrite Hua, HnZw, fg64 by (unfold two64; lia). lia.
  - rom_tac.
  - apply own_nil. cbn [M' fix_M sm_own]. exact Hon.
  - rewrite Hblob0. apply blob_ok_nil. exact Hnm'.
Qed.
End MprotPost.

(* [comment removed for export] *)
Definition allow_M (M : smodel) (b : lin) (n : Z) : smodel :=
  SM (sm_maps M) ((b, n) :: sm_allow M) (sm_zr M) (sm_tid M) (sm_brk M) (sm_sbrk M) (sm_sp M) (sm_frz M) (sm_own M).

Section Allow.
Variable segs : list Segment.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.

#[using="Type"] Theorem den_allow : forall E S M ms model (b : lin) (n : Z),
  DEN segs LIMIT model0 mem0 E S M ms model -> lwf (s_next S) b = true -> 0 <= n ->
  eager_sum (s_facts S) (sm_maps M) + allow_bound ((b, n) :: sm_allow M) <= LIMIT ->
  DEN segs LIMIT model0 mem0 E S (allow_M M b n) ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model b n Hd Hwb Hn Hbud.
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  set (M' := allow_M M b n).
  assert (HA' : allowA E M' = allow1 E (b, n) :: allowA E M) by reflexivity.
  assert (Hanz' : Forall (fun p => 0 <= snd p) (sm_allow M')) by (cbn [sm_allow M' allow_M]; constructor; [exact Hn | exact Hanz]).
  assert (HH' : forall w, Hof E M model w = false -> Hof E M' model w = false).
  { intros w Hw. unfold Hof, mkH in *. rewrite HA'. destruct (page_in_ranges (page_base w) (m_vm_lazy model)); [|reflexivity].
    cbn [andb] in *. apply negb_false_iff in Hw. apply negb_false_iff.
    change (allow1 E (b, n) :: allowA E M) with ([allow1 E (b, n)] ++ allowA E M). apply page_allowedb_app_r. exact Hw. }
  assert (HH2 : forall w, Hof E M' model w = true -> Hof E M model w = true).
  { intros w Hw. destruct (Hof E M model w) eqn:E0; [reflexivity|]. rewrite (HH' w E0) in Hw. discriminate. }
  constructor.
  - (* [comment removed for export] *)
    intros E'' Ha. destruct (Hsd E'' Ha) as (Hpc & Hsv & Hrv & HR & HG & HD & HF & Hfrm).
    unfold sden0. cbn [restrict ms_pc_val ms_svc_pending ms_resv ms_regs ms_mem ms_fcsr] in *.
    split; [exact Hpc|]. split; [exact Hsv|]. split; [exact Hrv|]. split; [exact HR|]. split; [|split; [exact HD | split; [exact HF | exact Hfrm]]].
    apply Forall_forall. intros R HR'. rewrite Forall_forall in HG. pose proof (HG R HR') as HRok.
    apply (rg_ok_mem_eq segs E'' (mrestrict (Hof E M model) (ms_mem ms))); [exact HRok|].
    intros i Hi. pose proof (rg_ok_visible segs (Hof E M model) (ms_mem ms) E'' R Hhoff HRok i Hi) as Hv.
    unfold mrestrict. rewrite Hv, (HH' _ Hv). reflexivity.
  - unfold sm_wf in *. cbn [sm_maps sm_allow sm_tid sm_brk sm_sbrk sm_sp sm_frz sm_own M' allow_M] in *. cbn [forallb fst]. rewrite Hwb. cbn [andb].
    exact Hwf.
  - exact Hbw.
  - exact Hh.
  - exact (A_wf_allowA E M' Hanz').
  - exact Hanz'.
  - destruct Hminv as [N1 N2 N3 N4 N5]. constructor.
    + exact N1.
    + exact N2.
    + intros p Hp. unfold AM. rewrite HA'. change ((allow1 E (b, n) :: allowA E M) ++ blobA (blob_of model0)) with ([allow1 E (b, n)] ++ AM model0 E M).
      apply page_allowedb_app_r. exact (N3 p Hp).
    + exact N4.
    + assert (HFL : Forall (fact_ok E) (s_facts S)) by (destruct (sden_0 _ _ _ _ Hsd) as (_ & _ & _ & _ & _ & _ & X & _); exact X).
      pose proof (eager_le E M model (s_facts S) _ HFL Hmaps Hgsh Hkind Hblob) as He. pose proof (A_bytes_allowA E M' Hanz') as Hb.
      rewrite Hlim. unfold AM. rewrite A_bytes_app. cbn [sm_allow M' allow_M] in Hb. lia.
  - intros w Hw. exact (Hhoff w (HH2 w Hw)).
  - exact Hres.
  - exact Hlim.
  - exact Hsp.
  - exact Hspok.
  - exact Hbrk.
  - exact Hsbrk.
  - exact Htid.
  - exact Hmaps.
  - exact Hgsh.
  - exact Hgtop.
  - exact Hivwf.
  - exact Hpd.
  - exact Hmres.
  - exact Hkind.
  - exact Hlzm.
  - exact Hzrsh.
  - exact Hzrm.
  - exact Hzr.
  - exact Hrl.
  - exact Hvmo.
  - exact Hproc.
  - exact Hfrz.
  - rom_tac.
  - apply (own_keep mem0 E E S S M M' ms ms model model Hwf (agree_refl _ _) eq_refl); [| | | exact Hown].
    + intros w Ho. exact Ho.
    + intros w _. reflexivity.
    + intros x Hx. exact (HH' x Hx).
  - exact (blob_ok_same E M M' model model _ eq_refl eq_refl Hblob).
Qed.
End Allow.

(* [comment removed for export] *)
Lemma has_const_grant_In2 : forall gs b k, has_const_grant gs b k = true ->
  exists g, In g gs /\ is_const (fst (fst g)) = Some b /\ is_const (snd (fst g)) = Some k.
Proof.
  intros gs b k H. unfold has_const_grant in H. apply existsb_exists in H as (g & Hin & Hc).
  destruct (is_const (fst (fst g))) as [c|] eqn:Ec; [|discriminate]. destruct (is_const (snd (fst g))) as [z|] eqn:Ez; [|discriminate].
  apply andb_prop in Hc as [H1 H2].
  apply Z.eqb_eq in H1, H2. exists g. subst. auto.
Qed.

Lemma grant_noshadow : forall E BL M (model : Model) g x,
  vm_maps (m_vmmaps model) = lden_maps E BL (sm_maps M) -> pdisj (vm_maps (m_vmmaps model)) ->
  Forall (gshape_ok E) (sm_maps M) -> shadow_ok M = true -> In g (sm_maps M) -> is_const (fst (fst g)) = None ->
  in_iv (gden E g) x = true -> in_shadow x = false.
Proof.
  intros E BL M model g x Hm Hpd Hgsh Hsh Hg Hnc Hx. apply not_true_iff_false. intros Hs.
  assert (Hgm : is_mark g = false) by (unfold is_mark; rewrite Hnc; reflexivity).
  unfold in_shadow, SH_LO, SH_HI in Hs. apply andb_prop in Hs as [S1 S2]. apply Z.leb_le in S1. apply Z.ltb_lt in S2.
  unfold shadow_ok in Hsh. apply andb_prop in Hsh as [Hsh H3]. apply andb_prop in Hsh as [H1 H2].
  assert (Hone : forall b k, has_const_grant (sm_maps M) b k = true -> 0 <= b < two64 -> 0 <= k < two64 -> b <> MARKB -> b <= x < b + k -> False).
  { intros b k Hc Hb Hk Hbm Hin. destruct (has_const_grant_In2 _ _ _ Hc) as (gs0 & Hin0 & Hcs & Hks).
    destruct (In_nth_error _ _ Hg) as [i Hi]. destruct (In_nth_error _ _ Hin0) as [i0 Hi0].
    destruct (Nat.eq_dec i i0) as [->|Hne]; [rewrite Hi in Hi0; injection Hi0 as <-; rewrite Hnc in Hcs; discriminate|].
    rewrite Hm in Hpd.
    assert (Hgm0 : is_mark gs0 = false).
    { unfold is_mark. rewrite Hcs. rewrite (proj2 (Z.eqb_neq _ _) Hbm). reflexivity. }
    pose proof (pdisj_lden_nth E BL _ i i0 g gs0 Hpd Hi Hi0 Hne Hgm Hgm0) as Hdis. unfold iv_disj, B, S in Hdis. unfold gden in Hdis, Hx. cbn [fst snd] in Hdis.
    destruct (is_const_sound E _ _ Hcs) as [Hbe _]. destruct (is_const_sound E _ _ Hks) as [Hke _].
    rewrite Hbe, Hke in Hdis. rewrite (fg64 b Hb), (fg64 k Hk) in Hdis.
    rewrite Forall_forall in Hgsh. destruct (Hgsh g Hg) as (G1 & _ & _ & G4 & _).
    rewrite in_iv_word in Hx.
    apply andb_prop in Hx as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2. unfold gsz, uE in *. lia. }
  destruct (Z_lt_le_dec x GAP_B) as [Hl|Hl]; [|destruct (Z_lt_le_dec x HS_B) as [Hl2|Hl2]].
  - exact (Hone LS_B LS_K H1 ltac:(unfold LS_B, two64; lia) ltac:(unfold LS_K, two64; lia) ltac:(unfold LS_B, MARKB; lia) ltac:(unfold LS_B, LS_K, GAP_B in *; lia)).
  - exact (Hone GAP_B GAP_K H2 ltac:(unfold GAP_B, two64; lia) ltac:(unfold GAP_K, two64; lia) ltac:(unfold GAP_B, MARKB; lia) ltac:(unfold GAP_B, GAP_K, HS_B in *; lia)).
  - exact (Hone HS_B HS_K H3 ltac:(unfold HS_B, two64; lia) ltac:(unfold HS_K, two64; lia) ltac:(unfold HS_B, MARKB; lia) ltac:(unfold HS_B, HS_K in *; lia)).
Qed.

Definition mprot_ok (res : list (word * word)) (LIMIT : Z) (L : sst) (M : smodel) (n : Z) (j : nat) : bool :=
  let fs := s_facts L in let a := rget (s_regs L) (rkey a0r) in
  match a7c L, arg L 1, arg L 2, nth_error (sm_maps M) j with
  | Some c7, Some len, Some prot, Some g =>
      (Z.eqb c7 226 && Z.eqb prot 3 && Z.ltb 0 len && Z.ltb len 4611686018427387904 && Z.eqb n (page_round_up_Z len) &&
       gkind_eqb (snd g) GN && match is_const (fst (fst g)) with Some _ => false | None => true end &&
       contained_b fs a n (fst (fst g)) (gsz_lo fs g) && lal_ok a (fst (fst g)) && lwf (s_next L) a &&
       (let ar := irange fs a in      (* [comment removed for export] *)
        forallb (fun R => rgs_sepA fs a ar n R ||| sep_app2_b fs (sm_maps M) j (sm_sp M) a n R ||| sep_res_b res R) (s_rgs L)) &&      (* [comment removed for export] *)
       allow_cov fs a n (sm_allow M) && shadow_ok M &&
       Z.leb (eager_sum fs (set_kind j GE (sm_maps M)) + allow_bound (sm_allow M)) LIMIT)%bool
  | _, _, _, _ => false
  end.

Section MprotNode.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.
Hypothesis Hsegb : segs_below_b segs 0x800000000000 = true.
Hypothesis Hoff : sc_alloc cfg = false.

#[using="Hoff"] Theorem den_mprotect : forall E L M ms model T n j,
  DEN segs LIMIT model0 mem0 E L M ms model -> sm_own M = [] -> nomark (sm_maps M) = true ->
  mprot_ok (segments_reserved segs) LIMIT L M n j = true ->
  (forall ms' model', DEN segs LIMIT model0 mem0 E (add_post (mprot_post L) (rget (s_regs L) (rkey a0r)) n None)
                         (add_M (fix_M M j GE) n None) ms' model' ->
      realizes_cfg segs cfg (mkCfg ms' model') T) ->
  realizes_cfg segs cfg (mkCfg (svc_set ms) model) T.
Proof. LiaFast.lf_pins (fun (Hoff : LiaFast.U) => LiaFast.u0).
  intros E L M ms model T n j Hd Hon Hnm Hok Hk.
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  pose proof (eq_sym Hmaps) as HmapsL. den_noblob Hnm. apply eq_sym in HmapsL.
  unfold mprot_ok in Hok. set (a := rget (s_regs L) (rkey a0r)) in *.
  destruct (a7c L) as [c7|] eqn:H7; [|discriminate]. destruct (arg L 1) as [len|] eqn:H1; [|discriminate].
  destruct (arg L 2) as [prot|] eqn:H2; [|discriminate]. destruct (nth_error (sm_maps M) j) as [g|] eqn:Hj; [|discriminate].
  apply andb_prop in Hok as [Hok Hbud]. apply andb_prop in Hok as [Hok Hshok]. apply andb_prop in Hok as [Hok Halc].
  apply andb_prop in Hok as [Hok Hsepc]. apply andb_prop in Hok as [Hok Hwa]. apply andb_prop in Hok as [Hok Hdal].
  apply andb_prop in Hok as [Hok Hdc]. apply andb_prop in Hok as [Hok Hnc]. apply andb_prop in Hok as [Hok Hgn].
  apply andb_prop in Hok as [Hok Hlen]. apply andb_prop in Hok as [Hok Hlb]. apply andb_prop in Hok as [Hok Hlp].
  apply andb_prop in Hok as [Hc7 Hprot].
  apply Z.eqb_eq in Hc7, Hprot, Hlen. apply Z.ltb_lt in Hlp, Hlb. apply Z.leb_le in Hbud. subst c7 prot.
  assert (HgN : snd g = GN) by (destruct (snd g); try discriminate; reflexivity).
  assert (Hnc' : is_const (fst (fst g)) = None) by (destruct (is_const (fst (fst g))); [discriminate | reflexivity]).
  set (H := Hof E M model) in *. set (ms1 := svc_set ms).
  assert (Hx8 : ms_reg ms 17 = Z_to_bv 64 226) by exact (a7_const segs E L (restrict H ms) ms 226 Hsd eq_refl H7).
  assert (Hg0 : ms_gpr ms1 0 = lden E a) by exact (gpr_lin segs E L (restrict H ms) ms Hsd eq_refl).
  assert (Hg1 : ms_gpr ms1 1 = Z_to_bv 64 len) by exact (gpr_const segs E L (restrict H ms) ms 1 len Hsd eq_refl ltac:(lia) H1).
  assert (Hg2 : ms_gpr ms1 2 = Z_to_bv 64 3) by exact (gpr_const segs E L (restrict H ms) ms 2 3 Hsd eq_refl ltac:(lia) H2).
  assert (Hlen64 : bv_unsigned (Z_to_bv 64 len) = len) by (apply fg64; unfold two64; lia).
  assert (HnZpos : 0 < n) by (rewrite Hlen, <- Hlen64; apply (len_nZ_pos (Z_to_bv 64 len)); unfold w_is0, bv_eqb; rewrite Hlen64;
                                apply Z.eqb_neq; change (bv_unsigned (Z_to_bv 64 0)) with 0; lia).
  assert (HnZal : n mod 4096 = 0) by (rewrite Hlen; exact (page_round_up_Z_aligned' _)).
  assert (Hgj : In g (sm_maps M)) by exact (nth_error_In _ _ Hj).
  pose proof Hgsh as Hgsh0. rewrite Forall_forall in Hgsh0. destruct (Hgsh0 g Hgj) as (Gs1 & Gs2 & Gs3 & Gs4 & Gs5).
  destruct (sden_0 _ _ _ _ Hsd) as (Hpc0 & _ & _ & _ & HG0 & HD0 & HF0 & _).
  pose proof (gsz_bounds E (s_facts L) g HF0) as Gb. pose proof (gsz_lo_nonneg (s_facts L) g) as Gb0.
  destruct (contained_sound E (s_facts L) a n (fst (fst g)) (gsz_lo (s_facts L) g) HF0 Hdc HnZpos ltac:(unfold uE, two64 in *; lia)) as [Hlo Hhi0].
  assert (Hhi : uE E a + n <= uE E (fst (fst g)) + gsz E g) by lia.
  assert (Hal : uE E a mod 4096 = 0) by (apply (lal_ok_sound E a (fst (fst g)) Hdal Gs3 Hlo); unfold uE, two64 in *; lia).
  assert (HsepA : forall R, In R (s_rgs L) -> forall w, uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R -> ~ (uE E a <= w < uE E a + n)).
  { intros R HR w Hw Hin. rewrite Forall_forall in HG0. destruct (HG0 R HR) as (HRs & HRw & _).
    rewrite forallb_forall in Hsepc. pose proof (Hsepc R HR) as Hc. apply orb_prop in Hc as [Hc|Hc]; [apply orb_prop in Hc as [Hc|Hc]|].
    - exact (rgs_sepA_sound E (s_facts L) a n R HF0 ltac:(lia) ltac:(unfold uE in *; lia) HRw Hc w Hw Hin).
    - exact (sep_app2_sound E (s_facts L) (sm_maps M) model (sm_sp M) _ HF0 HmapsL Hpd Hgsh Hgtop Hsp (proj2 Hspok)
               j g a n R Hj (nomark_in _ g Hnm (nth_error_In _ _ Hj)) Hlo Hhi ltac:(unfold uE, two64 in *; lia) HRs HRw Hc w Hw Hin).
    - rewrite <- Hres in Hc. exact (sep_res_sound E (sm_maps M) model _ HmapsL Hgsh Hmres j g a n R Hj (nomark_in _ g Hnm (nth_error_In _ _ Hj)) Hlo Hhi Hc w Hw Hin). }
  pose proof (mprot_den segs LIMIT model0 mem0 E L M ms model a n j g Hd Hj HgN Hlo Hhi HnZpos HnZal Hal HsepA Hbud Hon Hnm) as HD'.
  set (ms' := advance_past_svc (apply_effect (svc_set ms) (mprot_eff (lden E a) (Z_to_bv 64 n)))) in *.
  set (model' := mprotect_model_next model (lden E a) (Z_to_bv 64 n)) in *.
  assert (HuA : bv_unsigned (lden E a) = uE E a) by reflexivity.
  assert (HnZw : bv_unsigned (Z_to_bv 64 n) = n) by (apply fg64; pose proof (u_lt (lden E a)); unfold uE, two64 in *; lia).
  assert (Hcm : forall x, uE E a <= x < uE E a + n -> covered (vm_maps (m_vmmaps model)) x = true /\ in_iv (gden E g) x = true).
  { intros x Hx. assert (Hi : in_iv (gden E g) x = true).
    { unfold gden. rewrite in_iv_word.
      apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; unfold gsz, uE in *; lia. }
    split; [|exact Hi]. rewrite Hmaps. apply (covered_In _ (gden E g)); [apply in_map; exact Hgj | exact Hi]. }
  assert (HD2 : DEN segs LIMIT model0 mem0 E (add_post (mprot_post L) a n None) (add_M (fix_M M j GE) n None) ms' model').
  { apply (den_add segs LIMIT model0 mem0 E (mprot_post L) (fix_M M j GE) ms' model' a n None HD' Hwa HnZpos HnZal Hal
             ltac:(unfold uE in *; lia)).
    - intros x Hx. destruct (Hcm x Hx) as [Hc Hi]. split; [unfold model'; rewrite mp_vmmaps; exact Hc|].
      exact (grant_noshadow E _ M model g x HmapsL Hpd Hgsh Hshok Hgj Hnc' Hi).
    - intros x Hx. split.
      + unfold ms'. unfold mprot_eff. rewrite (adv_eff_mem ms (Z_to_bv 64 0) [(lden E a, Z_to_bv 64 n)] [] []).
        change (apply_zeros (apply_unmaps (ms_mem ms) []) [(lden E a, Z_to_bv 64 n)]) with (fresh_mem false (ms_mem ms) (lden E a) (Z_to_bv 64 n)).
        apply fresh_mem_in. rewrite HuA, HnZw, fg64 by (unfold uE, two64 in *; lia). lia.
      + unfold Hof, model'. rewrite mp_lazy. apply mkH_allowed.
        apply (allow_cov_sound E (s_facts L) a n (sm_allow (fix_M M j GE)) HF0 Halc x Hx). unfold uE, two64 in *. lia.
    - intros R HR w Hw. exact (HsepA R HR w Hw).
    - intros P HP. discriminate.
    - exact Hbud.
    - intros P HP. discriminate.
    - intros P HP. discriminate. }
  eapply rzc_silent1; [|exact (Hk _ _ HD2)].
  assert (Hsvc : ms_svc_pending ms1 = Some (ms_reg ms 17)) by reflexivity.
  assert (Hno : bv_unsigned (ms_reg ms 17) = 226) by (rewrite Hx8; reflexivity).
  (* [comment removed for export] *)
  assert (Hina : map_contains (vm_noaccess (m_vmmaps model)) (lden E a) (Z_to_bv 64 n) = true).
  { rewrite Forall_forall in Hkind. pose proof (proj2 (Hkind g Hgj) HgN) as Hin0.
    apply (map_contains_intro _ _ _ (fst (gden E g)) (snd (gden E g))); [rewrite <- surjective_pairing; exact Hin0 | |].
    - unfold gden. cbn [fst]. unfold uE in *. lia.
    - unfold gden. cbn [fst snd]. rewrite HnZw, HuA. unfold gsz, uE in *. lia. }
  assert (Hinm : map_contains (vm_maps (m_vmmaps model)) (lden E a) (Z_to_bv 64 n) = true).
  { rewrite Hmaps. apply (map_contains_intro _ _ _ (fst (gden E g)) (snd (gden E g))); [rewrite <- surjective_pairing; apply in_map; exact Hgj | |].
    - unfold gden. cbn [fst]. unfold uE in *. lia.
    - unfold gden. cbn [fst snd]. rewrite HnZw, HuA. unfold gsz, uE in *. lia. }
  assert (HnZ : Z_to_bv 64 (page_round_up_Z (bv_unsigned (Z_to_bv 64 len))) = Z_to_bv 64 n) by (rewrite Hlen64, Hlen; reflexivity).
  assert (Hbudok : mprotect_budget_ok model (lden E a) (Z_to_bv 64 n) = true).
  { unfold mprotect_budget_ok, vm_backing_within_limit. apply Z.leb_le. fold model'.
    destruct HD' as [_ _ _ _ Hawf' _ Hminv' _ _ Hlim' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _].
    pose proof (vm_backing_used_le _ _ Hminv' (A_wf_app _ _ Hawf' (A_wf_blobA _))) as Hv. destruct Hminv' as [_ _ _ _ N5]. lia. }
  apply (node_mprotect_expose segs cfg Hoff ms1 model (ms_reg ms 17) (lden E a) (Z_to_bv 64 n) Hh Hsvc Hno); [|exact Hbudok].
  intros o. rewrite (syscall_spec_mprotect segs ms1 (ms_reg ms 17) model o Hno). rewrite Hg0, Hg1, Hg2.
  rewrite (mprotect_spec_expose (lden E a) (Z_to_bv 64 len) (Z_to_bv 64 3) _ model o); rewrite ?HnZ; [reflexivity | reflexivity | | | | reflexivity |].
  - apply Z.eqb_eq. rewrite HuA. exact Hal.
  - unfold w_is0, bv_eqb. rewrite Hlen64. apply Z.eqb_neq. change (bv_unsigned (Z_to_bv 64 0)) with 0. lia.
  - apply Z.leb_gt. rewrite Hlen64, <- Hlen, HuA. unfold two_pow_64. unfold uE in *. lia.
  - rewrite Hina, Hinm. reflexivity.
Qed.
End MprotNode.
