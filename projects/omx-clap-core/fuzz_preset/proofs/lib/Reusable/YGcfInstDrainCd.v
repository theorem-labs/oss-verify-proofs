(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/omx-clap-core/fuzz_preset/lib/Reusable/YGcfInstDrainCd.v, with its module paths changed. *)
(* Theorem Labs, 2026-10: the generic cf instance layer, lane F2b: the MODEL side of F12, the
   step transport of the drain's cut relation across SizeClassAllocator64LocalCache::Deallocate's no-growth arm.
   rule 24: no function proved (kind: model-level facts of cache_dealloc's state step).

   F12 (lane B1's H3 asks it of this layer, Main 00:4xZ) is
     ARXr_cf inst ly X W mem md -> cd_model X c off -> cache_dealloc c off X = IRet (tt, S') ->
     <the walk's own frame: YFgk.MEQ, at_RETK's written values, WIN presence> -> m_vmmaps md' = m_vmmaps md ->
     eager_used md' = eager_used md -> ARXr_cf inst ly S' W mem' md' /\ (AOX S' -> AOX X) /\ (puser X -> puser S'),
   the cf twin of YFez.cd_fin_ARm (YFez.v:770) over ARmcfR instead of cgif's ARm.  This file is its MODEL half: what
   the step does to the state, with no memory and no image in it.  [S'] is YFfh.XK_push c off (if the cache is full,
   of YFfh.XK_drain c X), which YFfh.cache_dealloc_eq_push / _eq_full give from cd_model's room clause (cf has no
   event term: cgif's YFez.HROOM, a room counted in events, is replaced by cd_model's
   4 * fa_len (rg_free (reg S c)) <= rg_mapped_fa (reg S c) and the growth test, DMwalkIF.v:448-460).
   What the fields of ARmcfR need: the chunks, the secondaries, the quarantine, the depot and the fake stack are
   untouched ([cdS_chunks] .. [cdS_depot]); only class [c]'s cache and free array change ([cd_reg_c], [cd_cache_c]),
   and every other class is untouched ([cd_reg_other], [cd_cache_other]); the derived sets the relation reads follow
   ([cd_sec_extents], [cd_aareas], [cd_fa_poison], [cd_prim_committed], [cd_abudget], [cd_xs]).
   Image-free and event-free (no event-count term, no event regime and no event-keyed budget appears). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0s YK0i YP09 YO0d YK08.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YI04 YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YGcfTok YG03cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YFfh.
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section U. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Section C.
Variable ly : alayout.
Variable X : astate.
Variables (c off : Z).
Hypothesis Hc : 1 <= c <= 30.
Hypothesis Hci : st_cache_inited X = true.
Hypothesis Hlen : (Z.to_nat c < length (st_cache X))%nat.
Hypothesis Hlenr : (Z.to_nat c < length (st_regions X))%nat.
Definition cdfull : bool := Z.of_nat (length (pc_chunks (cache X c))) =? pc_max (cache X c).
(* cd_model's room clause, in the no-growth form: the free array holds the drained half.  GUARDED by the cache
   being full, the only arm that drains into the free array; the walk's premise is guarded the same way (H3's
   rd_step: 4 * (old + (if cnt =? MAXv then Nv else 0)) <= mf).  An explicit premise of the three lemmas that read
   it, not a Section hypothesis, so no other lemma of the section can come to depend on it. *)
Definition cd_room : Prop := cdfull = true ->
4 * (fa_len (rg_free (reg X c)) + Z.of_nat (length (kdrained c X))) <= rg_mapped_fa (reg X c).
Definition cdX1 : astate := if cdfull then XK_drain c X else X.
Definition cdS : astate := XK_push c off cdX1.

Lemma cd_eq : cd_room -> cache_dealloc c off X = IRet (tt, cdS).
Proof.
intros Hroom. unfold cdS, cdX1, cdfull. destruct (Z.eqb_spec (Z.of_nat (length (pc_chunks (cache X c)))) (pc_max (cache X c))) as [E|NE].
- exact (cache_dealloc_eq_full c off X Hci ltac:(lia) Hlen E (Hroom ltac:(unfold cdfull; apply Z.eqb_eq; exact E))).
- exact (cache_dealloc_eq_push c off X Hci NE).
Qed.

(* The model post at the no-growth step (YG03cf.cache_dealloc_ok_cf, read off at the IRet). *)
Lemma cd_post : cd_room -> forall U pp cc bb ns, WfR_cf U pp cc bb X ->
0 <= off - region_off c < rg_alloc_user (reg X c) -> (off - region_off c) mod class_size c = 0 ->
~ In (off - region_off c) (class_elems X c) ->
cache_dealloc_post_cf U pp cc bb X c (off - region_off c) ns (tt, cdS).
Proof.
intros Hroom.
intros U pp cc bb ns W H1 H2 H3.
pose proof (cache_dealloc_ok_cf U pp cc bb X c off ns W ltac:(lia) H1 H2 H3) as OK.
rewrite (cd_eq Hroom) in OK. exact OK.
Qed.

Lemma cd_WfR : cd_room -> forall U pp cc bb, WfR_cf U pp cc bb X ->
0 <= off - region_off c < rg_alloc_user (reg X c) -> (off - region_off c) mod class_size c = 0 ->
~ In (off - region_off c) (class_elems X c) -> WfR_cf U pp cc bb cdS.
Proof. intros Hroom U pp cc bb W H1 H2 H3. exact (proj1 (cd_post Hroom U pp cc bb true W H1 H2 H3)). Qed.

(* The state fields the relation reads outside class [c]'s cache and free array. *)
Lemma cdX1_chunks : st_chunks cdX1 = st_chunks X. Proof. unfold cdX1, XK_drain, upd_pc, upd_reg. destruct cdfull; reflexivity. Qed.
Lemma cdS_chunks : st_chunks cdS = st_chunks X. Proof. unfold cdS, XK_push, upd_pc. cbn [st_chunks set_cache]. exact cdX1_chunks. Qed.
Lemma cdS_secs : st_secs cdS = st_secs X. Proof. unfold cdS, cdX1, XK_push, XK_drain, upd_pc, upd_reg. destruct cdfull; reflexivity. Qed.
Lemma cdS_sec_arr : st_sec_arr cdS = st_sec_arr X. Proof. unfold cdS, cdX1, XK_push, XK_drain, upd_pc, upd_reg. destruct cdfull; reflexivity. Qed.
Lemma cdS_sec_res : st_sec_reserved cdS = st_sec_reserved X. Proof. unfold cdS, cdX1, XK_push, XK_drain, upd_pc, upd_reg. destruct cdfull; reflexivity. Qed.
Lemma cdS_qthread : st_qthread cdS = st_qthread X. Proof. unfold cdS, cdX1, XK_push, XK_drain, upd_pc, upd_reg. destruct cdfull; reflexivity. Qed.
Lemma cdS_qglobal : st_qglobal cdS = st_qglobal X. Proof. unfold cdS, cdX1, XK_push, XK_drain, upd_pc, upd_reg. destruct cdfull; reflexivity. Qed.
Lemma cdS_fs : st_fs cdS = st_fs X. Proof. unfold cdS, cdX1, XK_push, XK_drain, upd_pc, upd_reg. destruct cdfull; reflexivity. Qed.
Lemma cdS_depot : st_depot cdS = st_depot X. Proof. unfold cdS, cdX1, XK_push, XK_drain, upd_pc, upd_reg. destruct cdfull; reflexivity. Qed.
Lemma cdS_inited : st_internal_inited cdS = st_internal_inited X. Proof. unfold cdS, cdX1, XK_push, XK_drain, upd_pc, upd_reg. destruct cdfull; reflexivity. Qed.
Lemma cdS_cinit : st_cache_inited cdS = true. Proof. unfold cdS, cdX1, XK_push, XK_drain, upd_pc, upd_reg. destruct cdfull; cbn; exact Hci. Qed.

Lemma cd_reg_other : forall c', 0 <= c' -> c' <> c -> reg cdS c' = reg X c'.
Proof.
intros c' H1 H2. unfold cdS, XK_push. rewrite reg_upd_pc'. unfold cdX1, XK_drain. destruct cdfull; [|reflexivity].
rewrite reg_upd_pc'. apply reg_upd_reg_other; lia.
Qed.
Lemma cd_reg_c : reg cdS c =
(if cdfull then let r := reg X c in mkRegion (rg_mapped_user r) (rg_alloc_user r) (rg_mapped_fa r) (fa_push_list (rg_free r) (kdrained c X)) (rg_holes r)
 else reg X c).
Proof.
unfold cdS, XK_push. rewrite reg_upd_pc'. unfold cdX1, XK_drain. destruct cdfull; [|reflexivity].
rewrite reg_upd_pc'. apply reg_upd_reg; [lia | exact Hlenr].
Qed.
Lemma cd_reg_fields : forall c', 0 <= c' ->
rg_mapped_user (reg cdS c') = rg_mapped_user (reg X c') /\ rg_alloc_user (reg cdS c') = rg_alloc_user (reg X c') /\
rg_mapped_fa (reg cdS c') = rg_mapped_fa (reg X c') /\ rg_holes (reg cdS c') = rg_holes (reg X c').
Proof.
intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE]; [|rewrite cd_reg_other by lia; repeat split; reflexivity].
rewrite cd_reg_c. destruct cdfull; cbn; repeat split; reflexivity.
Qed.
Lemma cd_cache_other : forall c', 0 <= c' -> c' <> c -> cache cdS c' = cache X c'.
Proof.
intros c' H1 H2. unfold cdS, XK_push. cbv zeta. rewrite cache_upd_pc_other by lia.
unfold cdX1, XK_drain. destruct cdfull; [|reflexivity]. cbv zeta. rewrite cache_upd_pc_other by lia. rewrite cache_upd_reg'. reflexivity.
Qed.
Definition cdkept : list Z := if cdfull then kkeep c X else pc_chunks (cache X c).
Lemma cd_cache_X1 : cache cdX1 c = mkPC (pc_max (cache X c)) cdkept /\ (Z.to_nat c < length (st_cache cdX1))%nat.
Proof.
unfold cdX1, cdkept, XK_drain. destruct cdfull.
- cbv zeta. split; [rewrite cache_upd_pc_same; [reflexivity | lia | cbn; exact Hlen]|].
  unfold upd_pc, upd_reg. cbn [st_cache set_cache set_regions]. rewrite zupd_length. exact Hlen.
- split; [destruct (cache X c); reflexivity | exact Hlen].
Qed.
Lemma cd_cache_c : cache cdS c = mkPC (pc_max (cache X c)) (cdkept ++ [off - region_off c]).
Proof.
destruct cd_cache_X1 as [E Lc]. unfold cdS, XK_push. cbv zeta. rewrite cache_upd_pc_same; [|lia|exact Lc]. rewrite E. reflexivity.
Qed.

(* The derived sets the relation reads. *)
Lemma cd_sec_extents : sec_extents ly cdS = sec_extents ly X.
Proof. unfold sec_extents. rewrite cdS_chunks. reflexivity. Qed.
Lemma cd_all_batches : all_batches cdS = all_batches X.
Proof. unfold all_batches. rewrite cdS_qthread, cdS_qglobal. reflexivity. Qed.
Lemma cd_frames : frames cdS = frames X. Proof. unfold frames. rewrite cdS_fs. reflexivity. Qed.
Lemma flat_map_ext_in' {V W : Type} : forall (f g : V -> list W) (l0 : list V), (forall y, In y l0 -> f y = g y) -> flat_map f l0 = flat_map g l0.
Proof. intros f g l0. induction l0 as [|y t IH]; intros H; cbn; [reflexivity|]. rewrite H by (left; reflexivity). rewrite IH; [reflexivity|]. intros z Hz. apply H. right. exact Hz. Qed.
Lemma cd_fa_poison : fa_poison_ranges ly cdS = fa_poison_ranges ly X.
Proof.
unfold fa_poison_ranges. rewrite cdS_chunks. f_equal. apply flat_map_ext_in'. intros c' Hc'. apply zseq_In in Hc'.
destruct (cd_reg_fields c' ltac:(lia)) as (E1 & E2 & E3 & E4). rewrite E1, E3. reflexivity.
Qed.
Lemma cd_aareas : aareas cdS = aareas X.
Proof.
unfold aareas. rewrite cdS_chunks, cdS_sec_res. f_equal. apply flat_map_ext_in'. intros c' Hc'. apply zseq_In in Hc'.
destruct (cd_reg_fields c' ltac:(lia)) as (E1 & E2 & E3 & E4). rewrite E1, E3. reflexivity.
Qed.
Lemma cd_aclient : aclient cdS = aclient X.
Proof. unfold aclient. rewrite cdS_chunks, cd_frames. reflexivity. Qed.
Lemma cd_ashadow : forall B g, ashadow B ly cdS g = ashadow B ly X g.
Proof. intros B g. unfold ashadow. rewrite cdS_chunks, cd_fa_poison. reflexivity. Qed.
Lemma cd_prim_committed : prim_committed cdS = prim_committed X.
Proof.
unfold cdS, XK_push. cbv zeta. change (prim_committed (upd_pc c ?[pp] cdX1)) with (prim_committed cdX1).
unfold cdX1, XK_drain. destruct cdfull; [|reflexivity]. cbv zeta.
match goal with |- prim_committed (upd_pc c ?pp ?XX) = _ => change (prim_committed (upd_pc c pp XX)) with (prim_committed XX) end.
unfold upd_reg. rewrite prim_committed_set_region by (lia || exact Hlenr). cbn [rg_mapped_user rg_mapped_fa]. unfold reg. lia.
Qed.
Lemma cd_sec_live : sec_live_bytes cdS = sec_live_bytes X.
Proof. unfold sec_live_bytes. rewrite cdS_chunks. reflexivity. Qed.
Lemma cd_abudget : abudget_cf cdS = abudget_cf X.
Proof.
(* the hull round's term is the unit's cf_hull, kept by its frame law: the step changes neither st_secs nor the
   chunk list, so sec_live_hulls is the entry's (YGcfNames.cf_hull_frame) *)
assert (HH : cf_hull cdS = cf_hull X).
{ apply cf_hull_frame; [exact cdS_secs | unfold sec_live_hulls; rewrite cdS_chunks; reflexivity]. }
unfold abudget_cf, errb_cap_cf, errb_e. rewrite cd_prim_committed, cdS_sec_res, cd_sec_live, HH, cdS_secs. reflexivity.
Qed.
Lemma cd_xs : xs_cf ly cdS = xs_cf ly X.
Proof. unfold xs_cf, errb_cap_cf, errb_e. rewrite cdS_secs. reflexivity. Qed.
Lemma cd_xs_placed : xs_placed_cf ly X -> xs_placed_cf ly cdS.
Proof. unfold xs_placed_cf. rewrite cd_xs, cd_sec_extents. intros H. exact H. Qed.
Lemma cd_sec_placed : sec_placed ly X -> sec_placed ly cdS.
Proof. unfold sec_placed. rewrite cd_sec_extents. intros H. exact H. Qed.

End C.
End U.
