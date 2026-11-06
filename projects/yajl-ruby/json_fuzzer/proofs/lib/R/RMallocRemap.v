(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import PortShim.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import F_malloc_free MallocTree MallocKit_A MallocKit_AB MallocKit_A2 Malloc_fp.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree Malloc MallocCtrl Monad RawAlloc Realloc MI_Kit.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require MI_WRemap.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_A2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition ptrs_but (st : mstate) (rid : N) (g : aptr) : Prop :=
  let c := ctx st in
  let P := fun q : N => q <> rid in
  optr_in P (c_free_meta_head c) /\ optr_in P (c_avail_meta c) /\ optr_in P (c_meta_area_head c)
  /\ optr_in P (c_meta_area_tail c) /\ optr_in P (c_avail_meta_areas c)
  /\ (forall sc, optr_in P (active st sc))
  /\ match c_brk c with BrkLive q _ => P q | _ => True end
  /\ (forall q, optr_in P (m_prev (get_meta_rec st q)) /\ optr_in P (m_next (get_meta_rec st q))
             /\ (optr_in P (m_mem (get_meta_rec st q)) \/ (q = g /\ m_mem (get_meta_rec st q) = Some (rid, 0))))
  /\ (forall a ar, (s_areas st) !! a = Some ar -> P (fst a) /\ optr_in P (a_next ar))
  /\ (forall b gh, (s_groups st) !! b = Some gh -> optr_in P (g_meta gh) /\ (P (fst b) \/ b = (rid, 0))).

(* [comment removed for export] *)
Definition rrep_static (a : Z) : Prop :=
  RMLOCK <= a < RMLOCK + 4 \/ RLIBC <= a < RLIBC + 0x418 \/ RGOT_SSP <= a < RGOT_SSP + 8 \/ RSSP_GUARD <= a < RSSP_GUARD + 8.

Lemma round_up_pg_id x : 0 <= x -> x mod 4096 = 0 -> round_up_pg x = x.
Proof. intros. rewrite round_up_pg_eq. Z.div_mod_to_equations. lia. Qed.

Lemma ref_reserved_pos b k : In (b, k) ref_reserved -> 0 < k.
Proof. unfold ref_reserved. cbn. intros [H|[H|[H|[H|[]]]]]; inversion H; lia. Qed.

Lemma cell_read_cells_none sh o v : (r_cells sh) !! o = None -> cell_read sh o = Known v -> v = 0.
Proof. intros Hn Hc. unfold cell_read in Hc. rewrite Hn in Hc. destruct (_ || _); congruence. Qed.

(* [comment removed for export] *)
Lemma bytes_at1_some mx A b : bytes_at rsegs mx A [b] -> (A + 1 <= 0x10000 \/ 0x56000 <= A) -> mx (wa A) = Some b.
Proof.
  intros (A0 & A1 & HB) IMG. cbn in A1. specialize (HB 0%nat ltac:(cbn; lia)). cbn [nth_error] in HB. rewrite Z.add_0_r in HB.
  unfold mrd in HB. destruct (mx (wa A)) eqn:E; [congruence|]. rewrite ref_seg_rom_none in HB by (rewrite wa_unsigned by lia; lia). discriminate.
Qed.
Lemma bytes_at1_of_some mx A b : 0 <= A -> A + 1 <= 2^64 -> mx (wa A) = Some b -> bytes_at rsegs mx A [b].
Proof.
  intros A0 A1 E. split; [lia|]. split; [cbn; lia|]. intros i Hi. destruct i; [| cbn in Hi; lia]. cbn [nth_error].
  rewrite Z.add_0_r. unfold mrd. rewrite E. reflexivity.
Qed.
Lemma wr_at_some mx A n i : wr_at rsegs mx A n -> (A + n <= 0x10000 \/ 0x56000 <= A) -> 0 <= i < n -> mx (wa (A + i)) <> None.
Proof.
  intros (A0 & A1 & HW) IMG Hi E. apply (HW i Hi). rewrite ref_wview_overlay by (rewrite wa_unsigned by lia; lia). exact E.
Qed.

(* [comment removed for export] *)
Lemma rw_cells_shift mx my A A' cs :
  rw_cells rsegs mx A cs ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> my (wa (A' + i)) = mx (wa (A + i))) ->
  0 <= A' -> A' + Z.of_nat (cells_size cs) <= 2^64 ->
  (A + Z.of_nat (cells_size cs) <= 0x10000 \/ 0x56000 <= A) -> (A' + Z.of_nat (cells_size cs) <= 0x10000 \/ 0x56000 <= A') ->
  rw_cells rsegs my A' cs.
Proof.
  intros [[WFc HB] HW] SH A0 A1 I1 I2. pose proof HB as (B0 & B1 & HBi). rewrite cells_bytes_length in B1, HBi by exact WFc.
  split; [split; [exact WFc|]|].
  - split; [lia|]. rewrite cells_bytes_length by exact WFc. split; [lia|]. intros i Hi.
    rewrite <- (HBi i Hi). unfold mrd. rewrite (SH (Z.of_nat i)) by lia.
    rewrite !ref_seg_rom_none by (rewrite wa_unsigned by lia; lia). reflexivity.
  - split; [lia|]. split; [lia|]. intros i Hi E. destruct HW as (_ & _ & HWi). apply (HWi i Hi).
    rewrite ref_wview_overlay in E |- * by (rewrite wa_unsigned by lia; lia). rewrite <- (SH i Hi). exact E.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

Section REMAP.
Variables (st : mstate) (m m' : mem) (rid : N) (g : aptr) (r : region) (nb needed : Z).
Let old := r_base r.
Let osz := round_up_pg (r_len r).
Let mr := get_meta_rec st g.
Let st' := remap_region rid g nb needed st.
Let mr' := m_set_maplen (needed / 4096) mr.
Let nr := mkRegion RKGroup nb needed.
Let G := conc st g.

Hypothesis MR : rmrep st m.
Hypothesis Hr : (s_regions st) !! rid = Some r.
Hypothesis Kr : r_kind r = RKGroup.
Hypothesis MSL : meta_slot st g.
Hypothesis Hmem : m_mem mr = Some (rid, 0).
Hypothesis PT : ptrs_but st rid g.
Hypothesis NEL : forall q rq, (s_regions st) !! q = Some rq -> lr_lo rq < r_base rq + round_up_pg (r_len rq).
Hypothesis N0 : 0 < needed.
Hypothesis N52 : needed < 2^52.
Hypothesis NAL : needed mod 4096 = 0.
Hypothesis NB0 : 0 < nb.
Hypothesis NBAL : nb mod 4096 = 0.
Hypothesis NBC : nb + needed <= alloc_ceiling.
Hypothesis ANS : (nb = old /\ (needed <= osz \/ ranges_free (live_ranges st) (old + osz) (needed - osz) = true))
                 \/ ranges_free (live_ranges st) nb needed = true.

(* [comment removed for export] *)
Lemma rr_regions : s_regions st' = <[rid := nr]> (s_regions st).
Proof.
  unfold st', remap_region, upd_meta, put_meta. rewrite s_regions_set_metas, s_regions_upd_shadow.
  unfold upd_region, get_region. rewrite Hr. cbn [s_regions set_regions]. rewrite Kr. reflexivity.
Qed.
Lemma rr_lookup q : (s_regions st') !! q = if (q =? rid)%N then Some nr else (s_regions st) !! q.
Proof. rewrite rr_regions. destruct (N.eqb_spec q rid) as [->|NE]; [apply lookup_insert_eq| apply lookup_insert_ne; congruence]. Qed.
Lemma rr_lookup_new : (s_regions st') !! rid = Some nr.
Proof. rewrite rr_lookup, N.eqb_refl. reflexivity. Qed.
Lemma rr_lookup_old q : q <> rid -> (s_regions st') !! q = (s_regions st) !! q.
Proof. intros NE. rewrite rr_lookup. destruct (N.eqb_spec q rid); [congruence| reflexivity]. Qed.
Lemma rr_lookup_inv q rq : (s_regions st') !! q = Some rq -> (q = rid /\ rq = nr) \/ (q <> rid /\ (s_regions st) !! q = Some rq).
Proof. rewrite rr_lookup. destruct (N.eqb_spec q rid) as [->|NE]; intros H; [left; split; congruence| right; auto]. Qed.
Lemma rr_conc q : fst q <> rid -> conc st' q = conc st q.
Proof. intros NE. unfold conc, get_region. rewrite rr_lookup_old by exact NE. reflexivity. Qed.
Lemma rr_conc_new o : conc st' (rid, o) = nb + o.
Proof. unfold conc, get_region. cbn [fst snd]. rewrite rr_lookup_new. reflexivity. Qed.
Lemma rr_shadow q : get_shadow st' q = if (q =? rid)%N then shadow_trunc needed (get_shadow st rid) else get_shadow st q.
Proof.
  unfold st', remap_region, upd_meta, put_meta, get_shadow. rewrite s_shadow_set_metas. unfold upd_shadow. cbn [s_shadow set_shadow].
  rewrite s_shadow_upd_region. unfold get_shadow. rewrite s_shadow_upd_region.
  destruct (N.eqb_spec q rid) as [->|NE]; [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity.
Qed.
Lemma rr_shadow_old q : q <> rid -> get_shadow st' q = get_shadow st q.
Proof. intros NE. rewrite rr_shadow. destruct (N.eqb_spec q rid); [congruence| reflexivity]. Qed.
Lemma rr_shadow_new : get_shadow st' rid = shadow_trunc needed (get_shadow st rid).
Proof. rewrite rr_shadow, N.eqb_refl. reflexivity. Qed.
Lemma rr_ctx : ctx st' = ctx st.
Proof. unfold ctx, st', remap_region, upd_meta, put_meta. rewrite s_ctx_set_metas, s_ctx_upd_shadow, s_ctx_upd_region. reflexivity. Qed.
Lemma rr_groups : s_groups st' = s_groups st.
Proof. unfold st', remap_region, upd_meta, put_meta. rewrite s_groups_set_metas, s_groups_upd_shadow, s_groups_upd_region. reflexivity. Qed.
Lemma rr_areas : s_areas st' = s_areas st.
Proof. unfold st', remap_region, upd_meta, put_meta. rewrite s_areas_set_metas, s_areas_upd_shadow, s_areas_upd_region. reflexivity. Qed.
Lemma rr_slots : s_slots st' = s_slots st.
Proof. unfold st', remap_region, upd_meta, put_meta. rewrite s_slots_set_metas, s_slots_upd_shadow, s_slots_upd_region. reflexivity. Qed.
Lemma rr_tick : s_tick st' = s_tick st.
Proof. unfold st', remap_region, upd_meta, put_meta. rewrite s_tick_set_metas, s_tick_upd_shadow, s_tick_upd_region. reflexivity. Qed.
Lemma rr_reserved : s_reserved st' = s_reserved st.
Proof. unfold st', remap_region, upd_meta, put_meta. rewrite s_reserved_set_metas, s_reserved_upd_shadow, s_reserved_upd_region. reflexivity. Qed.
Lemma rr_shadow_map : s_shadow st' = <[rid := shadow_trunc needed (get_shadow st rid)]> (s_shadow st).
Proof.
  unfold st', remap_region, upd_meta, put_meta. rewrite s_shadow_set_metas. unfold upd_shadow. cbn [s_shadow set_shadow].
  rewrite s_shadow_upd_region. unfold get_shadow. rewrite s_shadow_upd_region. reflexivity.
Qed.
Lemma rr_meta q : get_meta_rec st' q = if aptr_eqb q g then mr' else get_meta_rec st q.
Proof.
  unfold st', remap_region. rewrite get_meta_rec_upd. unfold mr', mr.
  replace (get_meta_rec (upd_shadow rid (shadow_trunc needed) (upd_region rid (fun r0 => mkRegion (r_kind r0) nb needed) st)) g) with (get_meta_rec st g).
  2:{ unfold get_meta_rec. rewrite s_metas_upd_shadow, s_metas_upd_region. reflexivity. }
  destruct (aptr_eqb q g); [reflexivity|]. unfold get_meta_rec. rewrite s_metas_upd_shadow, s_metas_upd_region. reflexivity.
Qed.
Lemma rr_meta_old q : q <> g -> get_meta_rec st' q = get_meta_rec st q.
Proof. intros NE. rewrite rr_meta. destruct (aptr_eqb_spec q g); [congruence| reflexivity]. Qed.
Lemma rr_meta_g : get_meta_rec st' g = mr'.
Proof. rewrite rr_meta, aptr_eqb_refl. reflexivity. Qed.

Lemma mr'_maplen : m_maplen mr' = needed / 4096.
Proof.
  unfold mr', m_set_maplen. cbn [m_maplen]. change (2^52 - 1) with (Z.ones 52). rewrite Z.land_ones by lia.
  apply Z.mod_small. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. lia.
Qed.
Lemma mr'_word : 0 <= m_last_idx mr < 32 -> 0 <= m_freeable mr < 2 -> 0 <= m_sizeclass mr < 64 -> 0 <= m_maplen mr ->
  meta_word mr' = meta_word mr mod 4096 + needed.
Proof.
  intros L F S M. unfold meta_word. rewrite mr'_maplen. unfold mr'. cbn [m_last_idx m_freeable m_sizeclass m_set_maplen].
  replace ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr) mod 4096)
     with (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr) by (Z.div_mod_to_equations; lia).
  Z.div_mod_to_equations. lia.
Qed.

Lemma rr_pw p : optr_in (fun q => q <> rid) p -> pw st' p = pw st p.
Proof. destruct p as [q|]; cbn; intros H; unfold pw, oconc; [rewrite rr_conc by exact H|]; reflexivity. Qed.

Lemma ticks_ok_remap : ticks_ok st -> ticks_ok st'.
Proof.
  intros [T1 T2]. split.
  - intros q sh u hl ch Hq Hu Hin. rewrite rr_tick. rewrite rr_shadow_map in Hq.
    destruct (N.eq_dec q rid) as [->|NE].
    + rewrite lookup_insert_eq in Hq. injection Hq as <-. unfold shadow_trunc in Hu. cbn [r_hav] in Hu.
      rewrite (MI_WRemap.lookup_filter_lt needed 16) in Hu. destruct (u * 16 <? needed); [| discriminate].
      unfold get_shadow in Hu. destruct (s_shadow st !! rid) as [sh0|] eqn:E0; cbn in Hu; [exact (T1 rid sh0 u hl ch E0 Hu Hin)| rewrite lookup_empty in Hu; discriminate].
    + rewrite lookup_insert_ne in Hq by congruence. exact (T1 q sh u hl ch Hq Hu Hin).
  - intros q sh pg t Hq Hp. rewrite rr_tick. rewrite rr_shadow_map in Hq.
    destruct (N.eq_dec q rid) as [->|NE].
    + rewrite lookup_insert_eq in Hq. injection Hq as <-. unfold shadow_trunc in Hp. cbn [r_havp] in Hp.
      rewrite (MI_WRemap.lookup_filter_lt needed 4096) in Hp. destruct (pg * 4096 <? needed); [| discriminate].
      unfold get_shadow in Hp. destruct (s_shadow st !! rid) as [sh0|] eqn:E0; cbn in Hp; [exact (T2 rid sh0 pg t E0 Hp)| rewrite lookup_empty in Hp; discriminate].
    + rewrite lookup_insert_ne in Hq by congruence. exact (T2 q sh pg t Hq Hp).
Qed.


(* [comment removed for export] *)
Lemma rr_wf : rregions_wf st. Proof. exact (proj1 MR). Qed.

Lemma old_facts : 0 < old /\ old mod 4096 = 0 /\ 0 <= r_len r /\ old + osz <= alloc_ceiling
  /\ ranges_free ref_reserved old osz = true /\ r_len r <= osz /\ osz mod 4096 = 0.
Proof.
  pose proof rr_wf as (_ & WR & _). destruct (WR rid r Hr) as (O0 & OAL & OL & OC & ORF).
  pose proof (round_up_pg_ge (r_len r)). pose proof (round_up_pg_mod (r_len r)). unfold old, osz. repeat split; auto.
Qed.

Lemma resv_sub_live b k : In (b, k) ref_reserved -> In (b, k) (live_ranges st).
Proof. intros H. pose proof rr_wf as (RS & _). unfold live_ranges. apply in_or_app. left. rewrite RS. exact H. Qed.

Lemma new_resv_free : ranges_free ref_reserved nb needed = true.
Proof.
  pose proof old_facts as (O0 & OAL & OL & OC & ORF & OLE & OM).
  apply ranges_free_intro. intros b k HI. pose proof (ranges_free_In _ _ _ _ _ ORF HI) as X.
  destruct ANS as [[E [LE|RF]]|RF].
  - rewrite E. lia.
  - rewrite E. pose proof (ranges_free_In _ _ _ _ _ RF (resv_sub_live _ _ HI)). pose proof (ref_reserved_pos _ _ HI). lia.
  - exact (ranges_free_In _ _ _ _ _ RF (resv_sub_live _ _ HI)).
Qed.

Lemma new_off_image : nb + needed <= 0x10000 \/ 0x56000 <= nb.
Proof. apply rreserved_disjoint1; [exact new_resv_free| lia]. Qed.

Lemma old_off_image : osz = 0 \/ old + osz <= 0x10000 \/ 0x56000 <= old.
Proof.
  pose proof old_facts as (O0 & OAL & OL & OC & ORF & OLE & OM). pose proof (round_up_pg_ge (r_len r)).
  destruct (Z.eq_dec osz 0); [left; assumption| right]. apply rreserved_disjoint1; [exact ORF| unfold osz in *; lia].
Qed.

(* [comment removed for export] *)
Lemma new_vs_region q rq : (s_regions st) !! q = Some rq -> q <> rid ->
  nb + needed <= lr_lo rq \/ r_base rq + round_up_pg (r_len rq) <= nb.
Proof.
  intros Hq NE. pose proof rr_wf as (_ & _ & DJ & _).
  pose proof (DJ rid r q rq Hr Hq ltac:(congruence)) as D. rewrite (lr_lo_group r Kr) in D. fold old osz in D.
  pose proof (In_live_ranges st q rq Hq) as HI.
  assert (LV : forall x L, ranges_free (live_ranges st) x L = true -> x + L <= lr_lo rq \/ r_base rq + round_up_pg (r_len rq) <= x).
  { intros x L RF. unfold region_live_range in HI. unfold lr_lo. destruct (r_kind rq); (pose proof (ranges_free_In _ _ _ _ _ RF HI); unfold PGSZ in *; lia). }
  destruct ANS as [[E [LE|RF]]|RF].
  - rewrite E. unfold old, osz in *. lia.
  - rewrite E in *. pose proof (LV _ _ RF). pose proof (NEL q rq Hq). unfold old, osz in *. lia.
  - exact (LV _ _ RF).
Qed.

(* [comment removed for export] *)
Lemma old_vs_region q rq : (s_regions st) !! q = Some rq -> q <> rid ->
  old + osz <= lr_lo rq \/ r_base rq + round_up_pg (r_len rq) <= old.
Proof.
  intros Hq NE. pose proof rr_wf as (_ & _ & DJ & _).
  pose proof (DJ rid r q rq Hr Hq ltac:(congruence)) as D. rewrite (lr_lo_group r Kr) in D. unfold old, osz. lia.
Qed.

Lemma G_area : exists a ar k ra, (s_areas st) !! a = Some ar /\ 0 <= k < NSLOTS /\ g = aadd a (AREA_HDR + META_SIZE * k)
  /\ (s_regions st) !! (fst a) = Some ra /\ fst a <> rid /\ r_kind ra <> RKGroup
  /\ G = conc st a + (AREA_HDR + META_SIZE * k) /\ conc st a = r_base ra + snd a
  /\ lr_lo ra <= conc st a /\ 0 <= snd a /\ conc st a + 4096 <= r_base ra + round_up_pg (r_len ra) /\ snd a mod 4096 = 0
  /\ 0 < r_base ra /\ r_base ra + round_up_pg (r_len ra) <= alloc_ceiling.
Proof.
  pose proof rr_wf as WF. destruct MSL as (a & ar & k & Ha & Hk & Eg).
  destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
  pose proof (rarea_lr_lo st a ar ra WF Ha Hra) as LR.
  exists a, ar, k, ra. repeat split; auto; try lia.
  - intros E. rewrite E, Hr in Hra. inversion Hra; subst. exact (NK Kr).
  - unfold G. rewrite Eg, conc_aadd by (rewrite Hra; eauto). reflexivity.
Qed.

Lemma G_bounds : 0 < G /\ G + 40 <= alloc_ceiling /\ (G + 40 <= 0x10000 \/ 0x56000 <= G)
  /\ (G + 40 <= old \/ old + osz <= G) /\ (G + 40 <= nb \/ nb + needed <= G).
Proof.
  destruct G_area as (a & ar & k & ra & Ha & Hk & Eg & Hra & NEa & NK & HG & Ca & LR & Sa0 & Sa1 & SaL & RB0 & RBC).
  pose proof (rmeta_slot_bounds st m g MR MSL) as (B1 & B2 & B3 & _). fold G in B1, B2, B3.
  pose proof (new_vs_region _ _ Hra NEa). pose proof (old_vs_region _ _ Hra NEa).
  unfold AREA_HDR, META_SIZE, NSLOTS, alloc_ceiling in *. lia.
Qed.

(* [comment removed for export] *)
Hypothesis AG : forall a, 0 <= a < 2^64 -> (a + 1 <= G \/ G + 40 <= a) ->
  (rrep_static a \/ exists q rq, (s_regions st) !! q = Some rq /\ q <> rid /\ lr_lo rq <= a < r_base rq + round_up_pg (r_len rq)) ->
  m' (wa a) = m (wa a).
Hypothesis CP : forall o, 0 <= o < Z.min osz needed -> m' (wa (nb + o)) = m (wa (old + o)).
Hypothesis ZF : forall o, osz <= o < needed -> m' (wa (nb + o)) = Some (b8 0).
Hypothesis MG : rw_cells rsegs m' G [C8 (pw st (m_prev mr)); C8 (pw st (m_next mr)); C8 (wz nb);
                                  C4 (wz (m_avail mr)); C4 (wz (m_freed mr)); C8 (wz (meta_word mr'))].

Lemma agree_static A n : (forall a, A <= a < A + n -> rrep_static a) -> MallocKit_A2.agree_on m m' A n.
Proof.
  intros HS a Ha. pose proof (HS a Ha) as R. pose proof G_bounds as (B1 & B2 & B3 & _).
  pose proof R as R'. unfold rrep_static, RMLOCK, RLIBC, RGOT_SSP, RSSP_GUARD in R'.
  apply AG; [lia| lia| left; exact R].
Qed.

Lemma agree_region q rq A n : (s_regions st) !! q = Some rq -> q <> rid ->
  lr_lo rq <= A -> A + n <= r_base rq + round_up_pg (r_len rq) -> (A + n <= G \/ G + 40 <= A) ->
  MallocKit_A2.agree_on m m' A n.
Proof.
  intros Hq NE LO HI DG a Ha. pose proof rr_wf as (_ & WR & _). destruct (WR q rq Hq) as (B0 & _ & _ & BC & _).
  pose proof (lr_lo_ge rq). unfold alloc_ceiling in BC.
  apply AG; [lia| lia|]. right. exists q, rq. split; [exact Hq|]. split; [exact NE|]. lia.
Qed.

(* [comment removed for export] *)
Theorem rmrep_remap :
  0 <= m_last_idx mr < 32 -> 0 <= m_freeable mr < 2 -> 0 <= m_sizeclass mr < 64 -> 0 <= m_maplen mr ->
  rmrep st' m'.
Proof.
  intros ML MF MS MM.
  pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (RS & WR & DJ & WA & WG).
  pose proof old_facts as (O0 & OAL & OL & OC & ORF & OLE & OM).
  pose proof G_bounds as (GB1 & GB2 & GB3 & GB4 & GB5).
  destruct G_area as (a0 & ar0 & k0 & ra0 & Ha0 & Hk0 & Eg & Hra0 & NEa0 & NK0 & HG & Ca0 & LR0 & Sa00 & Sa01 & SaL0 & RB00 & RBC0).
  pose proof new_off_image as NI. pose proof old_off_image as OI.
  destruct PT as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10).
  unfold alloc_ceiling in *.
  assert (N4096 : 4096 <= needed) by (clear -N0 NAL; Z.div_mod_to_equations; nia).
  assert (OSZ16 : forall b gh, (s_groups st) !! b = Some gh -> fst b = rid -> 16 <= osz).
  { intros b gh Hb Hf. destruct (WG b gh Hb) as (rb & Hrb & _ & Sb0 & Sb1 & _). rewrite Hf, Hr in Hrb. inversion Hrb; subst rb. unfold osz. lia. }
  assert (Hconc : forall q, fst q <> rid -> conc st' q = conc st q) by (intros q Hq; apply rr_conc; exact Hq).
  assert (Hpw : forall p, optr_in (fun q => q <> rid) p -> pw st' p = pw st p) by (intros p Hp; apply rr_pw; exact Hp).
  assert (MCELLS : forall q, q <> g -> meta_cells st' (get_meta_rec st' q) = meta_cells st (get_meta_rec st q)).
  { intros q NE. rewrite rr_meta_old by exact NE. destruct (P8 q) as (X1 & X2 & X3).
    destruct X3 as [X3|[X3 _]]; [| congruence]. unfold meta_cells. rewrite !Hpw by assumption. reflexivity. }
  assert (MCELLg : meta_cells st' mr' = [C8 (pw st (m_prev mr)); C8 (pw st (m_next mr)); C8 (wz nb);
                                         C4 (wz (m_avail mr)); C4 (wz (m_freed mr)); C8 (wz (meta_word mr'))]).
  { destruct (P8 g) as (X1 & X2 & _). unfold meta_cells, mr'. cbn [m_prev m_next m_mem m_avail m_freed m_set_maplen]. fold mr.
    rewrite !Hpw by assumption. fold mr'.
    rewrite Hmem. unfold pw at 3. unfold oconc. rewrite rr_conc_new, Z.add_0_r. reflexivity. }
  split; [| split; [| split; [| split; [| split]]]].
  - (* [comment removed for export] *)
    split; [rewrite rr_reserved; exact RS|]. split; [| split; [| split]].
    + intros q rq Hq. destruct (rr_lookup_inv q rq Hq) as [[-> ->]|[NE H]].
      * cbn [r_base r_len nr]. rewrite (round_up_pg_id needed) by lia. unfold alloc_ceiling. repeat split; try lia. exact new_resv_free.
      * exact (WR q rq H).
    + intros q1 r1 q2 r2 H1 H2 NE.
      destruct (rr_lookup_inv q1 r1 H1) as [[-> ->]|[NE1 H1']]; destruct (rr_lookup_inv q2 r2 H2) as [[-> ->]|[NE2 H2']].
      * congruence.
      * cbn [r_base r_len nr]. rewrite (round_up_pg_id needed) by lia. pose proof (new_vs_region q2 r2 H2' NE2).
        replace (lr_lo nr) with nb by reflexivity. lia.
      * cbn [r_base r_len nr]. rewrite (round_up_pg_id needed) by lia. pose proof (new_vs_region q1 r1 H1' NE1).
        replace (lr_lo nr) with nb by reflexivity. lia.
      * exact (DJ q1 r1 q2 r2 H1' H2' NE).
    + intros a ar Ha. rewrite rr_areas in Ha. destruct (WA a ar Ha) as (ra & Hra & REST). destruct (P9 a ar Ha) as [Pa _].
      exists ra. rewrite rr_lookup_old by exact Pa. auto.
    + intros b gh Hb. rewrite rr_groups in Hb. destruct (WG b gh Hb) as (rb & Hrb & REST). destruct (P10 b gh Hb) as [_ [Pb| ->]].
      * exists rb. rewrite rr_lookup_old by exact Pb. auto.
      * exists nr. rewrite rr_lookup_new. cbn [fst snd r_kind r_len nr]. rewrite (round_up_pg_id needed) by lia.
        repeat split; try lia; try reflexivity.
  - (* [comment removed for export] *)
    destruct CX as (C1 & C2 & C3 & C4 & C5 & C6).
    assert (E1 : ctx_head_cells st' = ctx_head_cells st).
    { unfold ctx_head_cells. rewrite rr_ctx. rewrite !Hpw by assumption. reflexivity. }
    assert (E2 : actives st' = actives st).
    { unfold actives. apply map_ext. intros x. unfold active. rewrite rr_ctx. apply Hpw. apply (P6 (Z.of_nat x)). }
    assert (E3 : usages st' = usages st). { unfold usages. apply map_ext. intros. unfold usage. rewrite rr_ctx. reflexivity. }
    assert (E4 : unmap_seqs st' = unmap_seqs st). { unfold unmap_seqs. apply map_ext. intros. unfold unmap_seq. rewrite rr_ctx. reflexivity. }
    assert (E5 : bouncess st' = bouncess st). { unfold bouncess. apply map_ext. intros. unfold bounces. rewrite rr_ctx. reflexivity. }
    assert (E6 : ctx_tail_cells st' = ctx_tail_cells st).
    { unfold ctx_tail_cells, brk_word. rewrite rr_ctx. destruct (c_brk (ctx st)) as [| |q off]; try reflexivity.
      rewrite (Hconc (q, off)) by exact P7. reflexivity. }
    unfold rmrep_ctx. rewrite E1, E2, E3, E4, E5, E6.
    assert (L1 : length (actives st) = 48%nat) by (unfold actives; rewrite length_map, length_seq; reflexivity).
    assert (L2 : length (usages st) = 48%nat) by (unfold usages; rewrite length_map, length_seq; reflexivity).
    assert (L3 : length (unmap_seqs st) = 32%nat) by (unfold unmap_seqs; rewrite length_map, length_seq; reflexivity).
    assert (L4 : length (bouncess st) = 32%nat) by (unfold bouncess; rewrite length_map, length_seq; reflexivity).
    assert (AGC : MallocKit_A2.agree_on m m' RLIBC 0x418).
    { apply agree_static. intros; unfold rrep_static; lia. }
    unfold RLIBC, RCTX in *.
    split; [|split; [|split; [|split; [|split]]]].
    + eapply rrw_cells_agree; [exact C1|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply ru64arr_agree; [exact C2|]. rewrite L1. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply ru64arr_agree; [exact C3|]. rewrite L2. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply ru8arr_agree; [exact C4|]. rewrite L3. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply ru8arr_agree; [exact C5|]. rewrite L4. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply rrw_cells_agree; [exact C6|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
  - (* [comment removed for export] *)
    destruct GL as (G1 & G2 & G3 & G4 & G5). unfold rmrep_globals.
    split; [|split; [|split; [|split]]].
    + eapply rrw_cells_agree; [exact G1|]. apply agree_static; cbn; intros; unfold rrep_static; lia.
    + eapply rrw_cells_agree; [exact G2|]. apply agree_static; cbn; intros; unfold rrep_static, RLIBC, RNEED_LOCKS in *; lia.
    + eapply rrw_cells_agree; [exact G3|]. apply agree_static; cbn; intros; unfold rrep_static, RLIBC, RPAGE_SIZE in *; lia.
    + eapply rrw_cells_agree; [exact G4|]. apply agree_static; cbn; intros; unfold rrep_static; lia.
    + eapply rrw_cells_agree; [exact G5|]. apply agree_static; cbn; intros; unfold rrep_static; lia.
  - (* [comment removed for export] *)
    intros a ar Ha. rewrite rr_areas in Ha. destruct (AR a ar Ha) as (A1 & A2 & A3). destruct (P9 a ar Ha) as [Pa Pn].
    destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC). unfold alloc_ceiling in RBC.
    pose proof (rarea_lr_lo st a ar ra WF Ha Hra) as LRa.
    (* [comment removed for export] *)
    assert (DD : a = a0 \/ (conc st a + 4096 <= G \/ G + 40 <= conc st a)).
    { destruct (decide (a = a0)) as [->|NEa]; [left; reflexivity| right].
      rewrite HG, Ca, Ca0. destruct (N.eq_dec (fst a) (fst a0)) as [E|NE].
      - rewrite E, Hra0 in Hra. inversion Hra; subst ra.
        assert (snd a <> snd a0) by (intros E2; apply NEa; destruct a, a0; cbn in *; congruence).
        unfold AREA_HDR, META_SIZE, NSLOTS in *. clear -H E Sa0 Sa00 SaL SaL0 Hk0. Z.div_mod_to_equations. nia.
      - pose proof (DJ (fst a) ra (fst a0) ra0 Hra Hra0 NE). unfold AREA_HDR, META_SIZE, NSLOTS in *. lia. }
    unfold rarea_rep. rewrite (Hconc a Pa), (Hpw _ Pn).
    assert (AGA : forall A n, conc st a <= A -> A + n <= conc st a + 4096 -> (A + n <= G \/ G + 40 <= A) -> MallocKit_A2.agree_on m m' A n).
    { intros A n LO HI DG. eapply agree_region; [exact Hra| exact Pa| lia| lia| exact DG]. }
    split; [|split].
    + eapply rrw_cells_agree; [exact A1|]. apply AGA; [lia| cbn; lia|]. cbn. rewrite HG in *. unfold AREA_HDR, META_SIZE in *. destruct DD as [->|DD]; lia.
    + intros k Hk. unfold AREA_HDR, META_SIZE, NSLOTS in *.
      destruct (aptr_eq_dec (aadd a (24 + 40 * k)) g) as [Eq|NEq].
      * (* [comment removed for export] *)
        assert (Ea : a = a0 /\ k = k0).
        { rewrite Eg in Eq. unfold aadd in Eq. destruct a as [fa sa], a0 as [fa0 sa0]. cbn in Eq. inversion Eq.
          destruct DD as [DD|DD]; [inversion DD; subst; split; [reflexivity| lia]|].
          exfalso. subst fa. rewrite Hra0 in Hra. inversion Hra; subst ra. cbn [fst snd] in *.
          clear -H1 Sa0 Sa00 SaL SaL0 Hk Hk0 DD HG Ca Ca0. rewrite HG in DD. rewrite Ca in DD. rewrite Ca0 in DD. cbn [snd] in *. Z.div_mod_to_equations. nia. }
        destruct Ea as [-> ->]. rewrite Eq, rr_meta_g, MCELLg. replace (conc st a0 + 24 + 40 * k0) with G by (rewrite HG; lia). exact MG.
      * rewrite (MCELLS _ NEq). eapply rrw_cells_agree; [apply A2; exact Hk|].
        unfold meta_cells. cbn [cells_size csize Nat.add length]. apply AGA; [lia| lia|].
        destruct DD as [->|DD]; [| lia]. rewrite HG.
        assert (k <> k0) by (intros ->; apply NEq; rewrite Eg; reflexivity). nia.
    + eapply rrw_cells_agree; [exact A3|]. apply AGA; [lia| cbn; lia|]. cbn. rewrite HG in *. unfold AREA_HDR, META_SIZE, NSLOTS in *. destruct DD as [->|DD]; lia.
  - (* [comment removed for export] *)
    intros b gh Hb. rewrite rr_groups in Hb. destruct (GR b gh Hb) as (w8 & R & Hw8). destruct (P10 b gh Hb) as [Pg Pb].
    exists w8. split; [| exact Hw8]. rewrite (Hpw _ Pg).
    destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & SbA & RBb & RBCb). unfold alloc_ceiling in RBCb.
    destruct Pb as [Pb| ->].
    + rewrite (Hconc b Pb). eapply rrw_cells_agree; [exact R|]. cbn.
      eapply agree_region; [exact Hrb| exact Pb| rewrite (lr_lo_group rb Kb); lia| lia|].
      assert (NE : fst b <> fst a0) by (intros E; rewrite E, Hra0 in Hrb; inversion Hrb; subst; exact (NK0 Kb)).
      pose proof (DJ (fst b) rb (fst a0) ra0 Hrb Hra0 NE). rewrite (lr_lo_group rb Kb) in *. rewrite HG. unfold AREA_HDR, META_SIZE, NSLOTS in *. lia.
    + rewrite rr_conc_new, Z.add_0_r. cbn [fst] in Hrb. rewrite Hr in Hrb. inversion Hrb; subst rb.
      pose proof (OSZ16 _ _ Hb eq_refl) as O16. rewrite Cb in R. cbn [snd] in R. rewrite Z.add_0_r in R. fold old in R.
      eapply (rw_cells_shift m m' old nb); [exact R| | lia| cbn; lia| cbn; lia| cbn; lia].
      cbn. intros i Hi. apply CP. lia.
  - (* [comment removed for export] *)
    intros q rq Hq Hk. destruct (rr_lookup_inv q rq Hq) as [[-> ->]|[NE H]].
    + (* [comment removed for export] *)
      destruct (SH rid r Hr Kr) as (HW & HB & HBD). fold old osz in HW, HB, HBD.
      unfold rshadow_rep. cbn [r_base r_len nr]. rewrite (round_up_pg_id needed) by lia. rewrite rr_shadow_new.
      split; [| split].
      * split; [lia|]. split; [lia|]. intros i Hi. rewrite ref_wview_overlay by (rewrite wa_unsigned by lia; lia).
        destruct (Z.lt_ge_cases i osz).
        -- rewrite CP by lia. apply (wr_at_some m old osz i HW); lia.
        -- rewrite ZF by lia. discriminate.
      * intros o v Ho Hc. rewrite MI_WRemap.cell_read_trunc in Hc by lia.
        destruct (Z.lt_ge_cases o osz).
        -- destruct (HB o v ltac:(lia) Hc) as [Bt Hv]. split; [| exact Hv].
           apply bytes_at1_of_some; [lia| lia|]. rewrite CP by lia. apply (bytes_at1_some m); [exact Bt| lia].
        -- destruct (r_cells (get_shadow st rid) !! o) as [c|] eqn:Ec.
           ++ exfalso. pose proof (HBD o c Ec). lia.
           ++ pose proof (cell_read_cells_none _ _ _ Ec Hc) as ->. split; [| lia].
              apply bytes_at1_of_some; [lia| lia|]. apply ZF. lia.
      * intros o c Ho. unfold shadow_trunc in Ho. cbn [r_cells] in Ho. rewrite MI_WRemap.lookup_filter_lt1 in Ho.
        destruct (Z.ltb_spec o needed); [lia| discriminate].
    + eapply rshadow_rep_ext; [apply rr_shadow_old; exact NE|].
      destruct (SH q rq H Hk) as (HW & HB & HBD).
      assert (AGR : MallocKit_A2.agree_on m m' (r_base rq) (round_up_pg (r_len rq))).
      { eapply agree_region; [exact H| exact NE| rewrite (lr_lo_group rq Hk); lia| lia|].
        assert (NEq : q <> fst a0) by (intros E; rewrite <- E, H in Hra0; inversion Hra0; subst; exact (NK0 Hk)).
        pose proof (DJ q rq (fst a0) ra0 H Hra0 NEq). rewrite (lr_lo_group rq Hk) in *. rewrite HG. unfold AREA_HDR, META_SIZE, NSLOTS in *. lia. }
      split; [| split; [| exact HBD]].
      * eapply rwr_at_agree; eauto.
      * intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
        eapply rbytes_at_agree; [exact Bt|]. cbn. eapply agree_on_sub; [exact AGR| lia| lia].
Qed.

End REMAP.
End RC__1.
