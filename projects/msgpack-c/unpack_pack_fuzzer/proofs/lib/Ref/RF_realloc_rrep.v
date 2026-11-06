(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import A_F_malloc_free A_MallocTree A_MallocKit_A A_MallocKit_AB A_MallocKit_A2 A_MallocRep A_F_am_K2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc Require Import STree Malloc MallocCtrl MI_Kit Realloc.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import Monad Prog.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ref Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_A RMallocKit_A2.

Set Keyed Unification.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import CeilLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Lemma rw_cells_app2 m A cs1 cs2 :
  rw_cells rsegs m A cs1 -> rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2 -> rw_cells rsegs m A (cs1 ++ cs2).
Proof.
  intros [[W1 B1] R1] [[W2 B2] R2]. split; [split|].
  - apply cells_wf_app. auto.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|]. rewrite cells_bytes_length by exact W1. exact B2.
  - rewrite cells_size_app. destruct R1 as (X0 & X1 & XW). destruct R2 as (Y0 & Y1 & YW). split; [lia|]. split; [lia|].
    intros i Hi. destruct (Z.lt_ge_cases i (Z.of_nat (cells_size cs1))) as [LT|GE]; [apply XW; lia|].
    replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia. apply YW. lia.
Qed.

Lemma rw_cells_app_inv m A cs1 cs2 :
  rw_cells rsegs m A (cs1 ++ cs2) -> rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros [[W B] R]. apply cells_wf_app in W as [W1 W2]. rewrite cells_bytes_app in B. apply bytes_at_app in B as [B1 B2].
  rewrite cells_bytes_length in B2 by exact W1. rewrite cells_size_app in R.
  split; (split; [split; assumption|]); [eapply wr_at_sub; [exact R| lia| lia]|].
  eapply wr_at_sub; [exact R| lia| lia].
Qed.

Lemma rbytes_at_moved m1 m3 (src dst : Z) bs :
  bytes_at rsegs m1 src bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> m3 (wa (dst + i)) = m1 (wa (src + i))) ->
  0 <= dst -> dst + Z.of_nat (length bs) <= 2^64 ->
  (src + Z.of_nat (length bs) <= 0x10000 \/ 0x88000 <= src) -> (dst + Z.of_nat (length bs) <= 0x10000 \/ 0x88000 <= dst) ->
  bytes_at rsegs m3 dst bs.
Proof.
  intros (H0 & H1 & HB) CP D0 D1 IS ID. split; [exact D0|]. split; [exact D1|]. intros i Hi.
  rewrite ref_mrd_overlay by (rewrite wa_unsigned by lia; lia). rewrite CP by lia.
  rewrite <- (HB i Hi). rewrite ref_mrd_overlay by (rewrite wa_unsigned by lia; lia). reflexivity.
Qed.

Lemma rtrim_lookup_lt k cs o : o < k -> trim_cells k cs !! o = cs !! o.
Proof.
  intros Ho. unfold trim_cells. rewrite map_lookup_filter. destruct (cs !! o) as [x|]; cbn; [| reflexivity].
  rewrite option_guard_True by (cbn; exact Ho). reflexivity.
Qed.
Lemma rtrim_lookup_Some k cs o x : trim_cells k cs !! o = Some x -> cs !! o = Some x /\ o < k.
Proof. intros H. unfold trim_cells in H. apply map_lookup_filter_Some in H. cbn in H. exact H. Qed.

Ltac fixaddr v := lazymatch goal with |- rw_cells _ _ ?A _ => replace A with v by (cbn; lia) end.

Section RREMAP.
Variables (st : mstate) (m1 m3 : mem) (rid : N) (r0 : region) (g : aptr) (ai : Z) (nb needed : Z).
Let bg : aptr := (rid, 0).
Let OL : Z := round_up_pg (r_len r0).
Let oldb : Z := r_base r0.
Let r' : region := mkRegion RKGroup nb needed.
Let f : meta -> meta := m_set_maplen (needed / 4096).
Let P : N -> Prop := fun q => q <> rid.
Definition rstR : mstate := upd_meta g f (set_regions (<[rid := r']> (s_regions st)) st).
Let kt : Z := Z.min (m_maplen (get_meta_rec st g) * 4096) needed.
Definition rstT : mstate := trim_shadow rid kt rstR.

Hypothesis MR : rmrep st m1.
Hypothesis Hr0 : (s_regions st) !! rid = Some r0.
Hypothesis Kr0 : r_kind r0 = RKGroup.
Hypothesis Hg : (s_groups st) !! bg = Some (mkGhdr (Some g) ai).
Hypothesis HMEM : m_mem (get_meta_rec st g) = Some bg.
Hypothesis MSL : meta_slot st g.
Hypothesis MLEN : m_maplen (get_meta_rec st g) * 4096 = OL.
Hypothesis MWOK : 0 <= m_last_idx (get_meta_rec st g) < 32 /\ 0 <= m_freeable (get_meta_rec st g) < 2 /\ 0 <= m_sizeclass (get_meta_rec st g) < 64.
Hypothesis ONLYG : forall b gh, (s_groups st) !! b = Some gh -> fst b = rid -> b = bg.

Hypothesis PC1 : optr_in P (c_free_meta_head (ctx st)).
Hypothesis PC2 : optr_in P (c_avail_meta (ctx st)).
Hypothesis PC3 : optr_in P (c_meta_area_head (ctx st)).
Hypothesis PC4 : optr_in P (c_meta_area_tail (ctx st)).
Hypothesis PC5 : optr_in P (c_avail_meta_areas (ctx st)).
Hypothesis PC6 : forall sc, optr_in P (active st sc).
Hypothesis PC7 : match c_brk (ctx st) with BrkLive q _ => P q | _ => True end.
Hypothesis PM : forall g', optr_in P (m_prev (get_meta_rec st g')) /\ optr_in P (m_next (get_meta_rec st g'))
                           /\ (g' <> g -> optr_in P (m_mem (get_meta_rec st g'))).
Hypothesis PA : forall a ar, (s_areas st) !! a = Some ar -> P (fst a) /\ optr_in P (a_next ar).
Hypothesis PG : forall b gh, (s_groups st) !! b = Some gh -> optr_in P (g_meta gh).

Hypothesis NB0 : 0 < nb.
Hypothesis NBA : nb mod 4096 = 0.
Hypothesis NDA : needed mod 4096 = 0.
Hypothesis NDP : 0 < needed.
Hypothesis NCEIL : nb + needed <= alloc_ceiling.
Hypothesis RFR : ranges_free ref_reserved nb needed = true.
Hypothesis DJ' : forall q rq, (s_regions st) !! q = Some rq -> q <> rid -> nb + needed <= lr_lo rq \/ r_base rq + round_up_pg (r_len rq) <= nb.

Hypothesis AGL : agree_on m1 m3 RMLOCK 4.
Hypothesis AGC : agree_on m1 m3 RLIBC 0x418.
Hypothesis AGS1 : agree_on m1 m3 RGOT_SSP 8.
Hypothesis AGS2 : agree_on m1 m3 RSSP_GUARD 8.
Hypothesis AGA : forall a ar, (s_areas st) !! a = Some ar ->
  forall x, conc st a <= x < conc st a + 4096 -> ~ (conc st g + 16 <= x < conc st g + 24) -> ~ (conc st g + 32 <= x < conc st g + 40) ->
  m3 (wa x) = m1 (wa x).
Hypothesis NEWM : rw_cells rsegs m3 (conc st g + 16) [C8 (wz nb)].
Hypothesis NEWW : rw_cells rsegs m3 (conc st g + 32) [C8 (wz (meta_word (f (get_meta_rec st g))))].
Hypothesis AGG : forall b gh, (s_groups st) !! b = Some gh -> fst b <> rid -> agree_on m1 m3 (conc st b) 9.
Hypothesis AGR : forall q rq, (s_regions st) !! q = Some rq -> r_kind rq = RKGroup -> q <> rid -> agree_on m1 m3 (r_base rq) (round_up_pg (r_len rq)).
Hypothesis COPY : forall i, 0 <= i < kt -> m3 (wa (nb + i)) = m1 (wa (oldb + i)).
Hypothesis ZERO : forall i, kt <= i < needed -> m3 (wa (nb + i)) = Some (b8 0).
Hypothesis WRN : wr_at rsegs m3 nb needed.

Lemma rr_round : round_up_pg needed = needed.
Proof. apply round_up_pg_aligned. exact NDA. Qed.

Lemma rr_regions : s_regions rstT = <[rid := r']> (s_regions st).
Proof. reflexivity. Qed.
Lemma rr_lookup_inv q rq : (s_regions rstT) !! q = Some rq -> (q = rid /\ rq = r') \/ (q <> rid /\ (s_regions st) !! q = Some rq).
Proof.
  intros H. rewrite rr_regions in H. destruct (N.eq_dec q rid) as [->|NE].
  - left. rewrite lookup_insert_eq in H. inversion H. auto.
  - right. rewrite lookup_insert_ne in H by congruence. auto.
Qed.
Lemma rr_lookup_old q : q <> rid -> (s_regions rstT) !! q = (s_regions st) !! q.
Proof. intros. rewrite rr_regions, lookup_insert_ne by congruence. reflexivity. Qed.
Lemma rr_lookup_new : (s_regions rstT) !! rid = Some r'.
Proof. rewrite rr_regions. apply lookup_insert_eq. Qed.
Lemma rr_conc q : P (fst q) -> conc rstT q = conc st q.
Proof. intros H. unfold conc, get_region. rewrite rr_lookup_old by exact H. reflexivity. Qed.
Lemma rr_conc_new off : conc rstT (rid, off) = nb + off.
Proof. unfold conc, get_region. cbn [fst snd]. rewrite rr_lookup_new. reflexivity. Qed.
Lemma rr_pw p : optr_in P p -> pw rstT p = pw st p.
Proof. destruct p as [q|]; cbn; intros H; unfold pw, oconc; [rewrite rr_conc by exact H|]; reflexivity. Qed.
Lemma rr_ctx : ctx rstT = ctx st. Proof. reflexivity. Qed.
Lemma rr_areas : s_areas rstT = s_areas st. Proof. reflexivity. Qed.
Lemma rr_groups : s_groups rstT = s_groups st. Proof. reflexivity. Qed.
Lemma rr_meta x : get_meta_rec rstT x = if aptr_eqb x g then f (get_meta_rec st g) else get_meta_rec st x.
Proof.
  change (get_meta_rec rstT x) with (get_meta_rec rstR x). unfold rstR. rewrite (MI_Kit.get_meta_rec_upd (set_regions (<[rid := r']> (s_regions st)) st) g f x).
  reflexivity.
Qed.
Lemma rr_meta_other x : x <> g -> get_meta_rec rstT x = get_meta_rec st x.
Proof. intros NE. rewrite rr_meta. destruct (aptr_eqb_spec x g); [congruence| reflexivity]. Qed.
Lemma rr_meta_g : get_meta_rec rstT g = f (get_meta_rec st g).
Proof. rewrite rr_meta, aptr_eqb_refl. reflexivity. Qed.
Lemma rr_shadow_other q : q <> rid -> get_shadow rstT q = get_shadow st q.
Proof. intros NE. rewrite (get_shadow_eq rstT). unfold rstT, trim_shadow, upd_shadow. cbn [s_shadow set_shadow]. rewrite lookup_insert_ne by congruence. reflexivity. Qed.
Lemma rr_shadow_rid : get_shadow rstT rid = mkShadow (trim_cells kt (r_cells (get_shadow st rid))) (r_hav (get_shadow st rid)) (r_havp (get_shadow st rid)).
Proof. rewrite (get_shadow_eq rstT). unfold rstT, trim_shadow, upd_shadow. cbn [s_shadow set_shadow]. rewrite lookup_insert_eq. reflexivity. Qed.

Lemma rr_kt : 0 <= kt <= needed /\ kt <= OL.
Proof.
  pose proof MR as (WF & _). pose proof WF as (_ & WR & _). destruct (WR _ _ Hr0) as (_ & _ & L0 & _).
  subst kt. rewrite MLEN. pose proof (round_up_pg_ge (r_len r0)). subst OL. lia.
Qed.

Lemma rr_meta_cells_other x : x <> g -> meta_cells rstT (get_meta_rec rstT x) = meta_cells st (get_meta_rec st x).
Proof.
  intros NE. rewrite (rr_meta_other x NE). destruct (PM x) as (X1 & X2 & X3). unfold meta_cells. rewrite !rr_pw by auto. reflexivity.
Qed.

Lemma rr_nd : 4096 <= needed.
Proof. clear - NDA NDP. Z.div_mod_to_equations. lia. Qed.

Lemma rr_regions_wf : rregions_wf rstT.
Proof.
  pose proof MR as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG). pose proof rr_round as RR. pose proof rr_nd as ND.
  destruct (WR _ _ Hr0) as (B0 & BAL & L0 & BC & RF0).
  split; [exact RS|]. split; [|split; [|split]].
  - intros q rq Hq. destruct (rr_lookup_inv q rq Hq) as [[-> ->]|[NE H]].
    + cbn [r_base r_len r']. rewrite RR. repeat split; try lia. exact RFR.
    + exact (WR q rq H).
  - intros q1 rq1 q2 rq2 H1 H2 NE.
    destruct (rr_lookup_inv q1 rq1 H1) as [[-> ->]|[NE1 H1']]; destruct (rr_lookup_inv q2 rq2 H2) as [[-> ->]|[NE2 H2']].
    + congruence.
    + cbn [r_base r_len r']. rewrite RR. pose proof (DJ' q2 rq2 H2' NE2). unfold lr_lo at 2. cbn [r_kind r_base r']. lia.
    + cbn [r_base r_len r']. rewrite RR. pose proof (DJ' q1 rq1 H1' NE1). unfold lr_lo at 1. cbn [r_kind r_base r']. lia.
    + exact (DJ q1 rq1 q2 rq2 H1' H2' NE).
  - intros a ar Ha. rewrite rr_areas in Ha. destruct (WA a ar Ha) as (ra & Hra & REST). destruct (PA a ar Ha) as [Pa _].
    exists ra. rewrite rr_lookup_old by exact Pa. auto.
  - intros b gh Hb. rewrite rr_groups in Hb. destruct (WG b gh Hb) as (rb & Hrb & REST).
    destruct (N.eq_dec (fst b) rid) as [E|NE].
    + pose proof (ONLYG b gh Hb E) as ->. exists r'. cbn [fst]. rewrite rr_lookup_new. split; [reflexivity|].
      cbn [r_kind r_len r' snd]. rewrite RR. split; [reflexivity|]. change (snd bg) with 0. split; [clear; lia|]. split; [clear -ND; lia| reflexivity].
    + exists rb. rewrite rr_lookup_old by exact NE. auto.
Qed.

Theorem rmrep_remap : rmrep rstT m3.
Proof.
  pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (RS & WR & DJ & WA & WG). pose proof rr_round as RR. pose proof rr_kt as KT. pose proof rr_nd as ND.
  destruct (WR _ _ Hr0) as (B0 & BAL & L0 & BC & RF0). pose_ceil.
  pose proof (rreserved_disjoint1 _ _ RFR NDP) as DRn.
  assert (OL16 : 16 <= OL).
  { destruct (WG bg _ Hg) as (rb & Hrb & _ & _ & X & _). change (fst bg) with rid in Hrb. change (snd bg) with 0 in X. rewrite Hr0 in Hrb. injection Hrb as ->. subst OL. clear - X. lia. }
  pose proof (rreserved_disjoint1 _ _ RF0 ltac:(fold OL; lia)) as DRo. fold OL oldb in DRo.
  assert (KT16 : 16 <= kt) by (subst kt; rewrite MLEN; clear - OL16 ND; lia).
  split; [exact rr_regions_wf|]. split; [|split; [|split; [|split]]].
  -
    destruct CX as (C1 & C2 & C3 & C4 & C5 & C6). unfold rmrep_ctx.
    assert (E1 : ctx_head_cells rstT = ctx_head_cells st) by (unfold ctx_head_cells; rewrite rr_ctx, !rr_pw by assumption; reflexivity).
    assert (E2 : actives rstT = actives st).
    { unfold actives. apply map_ext. intros a. unfold active. rewrite rr_ctx. apply rr_pw. apply (PC6 (Z.of_nat a)). }
    assert (E3 : usages rstT = usages st). { unfold usages. apply map_ext. intros. unfold usage. rewrite rr_ctx. reflexivity. }
    assert (E4 : unmap_seqs rstT = unmap_seqs st). { unfold unmap_seqs. apply map_ext. intros. unfold unmap_seq. rewrite rr_ctx. reflexivity. }
    assert (E5 : bouncess rstT = bouncess st). { unfold bouncess. apply map_ext. intros. unfold bounces. rewrite rr_ctx. reflexivity. }
    assert (E6 : ctx_tail_cells rstT = ctx_tail_cells st).
    { unfold ctx_tail_cells. rewrite rr_ctx. unfold brk_word. rewrite rr_ctx. destruct (c_brk (ctx st)) as [| |q off]; [reflexivity| reflexivity|].
      cbn in PC7. rewrite (rr_conc (q, off)) by exact PC7. reflexivity. }
    rewrite E1, E2, E3, E4, E5, E6.
    assert (L1 : length (actives st) = 48%nat) by (unfold actives; rewrite length_map, length_seq; reflexivity).
    assert (L2 : length (usages st) = 48%nat) by (unfold usages; rewrite length_map, length_seq; reflexivity).
    assert (L3 : length (unmap_seqs st) = 32%nat) by (unfold unmap_seqs; rewrite length_map, length_seq; reflexivity).
    assert (L4 : length (bouncess st) = 32%nat) by (unfold bouncess; rewrite length_map, length_seq; reflexivity).
    unfold RLIBC, RCTX in *.
    split; [|split; [|split; [|split; [|split]]]].
    + eapply rrw_cells_agree; [exact C1|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply ru64arr_agree; [exact C2|]. rewrite L1. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply ru64arr_agree; [exact C3|]. rewrite L2. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply ru8arr_agree; [exact C4|]. rewrite L3. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply ru8arr_agree; [exact C5|]. rewrite L4. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply rrw_cells_agree; [exact C6|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
  -
    destruct GL as (G1 & G2 & G3 & G4 & G5). unfold rmrep_globals, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RLIBC, RGOT_SSP, RSSP_GUARD in *.
    split; [|split; [|split; [|split]]].
    + eapply rrw_cells_agree; [exact G1|]. eapply agree_on_sub; [exact AGL| lia| cbn; lia].
    + eapply rrw_cells_agree; [exact G2|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply rrw_cells_agree; [exact G3|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply rrw_cells_agree; [exact G4|]. eapply agree_on_sub; [exact AGS1| lia| cbn; lia].
    + eapply rrw_cells_agree; [exact G5|]. eapply agree_on_sub; [exact AGS2| lia| cbn; lia].
  -
    destruct MSL as (ag & arg & kg & Hag & Hkg & Eg).
    destruct (rarea_conc st ag arg WF Hag) as (rga & Hrga & Cga & Sga0 & Sga1 & SgaL & NKg & RgB0 & RgAL & RgC).
    assert (HG : conc st g = conc st ag + (AREA_HDR + META_SIZE * kg)) by (rewrite Eg, conc_aadd by (rewrite Hrga; eauto); reflexivity).
    pose proof (rarea_lr_lo st ag arg rga WF Hag Hrga) as LRga.
    unfold AREA_HDR, META_SIZE, NSLOTS in *.
    intros a ar Ha. rewrite rr_areas in Ha. destruct (AR a ar Ha) as (A1 & A2 & A3). destruct (PA a ar Ha) as [Pa Pn].
    destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RaB0 & RaAL & RaC).
    pose proof (rarea_lr_lo st a ar ra WF Ha Hra) as LRa.
    assert (AGa : forall x, conc st a <= x < conc st a + 4096 -> ~ (conc st g + 16 <= x < conc st g + 24) -> ~ (conc st g + 32 <= x < conc st g + 40) -> m3 (wa x) = m1 (wa x))
      by (intros; eapply (AGA a ar Ha); eauto).

    assert (APG : a <> ag -> conc st a + 4096 <= conc st ag \/ conc st ag + 4096 <= conc st a).
    { intros NEa. destruct (N.eq_dec (fst a) (fst ag)) as [E|NE].
      - rewrite E, Hrga in Hra. injection Hra as ->. rewrite Ca, Cga.
        assert (snd a <> snd ag) by (intros E2; apply NEa; destruct a, ag; cbn in *; congruence).
        clear - H SaL SgaL. Z.div_mod_to_equations. nia.
      - pose proof (DJ _ _ _ _ Hra Hrga NE) as D. rewrite Ca, Cga. clear - D LRa LRga Sa0 Sa1 Sga0 Sga1. lia. }
    unfold rarea_rep. unfold AREA_HDR, META_SIZE, NSLOTS. rewrite (rr_conc a Pa), (rr_pw _ Pn).
    split; [|split].
    + eapply rrw_cells_agree; [exact A1|]. cbn [cells_size csize Nat.add]. intros x Hx. apply AGa; [clear - Hx; lia| |].
      all: destruct (aptr_eq_dec a ag) as [->|NEa]; [rewrite HG; clear - Hx Hkg; lia| pose proof (APG NEa) as D; rewrite HG; clear - Hx Hkg D; lia].
    + intros k Hk. unfold NSLOTS in Hk. rewrite rr_meta. destruct (aptr_eqb_spec (aadd a (24 + 40 * k)) g) as [EQ|NEQ].
      *
        assert (a = ag /\ k = kg) as [-> ->].
        { rewrite Eg in EQ. unfold aadd in EQ. clear - EQ Hk Hkg SaL SgaL. destruct a as [a1 a2], ag as [g1 g2]. cbn in EQ, SaL, SgaL. injection EQ as E1 E2.
          unfold NSLOTS in *. assert (a2 = g2) by (Z.div_mod_to_equations; lia). subst. split; [reflexivity| lia]. }
        assert (EC : conc st ag + 24 + 40 * kg = conc st g) by (rewrite HG; clear; lia). rewrite EC.
        pose proof (A2 kg Hkg) as OLD. rewrite <- Eg in OLD. rewrite EC in OLD.

        unfold meta_cells in OLD |- *.
        change [C8 (pw st (m_prev (get_meta_rec st g))); C8 (pw st (m_next (get_meta_rec st g))); C8 (pw st (m_mem (get_meta_rec st g)));
                C4 (wz (m_avail (get_meta_rec st g))); C4 (wz (m_freed (get_meta_rec st g))); C8 (wz (meta_word (get_meta_rec st g)))]
          with ([C8 (pw st (m_prev (get_meta_rec st g))); C8 (pw st (m_next (get_meta_rec st g)))] ++ [C8 (pw st (m_mem (get_meta_rec st g)))]
                ++ [C4 (wz (m_avail (get_meta_rec st g))); C4 (wz (m_freed (get_meta_rec st g)))] ++ [C8 (wz (meta_word (get_meta_rec st g)))]) in OLD.
        apply rw_cells_app_inv in OLD as [O1 OLD]. apply rw_cells_app_inv in OLD as [_ OLD]. apply rw_cells_app_inv in OLD as [O3 _].
        cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.to_nat] in O1, O3.
        replace (conc st g + 16 + 8) with (conc st g + 24) in O3 by (clear; lia).
        destruct (PM g) as (X1 & X2 & _).
        cbn [m_prev m_next m_mem m_avail m_freed f m_set_maplen]. rewrite (rr_pw _ X1), (rr_pw _ X2), HMEM. unfold pw at 3. cbn [oconc]. rewrite rr_conc_new, Z.add_0_r.
        change [C8 (pw st (m_prev (get_meta_rec st g))); C8 (pw st (m_next (get_meta_rec st g))); C8 (wz nb);
                C4 (wz (m_avail (get_meta_rec st g))); C4 (wz (m_freed (get_meta_rec st g))); C8 (wz (meta_word (f (get_meta_rec st g))))]
          with ([C8 (pw st (m_prev (get_meta_rec st g))); C8 (pw st (m_next (get_meta_rec st g)))] ++ ([C8 (wz nb)]
                ++ ([C4 (wz (m_avail (get_meta_rec st g))); C4 (wz (m_freed (get_meta_rec st g)))] ++ [C8 (wz (meta_word (f (get_meta_rec st g))))]))).
        pose proof (proj1 (proj2 A1)) as _x. clear _x.
        assert (GA : conc st ag <= conc st g /\ conc st g + 40 <= conc st ag + 4096) by (rewrite HG; clear - Hkg; lia).
        apply rw_cells_app2; [| apply rw_cells_app2; [| apply rw_cells_app2]].
        -- eapply rrw_cells_agree; [exact O1|]. cbn [cells_size csize Nat.add]. intros x Hx. apply (AGa x); clear - Hx GA; lia.
        -- fixaddr (conc st g + 16). exact NEWM.
        -- fixaddr (conc st g + 24). eapply rrw_cells_agree; [exact O3|]. cbn [cells_size csize Nat.add]. intros x Hx. apply (AGa x); clear - Hx GA; lia.
        -- fixaddr (conc st g + 32). exact NEWW.
      *
        rewrite <- (rr_meta_other _ NEQ), rr_meta_cells_other by exact NEQ.
        eapply rrw_cells_agree; [apply A2; exact Hk|]. unfold meta_cells. cbn [cells_size csize Nat.add length].
        intros x Hx. apply AGa; [clear - Hx Hk; lia| |].
        all: destruct (aptr_eq_dec a ag) as [->|NEa];
          [ assert (k <> kg) by (intros ->; apply NEQ; rewrite Eg; reflexivity); rewrite HG; clear - Hx Hk Hkg H; nia
          | pose proof (APG NEa) as D; rewrite HG; clear - Hx Hk Hkg D; lia ].
    + eapply rrw_cells_agree; [exact A3|]. cbn [cells_size csize Nat.add]. intros x Hx. apply AGa; [clear - Hx; lia| |].
      all: destruct (aptr_eq_dec a ag) as [->|NEa]; [rewrite HG; clear - Hx Hkg; lia| pose proof (APG NEa) as D; rewrite HG; clear - Hx Hkg D; lia].
  -
    intros b gh Hb. rewrite rr_groups in Hb. destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8].
    rewrite (rr_pw _ (PG b gh Hb)).
    destruct (N.eq_dec (fst b) rid) as [E|NE].
    +
      pose proof (ONLYG b gh Hb E) as ->. change bg with (rid, 0). rewrite rr_conc_new, Z.add_0_r.
      change bg with (rid, 0) in R. rewrite (conc_region st rid 0 r0 Hr0), Z.add_0_r in R. fold oldb in R.
      destruct R as [[Rwf RB] RW]. cbn [cells_size csize Nat.add] in RW. split; [split; [exact Rwf|]|].
      * eapply (rbytes_at_moved m1 m3 oldb nb); [exact RB| | clear - NB0; lia| | exact (or_intror _ _ eq_refl) || idtac |].
        all: rewrite (cells_bytes_length _ Rwf); cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add].
        all: match goal with |- ?G => idtac G end.
        -- intros i Hi. apply COPY. clear - Hi KT16. lia.
        -- clear - NCEIL ND. lia.
        -- clear - DRo OL16. lia.
        -- clear - DRn ND. lia.
      * cbn [cells_size csize Nat.add]. eapply wr_at_sub; [exact WRN| clear; lia| clear - ND; lia].
    + rewrite (rr_conc b NE). eapply rrw_cells_agree; [exact R|]. cbn. exact (AGG b gh Hb NE).
  -
    intros q rq Hq Hk. destruct (rr_lookup_inv q rq Hq) as [[-> ->]|[NE H]].
    +
      destruct (SH rid r0 Hr0 Kr0) as [HWr HB]. unfold rshadow_rep. cbn [r_base r_len r']. rewrite RR. split; [exact WRN|].
      intros o v Ho Hc. rewrite rr_shadow_rid in Hc. unfold cell_read in Hc. cbn [r_cells r_hav r_havp] in Hc.
      destruct (Z.lt_ge_cases o kt) as [LT|GE].
      *
        rewrite (rtrim_lookup_lt kt _ o LT) in Hc. fold (cell_read (get_shadow st rid) o) in Hc.
        destruct (HB o v ltac:(clear - Ho LT KT; subst OL; lia) Hc) as [Bt Hv]. split; [|exact Hv].
        eapply (rbytes_at_moved m1 m3 (oldb + o) (nb + o)); [exact Bt| | clear - NB0 Ho; lia| | |]; cbn [length Z.of_nat Pos.of_succ_nat].
        -- intros i Hi. replace (nb + o + i) with (nb + (o + i)) by lia. replace (oldb + o + i) with (oldb + (o + i)) by lia. apply COPY. clear - Hi LT Ho; lia.
        -- clear - NCEIL Ho; lia.
        -- clear - DRo Ho LT KT; lia.
        -- clear - DRn Ho; lia.
      *
        assert (NONE : trim_cells kt (r_cells (get_shadow st rid)) !! o = None).
        { destruct (trim_cells kt (r_cells (get_shadow st rid)) !! o) as [x|] eqn:E; [| reflexivity].
          apply rtrim_lookup_Some in E as [_ E]. clear - E GE. lia. }
        rewrite NONE in Hc.
        assert (Hv : v = 0) by (destruct (stale_pg _ _ || stale _ _ _); inversion Hc; reflexivity). subst v.
        split; [| clear; lia]. split; [clear - NB0 Ho; lia|]. split; [cbn; clear - NCEIL Ho; lia|].
        intros i Hi. destruct i; [| cbn in Hi; lia]. cbn [nth_error]. rewrite Z.add_0_r.
        rewrite ref_mrd_overlay by (rewrite wa_unsigned by (clear - NB0 Ho NCEIL; lia); clear - DRn Ho NB0; lia).
        apply ZERO. clear - GE Ho; lia.
    + eapply rshadow_rep_ext; [apply rr_shadow_other; exact NE|].
      destruct (SH q rq H Hk) as [HWr HB]. pose proof (AGR q rq H Hk NE) as AG. split.
      * eapply rwr_at_agree; eauto.
      * intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
        eapply rbytes_at_agree; [exact Bt|]. cbn. eapply agree_on_sub; [exact AG| lia| lia].
Qed.
End RREMAP.

End CEIL.

Ltac fixaddr v := lazymatch goal with |- rw_cells _ _ ?A _ => replace A with v by (cbn; lia) end.

From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import Ubsan.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Tac OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Image OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Decode OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Arr.
Import OSSVerify.msgpack_c.unpack_pack_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_F_malloc_free OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocTree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocKit_A OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocKit_AB OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocKit_A2 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocRep OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_F_am_K2.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Malloc OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MallocCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MI_Kit OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Realloc.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.Monad OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.Prog.
Import RMallocRep.TwinB RMallocTree.TwinB RMallocKit_B.TwinB RMallocKit_A.TwinB RMallocKit_A2.TwinB.

Set Keyed Unification.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.CeilLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Lemma rw_cells_app2 m A cs1 cs2 :
  rw_cells rsegs m A cs1 -> rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2 -> rw_cells rsegs m A (cs1 ++ cs2).
Proof.
  intros [[W1 B1] R1] [[W2 B2] R2]. split; [split|].
  - apply cells_wf_app. auto.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|]. rewrite cells_bytes_length by exact W1. exact B2.
  - rewrite cells_size_app. destruct R1 as (X0 & X1 & XW). destruct R2 as (Y0 & Y1 & YW). split; [lia|]. split; [lia|].
    intros i Hi. destruct (Z.lt_ge_cases i (Z.of_nat (cells_size cs1))) as [LT|GE]; [apply XW; lia|].
    replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia. apply YW. lia.
Qed.

Lemma rw_cells_app_inv m A cs1 cs2 :
  rw_cells rsegs m A (cs1 ++ cs2) -> rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros [[W B] R]. apply cells_wf_app in W as [W1 W2]. rewrite cells_bytes_app in B. apply bytes_at_app in B as [B1 B2].
  rewrite cells_bytes_length in B2 by exact W1. rewrite cells_size_app in R.
  split; (split; [split; assumption|]); [eapply wr_at_sub; [exact R| lia| lia]|].
  eapply wr_at_sub; [exact R| lia| lia].
Qed.

Lemma rbytes_at_moved m1 m3 (src dst : Z) bs :
  bytes_at rsegs m1 src bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> m3 (wa (dst + i)) = m1 (wa (src + i))) ->
  0 <= dst -> dst + Z.of_nat (length bs) <= 2^64 ->
  (src + Z.of_nat (length bs) <= 0x10000 \/ 0x8a000 <= src) -> (dst + Z.of_nat (length bs) <= 0x10000 \/ 0x8a000 <= dst) ->
  bytes_at rsegs m3 dst bs.
Proof.
  intros (H0 & H1 & HB) CP D0 D1 IS ID. split; [exact D0|]. split; [exact D1|]. intros i Hi.
  rewrite ref_mrd_overlay by (rewrite wa_unsigned by lia; lia). rewrite CP by lia.
  rewrite <- (HB i Hi). rewrite ref_mrd_overlay by (rewrite wa_unsigned by lia; lia). reflexivity.
Qed.

Lemma rtrim_lookup_lt k cs o : o < k -> trim_cells k cs !! o = cs !! o.
Proof.
  intros Ho. unfold trim_cells. rewrite map_lookup_filter. destruct (cs !! o) as [x|]; cbn; [| reflexivity].
  rewrite option_guard_True by (cbn; exact Ho). reflexivity.
Qed.
Lemma rtrim_lookup_Some k cs o x : trim_cells k cs !! o = Some x -> cs !! o = Some x /\ o < k.
Proof. intros H. unfold trim_cells in H. apply map_lookup_filter_Some in H. cbn in H. exact H. Qed.

Ltac fixaddr v := lazymatch goal with |- rw_cells _ _ ?A _ => replace A with v by (cbn; lia) end.

Section RREMAP.
Variables (st : mstate) (m1 m3 : mem) (rid : N) (r0 : region) (g : aptr) (ai : Z) (nb needed : Z).
Let bg : aptr := (rid, 0).
Let OL : Z := round_up_pg (r_len r0).
Let oldb : Z := r_base r0.
Let r' : region := mkRegion RKGroup nb needed.
Let f : meta -> meta := m_set_maplen (needed / 4096).
Let P : N -> Prop := fun q => q <> rid.
Definition rstR : mstate := upd_meta g f (set_regions (<[rid := r']> (s_regions st)) st).
Let kt : Z := Z.min (m_maplen (get_meta_rec st g) * 4096) needed.
Definition rstT : mstate := trim_shadow rid kt rstR.

Hypothesis MR : rmrep st m1.
Hypothesis Hr0 : (s_regions st) !! rid = Some r0.
Hypothesis Kr0 : r_kind r0 = RKGroup.
Hypothesis Hg : (s_groups st) !! bg = Some (mkGhdr (Some g) ai).
Hypothesis HMEM : m_mem (get_meta_rec st g) = Some bg.
Hypothesis MSL : meta_slot st g.
Hypothesis MLEN : m_maplen (get_meta_rec st g) * 4096 = OL.
Hypothesis MWOK : 0 <= m_last_idx (get_meta_rec st g) < 32 /\ 0 <= m_freeable (get_meta_rec st g) < 2 /\ 0 <= m_sizeclass (get_meta_rec st g) < 64.
Hypothesis ONLYG : forall b gh, (s_groups st) !! b = Some gh -> fst b = rid -> b = bg.

Hypothesis PC1 : optr_in P (c_free_meta_head (ctx st)).
Hypothesis PC2 : optr_in P (c_avail_meta (ctx st)).
Hypothesis PC3 : optr_in P (c_meta_area_head (ctx st)).
Hypothesis PC4 : optr_in P (c_meta_area_tail (ctx st)).
Hypothesis PC5 : optr_in P (c_avail_meta_areas (ctx st)).
Hypothesis PC6 : forall sc, optr_in P (active st sc).
Hypothesis PC7 : match c_brk (ctx st) with BrkLive q _ => P q | _ => True end.
Hypothesis PM : forall g', optr_in P (m_prev (get_meta_rec st g')) /\ optr_in P (m_next (get_meta_rec st g'))
                           /\ (g' <> g -> optr_in P (m_mem (get_meta_rec st g'))).
Hypothesis PA : forall a ar, (s_areas st) !! a = Some ar -> P (fst a) /\ optr_in P (a_next ar).
Hypothesis PG : forall b gh, (s_groups st) !! b = Some gh -> optr_in P (g_meta gh).

Hypothesis NB0 : 0 < nb.
Hypothesis NBA : nb mod 4096 = 0.
Hypothesis NDA : needed mod 4096 = 0.
Hypothesis NDP : 0 < needed.
Hypothesis NCEIL : nb + needed <= alloc_ceiling.
Hypothesis RFR : ranges_free ref_reserved nb needed = true.
Hypothesis DJ' : forall q rq, (s_regions st) !! q = Some rq -> q <> rid -> nb + needed <= lr_lo rq \/ r_base rq + round_up_pg (r_len rq) <= nb.

Hypothesis AGL : agree_on m1 m3 RMLOCK 4.
Hypothesis AGC : agree_on m1 m3 RLIBC 0x418.
Hypothesis AGS1 : agree_on m1 m3 RGOT_SSP 8.
Hypothesis AGS2 : agree_on m1 m3 RSSP_GUARD 8.
Hypothesis AGA : forall a ar, (s_areas st) !! a = Some ar ->
  forall x, conc st a <= x < conc st a + 4096 -> ~ (conc st g + 16 <= x < conc st g + 24) -> ~ (conc st g + 32 <= x < conc st g + 40) ->
  m3 (wa x) = m1 (wa x).
Hypothesis NEWM : rw_cells rsegs m3 (conc st g + 16) [C8 (wz nb)].
Hypothesis NEWW : rw_cells rsegs m3 (conc st g + 32) [C8 (wz (meta_word (f (get_meta_rec st g))))].
Hypothesis AGG : forall b gh, (s_groups st) !! b = Some gh -> fst b <> rid -> agree_on m1 m3 (conc st b) 9.
Hypothesis AGR : forall q rq, (s_regions st) !! q = Some rq -> r_kind rq = RKGroup -> q <> rid -> agree_on m1 m3 (r_base rq) (round_up_pg (r_len rq)).
Hypothesis COPY : forall i, 0 <= i < kt -> m3 (wa (nb + i)) = m1 (wa (oldb + i)).
Hypothesis ZERO : forall i, kt <= i < needed -> m3 (wa (nb + i)) = Some (b8 0).
Hypothesis WRN : wr_at rsegs m3 nb needed.

Lemma rr_round : round_up_pg needed = needed.
Proof. apply round_up_pg_aligned. exact NDA. Qed.

Lemma rr_regions : s_regions rstT = <[rid := r']> (s_regions st).
Proof. reflexivity. Qed.
Lemma rr_lookup_inv q rq : (s_regions rstT) !! q = Some rq -> (q = rid /\ rq = r') \/ (q <> rid /\ (s_regions st) !! q = Some rq).
Proof.
  intros H. rewrite rr_regions in H. destruct (N.eq_dec q rid) as [->|NE].
  - left. rewrite lookup_insert_eq in H. inversion H. auto.
  - right. rewrite lookup_insert_ne in H by congruence. auto.
Qed.
Lemma rr_lookup_old q : q <> rid -> (s_regions rstT) !! q = (s_regions st) !! q.
Proof. intros. rewrite rr_regions, lookup_insert_ne by congruence. reflexivity. Qed.
Lemma rr_lookup_new : (s_regions rstT) !! rid = Some r'.
Proof. rewrite rr_regions. apply lookup_insert_eq. Qed.
Lemma rr_conc q : P (fst q) -> conc rstT q = conc st q.
Proof. intros H. unfold conc, get_region. rewrite rr_lookup_old by exact H. reflexivity. Qed.
Lemma rr_conc_new off : conc rstT (rid, off) = nb + off.
Proof. unfold conc, get_region. cbn [fst snd]. rewrite rr_lookup_new. reflexivity. Qed.
Lemma rr_pw p : optr_in P p -> pw rstT p = pw st p.
Proof. destruct p as [q|]; cbn; intros H; unfold pw, oconc; [rewrite rr_conc by exact H|]; reflexivity. Qed.
Lemma rr_ctx : ctx rstT = ctx st. Proof. reflexivity. Qed.
Lemma rr_areas : s_areas rstT = s_areas st. Proof. reflexivity. Qed.
Lemma rr_groups : s_groups rstT = s_groups st. Proof. reflexivity. Qed.
Lemma rr_meta x : get_meta_rec rstT x = if aptr_eqb x g then f (get_meta_rec st g) else get_meta_rec st x.
Proof.
  change (get_meta_rec rstT x) with (get_meta_rec rstR x). unfold rstR. rewrite (MI_Kit.get_meta_rec_upd (set_regions (<[rid := r']> (s_regions st)) st) g f x).
  reflexivity.
Qed.
Lemma rr_meta_other x : x <> g -> get_meta_rec rstT x = get_meta_rec st x.
Proof. intros NE. rewrite rr_meta. destruct (aptr_eqb_spec x g); [congruence| reflexivity]. Qed.
Lemma rr_meta_g : get_meta_rec rstT g = f (get_meta_rec st g).
Proof. rewrite rr_meta, aptr_eqb_refl. reflexivity. Qed.
Lemma rr_shadow_other q : q <> rid -> get_shadow rstT q = get_shadow st q.
Proof. intros NE. rewrite (get_shadow_eq rstT). unfold rstT, trim_shadow, upd_shadow. cbn [s_shadow set_shadow]. rewrite lookup_insert_ne by congruence. reflexivity. Qed.
Lemma rr_shadow_rid : get_shadow rstT rid = mkShadow (trim_cells kt (r_cells (get_shadow st rid))) (r_hav (get_shadow st rid)) (r_havp (get_shadow st rid)).
Proof. rewrite (get_shadow_eq rstT). unfold rstT, trim_shadow, upd_shadow. cbn [s_shadow set_shadow]. rewrite lookup_insert_eq. reflexivity. Qed.

Lemma rr_kt : 0 <= kt <= needed /\ kt <= OL.
Proof.
  pose proof MR as (WF & _). pose proof WF as (_ & WR & _). destruct (WR _ _ Hr0) as (_ & _ & L0 & _).
  subst kt. rewrite MLEN. pose proof (round_up_pg_ge (r_len r0)). subst OL. lia.
Qed.

Lemma rr_meta_cells_other x : x <> g -> meta_cells rstT (get_meta_rec rstT x) = meta_cells st (get_meta_rec st x).
Proof.
  intros NE. rewrite (rr_meta_other x NE). destruct (PM x) as (X1 & X2 & X3). unfold meta_cells. rewrite !rr_pw by auto. reflexivity.
Qed.

Lemma rr_nd : 4096 <= needed.
Proof. clear - NDA NDP. Z.div_mod_to_equations. lia. Qed.

Lemma rr_regions_wf : rregions_wf rstT.
Proof.
  pose proof MR as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG). pose proof rr_round as RR. pose proof rr_nd as ND.
  destruct (WR _ _ Hr0) as (B0 & BAL & L0 & BC & RF0).
  split; [exact RS|]. split; [|split; [|split]].
  - intros q rq Hq. destruct (rr_lookup_inv q rq Hq) as [[-> ->]|[NE H]].
    + cbn [r_base r_len r']. rewrite RR. repeat split; try lia. exact RFR.
    + exact (WR q rq H).
  - intros q1 rq1 q2 rq2 H1 H2 NE.
    destruct (rr_lookup_inv q1 rq1 H1) as [[-> ->]|[NE1 H1']]; destruct (rr_lookup_inv q2 rq2 H2) as [[-> ->]|[NE2 H2']].
    + congruence.
    + cbn [r_base r_len r']. rewrite RR. pose proof (DJ' q2 rq2 H2' NE2). unfold lr_lo at 2. cbn [r_kind r_base r']. lia.
    + cbn [r_base r_len r']. rewrite RR. pose proof (DJ' q1 rq1 H1' NE1). unfold lr_lo at 1. cbn [r_kind r_base r']. lia.
    + exact (DJ q1 rq1 q2 rq2 H1' H2' NE).
  - intros a ar Ha. rewrite rr_areas in Ha. destruct (WA a ar Ha) as (ra & Hra & REST). destruct (PA a ar Ha) as [Pa _].
    exists ra. rewrite rr_lookup_old by exact Pa. auto.
  - intros b gh Hb. rewrite rr_groups in Hb. destruct (WG b gh Hb) as (rb & Hrb & REST).
    destruct (N.eq_dec (fst b) rid) as [E|NE].
    + pose proof (ONLYG b gh Hb E) as ->. exists r'. cbn [fst]. rewrite rr_lookup_new. split; [reflexivity|].
      cbn [r_kind r_len r' snd]. rewrite RR. split; [reflexivity|]. change (snd bg) with 0. split; [clear; lia|]. split; [clear -ND; lia| reflexivity].
    + exists rb. rewrite rr_lookup_old by exact NE. auto.
Qed.

Theorem rmrep_remap : rmrep rstT m3.
Proof.
  pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (RS & WR & DJ & WA & WG). pose proof rr_round as RR. pose proof rr_kt as KT. pose proof rr_nd as ND.
  destruct (WR _ _ Hr0) as (B0 & BAL & L0 & BC & RF0). pose_ceil.
  pose proof (rreserved_disjoint1 _ _ RFR NDP) as DRn.
  assert (OL16 : 16 <= OL).
  { destruct (WG bg _ Hg) as (rb & Hrb & _ & _ & X & _). change (fst bg) with rid in Hrb. change (snd bg) with 0 in X. rewrite Hr0 in Hrb. injection Hrb as ->. subst OL. clear - X. lia. }
  pose proof (rreserved_disjoint1 _ _ RF0 ltac:(fold OL; lia)) as DRo. fold OL oldb in DRo.
  assert (KT16 : 16 <= kt) by (subst kt; rewrite MLEN; clear - OL16 ND; lia).
  split; [exact rr_regions_wf|]. split; [|split; [|split; [|split]]].
  -
    destruct CX as (C1 & C2 & C3 & C4 & C5 & C6). unfold rmrep_ctx.
    assert (E1 : ctx_head_cells rstT = ctx_head_cells st) by (unfold ctx_head_cells; rewrite rr_ctx, !rr_pw by assumption; reflexivity).
    assert (E2 : actives rstT = actives st).
    { unfold actives. apply map_ext. intros a. unfold active. rewrite rr_ctx. apply rr_pw. apply (PC6 (Z.of_nat a)). }
    assert (E3 : usages rstT = usages st). { unfold usages. apply map_ext. intros. unfold usage. rewrite rr_ctx. reflexivity. }
    assert (E4 : unmap_seqs rstT = unmap_seqs st). { unfold unmap_seqs. apply map_ext. intros. unfold unmap_seq. rewrite rr_ctx. reflexivity. }
    assert (E5 : bouncess rstT = bouncess st). { unfold bouncess. apply map_ext. intros. unfold bounces. rewrite rr_ctx. reflexivity. }
    assert (E6 : ctx_tail_cells rstT = ctx_tail_cells st).
    { unfold ctx_tail_cells. rewrite rr_ctx. unfold brk_word. rewrite rr_ctx. destruct (c_brk (ctx st)) as [| |q off]; [reflexivity| reflexivity|].
      cbn in PC7. rewrite (rr_conc (q, off)) by exact PC7. reflexivity. }
    rewrite E1, E2, E3, E4, E5, E6.
    assert (L1 : length (actives st) = 48%nat) by (unfold actives; rewrite length_map, length_seq; reflexivity).
    assert (L2 : length (usages st) = 48%nat) by (unfold usages; rewrite length_map, length_seq; reflexivity).
    assert (L3 : length (unmap_seqs st) = 32%nat) by (unfold unmap_seqs; rewrite length_map, length_seq; reflexivity).
    assert (L4 : length (bouncess st) = 32%nat) by (unfold bouncess; rewrite length_map, length_seq; reflexivity).
    unfold RLIBC, RCTX in *.
    split; [|split; [|split; [|split; [|split]]]].
    + eapply rrw_cells_agree; [exact C1|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply ru64arr_agree; [exact C2|]. rewrite L1. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply ru64arr_agree; [exact C3|]. rewrite L2. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply ru8arr_agree; [exact C4|]. rewrite L3. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply ru8arr_agree; [exact C5|]. rewrite L4. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply rrw_cells_agree; [exact C6|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
  -
    destruct GL as (G1 & G2 & G3 & G4 & G5). unfold rmrep_globals, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RLIBC, RGOT_SSP, RSSP_GUARD in *.
    split; [|split; [|split; [|split]]].
    + eapply rrw_cells_agree; [exact G1|]. eapply agree_on_sub; [exact AGL| lia| cbn; lia].
    + eapply rrw_cells_agree; [exact G2|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply rrw_cells_agree; [exact G3|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply rrw_cells_agree; [exact G4|]. eapply agree_on_sub; [exact AGS1| lia| cbn; lia].
    + eapply rrw_cells_agree; [exact G5|]. eapply agree_on_sub; [exact AGS2| lia| cbn; lia].
  -
    destruct MSL as (ag & arg & kg & Hag & Hkg & Eg).
    destruct (rarea_conc st ag arg WF Hag) as (rga & Hrga & Cga & Sga0 & Sga1 & SgaL & NKg & RgB0 & RgAL & RgC).
    assert (HG : conc st g = conc st ag + (AREA_HDR + META_SIZE * kg)) by (rewrite Eg, conc_aadd by (rewrite Hrga; eauto); reflexivity).
    pose proof (rarea_lr_lo st ag arg rga WF Hag Hrga) as LRga.
    unfold AREA_HDR, META_SIZE, NSLOTS in *.
    intros a ar Ha. rewrite rr_areas in Ha. destruct (AR a ar Ha) as (A1 & A2 & A3). destruct (PA a ar Ha) as [Pa Pn].
    destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RaB0 & RaAL & RaC).
    pose proof (rarea_lr_lo st a ar ra WF Ha Hra) as LRa.
    assert (AGa : forall x, conc st a <= x < conc st a + 4096 -> ~ (conc st g + 16 <= x < conc st g + 24) -> ~ (conc st g + 32 <= x < conc st g + 40) -> m3 (wa x) = m1 (wa x))
      by (intros; eapply (AGA a ar Ha); eauto).

    assert (APG : a <> ag -> conc st a + 4096 <= conc st ag \/ conc st ag + 4096 <= conc st a).
    { intros NEa. destruct (N.eq_dec (fst a) (fst ag)) as [E|NE].
      - rewrite E, Hrga in Hra. injection Hra as ->. rewrite Ca, Cga.
        assert (snd a <> snd ag) by (intros E2; apply NEa; destruct a, ag; cbn in *; congruence).
        clear - H SaL SgaL. Z.div_mod_to_equations. nia.
      - pose proof (DJ _ _ _ _ Hra Hrga NE) as D. rewrite Ca, Cga. clear - D LRa LRga Sa0 Sa1 Sga0 Sga1. lia. }
    unfold rarea_rep. unfold AREA_HDR, META_SIZE, NSLOTS. rewrite (rr_conc a Pa), (rr_pw _ Pn).
    split; [|split].
    + eapply rrw_cells_agree; [exact A1|]. cbn [cells_size csize Nat.add]. intros x Hx. apply AGa; [clear - Hx; lia| |].
      all: destruct (aptr_eq_dec a ag) as [->|NEa]; [rewrite HG; clear - Hx Hkg; lia| pose proof (APG NEa) as D; rewrite HG; clear - Hx Hkg D; lia].
    + intros k Hk. unfold NSLOTS in Hk. rewrite rr_meta. destruct (aptr_eqb_spec (aadd a (24 + 40 * k)) g) as [EQ|NEQ].
      *
        assert (a = ag /\ k = kg) as [-> ->].
        { rewrite Eg in EQ. unfold aadd in EQ. clear - EQ Hk Hkg SaL SgaL. destruct a as [a1 a2], ag as [g1 g2]. cbn in EQ, SaL, SgaL. injection EQ as E1 E2.
          unfold NSLOTS in *. assert (a2 = g2) by (Z.div_mod_to_equations; lia). subst. split; [reflexivity| lia]. }
        assert (EC : conc st ag + 24 + 40 * kg = conc st g) by (rewrite HG; clear; lia). rewrite EC.
        pose proof (A2 kg Hkg) as OLD. rewrite <- Eg in OLD. rewrite EC in OLD.

        unfold meta_cells in OLD |- *.
        change [C8 (pw st (m_prev (get_meta_rec st g))); C8 (pw st (m_next (get_meta_rec st g))); C8 (pw st (m_mem (get_meta_rec st g)));
                C4 (wz (m_avail (get_meta_rec st g))); C4 (wz (m_freed (get_meta_rec st g))); C8 (wz (meta_word (get_meta_rec st g)))]
          with ([C8 (pw st (m_prev (get_meta_rec st g))); C8 (pw st (m_next (get_meta_rec st g)))] ++ [C8 (pw st (m_mem (get_meta_rec st g)))]
                ++ [C4 (wz (m_avail (get_meta_rec st g))); C4 (wz (m_freed (get_meta_rec st g)))] ++ [C8 (wz (meta_word (get_meta_rec st g)))]) in OLD.
        apply rw_cells_app_inv in OLD as [O1 OLD]. apply rw_cells_app_inv in OLD as [_ OLD]. apply rw_cells_app_inv in OLD as [O3 _].
        cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.to_nat] in O1, O3.
        replace (conc st g + 16 + 8) with (conc st g + 24) in O3 by (clear; lia).
        destruct (PM g) as (X1 & X2 & _).
        cbn [m_prev m_next m_mem m_avail m_freed f m_set_maplen]. rewrite (rr_pw _ X1), (rr_pw _ X2), HMEM. unfold pw at 3. cbn [oconc]. rewrite rr_conc_new, Z.add_0_r.
        change [C8 (pw st (m_prev (get_meta_rec st g))); C8 (pw st (m_next (get_meta_rec st g))); C8 (wz nb);
                C4 (wz (m_avail (get_meta_rec st g))); C4 (wz (m_freed (get_meta_rec st g))); C8 (wz (meta_word (f (get_meta_rec st g))))]
          with ([C8 (pw st (m_prev (get_meta_rec st g))); C8 (pw st (m_next (get_meta_rec st g)))] ++ ([C8 (wz nb)]
                ++ ([C4 (wz (m_avail (get_meta_rec st g))); C4 (wz (m_freed (get_meta_rec st g)))] ++ [C8 (wz (meta_word (f (get_meta_rec st g))))]))).
        pose proof (proj1 (proj2 A1)) as _x. clear _x.
        assert (GA : conc st ag <= conc st g /\ conc st g + 40 <= conc st ag + 4096) by (rewrite HG; clear - Hkg; lia).
        apply rw_cells_app2; [| apply rw_cells_app2; [| apply rw_cells_app2]].
        -- eapply rrw_cells_agree; [exact O1|]. cbn [cells_size csize Nat.add]. intros x Hx. apply (AGa x); clear - Hx GA; lia.
        -- fixaddr (conc st g + 16). exact NEWM.
        -- fixaddr (conc st g + 24). eapply rrw_cells_agree; [exact O3|]. cbn [cells_size csize Nat.add]. intros x Hx. apply (AGa x); clear - Hx GA; lia.
        -- fixaddr (conc st g + 32). exact NEWW.
      *
        rewrite <- (rr_meta_other _ NEQ), rr_meta_cells_other by exact NEQ.
        eapply rrw_cells_agree; [apply A2; exact Hk|]. unfold meta_cells. cbn [cells_size csize Nat.add length].
        intros x Hx. apply AGa; [clear - Hx Hk; lia| |].
        all: destruct (aptr_eq_dec a ag) as [->|NEa];
          [ assert (k <> kg) by (intros ->; apply NEQ; rewrite Eg; reflexivity); rewrite HG; clear - Hx Hk Hkg H; nia
          | pose proof (APG NEa) as D; rewrite HG; clear - Hx Hk Hkg D; lia ].
    + eapply rrw_cells_agree; [exact A3|]. cbn [cells_size csize Nat.add]. intros x Hx. apply AGa; [clear - Hx; lia| |].
      all: destruct (aptr_eq_dec a ag) as [->|NEa]; [rewrite HG; clear - Hx Hkg; lia| pose proof (APG NEa) as D; rewrite HG; clear - Hx Hkg D; lia].
  -
    intros b gh Hb. rewrite rr_groups in Hb. destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8].
    rewrite (rr_pw _ (PG b gh Hb)).
    destruct (N.eq_dec (fst b) rid) as [E|NE].
    +
      pose proof (ONLYG b gh Hb E) as ->. change bg with (rid, 0). rewrite rr_conc_new, Z.add_0_r.
      change bg with (rid, 0) in R. rewrite (conc_region st rid 0 r0 Hr0), Z.add_0_r in R. fold oldb in R.
      destruct R as [[Rwf RB] RW]. cbn [cells_size csize Nat.add] in RW. split; [split; [exact Rwf|]|].
      * eapply (rbytes_at_moved m1 m3 oldb nb); [exact RB| | clear - NB0; lia| | exact (or_intror _ _ eq_refl) || idtac |].
        all: rewrite (cells_bytes_length _ Rwf); cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add].
        all: match goal with |- ?G => idtac G end.
        -- intros i Hi. apply COPY. clear - Hi KT16. lia.
        -- clear - NCEIL ND. lia.
        -- clear - DRo OL16. lia.
        -- clear - DRn ND. lia.
      * cbn [cells_size csize Nat.add]. eapply wr_at_sub; [exact WRN| clear; lia| clear - ND; lia].
    + rewrite (rr_conc b NE). eapply rrw_cells_agree; [exact R|]. cbn. exact (AGG b gh Hb NE).
  -
    intros q rq Hq Hk. destruct (rr_lookup_inv q rq Hq) as [[-> ->]|[NE H]].
    +
      destruct (SH rid r0 Hr0 Kr0) as [HWr HB]. unfold rshadow_rep. cbn [r_base r_len r']. rewrite RR. split; [exact WRN|].
      intros o v Ho Hc. rewrite rr_shadow_rid in Hc. unfold cell_read in Hc. cbn [r_cells r_hav r_havp] in Hc.
      destruct (Z.lt_ge_cases o kt) as [LT|GE].
      *
        rewrite (rtrim_lookup_lt kt _ o LT) in Hc. fold (cell_read (get_shadow st rid) o) in Hc.
        destruct (HB o v ltac:(clear - Ho LT KT; subst OL; lia) Hc) as [Bt Hv]. split; [|exact Hv].
        eapply (rbytes_at_moved m1 m3 (oldb + o) (nb + o)); [exact Bt| | clear - NB0 Ho; lia| | |]; cbn [length Z.of_nat Pos.of_succ_nat].
        -- intros i Hi. replace (nb + o + i) with (nb + (o + i)) by lia. replace (oldb + o + i) with (oldb + (o + i)) by lia. apply COPY. clear - Hi LT Ho; lia.
        -- clear - NCEIL Ho; lia.
        -- clear - DRo Ho LT KT; lia.
        -- clear - DRn Ho; lia.
      *
        assert (NONE : trim_cells kt (r_cells (get_shadow st rid)) !! o = None).
        { destruct (trim_cells kt (r_cells (get_shadow st rid)) !! o) as [x|] eqn:E; [| reflexivity].
          apply rtrim_lookup_Some in E as [_ E]. clear - E GE. lia. }
        rewrite NONE in Hc.
        assert (Hv : v = 0) by (destruct (stale_pg _ _ || stale _ _ _); inversion Hc; reflexivity). subst v.
        split; [| clear; lia]. split; [clear - NB0 Ho; lia|]. split; [cbn; clear - NCEIL Ho; lia|].
        intros i Hi. destruct i; [| cbn in Hi; lia]. cbn [nth_error]. rewrite Z.add_0_r.
        rewrite ref_mrd_overlay by (rewrite wa_unsigned by (clear - NB0 Ho NCEIL; lia); clear - DRn Ho NB0; lia).
        apply ZERO. clear - GE Ho; lia.
    + eapply rshadow_rep_ext; [apply rr_shadow_other; exact NE|].
      destruct (SH q rq H Hk) as [HWr HB]. pose proof (AGR q rq H Hk NE) as AG. split.
      * eapply rwr_at_agree; eauto.
      * intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
        eapply rbytes_at_agree; [exact Bt|]. cbn. eapply agree_on_sub; [exact AG| lia| lia].
Qed.
End RREMAP.

End CEIL.

Ltac fixaddr v := lazymatch goal with |- rw_cells _ _ ?A _ => replace A with v by (cbn; lia) end.
End TwinB.
