(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs ImgFacts.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import STree Malloc MallocCtrl KRemapDef MRemapOp MI_Inv MI_Kit MI_Ext MI_WGroup MI_WAMeta MI_Cnt MI_Pres2 MI_WFree MI_WRealloc MI_WRemap.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Malloc Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocKit_A MallocBlocks.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Malloc Require Import MallocFacts_B MallocFacts_Bpres MallocFacts_inv MallocFacts_inv3 F_free_K MallocRep.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import RMallocRep RMallocTree RMallocKit_A RMallocKit_B RMallocKit_B2 RMalloc_fp RF_realloc_C RF_realloc_rep.
Import ListNotations.

Local Ltac arith_atom T := lazymatch T with
  | Z.le _ _ => idtac | Z.lt _ _ => idtac | Z.ge _ _ => idtac | Z.gt _ _ => idtac
  | @eq Z _ _ => idtac | @eq nat _ _ => idtac | @eq N _ _ => idtac | @eq positive _ _ => idtac
  | le _ _ => idtac | lt _ _ => idtac | ge _ _ => idtac | gt _ _ => idtac | N.le _ _ => idtac | N.lt _ _ => idtac
  | True => idtac | False => idtac end.
Local Ltac arith_prop T := lazymatch T with
  | ?A \/ ?B => arith_prop A; arith_prop B | ?A /\ ?B => arith_prop A; arith_prop B | not ?A => arith_prop A
  | ?A <-> ?B => arith_prop A; arith_prop B | ?A -> ?B => arith_prop A; arith_prop B | _ => arith_atom T end.
Local Ltac arith_goal := lazymatch goal with |- ?G => arith_prop G end.
Local Ltac clear_props := repeat match goal with H : ?T |- _ => lazymatch type of T with Prop => clear H end end.

Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section SS_REP.
Context {HGW : HasGuard}.
Context {HCEIL : HasCeiling}.
Variables (stB : mstate) (mB : mem) (c : cptr) (off n' : Z) (S b3 : Z) (r : region).

Let p : aptr := aadd c (UNIT * off).
Let e : aptr := aadd c (S - IB).
Let P := r_base r + snd c + UNIT * off.
Let E := r_base r + snd c + S - IB.

Hypothesis HMR : rmrep stB mB.
Hypothesis TK : ticks_ok stB.
Hypothesis Hr : (s_regions stB) !! (fst c) = Some r.
Hypothesis Hk : r_kind r = RKGroup.
Hypothesis C4 : 4 <= snd c.
Hypothesis CE : snd c + S - IB + 1 <= round_up_pg (r_len r).
Hypothesis NOGRP : forall b' gh, (s_groups stB) !! b' = Some gh -> fst b' = fst c ->
  snd b' + 9 <= snd c - 3 \/ snd c + S - IB <= snd b'.
Hypothesis OFF0 : 0 <= off.
Hypothesis N0 : 0 <= n'.
Hypothesis FIT : UNIT * off + n' <= S - IB.
Hypothesis R32 : S - IB - UNIT * off - n' < 2^32.
Hypothesis B3 : 0 <= b3.

#[using="off P E Hr Hk C4 CE NOGRP"] Lemma rss_wr8 : forall stx mx (o v : Z),
  rmrep stx mx -> ticks_ok stx ->
  s_regions stx = s_regions stB -> s_groups stx = s_groups stB ->
  snd c - 3 <= o < snd c + S - IB -> 0 <= v < 256 ->
  rmrep (wr8 (fst c, o) v stx) (write_to_mem mx (wa (r_base r + o)) [b8 v]) /\ ticks_ok (wr8 (fst c, o) v stx).
Proof.
  intros stx mx o v MRx TKx ER EG Ho Hv.
  split; [|apply ticks_ok_wr8; exact TKx].
  apply (rmrep_wr8 stx mx (fst c, o) v r MRx TKx); cbn [fst snd]; [rewrite ER; exact Hr| exact Hk| unfold IB in *; lia| |exact Hv].
  intros b' gh Hb' Hf. rewrite EG in Hb'. destruct (NOGRP b' gh Hb' Hf); lia.
Qed.

#[using="off P E Hr Hk C4 CE NOGRP"] Lemma rss_wr32 : forall stx mx (o v : Z),
  rmrep stx mx -> ticks_ok stx ->
  s_regions stx = s_regions stB -> s_groups stx = s_groups stB ->
  snd c - 3 <= o -> o + 4 <= snd c + S - IB -> 0 <= v < 2^32 ->
  rmrep (wr32 (fst c, o) v stx) (write_to_mem mx (wa (r_base r + o)) (le4 (wz v))) /\ ticks_ok (wr32 (fst c, o) v stx).
Proof.
  intros stx mx o v MRx TKx ER EG Ho Ho4 Hv.
  apply (rmrep_wr32 stx mx (fst c, o) v r MRx TKx); cbn [fst snd]; [rewrite ER; exact Hr| exact Hk| unfold IB in *; lia| unfold IB in *; lia| |exact Hv].
  intros b' gh Hb' Hf. rewrite EG in Hb'. destruct (NOGRP b' gh Hb' Hf); lia.
Qed.

#[using="HMR TK Hr Hk C4 CE NOGRP OFF0 N0 FIT R32 B3"] Lemma rss_mrep :
  rmrep (havoc p n' (wrs (ss_list p e n' b3) stB)) (rset_size_mem mB P E n' b3)
  /\ ticks_ok (havoc p n' (wrs (ss_list p e n' b3) stB)).
Proof.
  assert (ST2 : rmrep (wrs (ss_list p e n' b3) stB) (rset_size_mem mB P E n' b3) /\ ticks_ok (wrs (ss_list p e n' b3) stB)).
  { assert (ER1 : s_regions stB = s_regions stB) by reflexivity. assert (EG1 : s_groups stB = s_groups stB) by reflexivity.
    unfold ss_list, rset_size_mem. unfold p, e, aadd. cbn [fst snd].
    set (rsv := snd c + (S - IB) - (snd c + UNIT * off) - n').
    assert (Ersv : E - P - n' = rsv) by (unfold rsv, E, P; lia). rewrite Ersv.
    assert (RSV : 0 <= rsv < 2^32) by (unfold rsv; unfold UNIT, IB in *; lia).
    assert (KV : forall r', 0 <= r' <= 5 -> 0 <= Z.land b3 31 + Z.shiftl r' 5 < 256).
    { intros r' Hr'. rewrite Z.shiftl_mul_pow2 by lia. change (2^5) with 32.
      assert (0 <= Z.land b3 31 < 32) by (change 31 with (Z.ones 5); rewrite Z.land_ones by lia; pose proof (Z.mod_pos_bound b3 (2^5)); lia). lia. }
    assert (PFX : forall (o : Z) stx mx, snd c - 3 <= snd c + (S - IB) + - o -> 0 < o ->
              rmrep stx mx -> ticks_ok stx -> s_regions stx = s_regions stB -> s_groups stx = s_groups stB ->
              rmrep (wr8 (fst c, snd c + (S - IB) + - o) 0 stx) (write_to_mem mx (wa (E - o)) [b8 0]) /\ ticks_ok (wr8 (fst c, snd c + (S - IB) + - o) 0 stx)).
    { intros o stx mx Ho Ho' MRx TKx ERx EGx.
      replace (E - o) with (r_base r + (snd c + (S - IB) + - o)) by (unfold E; lia).
      apply (rss_wr8 stx mx _ 0 MRx TKx ERx EGx); lia. }
    assert (PL : forall stx mx r', 0 <= r' <= 5 -> rmrep stx mx -> ticks_ok stx -> s_regions stx = s_regions stB -> s_groups stx = s_groups stB ->
              rmrep (wr8 (fst c, snd c + UNIT * off + -3) (Z.land b3 31 + Z.shiftl r' 5) stx) (write_to_mem mx (wa (P - 3)) [b8 (Z.land b3 31 + Z.shiftl r' 5)])
              /\ ticks_ok (wr8 (fst c, snd c + UNIT * off + -3) (Z.land b3 31 + Z.shiftl r' 5) stx)).
    { intros stx mx r' Hr' MRx TKx ERx EGx.
      replace (P - 3) with (r_base r + (snd c + UNIT * off + -3)) by (unfold P; lia).
      apply (rss_wr8 stx mx _ _ MRx TKx ERx EGx); [unfold UNIT, IB in *; lia| apply KV; lia]. }
    destruct (Z.eqb_spec rsv 0) as [R0|RN0]; [| destruct (Z.leb_spec 5 rsv) as [R5|R5]]; cbn [negb app wrs].
    - replace (5 <=? rsv) with false by (symmetry; apply Z.leb_gt; lia). cbn [app wrs].
      apply (PL stB mB rsv ltac:(lia) HMR TK ER1 EG1).
    - destruct (PFX rsv stB mB ltac:(unfold rsv; unfold UNIT, IB in *; lia) ltac:(lia) HMR TK ER1 EG1) as [MA TA].
      set (stA := wr8 _ 0 stB) in MA, TA |- *. set (mA := write_to_mem mB _ _) in MA |- *.
      change (wr8 (fst c, snd c + (S - IB) + -5) 0
                (wr8 (fst c, snd c + (S - IB) + -4 + 3) (Z.shiftr rsv 24) (wr8 (fst c, snd c + (S - IB) + -4 + 2) (Z.shiftr rsv 16)
                  (wr8 (fst c, snd c + (S - IB) + -4 + 1) (Z.shiftr rsv 8) (wr8 (fst c, snd c + (S - IB) + -4) rsv stA)))))
        with (wr8 (fst c, snd c + (S - IB) + -5) 0 (wr32 (fst c, snd c + (S - IB) + -4) rsv stA)).
      rewrite (wr32_wr8_comm' (fst c, snd c + (S - IB) + -4) (fst c, snd c + (S - IB) + -5)) by (cbn; lia || reflexivity).
      destruct (PFX 5 stA mA ltac:(unfold UNIT, IB in *; lia) ltac:(lia) MA TA eq_refl eq_refl) as [MB' TB].
      destruct (rss_wr32 _ _ (snd c + (S - IB) + -4) rsv MB' TB eq_refl eq_refl) as [MC TC]; [unfold UNIT, IB in *; lia| unfold UNIT, IB in *; lia| lia|].
      replace (E - 4) with (r_base r + (snd c + (S - IB) + -4)) by (unfold E; lia).
      apply (PL _ _ 5 ltac:(lia) MC TC eq_refl eq_refl).
    - destruct (PFX rsv stB mB ltac:(unfold rsv; unfold UNIT, IB in *; lia) ltac:(lia) HMR TK ER1 EG1) as [MA TA].
      apply (PL _ _ rsv ltac:(lia) MA TA eq_refl eq_refl). }
  destruct ST2 as [M2 T2]. exact (rmrep_havoc _ _ p n' M2 T2).
Qed.
End SS_REP.

Lemma write_other : forall m (a : Z) bs (x : Z), 0 <= a -> a + Z.of_nat (length bs) <= 2^64 -> 0 <= x < 2^64 ->
  ~ (a <= x < a + Z.of_nat (length bs)) -> write_to_mem m (wa a) bs (wa x) = m (wa x).
Proof.
  intros m a bs x Ha Hl Hx Hn. rewrite write_to_mem_spec by lia. rewrite wa_unsigned by lia.
  destruct (Z.leb_spec0 a x); destruct (Z.ltb_spec0 x (a + Z.of_nat (length bs))); cbn [andb]; try reflexivity. exfalso; lia.
Qed.
Lemma le8_len z : length (le8 (wz z)) = 8%nat. Proof. reflexivity. Qed.

Lemma rw_cells_shift : forall m m' A A' cs,
  rw_cells rsegs m A cs ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> m' (wa (A' + i)) = m (wa (A + i))) ->
  0 <= A' -> A' + Z.of_nat (cells_size cs) <= 2^64 ->
  (A' + Z.of_nat (cells_size cs) <= 0x10000 \/ 0x2a000 <= A') /\ (A' + Z.of_nat (cells_size cs) <= 0x2a000 \/ 0x5d000 <= A') ->
  (A + Z.of_nat (cells_size cs) <= 0x10000 \/ 0x2a000 <= A) /\ (A + Z.of_nat (cells_size cs) <= 0x2a000 \/ 0x5d000 <= A) ->
  rw_cells rsegs m' A' cs.
Proof.
  intros m m' A A' cs [[Hwf (B0 & B1 & HB)] (W0 & W1 & HW)] SH A0 A1 IMG IMGA.
  pose proof (cells_bytes_length cs Hwf) as L.
  split; [split; [exact Hwf|]|].
  - split; [lia|]. split; [lia|]. intros i Hi. rewrite L in Hi.
    specialize (HB i ltac:(rewrite L; exact Hi)). specialize (HW (Z.of_nat i) ltac:(lia)). specialize (SH (Z.of_nat i) ltac:(lia)).
    unfold mrd in HB |- *. unfold wview in HW. rewrite SH. destruct (m (wa (A + Z.of_nat i))); [exact HB| exfalso; apply HW].
    rewrite p0_find_segment_none2; [reflexivity| lia| rewrite wa_unsigned by lia; lia].
  - split; [lia|]. split; [lia|]. intros i Hi. specialize (HW i Hi). specialize (SH i Hi).
    unfold wview in HW |- *. rewrite SH. destruct (m (wa (A + i))); [discriminate|]. exfalso. apply HW.
    rewrite p0_find_segment_none2; [reflexivity| lia| rewrite wa_unsigned by lia; lia].
Qed.

Section REMAP_REP.
Context {HGW : HasGuard}.
Context {HCEIL : HasCeiling}.
Variables (st : mstate) (m1 m2 : mem) (c : cptr) (g : aptr) (rg : region) (gh : ghdr) (off n n' dst : Z).
Let rid := fst c.
Let old := r_base rg.
Let on := m_maplen (get_meta_rec st g) * 4096.
Let nn := mremap_needed off n'.
Let M := Z.min on nn.
Let GA := conc st g.
Let mg' := m_set_maplen (nn / 4096) (get_meta_rec st g).
Let W' := meta_word mg'.
Let r' := mkRegion RKGroup dst nn.
Let t1 := N.succ (s_tick st).
Let st1 := set_tick t1 st.
Let stC := rebase_ctrl st1 rid g dst nn.
Let stS := upd_shadow rid (shadow_cut M) stC.
Let m3 := write_to_mem (write_to_mem m2 (wa (GA + 16)) (le8 (wz dst))) (wa (GA + 32)) (le8 (wz W')).

Hypothesis HMR : rmrep st m1.
Hypothesis TK : ticks_ok st.
Hypothesis Hrg : (s_regions st) !! rid = Some rg.
Hypothesis Krg : r_kind rg = RKGroup.
Hypothesis EON : on = round_up_pg (r_len rg).
Hypothesis ON0 : 0 < on.
Hypothesis MEMg : m_mem (get_meta_rec st g) = Some (rid, 0).
Hypothesis GRP : (s_groups st) !! (rid, 0) = Some gh.
Hypothesis NOGRP : forall b gh', (s_groups st) !! b = Some gh' -> fst b = rid -> b = (rid, 0).
Hypothesis GSLOT : exists a0 ar0 k0, (s_areas st) !! a0 = Some ar0 /\ 0 <= k0 < NSLOTS /\ g = aadd a0 (AREA_HDR + META_SIZE * k0).

Let P : N -> Prop := fun x => x <> rid.
Hypothesis PCTX : optr_in P (c_free_meta_head (ctx st)) /\ optr_in P (c_avail_meta (ctx st)) /\ optr_in P (c_meta_area_head (ctx st))
  /\ optr_in P (c_meta_area_tail (ctx st)) /\ optr_in P (c_avail_meta_areas (ctx st)) /\ (forall sc, optr_in P (active st sc))
  /\ match Malloc.c_brk (ctx st) with BrkLive brid _ => P brid | _ => True end.
Hypothesis PMET : forall q, optr_in P (m_prev (get_meta_rec st q)) /\ optr_in P (m_next (get_meta_rec st q)) /\ (q <> g -> optr_in P (m_mem (get_meta_rec st q))).
Hypothesis PAR : forall a ar, (s_areas st) !! a = Some ar -> optr_in P (a_next ar).
Hypothesis PGM : forall b gh', (s_groups st) !! b = Some gh' -> optr_in P (g_meta gh').

Hypothesis D0 : 0 < dst.
Hypothesis DA : dst mod 4096 = 0.
Hypothesis NA : nn mod 4096 = 0.
Hypothesis N2 : 2 * 4096 <= nn.
Hypothesis DC : dst + nn <= alloc_ceiling.
Hypothesis RESV : ranges_free p0_reserved dst nn = true.
Hypothesis DISJ : forall k2 r2, (s_regions st) !! k2 = Some r2 -> k2 <> rid -> dst + nn <= lr_lo r2 \/ r_base r2 + round_up_pg (r_len r2) <= dst.

Hypothesis H2a : forall a, 0 <= a < 2^64 -> ~ (old <= a < old + on) -> ~ (dst <= a < dst + nn) -> m2 (wa a) = m1 (wa a).
Hypothesis H2b : forall o, 0 <= o < M -> m2 (wa (dst + o)) = m1 (wa (old + o)).
Hypothesis H2c : forall o, M <= o < nn -> m2 (wa (dst + o)) = Some (b8 0).

#[using="HGW m1 HMR"] Lemma rr_wf : rregions_wf st. Proof. exact (proj1 HMR). Qed.
#[using="HGW m1 c rid HMR Hrg EON ON0 NA"] Lemma rnn : round_up_pg nn = nn /\ 0 < on /\ on mod 4096 = 0 /\ 0 <= r_len rg /\ old + on <= alloc_ceiling /\ 0 < old /\ old mod 4096 = 0
  /\ nn / 4096 * 4096 = nn.
Proof.
  pose proof rr_wf as (Hres & CE & WR & _). destruct (WR _ _ Hrg) as (R0 & RA & RL & RC & _). fold old in R0, RA, RC. rewrite <- EON in RC.
  split; [apply round_up_pg_id; exact NA|]. pose proof (round_up_pg_spec (r_len rg)) as [RS RM]. rewrite <- EON in RS, RM.
  split; [exact ON0|]. split; [exact RM|]. split; [exact RL|]. split; [exact RC|]. split; [exact R0|]. split; [exact RA|].
  clear - NA N2. Z.div_mod_to_equations. lia.
Qed.

#[using="HGW HCEIL m1 rg off n' dst old on nn M mg' W' t1 HMR Hrg Krg GSLOT"] Lemma g_area : exists a0 ar0 k0 ra0, (s_areas st) !! a0 = Some ar0 /\ 0 <= k0 < NSLOTS /\ g = aadd a0 (AREA_HDR + META_SIZE * k0)
  /\ (s_regions st) !! (fst a0) = Some ra0 /\ fst a0 <> rid /\ GA = conc st a0 + AREA_HDR + META_SIZE * k0
  /\ lr_lo ra0 <= conc st a0 /\ conc st a0 + 4096 <= r_base ra0 + round_up_pg (r_len ra0) /\ r_kind ra0 <> RKGroup.
Proof.
  destruct GSLOT as (a0 & ar0 & k0 & Ha0 & Hk0 & Eg). pose proof rr_wf as (Hres & CE & WR & DJ & WA & WG).
  destruct (WA a0 ar0 Ha0) as (ra0 & Hra0 & S0 & S1 & SAL & NK & LLO).
  exists a0, ar0, k0, ra0. split; [exact Ha0|]. split; [exact Hk0|]. split; [exact Eg|]. split; [exact Hra0|]. split.
  { intros E. unfold rid in *. rewrite E, Hrg in Hra0. injection Hra0 as <-. exact (NK Krg). }
  split. { unfold GA. rewrite Eg. unfold conc, aadd, get_region. cbn [fst snd]. rewrite Hra0. lia. }
  unfold conc, get_region. rewrite Hra0. split; [exact LLO| split; [lia| exact NK]].
Qed.

#[using="HGW HCEIL c rid M t1 HMR Hrg Krg EON ON0 GSLOT D0 NA N2 H2a"] Lemma m3_agree : forall a, 0 <= a < 2^64 -> ~ (old <= a < old + on) -> ~ (dst <= a < dst + nn) -> ~ (GA + 16 <= a < GA + 40) -> m3 (wa a) = m1 (wa a).
Proof.
  intros a Ha N1 N2' N3. unfold m3. pose proof rnn as (_ & _ & _ & _ & _ & _ & _ & _).
  destruct g_area as (a0 & ar0 & k0 & ra0 & Ha0 & Hk0 & Eg & Hra0 & NE0 & EGA & LO0 & HI0 & NK0).
  pose proof rr_wf as (Hres & CE & WR & _). destruct (WR _ _ Hra0) as (RB0 & _ & _ & RC0 & _). pose proof (lr_lo_ge ra0). ceil_facts.
  unfold AREA_HDR, META_SIZE, NSLOTS in *.
  rewrite !write_other; rewrite ?le8_len; try lia. apply H2a; auto.
Qed.

#[using="Type"] Lemma sS_regions : s_regions stS = <[rid := r']> (s_regions st). Proof. reflexivity. Qed.
#[using="Type"] Lemma sS_lookup k : s_regions stS !! k = if (k =? rid)%N then Some r' else s_regions st !! k.
Proof. rewrite sS_regions. destruct (N.eqb_spec k rid) as [->|NE]; [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity. Qed.
#[using="Type"] Lemma sS_some k rk : s_regions stS !! k = Some rk -> (k = rid /\ rk = r') \/ (k <> rid /\ s_regions st !! k = Some rk).
Proof. rewrite sS_lookup. destruct (N.eqb_spec k rid) as [->|NE]; [intros E; injection E as <-; auto| auto]. Qed.
#[using="r'"] Lemma sS_keep k rk : s_regions st !! k = Some rk -> k <> rid -> s_regions stS !! k = Some rk.
Proof. intros H NE. rewrite sS_lookup. destruct (N.eqb_spec k rid); [congruence| exact H]. Qed.
#[using="Type"] Lemma sS_areas : s_areas stS = s_areas st. Proof. reflexivity. Qed.
#[using="Type"] Lemma sS_groups : s_groups stS = s_groups st. Proof. reflexivity. Qed.
#[using="Type"] Lemma sS_ctx : ctx stS = ctx st. Proof. reflexivity. Qed.
#[using="Type"] Lemma sS_reserved : s_reserved stS = s_reserved st. Proof. reflexivity. Qed.
#[using="Type"] Lemma sS_tick : s_tick stS = t1. Proof. reflexivity. Qed.
#[using="Type"] Lemma sS_MR q : get_meta_rec stS q = if aptr_eqb q g then mg' else get_meta_rec st q.
Proof.
  unfold get_meta_rec at 1. unfold stS, stC, rebase_ctrl. cbn -[upd_meta rebase_regions]. rewrite s_metas_upd_meta.
  destruct (aptr_eqb_spec q g) as [->|NE]; [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity.
Qed.
#[using="r'"] Lemma sS_conc q : conc stS q = if (fst q =? rid)%N then dst + snd q else conc st q.
Proof. unfold conc, get_region. rewrite sS_lookup. destruct (N.eqb_spec (fst q) rid); reflexivity. Qed.
#[using="r'"] Lemma sS_conc_other q : fst q <> rid -> conc stS q = conc st q.
Proof. intros NE. rewrite sS_conc. destruct (N.eqb_spec (fst q) rid); [contradiction| reflexivity]. Qed.
#[using="r'"] Lemma sS_pw p : optr_in P p -> pw stS p = pw st p.
Proof. destruct p as [q|]; cbn; intros H; [| reflexivity]. unfold pw. cbn [oconc]. rewrite sS_conc_other by exact H. reflexivity. Qed.
#[using="Type"] Lemma sS_shadow k : get_shadow stS k = if (k =? rid)%N then shadow_cut M (get_shadow st rid) else get_shadow st k.
Proof. unfold stS. rewrite get_shadow_upd_shadow. reflexivity. Qed.

#[using="mg' r' P PMET"] Lemma sS_meta_cells q : q <> g -> meta_cells stS (get_meta_rec stS q) = meta_cells st (get_meta_rec st q).
Proof.
  intros NE. rewrite sS_MR, MI_Kit.aptr_eqb_neq by exact NE. destruct (PMET q) as (P1 & P2 & P3).
  unfold meta_cells. rewrite !sS_pw by auto. reflexivity.
Qed.
#[using="r' MEMg P PMET"] Lemma sS_meta_cells_g : meta_cells stS (get_meta_rec stS g) =
  [C8 (pw st (m_prev (get_meta_rec st g))); C8 (pw st (m_next (get_meta_rec st g))); C8 (wz dst);
   C4 (wz (m_avail (get_meta_rec st g))); C4 (wz (m_freed (get_meta_rec st g))); C8 (wz W')].
Proof.
  rewrite sS_MR, MI_Kit.aptr_eqb_refl. destruct (PMET g) as (P1 & P2 & _). unfold meta_cells, mg', m_set_maplen. cbn -[pw wz W' conc].
  rewrite !sS_pw by auto. rewrite MEMg. unfold pw. cbn [oconc]. rewrite sS_conc. cbn [fst snd]. rewrite N.eqb_refl, Z.add_0_r. reflexivity.
Qed.

Local Notation agree := MallocKit_B.agree_on.

#[using="HGW m1 M mg' W' t1 HMR Hrg Krg EON ON0 GSLOT D0 NA N2 RESV DISJ"] Lemma geo : exists a0 ar0 k0 ra0,
  (s_areas st) !! a0 = Some ar0 /\ 0 <= k0 < NSLOTS /\ g = aadd a0 (AREA_HDR + META_SIZE * k0)
  /\ (s_regions st) !! (fst a0) = Some ra0 /\ fst a0 <> rid /\ GA = conc st a0 + AREA_HDR + META_SIZE * k0
  /\ lr_lo ra0 <= conc st a0 /\ conc st a0 + 4096 <= r_base ra0 + round_up_pg (r_len ra0) /\ r_kind ra0 <> RKGroup

  /\ (old + on <= 0x10000 \/ 0x2a000 <= old) /\ (old + on <= 0x2a000 \/ 0x5d000 <= old)
  /\ (dst + nn <= 0x10000 \/ 0x2a000 <= dst) /\ (dst + nn <= 0x2a000 \/ 0x5d000 <= dst)
  /\ (conc st a0 + 4096 <= 0x10000 \/ 0x2a000 <= conc st a0) /\ (conc st a0 + 4096 <= 0x2a000 \/ 0x5d000 <= conc st a0)
  /\ (old + on <= conc st a0 \/ conc st a0 + 4096 <= old) /\ (dst + nn <= conc st a0 \/ conc st a0 + 4096 <= dst)
  /\ 0 < conc st a0 /\ conc st a0 + 4096 <= alloc_ceiling /\ old + on <= alloc_ceiling.
Proof.
  destruct g_area as (a0 & ar0 & k0 & ra0 & Ha0 & Hk0 & Eg & Hra0 & NE0 & EGA & LO0 & HI0 & NK0).
  pose proof rr_wf as (Hres & CE & WR & DJ & WA & WG). pose proof rnn as (RN & ON0' & ONA & RL & OC & O0 & OA & _).
  destruct (WR _ _ Hra0) as (RB0 & _ & _ & RC0 & RF0). destruct (WR _ _ Hrg) as (_ & _ & _ & _ & RFg). fold old in RFg. rewrite <- EON in RFg.
  pose proof (lr_lo_ge ra0) as LG0.
  pose proof (rreserved_disjoint1 _ _ RFg ltac:(lia)) as [IO1 IO2]. pose proof (rreserved_disjoint1 _ _ RESV ltac:(lia)) as [ID1 ID2].
  pose proof (rreserved_disjoint1 _ _ RF0 ltac:(pose proof (round_up_pg_spec (r_len ra0)); lia)) as [IA1 IA2].
  pose proof (DJ _ _ _ _ Hrg Hra0 ltac:(intros E; apply NE0; symmetry; exact E)) as DJ0. rewrite (lr_lo_group rg Krg) in DJ0. fold old in DJ0. rewrite <- EON in DJ0.
  pose proof (DISJ _ _ Hra0 NE0) as DS0. ceil_facts.
  exists a0, ar0, k0, ra0. repeat (split; [assumption|]). repeat split; try (first [solve [clear - LO0 HI0 LG0 IA1 IA2 DJ0 DS0 RB0 RC0 OC; lia] | lia]).
Qed.

#[using="m1 rg old r' HMR TK Hrg Krg EON ON0 MEMg NOGRP GSLOT P PCTX PMET PAR PGM D0 DA NA N2 DC RESV DISJ H2a H2b H2c"] Lemma rmrep_cut : rmrep stS m3 /\ ticks_ok stS.
Proof.
  pose proof HMR as (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & CE & WR & DJ & WA & WG).
  pose proof rnn as (RN & ON0' & ONA & RL & OC & O0 & OA & NND).
  destruct geo as (a0 & ar0 & k0 & ra0 & Ha0 & Hk0 & Eg & Hra0 & NE0 & EGA & LO0 & HI0 & NK0 & IO1 & IO2 & ID1 & ID2 & IA1 & IA2 & DOA & DDA & A00 & A0C & OC').
  ceil_facts. unfold AREA_HDR, META_SIZE, NSLOTS in Hk0, Eg, EGA.

  assert (MGE : 4096 <= M) by (unfold M; clear - ON0' ONA N2; Z.div_mod_to_equations; lia).
  assert (MLE : M <= on /\ M <= nn) by (unfold M; lia).

  assert (AGR : forall A k, (A + k <= old \/ old + on <= A) -> (A + k <= dst \/ dst + nn <= A) -> (A + k <= GA + 16 \/ GA + 40 <= A) ->
            0 <= A -> A + k <= 2^64 -> agree m1 m3 A k).
  { intros A k D1 D2 D3 HA HK a Ha. apply m3_agree; (first [solve [clear - HA HK Ha D1 D2 D3; lia] | lia]). }

  assert (DSTB : forall o, 0 <= o < nn -> m3 (wa (dst + o)) = m2 (wa (dst + o))).
  { intros o Ho. unfold m3. rewrite !write_other; rewrite ?le8_len; try (clear - Ho EGA Hk0 LO0 HI0 DDA A00 A0C DC D0 CEILB CEILA; lia). reflexivity. }

  split.
  2:{   destruct (ticks_ok_set_tick st t1 ltac:(unfold t1; lia) TK) as [T1 T2]. split; cbn [s_tick stS stC st1 set_tick upd_shadow set_shadow s_shadow rebase_ctrl upd_meta rebase_regions set_regions set_metas].
      - intros k sh u hl ch Hsh Hu Hin. change (s_tick stS) with t1. unfold stS, upd_shadow, set_shadow in Hsh. cbn [s_shadow] in Hsh.
        destruct (N.eq_dec k rid) as [->|NE].
        + rewrite lookup_insert_eq in Hsh. injection Hsh as <-. cbn [shadow_cut r_hav] in Hu.
          change (get_shadow stC rid) with (get_shadow st rid) in Hu.
          exact (proj1 (sh_ticks_of_ticks_ok _ rid (ticks_ok_set_tick st t1 ltac:(unfold t1; lia) TK)) u hl ch Hu Hin).
        + rewrite lookup_insert_ne in Hsh by congruence. exact (T1 k sh u hl ch Hsh Hu Hin).
      - intros k sh pg t Hsh Hp. unfold stS, upd_shadow, set_shadow in Hsh. cbn [s_shadow] in Hsh.
        destruct (N.eq_dec k rid) as [->|NE].
        + rewrite lookup_insert_eq in Hsh. injection Hsh as <-. cbn [shadow_cut r_havp] in Hp.
          change (get_shadow stC rid) with (get_shadow st rid) in Hp.
          exact (proj2 (sh_ticks_of_ticks_ok _ rid (ticks_ok_set_tick st t1 ltac:(unfold t1; lia) TK)) pg t Hp).
        + rewrite lookup_insert_ne in Hsh by congruence. exact (T2 k sh pg t Hsh Hp). }
  split; [| split; [| split; [| split; [| split]]]].
  -   split; [exact Hres|]. split; [exact CE|]. split; [|split; [|split]].
    + intros k rk Hk. destruct (sS_some k rk Hk) as [[-> ->]|[NE Hk']]; [| exact (WR k rk Hk')].
      cbn [r_base r_len r']. rewrite RN. split; [lia|]. split; [exact DA|]. split; [lia|]. split; [ceil_facts; lia| exact RESV].
    + intros k1 r1 k2 r2 H1 H2 NE.
      destruct (sS_some _ _ H1) as [[-> ->]|[N1 H1']]; destruct (sS_some _ _ H2) as [[-> ->]|[N2' H2']]; [congruence| | | exact (DJ _ _ _ _ H1' H2' NE)].
      * cbn [r_base r_len r']. rewrite RN. unfold lr_lo at 2. cbn [r_kind r' r_base]. destruct (DISJ _ _ H2' N2'); lia.
      * cbn [r_base r_len r']. rewrite RN. unfold lr_lo at 1. cbn [r_kind r' r_base]. destruct (DISJ _ _ H1' N1); lia.
    + intros a ar Ha. rewrite sS_areas in Ha. destruct (WA a ar Ha) as (ra & Hra & S0 & S1 & SAL & NK & LLO).
      assert (NEa : fst a <> rid). { intros E. unfold rid in *. rewrite E, Hrg in Hra. injection Hra as <-. exact (NK Krg). }
      exists ra. split; [exact (sS_keep _ _ Hra NEa)|]. auto 6.
    + intros b gh' Hb. rewrite sS_groups in Hb. destruct (WG b gh' Hb) as (rb & Hrb & Krb & B0 & B1 & BAL).
      destruct (N.eq_dec (fst b) rid) as [E|NE].
      * pose proof (NOGRP b gh' Hb E) as ->. exists r'. split; [rewrite sS_lookup, N.eqb_refl; reflexivity|]. cbn [r_kind r_len r' snd]. rewrite RN. repeat split; try lia; try reflexivity.
      * exists rb. split; [exact (sS_keep _ _ Hrb NE)|]. auto.
  -   destruct CX as (C1 & C2 & C3 & C4 & C5 & C6). destruct PCTX as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7).
    assert (E1 : ctx_head_cells stS = ctx_head_cells st) by (unfold ctx_head_cells; rewrite sS_ctx, !sS_pw by assumption; reflexivity).
    assert (E2 : actives stS = actives st). { unfold actives. apply map_ext. intros i. unfold active. rewrite sS_ctx. apply sS_pw. apply Q6. }
    assert (E3 : usages stS = usages st) by reflexivity. assert (E4 : unmap_seqs stS = unmap_seqs st) by reflexivity.
    assert (E5 : bouncess stS = bouncess st) by reflexivity.
    assert (E6 : ctx_tail_cells stS = ctx_tail_cells st).
    { unfold ctx_tail_cells, brk_word. rewrite sS_ctx. destruct (Malloc.c_brk (ctx st)) as [| |brid boff]; try reflexivity. rewrite (sS_conc_other (brid, boff)) by exact Q7. reflexivity. }
    unfold rmrep_ctx. rewrite E1, E2, E3, E4, E5, E6.
    pose proof (u64arr_bound rsegs m1 _ _ C2) as B2. pose proof (u64arr_bound rsegs m1 _ _ C3) as B3.
    pose proof (u8arr_bound rsegs m1 _ _ C4) as B4. pose proof (u8arr_bound rsegs m1 _ _ C5) as B5.
    rewrite actives_length in B2. rewrite usages_length in B3. rewrite unmap_seqs_length in B4. rewrite bouncess_length in B5.
    unfold RCTX in *.
    split; [| split; [| split; [| split; [| split]]]].
    + eapply rrw_cells_agree'; [exact C1|]. apply AGR; cbn; clear - IO2 ID2 IA2 EGA Hk0; lia.
    + eapply ru64arr_agree'; [exact C2|]. rewrite actives_length. apply AGR; cbn; clear - IO2 ID2 IA2 EGA Hk0; lia.
    + eapply ru64arr_agree'; [exact C3|]. rewrite usages_length. apply AGR; cbn; clear - IO2 ID2 IA2 EGA Hk0; lia.
    + eapply ru8arr_agree'; [exact C4|]. rewrite unmap_seqs_length. apply AGR; cbn; clear - IO2 ID2 IA2 EGA Hk0; lia.
    + eapply ru8arr_agree'; [exact C5|]. rewrite bouncess_length. apply AGR; cbn; clear - IO2 ID2 IA2 EGA Hk0; lia.
    + eapply rrw_cells_agree'; [exact C6|]. apply AGR; cbn; clear - IO2 ID2 IA2 EGA Hk0; lia.
  -   destruct GL as (G1 & G2 & G3 & G4 & G5 & G6). unfold rmrep_globals, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RGOT_SSP, RSSP_GUARD, RVMLOCK in *.
    split; [| split; [| split; [| split; [| split]]]];
      (eapply rrw_cells_agree'; [eassumption|]; apply AGR; cbn; clear - IO1 IO2 ID1 ID2 IA1 IA2 EGA Hk0; lia).
  -   intros a ar Ha. rewrite sS_areas in Ha. destruct (AR a ar Ha) as (HD & SL & PD).
    destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RBa & RBAL & RCa). ceil_facts.
    pose proof (rarea_lr_lo st a ar ra WF Ha Hra) as LRa.
    assert (NEa : fst a <> rid). { intros E. unfold rid in *. rewrite E, Hrg in Hra. injection Hra as <-. exact (NK Krg). }
    destruct (WR _ _ Hra) as (_ & _ & _ & _ & RFa). pose proof (rreserved_disjoint1 _ _ RFa ltac:(pose proof (round_up_pg_spec (r_len ra)); lia)) as [IAa1 IAa2].
    pose proof (DJ _ _ _ _ Hrg Hra ltac:(intros E; apply NEa; symmetry; exact E)) as DJa. rewrite (lr_lo_group rg Krg) in DJa. fold old in DJa. rewrite <- EON in DJa.
    pose proof (DISJ _ _ Hra NEa) as DSa.

    assert (PG : a = a0 \/ conc st a + 4096 <= conc st a0 \/ conc st a0 + 4096 <= conc st a).
    { destruct (decide (a = a0)) as [->|NEa0]; [left; reflexivity| right].
      destruct (rarea_conc st a0 ar0 WF Ha0) as (ra0' & Hra0' & Ca0 & S00 & S01 & S0L & _). rewrite Hra0 in Hra0'. injection Hra0' as <-.
      destruct (N.eq_dec (fst a) (fst a0)) as [E|NE].
      - rewrite E, Hra0 in Hra. injection Hra as ->. rewrite Ca, Ca0.
        assert (snd a <> snd a0) by (intros E2; apply NEa0; destruct a, a0; cbn in *; congruence). clear - H SaL S0L. Z.div_mod_to_equations. lia.
      - pose proof (DJ _ _ _ _ Hra Hra0 NE) as D. clear - D LRa Sa1 Sa0 LO0 S01 S00 HI0 Ca Ca0. lia. }
    assert (PGc : conc st a = conc st a0 \/ conc st a + 4096 <= conc st a0 \/ conc st a0 + 4096 <= conc st a) by (destruct PG as [->|PG]; [left; reflexivity| right; exact PG]).
    unfold rarea_rep. rewrite sS_conc_other by exact NEa. unfold AREA_HDR, META_SIZE, NSLOTS in *.
    split; [| split].
    + rewrite sS_pw by (exact (PAR _ _ Ha)). eapply rrw_cells_agree'; [exact HD|]. apply AGR; cbn; clear - DJa DSa LRa Ca Sa0 Sa1 RCa RBa PGc EGA Hk0 CEILB CEILA; lia.
    + intros k Hk. destruct (decide (aadd a (24 + 40 * k) = g)) as [E|NE].
      *
        rewrite E, sS_meta_cells_g.
        assert (Eak : a = a0 /\ k = k0).
        { rewrite Eg in E. unfold aadd in E. destruct PG as [->|PG].
          - split; [reflexivity|]. injection E as E2. clear - E2. lia.
          - exfalso. injection E as E1 E2.
            destruct (rarea_conc st a0 ar0 WF Ha0) as (ra0' & Hra0' & Ca0 & _). rewrite Hra0 in Hra0'. injection Hra0' as <-.
            rewrite E1, Hra0 in Hra. injection Hra as ->. rewrite Ca, Ca0 in PG. clear - PG E2 Hk Hk0. lia. }
        destruct Eak as [-> ->]. try rewrite <- Eg.
        pose proof (SL k0 Hk0) as SLg. rewrite <- Eg in SLg. rewrite <- EGA in SLg. rewrite <- EGA.

        assert (SL2 : rw_cells rsegs m2 GA (meta_cells st (get_meta_rec st g))).
        { eapply rrw_cells_agree'; [exact SLg|]. intros x Hx. cbn [meta_cells cells_size csize Nat.add length] in Hx. apply H2a; clear - Hx EGA Hk0 LO0 HI0 DOA DDA A00 A0C CEILB CEILA; lia. }
        unfold meta_cells in SL2. unfold m3.
        pose proof (rw_cells_write rsegs m2 GA _ 16%nat _ (C8 (wz dst)) SL2 eq_refl eq_refl I) as SL3. cbn [cell_upd csize Nat.eqb Nat.sub cbytes] in SL3.
        change (Z.of_nat 16) with 16 in SL3. change (Z_to_le_bytes 8 (bv_unsigned (wz dst))) with (le8 (wz dst)) in SL3.
        pose proof (rw_cells_write rsegs _ GA _ 32%nat _ (C8 (wz W')) SL3 eq_refl eq_refl I) as SL4. cbn [cell_upd csize Nat.eqb Nat.sub cbytes] in SL4.
        change (Z.of_nat 32) with 32 in SL4. change (Z_to_le_bytes 8 (bv_unsigned (wz W'))) with (le8 (wz W')) in SL4. exact SL4.
      * rewrite (sS_meta_cells _ NE). eapply rrw_cells_agree'; [apply SL; exact Hk|].
        assert (DG : conc st a + (24 + 40 * k) + 40 <= GA + 16 \/ GA + 40 <= conc st a + (24 + 40 * k)).
        { destruct PG as [->|PG]; [| clear - PG EGA Hk Hk0; lia]. assert (KK : k <> k0) by (intros ->; apply NE; rewrite Eg; reflexivity). clear - KK EGA Hk Hk0. lia. }
        apply AGR; cbn [meta_cells cells_size csize Nat.add length]; clear - DJa DSa LRa Ca Sa0 Sa1 RCa RBa PGc EGA Hk0 Hk DG CEILB CEILA; lia.
    + eapply rrw_cells_agree'; [exact PD|]. apply AGR; cbn; clear - DJa DSa LRa Ca Sa0 Sa1 RCa RBa PGc EGA Hk0 CEILB CEILA; lia.
  -   intros b gh' Hb. rewrite sS_groups in Hb. destruct (GR b gh' Hb) as (w8 & R1 & R2).
    destruct (rgroup_conc st b gh' WF Hb) as (rb & Hrb & Cb & Krb & B0 & B1 & BAL & RBb & RCb). ceil_facts.
    exists w8. split; [| exact R2]. rewrite sS_pw by (exact (PGM _ _ Hb)).
    destruct (N.eq_dec (fst b) rid) as [E|NE].
    + pose proof (NOGRP b gh' Hb E) as Eb. rewrite Eb in Hb, Cb, R1 |- *. rewrite sS_conc. cbn [fst snd]. rewrite N.eqb_refl, Z.add_0_r.
      rewrite E, Hrg in Hrb. injection Hrb as <-. rewrite Cb in R1. cbn [snd] in R1. fold old in R1. rewrite Z.add_0_r in R1.
      eapply (rw_cells_shift m1 m3 old dst); [exact R1| | clear - D0; lia| cbn; clear - DC N2 CEILB CEILA; lia| cbn; clear - ID1 ID2 N2 D0; lia| cbn; clear - IO1 IO2 MGE MLE O0; lia].
      intros i Hi. cbn in Hi. rewrite DSTB by (clear - Hi MLE N2; lia). apply H2b. clear - Hi MGE; lia.
    + rewrite sS_conc_other by exact NE. eapply rrw_cells_agree'; [exact R1|].
      pose proof (DJ _ _ _ _ Hrg Hrb ltac:(intros E; apply NE; symmetry; exact E)) as DJb. rewrite (lr_lo_group rg Krg), (lr_lo_group rb Krb) in DJb. fold old in DJb. rewrite <- EON in DJb.
      pose proof (DISJ _ _ Hrb NE) as DSb. rewrite (lr_lo_group rb Krb) in DSb.
      assert (NEr : fst b <> fst a0). { intros E2. rewrite E2, Hra0 in Hrb. injection Hrb as ->. exact (NK0 Krb). }
      pose proof (DJ _ _ _ _ Hrb Hra0 NEr) as DJab. rewrite (lr_lo_group rb Krb) in DJab.
      rewrite Cb. apply AGR; cbn; clear - DJb DSb DJab B0 B1 RCb RBb EGA Hk0 LO0 HI0 CEILB CEILA; lia.
  -   intros k rk Hk Kk. destruct (sS_some k rk Hk) as [[-> ->]|[NE Hk']].
    +   destruct (SH rid rg Hrg Krg) as [HW HB]. fold old in HW, HB. rewrite <- EON in HW, HB.
      unfold rshadow_rep. cbn [r_base r_len r']. rewrite RN. rewrite sS_shadow, N.eqb_refl.
      assert (OLDSOME : forall i, 0 <= i < on -> exists b, m1 (wa (old + i)) = Some b).
      { intros i Hi. destruct HW as (_ & _ & HWi). specialize (HWi i Hi). unfold wview in HWi.
        destruct (m1 (wa (old + i))) as [b|] eqn:Em; [exists b; reflexivity| exfalso; apply HWi].
        rewrite p0_find_segment_none2; [reflexivity| (first [solve [clear_props; lia] | lia])| rewrite wa_unsigned by (first [solve [clear - OC O0 CEILB Hi; lia] | lia]); (first [solve [clear - IO1 IO2 Hi; lia] | lia])]. }
      split.
      * split; [lia|]. split; [lia|]. intros i Hi. unfold wview. rewrite DSTB by lia.
        destruct (Z_lt_le_dec i M) as [LT|GE].
        -- rewrite H2b by lia. destruct (OLDSOME i ltac:(lia)) as [b ->]. discriminate.
        -- rewrite H2c by lia. discriminate.
      * intros o v Ho Hc. destruct (Z_lt_le_dec o M) as [LT|GE].
        -- rewrite cell_read_cut_lt in Hc by exact LT. change (get_shadow stC rid) with (get_shadow st rid) in Hc.
           destruct (HB o v ltac:(lia) Hc) as [Bt Hv]. split; [| exact Hv].
           destruct Bt as (_ & _ & Bt). specialize (Bt 0%nat ltac:(cbn; lia)). cbn [nth_error] in Bt. rewrite Z.add_0_r in Bt.
           split; [lia|]. split; [cbn; lia|]. intros j Hj. cbn in Hj. assert (j = 0%nat) as -> by lia. cbn [nth_error]. rewrite Z.add_0_r.
           unfold mrd in Bt |- *. rewrite DSTB by lia. rewrite H2b by lia. destruct (OLDSOME o ltac:(lia)) as [b Eb]. rewrite Eb in Bt |- *. exact Bt.
        -- pose proof (cell_read_cut_ge M _ o v GE Hc) as ->. split; [| lia].
           split; [lia|]. split; [cbn; lia|]. intros j Hj. cbn in Hj. assert (j = 0%nat) as -> by lia. cbn [nth_error]. rewrite Z.add_0_r.
           unfold mrd. rewrite DSTB by lia. rewrite H2c by lia. reflexivity.
    +   unfold rshadow_rep. rewrite sS_shadow. destruct (N.eqb_spec k rid); [contradiction|].
      destruct (SH k rk Hk' Kk) as [HW HB]. destruct (WR _ _ Hk') as (RB0 & _ & _ & RCk & RFk). ceil_facts.
      pose proof (DJ _ _ _ _ Hrg Hk' ltac:(intros E; apply NE; symmetry; exact E)) as DJk. rewrite (lr_lo_group rg Krg), (lr_lo_group rk Kk) in DJk. fold old in DJk. rewrite <- EON in DJk.
      pose proof (DISJ _ _ Hk' NE) as DSk. rewrite (lr_lo_group rk Kk) in DSk.
      assert (NEr : k <> fst a0). { intros E2. rewrite E2, Hra0 in Hk'. injection Hk' as ->. exact (NK0 Kk). }
      pose proof (DJ _ _ _ _ Hk' Hra0 NEr) as DJak. rewrite (lr_lo_group rk Kk) in DJak.
      assert (AG : agree m1 m3 (r_base rk) (round_up_pg (r_len rk))) by (apply AGR; clear - DJk DSk DJak RB0 RCk EGA Hk0 LO0 HI0 CEILB CEILA; lia).
      split; [eapply rwr_at_agree; [exact HW| exact AG]|].
      intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [| exact Hv].
      eapply RMallocKit_B.rbytes_at_agree; [exact Bt|]. cbn. intros x Hx. apply AG. lia.
Qed.

Let st2 := rebase_st st1 rid g dst nn on.
Let m3e := write_to_mem m3 (wa (dst + nn - 4)) [b8 0].
#[using="Type"] Lemma st2_eq : st2 = wr8 (rid, nn - 4) 0 stS. Proof. reflexivity. Qed.

#[using="m1 rg old M r' stC stS HMR TK Hrg Krg EON ON0 MEMg NOGRP GSLOT P PCTX PMET PAR PGM D0 DA NA N2 DC RESV DISJ H2a H2b H2c"] Lemma rmrep_end : rmrep st2 m3e /\ ticks_ok st2.
Proof.
  destruct rmrep_cut as [MRS TKS]. pose proof rnn as (RN & ON0' & ONA & RL & OC & O0 & OA & NND). rewrite st2_eq.
  split; [| apply ticks_ok_wr8; exact TKS].
  replace m3e with (write_to_mem m3 (wa (r_base r' + snd (rid, nn - 4))) [b8 0]) by (unfold m3e; cbn [r_base r' snd]; f_equal; f_equal; lia).
  apply (rmrep_wr8 stS m3 (rid, nn - 4) 0 r' MRS TKS).
  - cbn [fst]. rewrite sS_lookup, N.eqb_refl. reflexivity.
  - reflexivity.
  - cbn [snd r_len r']. rewrite RN. lia.
  - intros b gh' Hb Hf. cbn [fst snd] in Hf |- *. rewrite sS_groups in Hb. pose proof (NOGRP b gh' Hb Hf) as ->. cbn [snd]. lia.
  - lia.
Qed.

Hypothesis Hs : (s_slots st) !! c = Some (g, 0).
Hypothesis C16 : snd c = 16.
Hypothesis OFF0 : 0 <= off.
Hypothesis N0 : 0 <= n'.
Hypothesis RES0 : 0 <= get_stride (get_meta_rec st g) - IB - UNIT * off - n.

#[using="m1 rg rid old on M r' t1 st1 stC stS HMR TK Hrg Krg EON ON0 MEMg NOGRP GSLOT P PCTX PMET PAR PGM D0 DA NA N2 DC RESV DISJ H2a H2b H2c st2 Hs C16 OFF0 N0 RES0"] Theorem rremap_mrep :
  rmrep (mremap_full st c off n n' dst) (rset_size_mem m3e (dst + 16 + UNIT * off) (dst + nn - IB) n' (0 + 32 * Z.min (get_stride (get_meta_rec st g) - IB - UNIT * off - n) 5))
  /\ ticks_ok (mremap_full st c off n n' dst).
Proof.
  destruct rmrep_end as [MR2 TK2]. pose proof rnn as (RN & ON0' & ONA & RL & OC & O0 & OA & NND).
  assert (NG : n' + UNIT * off + UNIT + IB <= nn < n' + UNIT * off + UNIT + IB + 4096).
  { unfold nn, mremap_needed. pose proof (round_up_pg_spec (n' + UNIT * off + UNIT + IB)). lia. }
  assert (EMF : mremap_full st c off n n' dst = havoc (aadd c (UNIT * off)) n' (wrs (ss_list (aadd c (UNIT * off)) (aadd c (nn - UNIT - IB)) n' (0 + 32 * Z.min (get_stride (get_meta_rec st g) - IB - UNIT * off - n) 5)) st2)).
  { unfold mremap_full. rewrite Hs. reflexivity. }
  rewrite EMF.
  pose proof (rss_mrep st2 m3e c off n' (nn - UNIT) (0 + 32 * Z.min (get_stride (get_meta_rec st g) - IB - UNIT * off - n) 5) r' MR2 TK2) as RS.
  cbn [r_base r'] in RS. rewrite C16 in RS.
  replace (dst + 16 + (nn - UNIT) - IB) with (dst + nn - IB) in RS by (unfold UNIT; lia).
  replace (aadd c (nn - UNIT - IB)) with (aadd c ((nn - UNIT) - IB)) by (f_equal; lia).
  apply RS.
  - rewrite st2_eq. cbn [s_regions wr8 upd_shadow set_shadow]. fold rid. rewrite sS_lookup, N.eqb_refl. reflexivity.
  - reflexivity.
  - lia.
  - cbn [r_len r']. rewrite RN. unfold UNIT, IB. lia.
  - intros b' gh' Hb Hf. rewrite st2_eq in Hb. cbn [s_groups wr8 upd_shadow set_shadow] in Hb. rewrite sS_groups in Hb. fold rid in Hf.
    pose proof (NOGRP b' gh' Hb Hf) as ->. cbn [snd]. left. lia.
  - exact OFF0.
  - exact N0.
  - unfold UNIT, IB in *. lia.
  - unfold UNIT, IB in *. lia.
  - pose proof (Z.le_min_l (get_stride (get_meta_rec st g) - IB - UNIT * off - n) 5).
    assert (0 <= Z.min (get_stride (get_meta_rec st g) - IB - UNIT * off - n) 5) by (apply Z.min_glb; lia). lia.
Qed.
End REMAP_REP.

Section BRIDGE.
Context {HGW : HasGuard}.
Context {HCEIL : HasCeiling}.
Variables (st : mstate) (LB : list block) (blk : block) (m1 m2 : mem) (g : aptr) (off n' dst : Z).
Let c := blk_slot blk.
Let rid := fst c.
Let nn := mremap_needed off n'.
Let on := m_maplen (get_meta_rec st g) * 4096.
Let M := Z.min on nn.
Let GA := conc st g.
Let W' := meta_word (m_set_maplen (nn / 4096) (get_meta_rec st g)).
Hypothesis AR : AREACH_from p0_reserved st LB.
Hypothesis Hin : In blk LB.
Hypothesis Hoff : 0 <= off.
Hypothesis HA : blk_addr blk = conc st c + UNIT * off.
Hypothesis Hs : (s_slots st) !! c = Some (g, 0).
Hypothesis SC : m_sizeclass (get_meta_rec st g) = 63.
Hypothesis HMR : rmrep st m1.
Hypothesis N0 : 0 <= n'.
Hypothesis OK : cremap_ok (strip st) c dst nn.

#[using="HGW HCEIL LB m1 n' dst nn M GA W' AR Hin HA Hs SC HMR OK"] Lemma remap_facts : exists rg gh,
  (s_regions st) !! rid = Some rg /\ r_kind rg = RKGroup /\ on = round_up_pg (r_len rg) /\ 0 < on /\ c = (rid, 16)
  /\ m_mem (get_meta_rec st g) = Some (rid, 0) /\ (s_groups st) !! (rid, 0) = Some gh /\ g_meta gh = Some g
  /\ (forall b gh', (s_groups st) !! b = Some gh' -> fst b = rid -> b = (rid, 0))
  /\ (exists a0 ar0 k0, (s_areas st) !! a0 = Some ar0 /\ 0 <= k0 < NSLOTS /\ g = aadd a0 (AREA_HDR + META_SIZE * k0))
  /\ (let P := fun x : N => x <> rid in
      (optr_in P (c_free_meta_head (ctx st)) /\ optr_in P (c_avail_meta (ctx st)) /\ optr_in P (c_meta_area_head (ctx st))
       /\ optr_in P (c_meta_area_tail (ctx st)) /\ optr_in P (c_avail_meta_areas (ctx st)) /\ (forall sc, optr_in P (active st sc))
       /\ match Malloc.c_brk (ctx st) with BrkLive brid _ => P brid | _ => True end)
      /\ (forall q, optr_in P (m_prev (get_meta_rec st q)) /\ optr_in P (m_next (get_meta_rec st q)) /\ (q <> g -> optr_in P (m_mem (get_meta_rec st q))))
      /\ (forall a ar, (s_areas st) !! a = Some ar -> optr_in P (a_next ar))
      /\ (forall b gh', (s_groups st) !! b = Some gh' -> optr_in P (g_meta gh')))
  /\ ticks_ok st /\ blk_size blk <= get_stride (get_meta_rec st g) - IB - UNIT * off /\ 0 <= blk_size blk
  /\ conc st c = r_base rg + 16 /\ blk_addr blk = r_base rg + 16 + UNIT * off /\ 0 <= off <= 255
  /\ get_stride (get_meta_rec st g) = on - UNIT.
Proof.
  pose proof (areach_cinv_proof _ _ AR) as CI. pose proof (ci_ticks _ _ CI) as TK.
  pose proof (KINV_of_CINV _ _ CI) as K. pose proof (ZINV_of_CINV _ _ CI) as ZI. pose proof (ci_mp _ _ CI) as (M1 & M2 & M3 & M4 & M5).
  destruct (areach_inv _ st LB AR) as (L & LS & BL & INV & _ & _ & _ & CR).
  destruct (Forall2_In_l _ _ _ _ CR Hin) as (k & Hk & (K1 & K2 & K3)).
  destruct k as [[c0 bo] n]. cbn [bslot boff bsize fst snd] in K1, K2, K3. fold c in K1. subst c0.
  assert (bo = off) as -> by (rewrite HA in K3; unfold UNIT in K3; lia).
  destruct (block_facts x0 st L BL LS INV c off n Hk) as (g' & bm & i & ai & aa & ar & ka & BF).
  pose proof (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF) as Hs'. rewrite Hs in Hs'. injection Hs' as <- <-.
  pose proof OK as (D0 & _).
  pose proof (g_facts' x0 st L BL LS c g off n 0 0 INV Hk eq_refl Hs SC) as (HG & EC & LI & ML & _ & STR & GB & rg & Hrg & Krg & EON).
  fold rid on in Hrg, EON, HG, EC, GB |- *.
  pose proof (bf_mem _ _ _ _ _ _ _ _ _ _ _ BF) as MEM. pose proof (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF) as HST.
  assert (Ebm : bm = (rid, 0)). { unfold gbase in GB. rewrite MEM in GB. cbn in GB. exact GB. } subst bm.
  pose proof (bf_maplen _ _ _ _ _ _ _ _ _ _ _ BF) as MLN.
  pose proof HMR as (WF & _). pose proof WF as (Hres & CE & WR & DJ & WA & WG).
  assert (NOGRP : forall b gh', (s_groups st) !! b = Some gh' -> fst b = rid -> b = (rid, 0)).
  { intros b gh' Hb Fb. exact (rid_nogroup x0 st L BL LS c g dst nn on INV Hs SC eq_refl D0 b gh' Hb Fb). }
  assert (MSr : forall q, meta_slot st q -> fst q <> rid).
  { intros q (a1 & ar1 & k1 & Ha1 & Hk1 & ->) E. cbn in E. destruct (WA a1 ar1 Ha1) as (ra & Hra & _ & _ & _ & NK & _).
    unfold rid in *. rewrite E in Hra. fold rid in Hra. rewrite Hrg in Hra. injection Hra as <-. exact (NK Krg). }
  assert (NGr : forall p, ng_ptr st p -> optr_in (fun x => x <> rid) p).
  { intros [q|]; cbn; [| exact (fun _ => I)]. intros (r2 & Hr2 & NK) E. rewrite E, Hrg in Hr2. injection Hr2 as <-. exact (NK Krg). }
  assert (OM : forall p, (forall q, p = Some q -> meta_slot st q) -> optr_in (fun x => x <> rid) p).
  { intros [q|] H; cbn; [apply MSr; apply H; reflexivity| exact I]. }
  pose proof (ki_links _ _ _ K) as [LN LP LNN LSS].
  exists rg, (mkGhdr (Some g) ai).
  split; [exact Hrg|]. split; [exact Krg|]. split; [exact EON|]. split. { clear - ML MLN. unfold MR in ML, MLN. subst on. lia. }
  split; [exact EC|].
  split; [exact MEM|]. split; [exact HST|]. split; [reflexivity|]. split; [exact NOGRP|].
  split. { destruct (bf_area _ _ _ _ _ _ _ _ _ _ _ BF) as (Ha & _ & _ & Hka & Em). exists aa, ar, ka. auto. }
  split.
  { cbv zeta. split; [| split; [| split]].
    - split; [| split; [| split; [| split; [| split; [| split]]]]].
      + apply OM. intros h Hh. exact (proj1 (kinv_free_head st LB 0 h K Hh)).
      + apply NGr. exact M1.
      + apply NGr. exact M2.
      + apply NGr. exact M3.
      + apply NGr. exact M4.
      + intros sc. apply OM. intros a1 Ha1. exact (proj1 (proj2 (kinv_active st LB 0 sc a1 K Ha1))).
      + destruct (Malloc.c_brk (ctx st)) as [| |brid boff] eqn:HB; try exact I.
        intros E. destruct (ki_bk _ _ _ K brid boff HB) as (r2 & Hr2 & KK2). rewrite E, Hrg in Hr2. injection Hr2 as <-. rewrite Krg in KK2. discriminate.
    - intros q. split; [| split].
      + apply OM. intros pv Hp. exact (proj2 (LP q pv Hp)).
      + apply OM. intros nx Hn. exact (proj2 (LN q nx Hn)).
      + intros NEq. destruct (m_mem (get_meta_rec st q)) as [b|] eqn:MB; cbn; [| exact I].
        destruct (ZI q b MB) as [[ai2 Hb]|[]]. intros Fb. apply NEq.
        pose proof (NOGRP b _ Hb Fb) as ->. rewrite HST in Hb. injection Hb as E _. symmetry. exact E.
    - intros a1 ar1 Ha1. apply NGr. exact (M5 a1 ar1 Ha1).
    - intros b gh' Hb. destruct (ki_grps _ _ _ K b gh' Hb) as (g2 & Hg2 & _). rewrite Hg2. cbn. apply MSr.
      assert (HB2 : hosts st b g2) by (exists (g_active_idx gh'); rewrite Hb; destruct gh'; cbn in Hg2 |- *; subst; reflexivity).
      exact (go_slot _ _ _ (ki_gmetas _ _ _ K b g2 HB2)). }
  split; [exact TK|]. split; [rewrite K2; pose proof (bf_fit _ _ _ _ _ _ _ _ _ _ _ BF) as FIT; unfold MR in FIT; clear - FIT; lia|]. split; [rewrite K2; exact (bf_n _ _ _ _ _ _ _ _ _ _ _ BF)|].
  assert (CC : conc st c = r_base rg + 16). { rewrite EC. unfold conc, get_region. cbn [fst snd]. fold rid. rewrite Hrg. reflexivity. }
  split; [exact CC|]. split; [rewrite HA, CC; reflexivity|]. split; [exact (bf_off _ _ _ _ _ _ _ _ _ _ _ BF)| exact STR].
Qed.
End BRIDGE.
