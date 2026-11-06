(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec Require Import STree Malloc KInv MI_Tree MI_Inv MI_Kit MI_Arith MI_Geom MI_List MI_Ext MI_Shadow
  MI_Pres1 MI_Pres2 MI_Read MI_WFree2 MI_WGroup MI_Cnt MI_TF2 MI_WEnframe.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma havoc_le0 p n st : n <= 0 -> havoc p n st = st.
Proof. intros H. unfold havoc. destruct (Z.leb_spec n 0); [reflexivity| lia]. Qed.

Section ENFRAME.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (g bg : aptr) (idx n : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hg : hosts st bg g.
Hypothesis Hidx : 0 <= idx <= m_last_idx (MR st g).
Let c : aptr := (fst bg, sstart (MR st g) idx).
Hypothesis HP : x_pend X = Some c.
Hypothesis Hn : 0 <= n.
Hypothesis Hfit : n + IB <= get_stride (MR st g).
Hypothesis TF : TF2 st.
Hypothesis Hres : get_stride (MR st g) - IB - n < 2 ^ 32.
Let X' := xpend X None.
Let stride := get_stride (MR st g).
Let slack := (stride - IB - n) / UNIT.

Let IM := proj1 (proj2 (proj2 INV)).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))).
Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).
Let ISH := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

Lemma ef_gbase : gbase (MR st g) = bg. Proof. exact (hosts_gbase _ _ _ IM _ _ Hg). Qed.
Lemma ef_c : aadd (default (0%N, 0) (m_mem (get_meta_rec st g))) (UNIT + get_stride (get_meta_rec st g) * idx) = c.
Proof. fold (MR st g). change (default (0%N, 0) (m_mem (MR st g))) with (gbase (MR st g)). rewrite ef_gbase. unfold c, sstart, aadd. rewrite ef_gbase. f_equal. lia. Qed.
Lemma ef_slot : slot_start' (MR st g) idx = c. Proof. exact (slot_start'_eq _ _ _ IM _ _ idx Hg). Qed.
Lemma ef_slots : s_slots st !! c = Some (g, idx). Proof. rewrite <- ef_slot. exact (is_total _ _ _ IS _ _ _ Hg Hidx). Qed.
Lemma ef_stride : 16 <= stride /\ stride mod 16 = 0.
Proof. pose proof (stride_ge _ _ _ IG _ _ Hg) as [A B]. unfold UNIT in *. split; assumption. Qed.
Lemma ef_c16 : snd c mod 16 = 0.
Proof.
  pose proof (sstart_res X st L BL LS INV bg g idx Hg) as R. unfold c. cbn [snd]. unfold IB in R.
  pose proof (Z.div_mod (sstart (MR st g) idx - 4) 16 ltac:(lia)). pose proof (Z.div_mod (sstart (MR st g) idx) 16 ltac:(lia)).
  pose proof (Z.mod_pos_bound (sstart (MR st g) idx) 16 ltac:(lia)). lia.
Qed.
Lemma ef_NH : s_groups st !! c = None.
Proof.
  destruct Hg as [ai Hb]. pose proof (is_part _ _ _ IS _ _ _ idx Hb Hidx) as P5. cbn zeta in P5. rewrite ef_slot, HP in P5.
  destruct (s_groups st !! c) eqn:E; [| reflexivity]. exfalso. destruct P5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & nDE). apply nDE. split; [congruence| reflexivity].
Qed.
Lemma ef_NB k : In k BL -> bslot k <> c.
Proof.
  destruct Hg as [ai Hb]. pose proof (is_part _ _ _ IS _ _ _ idx Hb Hidx) as P5. cbn zeta in P5. rewrite ef_slot, HP in P5.
  intros Hk E. destruct P5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & nCE & _). apply nCE. split; [| reflexivity]. rewrite <- E. apply in_map. exact Hk.
Qed.
Lemma ef_q_range off : 0 <= off <= 255 -> UNIT * off + n <= stride - IB -> 0 <= (snd c + UNIT * off - (snd bg + UNIT)) / UNIT < 2 ^ 16.
Proof.

  pose proof Hfit as HFIT__. pose proof Hres as HRES__.
  intros Ho Hf. destruct Hg as [ai Hb]. pose proof (ig_ok _ _ _ IG _ _ _ Hb) as GO.
  pose proof (g_stride _ _ _ _ _ _ GO) as GS. pose proof (g_sc _ _ _ _ _ _ GO) as SC. pose proof (g_li _ _ _ _ _ _ GO) as LI.
  unfold c. cbn [snd]. unfold sstart. rewrite ef_gbase. fold stride. pose proof ef_stride as [S16 SM].
  replace (snd bg + UNIT + stride * idx + UNIT * off - (snd bg + UNIT)) with ((stride / 16 * idx + off) * 16)
    by (unfold UNIT; pose proof (Z.div_mod stride 16 ltac:(lia)) as DM__; set (q__ := stride / 16) in *; assert (E16__ : stride = 16 * q__) by lia; rewrite E16__; ring).
  unfold UNIT. rewrite Z.div_mul by lia.
  assert (0 <= stride / 16 * idx) by (apply Z.mul_nonneg_nonneg; [apply Z.div_pos; lia| lia]).
  split; [lia|].
  destruct SC as [[SC1 _]|(SC63 & L0 & _)].
  - destruct (GS ltac:(lia)) as (_ & _ & LT). unfold cnt_of in LT. fold stride in LT.
    assert (stride * idx <= stride * (m_last_idx (MR st g))) by (apply Z.mul_le_mono_nonneg_l; lia).
    pose proof (Z.div_mod stride 16 ltac:(lia)). unfold IB, UNIT in Hf.
    assert (E__ : stride * idx = 16 * (stride / 16 * idx)) by (assert (E16__ : stride = 16 * (stride / 16)) by lia; rewrite E16__ at 1; ring). lia.
  - rewrite L0 in Hidx. assert (idx = 0) by lia. subst idx. rewrite Z.mul_0_r. lia.
Qed.

Definition pp (off : Z) : aptr := aadd c (UNIT * off).
Definition ee : aptr := aadd c (stride - IB).
Definition resv (off : Z) : Z := snd ee - snd (pp off) - n.
Definition qv (off : Z) : Z := (snd (pp off) - (snd bg + UNIT)) / UNIT.
Definition EL (off : Z) : list (aptr * Z) :=
  (if negb (off =? 0) then [(aadd c (-2), off); (aadd (aadd c (-2)) 1, Z.shiftr off 8); (aadd c (-3), 224); (aadd (pp off) (-4), 0)] else [])
  ++ [(aadd (pp off) (-2), qv off); (aadd (aadd (pp off) (-2)) 1, Z.shiftr (qv off) 8); (aadd (pp off) (-3), idx)]
  ++ (if negb (resv off =? 0) then [(aadd ee (- resv off), 0)] else [])
  ++ (if 5 <=? resv off then [(aadd ee (-4), resv off); (aadd (aadd ee (-4)) 1, Z.shiftr (resv off) 8); (aadd (aadd ee (-4)) 2, Z.shiftr (resv off) 16); (aadd (aadd ee (-4)) 3, Z.shiftr (resv off) 24); (aadd ee (-5), 0)] else [])
  ++ [(aadd (pp off) (-3), Z.land idx 31 + Z.shiftl (if 5 <=? resv off then 5 else resv off) 5)].

Lemma EL_eq off : ef_list st g idx n off = EL off.
Proof.
  unfold ef_list, EL. rewrite (p0_eq st g idx n off). rewrite ef_c. fold (MR st g). fold stride.
  change (default (0%N, 0) (m_mem (MR st g))) with (gbase (MR st g)). rewrite ef_gbase. reflexivity.
Qed.

Lemma enframe_at_EL off : enframe_at st g idx n off = (wrs (EL off) st, pp off).
Proof. rewrite (enframe_at_eq st g idx n off), EL_eq, (p0_eq st g idx n off), ef_c. reflexivity. Qed.

Definition stw (off : Z) : mstate := wrs (EL off) st.
Definition stf (off : Z) : mstate := havoc (pp off) n (stw off).

Lemma stw_TKS off : TKS (stw off) (s_tick st).
Proof. apply wrs_TKS; [lia| exact (TKS_of _ _ _ _ _ INV)]. Qed.
Lemma stw_tick off : s_tick (stw off) = s_tick st. Proof. exact (proj2 (wrs_ctrl (EL off) st)). Qed.
Lemma stw_ctrl off : ctrl_eq st (stw off). Proof. exact (proj1 (wrs_ctrl (EL off) st)). Qed.
Lemma pp16 off : snd (pp off) mod 16 = 0.
Proof. unfold pp, aadd. cbn [snd]. unfold UNIT. rewrite Z.add_mod, ef_c16, Z.mul_comm, Z_mod_mult by lia. reflexivity. Qed.
Lemma stw_hav off u hl : r_hav (get_shadow (stw off) (fst (pp off))) !! u = Some hl -> hl_ticks hl (s_tick (stw off)).
Proof. intros Hu ch Hch. rewrite stw_tick. pose proof (stw_TKS off) as TK. rewrite <- (stw_tick off) in TK. rewrite <- (stw_tick off). exact (proj1 (sh_ticks_of _ _ TK) u hl ch Hu Hch). Qed.

Lemma stf_ctrl off : ctrl_eq st (stf off) /\ s_tick (stf off) = s_tick st.
Proof.
  destruct (havoc_ctrl (pp off) n (stw off)) as [C T]. split; [exact (ctrl_eq_trans _ _ _ (stw_ctrl off) C)| rewrite T; apply stw_tick].
Qed.

Lemma stf_read_out off r : ~ (fst r = fst bg /\ snd (pp off) <= snd r < snd (pp off) + n) ->
  cell_read (get_shadow (stf off) (fst r)) (snd r) = cell_read (get_shadow (stw off) (fst r)) (snd r).
Proof.
  intros Hr. unfold stf. destruct (Z.eq_dec n 0) as [N0|NZ]; [rewrite havoc_le0 by lia; reflexivity|].
  apply (cell_read_havoc_out (pp off) n (stw off) (pp16 off) ltac:(lia) (stw_hav off)). exact Hr.
Qed.

Lemma EL_addrs off a : 0 <= off -> UNIT * off + n <= stride - IB -> In a (map fst (EL off)) ->
  fst a = fst bg /\ snd c - 3 <= snd a < snd c + stride - 4 /\ ~ (snd (pp off) <= snd a < snd (pp off) + n).
Proof.
  intros Ho Hf Hin. pose proof ef_stride as [S16 _].
  assert (R : 0 <= resv off) by (unfold resv, ee, pp, aadd; cbn [fst snd]; unfold IB, UNIT in *; lia).
  unfold EL in Hin.
  destruct (Z.eqb_spec off 0) as [O0|O0]; destruct (Z.eqb_spec (resv off) 0) as [R0|R0]; destruct (Z.leb_spec 5 (resv off)) as [R5|R5];
    cbn [negb app map fst In] in Hin; unfold resv, ee, pp, aadd in *; cbn [fst snd] in *; unfold IB, UNIT in *;
    repeat match type of Hin with _ \/ _ => destruct Hin as [<-|Hin] | False => destruct Hin end; unfold c; cbn [fst snd]; (split; [reflexivity| lia]).
Qed.

Lemma stf_known_w off x w : 0 <= off -> UNIT * off + n <= stride - IB ->
  ~ (snd (pp off) <= x < snd (pp off) + n) ->
  lastw (EL off) (fst bg, x) None = Some w -> known (stf off) (fst bg, x) (Z.land w 255).
Proof.
  intros Ho Hf Hx HL. unfold known, SHd. cbn [fst snd].
  rewrite (stf_read_out off (fst bg, x)) by (cbn [fst snd]; tauto).
  unfold stw. rewrite (wrs_lastw (EL off) st (fst bg, x) (TKS_of _ _ _ _ _ INV)). rewrite HL. reflexivity.
Qed.

Lemma stf_known_old off x v : 0 <= off -> UNIT * off + n <= stride - IB ->
  ~ (snd (pp off) <= x < snd (pp off) + n) ->
  lastw (EL off) (fst bg, x) None = None -> known st (fst bg, x) v -> known (stf off) (fst bg, x) v.
Proof.
  intros Ho Hf Hx HL K. unfold known, SHd in *. cbn [fst snd] in *.
  rewrite (stf_read_out off (fst bg, x)) by (cbn [fst snd]; tauto).
  unfold stw. rewrite (wrs_lastw (EL off) st (fst bg, x) (TKS_of _ _ _ _ _ INV)). rewrite HL. exact K.
Qed.

Lemma EL_not_in off a : 0 <= off -> UNIT * off + n <= stride - IB ->
  snd (pp off) <= a < snd (pp off) + n -> ~ In (fst bg, a) (map fst (EL off)).
Proof. intros Ho Hf Ha Hin. destruct (EL_addrs off _ Ho Hf Hin) as (_ & _ & NR). apply NR. exact Ha. Qed.

Lemma stf_unknown off a : 0 <= off -> UNIT * off + n <= stride - IB ->
  snd (pp off) <= a < snd (pp off) + n -> unknown (stf off) (fst bg, a).
Proof.
  intros Ho Hf Ha. unfold unknown, SHd, stf. cbn [fst snd].
  destruct (cell_read_havoc_in (pp off) n (stw off) (pp16 off) ltac:(lia) (stw_hav off) (fst bg, a) eq_refl Ha) as [h Hh]; [| exists h; exact Hh].
  cbn [snd]. intros v tk Hc. unfold stw in Hc. rewrite wrs_cells_other in Hc by (apply EL_not_in; assumption).
  rewrite stw_tick. change (fst (pp off)) with (fst bg) in Hc.
  apply (TF2_interior_old X st L BL LS INV g bg idx Hg Hidx ef_NH TF a v tk Hc).
  unfold pp, aadd, c in Ha. cbn [fst snd] in Ha. rewrite sstart_succ. fold stride. unfold IB, UNIT in *. lia.
Qed.

Ltac aeq :=
  match goal with
  | |- context [aptr_eqb ?a ?b] =>
      first [ rewrite (aptr_eqb_neq a b) by (unfold pp, ee, aadd, c; cbn [fst snd]; intros E; apply (f_equal snd) in E; cbn [snd] in E; unfold IB, UNIT in *; lia)
            | rewrite (proj2 (aptr_eqb_eq a b)) by (unfold pp, ee, aadd, c; cbn [fst snd]; unfold IB, UNIT in *; f_equal; lia) ]
  end.
Ltac lastw_eval :=
  unfold EL; cbn [lastw app negb]; repeat aeq; reflexivity.

Lemma res_eq off : resv off = stride - IB - UNIT * off - n.
Proof. unfold resv, ee, pp, aadd. cbn [snd]. lia. Qed.
Lemma qv_eq off : qv off = (snd c + UNIT * off - (snd bg + UNIT)) / UNIT.
Proof. reflexivity. Qed.

Lemma blk_ok off : 0 <= off <= 255 -> UNIT * off + n <= stride - IB ->
  blk_shadow_ok (stf off) ((c, off), n) g idx.
Proof.
  intros Ho Hf. pose proof ef_stride as [S16 SM].
  destruct (stf_ctrl off) as [CE TK].
  assert (MRE : MR (stf off) g = MR st g) by (apply MR_ext; exact (ce_metas _ _ CE)).
  pose proof (res_eq off) as RE.
  destruct Hg as [ai Hb]. pose proof (g_li _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Hb)) as LI.
  unfold blk_shadow_ok. cbn [bslot boff bsize fst snd]. rewrite MRE, ef_gbase. fold stride.
  replace (snd c + stride - IB - (snd c + UNIT * off) - n) with (resv off) by (rewrite RE; lia).
  replace ((snd c + UNIT * off - snd bg - UNIT) / UNIT) with (qv off) by (unfold qv, pp, aadd; cbn [snd]; f_equal; lia).
  pose proof (ef_q_range off Ho Hf) as QR.
  replace ((snd c + UNIT * off - (snd bg + UNIT)) / UNIT) with (qv off) in QR by (unfold qv, pp, aadd; cbn [snd]; f_equal; lia).
  assert (R0 : 0 <= resv off) by (rewrite RE; unfold IB, UNIT in *; lia).
  assert (NP : forall x, x < snd (pp off) \/ snd (pp off) + n <= x -> ~ (snd (pp off) <= x < snd (pp off) + n)) by (intros; lia).
  assert (PP : snd (pp off) = snd c + UNIT * off) by reflexivity.
  split; [| split; [| split; [| split; [| split; [exact QR| split; [| split]]]]]].
  -   destruct (Z.eqb_spec off 0) as [O0|O0].
    + apply (stf_known_old off); [lia| exact Hf| apply NP; lia| |].
      * unfold EL. rewrite O0 at 1. cbn [Z.eqb negb app lastw].
        destruct (negb (resv off =? 0)); destruct (5 <=? resv off); cbn [lastw app]; try (exfalso; lia); repeat aeq; reflexivity.
      * subst off. pose proof (ish_hdr0 _ _ ISH bg g idx (ex_intro _ ai Hb) ltac:(unfold cnt_of; lia)) as K.
        unfold c. cbn [snd]. replace (sstart (MR st g) idx + UNIT * 0 - 4) with (sstart (MR st g) idx - IB) by (unfold IB, UNIT; lia). exact K.
    + apply (stf_known_w off _ 0); [lia| exact Hf| apply NP; lia|].
      unfold EL. replace (off =? 0) with false by (symmetry; apply Z.eqb_neq; exact O0). cbn [negb app lastw].
      destruct (negb (resv off =? 0)); destruct (5 <=? resv off); cbn [lastw app]; try (exfalso; lia); repeat aeq; reflexivity.
  -
    replace (idx + 32 * Z.min (resv off) 5) with (Z.land (Z.land idx 31 + Z.shiftl (if 5 <=? resv off then 5 else resv off) 5) 255).
    2:{ replace (Z.land idx 31) with idx by (change 31 with (Z.ones 5); rewrite Z.land_ones by lia; rewrite Z.mod_small; lia). rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
        destruct (Z.leb_spec 5 (resv off)).
        - rewrite Z.min_r by lia. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. rewrite Z.mod_small; lia.
        - rewrite Z.min_l by lia. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. rewrite Z.mod_small; lia. }
    apply (stf_known_w off); [lia| exact Hf| apply NP; lia|].
    unfold EL. destruct (off =? 0); destruct (negb (resv off =? 0)); destruct (5 <=? resv off); cbn [negb lastw app]; try (exfalso; lia); repeat aeq; reflexivity.
  -   unfold byte_of. rewrite Z.mul_0_r, Z.shiftr_0_r.
    apply (stf_known_w off); [lia| exact Hf| apply NP; lia|].
    unfold EL. destruct (off =? 0); destruct (Z.eqb_spec (resv off) 0); destruct (Z.leb_spec 5 (resv off)); cbn [negb lastw app]; try (exfalso; lia); repeat aeq; reflexivity.
  -   unfold byte_of. rewrite Z.mul_1_r.
    apply (stf_known_w off); [lia| exact Hf| apply NP; lia|].
    unfold EL. destruct (off =? 0); destruct (Z.eqb_spec (resv off) 0); destruct (Z.leb_spec 5 (resv off)); cbn [negb lastw app]; try (exfalso; lia); repeat aeq; reflexivity.
  -   intros R5. unfold byte_of. rewrite Z.mul_0_r, Z.shiftr_0_r, Z.mul_1_r.
    assert (RS : resv off < 2 ^ 32).
    { rewrite RE. fold stride in Hres. unfold UNIT. lia. }
    assert (E5 : (5 <=? resv off) = true) by (apply Z.leb_le; exact R5).
    assert (EZ : (resv off =? 0) = false) by (apply Z.eqb_neq; lia).
    split; [| split; [| split; [| split; [| split; [| exact RS]]]]].
    1-4: apply (stf_known_w off); [lia| exact Hf| apply NP; rewrite ?RE; unfold IB, UNIT in *; lia|];
         unfold EL; rewrite E5, EZ; destruct (off =? 0); cbn [negb lastw app]; repeat aeq; try reflexivity.
    all: try (change (8 * 2) with 16; reflexivity). all: try (change (8 * 3) with 24; reflexivity).
    apply (stf_known_w off _ 0); [lia| exact Hf| apply NP; rewrite ?RE; unfold IB, UNIT in *; lia|].
    unfold EL; rewrite E5, EZ; destruct (off =? 0); cbn [negb lastw app]; try (exfalso; lia); repeat aeq; reflexivity.
  -   intros RP.
    replace (snd c + stride - IB - resv off) with (snd (pp off) + n) by (rewrite RE, PP; lia).
    apply (stf_known_w off _ 0); [lia| exact Hf| apply NP; lia|].
    assert (EZ : (resv off =? 0) = false) by (apply Z.eqb_neq; lia).
    unfold EL; rewrite EZ. destruct (off =? 0); destruct (Z.leb_spec 5 (resv off)); cbn [negb lastw app];
      try (destruct (Z.eq_dec (resv off) 5)); try (exfalso; lia); repeat aeq; reflexivity.
  -   intros a Ha. apply (stf_unknown off); [lia| exact Hf|]. rewrite PP. exact Ha.
Qed.

Lemma ef_INVL off : 0 <= off <= 255 -> UNIT * off + n <= stride - IB ->
  INVL X' (stf off) L (((c, off), n) :: BL) LS.
Proof.
  intros Ho Hf. destruct (stf_ctrl off) as [CE TK]. pose proof ef_stride as [S16 _].
  destruct Hg as [ai Hb] eqn:EHg.
  apply (INVL_add_block X st (stf off) L BL LS c off n INV HP CE TK).
  - intros m i Hs q Hq. rewrite ef_slots in Hs. inversion Hs. subst m i.
    assert (NQ : ~ (fst q = fst bg /\ snd (pp off) <= snd q < snd (pp off) + n)).
    { intros [F R]. apply Hq. unfold inT, c. cbn [fst snd]. split; [exact F|]. unfold pp, aadd, c in R. cbn [snd] in R. rewrite sstart_succ. fold stride. unfold IB, UNIT in *. lia. }
    rewrite (stf_read_out off q NQ). unfold stw. apply wrs_read_other.
    intros Hin. destruct (EL_addrs off q ltac:(lia) Hf Hin) as (F & R & _). apply Hq. unfold inT, c. cbn [fst snd]. split; [exact F|].
    rewrite sstart_succ. fold stride. unfold c in R. cbn [snd] in R. unfold IB in *. lia.
  - intros rid sh Hsh. assert (REG' : exists r, s_regions st !! fst bg = Some r /\ r_kind r = RKGroup) by exact (ig_region _ _ _ IG _ _ Hb).
    revert rid sh Hsh. change (DOMS st (stf off)). unfold stf. destruct (Z.eq_dec n 0) as [N0|NZ].
    + rewrite havoc_le0 by lia. apply wrs_DOMS; [exact (DOMS_of _ _ _ _ _ INV)|]. intros q Hin. destruct (EL_addrs off q ltac:(lia) Hf Hin) as (F & _). rewrite F. exact REG'.
    + apply DOMS_havoc; [lia| | exact REG']. apply wrs_DOMS; [exact (DOMS_of _ _ _ _ _ INV)|]. intros q Hin. destruct (EL_addrs off q ltac:(lia) Hf Hin) as (F & _). rewrite F. exact REG'.
  - change (TKS (stf off) (s_tick st)). unfold stf. destruct (Z.eq_dec n 0) as [N0|NZ].
    + rewrite havoc_le0 by lia. apply stw_TKS.
    + rewrite <- (stw_tick off). apply TKS_havoc; [apply pp16| lia| rewrite stw_tick; apply stw_TKS].
  - intros m i Hs. rewrite ef_slots in Hs. inversion Hs. subst m i. split; [exact Ho|]. split; [exact Hn|]. split; [exact Hf|].
    apply blk_ok; assumption.
Qed.

Theorem enframe_ft ctr (Post : mled -> mstate * optr -> Prop) :
  (forall off st' , 0 <= off <= 255 -> UNIT * off + n <= stride - IB ->
     INVL X' st' L (((c, off), n) :: BL) LS -> ctrl_eq st st' -> s_tick st' = s_tick st ->
     Post L (st', Some (aadd c (UNIT * off)))) ->
  ftree L (enframe_full st g idx n ctr (fun st2 p => ret (havoc p n st2, Some p))) Post.
Proof.
  intros HPost. pose proof ef_stride as [S16 SM].
  assert (KR : forall q v, cell_read (get_shadow st (fst q)) (snd q) = Known v -> 0 <= v < 256) by (intros q v; apply (known_range _ _ _ _ _ q v INV)).
  assert (SL : 0 <= slack) by (unfold slack; apply Z.div_pos; unfold IB, UNIT in *; lia).
  assert (SL16 : UNIT * slack <= stride - IB - n).
  { unfold slack, UNIT, IB in *. pose proof (Z.div_mod (stride - 4 - n) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (stride - 4 - n) 16 ltac:(lia)). lia. }
  assert (GO : forall v, 0 <= v < 256 ->
    ftree L (let '(st1, p) := enframe_at st g idx n (fold_off v slack) in ret (havoc p n st1, Some p)) Post).
  { intros v Hv. pose proof (fold_off_le v slack Hv SL) as FO.
    assert (F255 : fold_off v slack <= 255).
    { unfold fold_off in *. destruct (Z.ltb_spec slack v); [| lia]. cbn zeta in FO. unfold fold_off in FO. lia. }
    rewrite enframe_at_EL. cbn [ftree ret]. apply HPost.
    - lia.
    - unfold UNIT, IB in *. lia.
    - apply ef_INVL; [lia|]. unfold UNIT, IB in *. lia.
    - exact (proj1 (stf_ctrl _)).
    - exact (proj2 (stf_ctrl _)). }
  unfold enframe_full, enframe_read_off. fold (MR st g). fold stride. rewrite ef_slot.
  change ((stride - IB - n) / UNIT) with slack.
  apply rd8_ftree; [intros v; apply KR|]. intros b3 Hb3.
  destruct (b3 =? 0); cbn [negb].
  - apply GO. apply land255_range.
  - apply rd16_ftree; [intros q v; apply KR|]. intros o16 Ho16. apply GO. apply land255_range.
Qed.
End ENFRAME.
