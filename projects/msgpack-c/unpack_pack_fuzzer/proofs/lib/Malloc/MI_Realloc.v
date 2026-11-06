(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc Require Import STree Malloc MallocCtrl KInv MI_Tree MI_Inv MI_Kit MI_Arith MI_Geom MI_List MI_Ext MI_Shadow
  MI_WFree2 MI_WGroup MI_TF2 MI_Pres1 MI_Pres2 MI_WEnframe MI_WEnframe2 MI_WMalloc MI_WFree Realloc.
Unset Nia Cache. Unset Nra Cache.
Unset Lia Cache.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Set Keyed Unification.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Section ADD_RESIZED.
Variables (X1 : extras) (stA : mstate) (L : mled) (BL1 : list blk) (LS : lhead -> list aptr).
Variables (c : cptr) (off n : Z) (g bg : aptr) (idx : Z).
Hypothesis INVA : INVL X1 stA L BL1 LS.
Hypothesis HP : x_pend X1 = Some c.
Hypothesis Hg : hosts stA bg g.
Hypothesis Hidx : 0 <= idx <= m_last_idx (MR stA g).
Hypothesis Hc : c = (fst bg, sstart (MR stA g) idx).
Hypothesis Hoff : 0 <= off <= 255.
Hypothesis Hn : 0 <= n.
Let stride := get_stride (MR stA g).
Hypothesis Hfit : UNIT * off + n <= stride - IB.
Hypothesis Hres : stride - IB - UNIT * off - n < 2 ^ 32.

Let IM := proj1 (proj2 (proj2 INVA)).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INVA)))).
Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INVA))))).
Let ISH := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INVA))))).

Definition pp : aptr := aadd c (UNIT * off).
Definition ee : aptr := aadd c (stride - IB).
Definition resv : Z := snd ee - snd pp - n.
Definition qv : Z := (snd pp - snd bg - UNIT) / UNIT.
Definition SL : list (aptr * Z) := ss_list pp ee n idx.
Definition stw : mstate := wrs SL stA.
Definition stf : mstate := havoc pp n stw.

Hypothesis K4 : known stA (fst bg, snd pp - 4) 0.
Hypothesis K2 : known stA (fst bg, snd pp - 2) (byte_of qv 0).
Hypothesis K1 : known stA (fst bg, snd pp - 1) (byte_of qv 1).
Hypothesis Q16 : 0 <= qv < 2 ^ 16.
Hypothesis OLD : forall x v t, r_cells (get_shadow stA (fst bg)) !! x = Some (v, t) -> snd pp <= x < snd pp + n -> (t < s_tick stA)%N.

Lemma ar_slots : s_slots stA !! c = Some (g, idx).
Proof. rewrite Hc, <- (slot_start'_eq _ _ _ IM _ _ idx Hg). exact (is_total _ _ _ IS _ _ _ Hg Hidx). Qed.
Lemma ar_stride : 16 <= stride /\ stride mod 16 = 0.
Proof. pose proof (stride_ge _ _ _ IG _ _ Hg) as [A B]. unfold UNIT in *. split; assumption. Qed.

Lemma res_eq : resv = stride - IB - UNIT * off - n.
Proof. unfold resv, ee, pp, aadd. cbn [snd]. lia. Qed.

Lemma SL_eq : SL =
  (if negb (resv =? 0) then [(aadd ee (- resv), 0)] else [])
  ++ (if 5 <=? resv then [(aadd ee (-5), 0); (aadd ee (-4), resv); (aadd (aadd ee (-4)) 1, Z.shiftr resv 8);
                          (aadd (aadd ee (-4)) 2, Z.shiftr resv 16); (aadd (aadd ee (-4)) 3, Z.shiftr resv 24)] else [])
  ++ [(aadd pp (-3), idx + 32 * Z.min resv 5)].
Proof. reflexivity. Qed.

Lemma stw_TKS : TKS stw (s_tick stA).
Proof. unfold stw. apply wrs_TKS; [cbn; lia| exact (TKS_of _ _ _ _ _ INVA)]. Qed.
Lemma stw_tick : s_tick stw = s_tick stA. Proof. exact (proj2 (wrs_ctrl SL stA)). Qed.
Lemma stw_ctrl : ctrl_eq stA stw. Proof. exact (proj1 (wrs_ctrl SL stA)). Qed.
Lemma c16 : snd c mod 16 = 0.
Proof.
  pose proof (sstart_res X1 stA L BL1 LS INVA bg g idx Hg) as RS. rewrite Hc. cbn [snd]. unfold IB in RS.
  pose proof (Z.div_mod (sstart (MR stA g) idx - 4) 16 ltac:(lia)). pose proof (Z.div_mod (sstart (MR stA g) idx) 16 ltac:(lia)).
  pose proof (Z.mod_pos_bound (sstart (MR stA g) idx) 16 ltac:(lia)). lia.
Qed.
Lemma pp16 : snd pp mod 16 = 0.
Proof. unfold pp, aadd. cbn [snd]. unfold UNIT. rewrite Z.add_mod, c16, Z.mul_comm, Z_mod_mult by lia. reflexivity. Qed.
Lemma stw_hav u hl : r_hav (get_shadow stw (fst pp)) !! u = Some hl -> hl_ticks hl (s_tick stw).
Proof. intros Hu ch Hch. rewrite stw_tick. pose proof stw_TKS as TK. rewrite <- stw_tick in TK. rewrite <- stw_tick. exact (proj1 (sh_ticks_of _ _ TK) u hl ch Hu Hch). Qed.

Lemma stf_ctrl : ctrl_eq stA stf /\ s_tick stf = s_tick stA.
Proof.
  destruct (havoc_ctrl pp n stw) as [C T]. split; [exact (ctrl_eq_trans _ _ _ stw_ctrl C)| rewrite T; apply stw_tick].
Qed.

Lemma stf_read_out r : ~ (fst r = fst bg /\ snd pp <= snd r < snd pp + n) ->
  cell_read (get_shadow stf (fst r)) (snd r) = cell_read (get_shadow stw (fst r)) (snd r).
Proof.
  intros Hr. unfold stf. destruct (Z.eq_dec n 0) as [N0|NZ]; [rewrite havoc_le0 by lia; reflexivity|].
  apply (cell_read_havoc_out pp n stw pp16 ltac:(lia) stw_hav). unfold pp at 1. rewrite Hc. cbn [aadd fst]. exact Hr.
Qed.

Lemma SL_addrs q : In q (map fst SL) ->
  fst q = fst bg /\ snd c - 3 <= snd q < snd c + stride - 4 /\ ~ (snd pp <= snd q < snd pp + n).
Proof.
  intros Hin. pose proof ar_stride as [S16 _]. pose proof Hoff as [O0 _].
  assert (RR : 0 <= resv) by (rewrite res_eq; unfold IB, UNIT in *; lia).
  rewrite SL_eq in Hin.
  destruct (Z.eqb_spec resv 0) as [R0|R0]; destruct (Z.leb_spec 5 resv) as [R5|R5];
    cbn [negb app map fst In] in Hin; rewrite ?res_eq in *; unfold ee, pp, aadd in *; cbn [fst snd] in *; unfold IB, UNIT in *;
    repeat match type of Hin with _ \/ _ => destruct Hin as [<-|Hin] | False => destruct Hin end; rewrite Hc; cbn [fst snd];
    rewrite <- ?Hc; (split; [reflexivity| lia]).
Qed.

Lemma stf_known_w x w : ~ (snd pp <= x < snd pp + n) ->
  lastw SL (fst bg, x) None = Some w -> known stf (fst bg, x) (Z.land w 255).
Proof.
  intros Hx HL. unfold known, SHd. cbn [fst snd].
  rewrite (stf_read_out (fst bg, x)) by (cbn [fst snd]; tauto).
  unfold stw. rewrite (wrs_lastw SL stA (fst bg, x) (TKS_of _ _ _ _ _ INVA)). rewrite HL. reflexivity.
Qed.

Lemma stf_known_old x v : ~ (snd pp <= x < snd pp + n) ->
  lastw SL (fst bg, x) None = None -> known stA (fst bg, x) v -> known stf (fst bg, x) v.
Proof.
  intros Hx HL K. unfold known, SHd in *. cbn [fst snd] in *.
  rewrite (stf_read_out (fst bg, x)) by (cbn [fst snd]; tauto).
  unfold stw. rewrite (wrs_lastw SL stA (fst bg, x) (TKS_of _ _ _ _ _ INVA)). rewrite HL. exact K.
Qed.

Lemma SL_not_in x : snd pp <= x < snd pp + n -> ~ In (fst bg, x) (map fst SL).
Proof. intros Ha Hin. destruct (SL_addrs _ Hin) as (_ & _ & NR). apply NR. exact Ha. Qed.

Lemma stf_unknown x : snd pp <= x < snd pp + n -> unknown stf (fst bg, x).
Proof.
  intros Hx. unfold unknown, SHd, stf. cbn [fst snd].
  assert (Fp : fst pp = fst bg) by (unfold pp; rewrite Hc; reflexivity).
  destruct (cell_read_havoc_in pp n stw pp16 ltac:(lia) stw_hav (fst bg, x) (eq_sym Fp) Hx) as [h Hh]; [| exists h; exact Hh].
  cbn [snd]. intros v tk Hcl. unfold stw in Hcl. rewrite Fp in Hcl. rewrite wrs_cells_other in Hcl by (apply SL_not_in; exact Hx).
  rewrite stw_tick. exact (OLD x v tk Hcl Hx).
Qed.

Ltac aeq :=
  match goal with
  | |- context [aptr_eqb ?u ?w] =>
      first [ rewrite (aptr_eqb_neq u w) by (unfold pp, ee, aadd; rewrite ?Hc; cbn [fst snd]; intros E; apply (f_equal snd) in E; cbn [snd] in E; unfold IB, UNIT in *; lia)
            | rewrite (proj2 (aptr_eqb_eq u w)) by (unfold pp, ee, aadd; rewrite ?Hc; cbn [fst snd]; unfold IB, UNIT in *; f_equal; lia) ]
  end.

Lemma blk_ok : blk_shadow_ok stf ((c, off), n) g idx.
Proof.
  pose proof ar_stride as [S16 SM]. pose proof Hoff as [O0 O255].
  destruct stf_ctrl as [CE TK].
  assert (MRE : MR stf g = MR stA g) by (apply MR_ext; exact (ce_metas _ _ CE)).
  pose proof res_eq as RE.
  pose proof Hg as Hg'. destruct Hg' as [ai Hb]. pose proof (g_li _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Hb)) as LI.
  unfold blk_shadow_ok. cbn [bslot boff bsize fst snd]. rewrite MRE, (hosts_gbase _ _ _ IM _ _ Hg). fold stride.
  replace (snd c + stride - IB - (snd c + UNIT * off) - n) with resv by (rewrite RE; lia).
  change ((snd c + UNIT * off - snd bg - UNIT) / UNIT) with qv.
  assert (R0 : 0 <= resv) by (rewrite RE; unfold IB, UNIT in *; lia).
  assert (NP' : forall x, x < snd pp \/ snd pp + n <= x -> ~ (snd pp <= x < snd pp + n)) by (intros; lia).
  assert (PP : snd pp = snd c + UNIT * off) by reflexivity.
  assert (FC : fst c = fst bg) by (rewrite Hc; reflexivity).
  rewrite FC, <- PP.
  split; [| split; [| split; [| split; [| split; [exact Q16| split; [| split]]]]]].
  -   apply stf_known_old; [apply NP'; lia| | exact K4].
    rewrite SL_eq. destruct (negb (resv =? 0)); destruct (5 <=? resv); cbn [lastw app]; repeat aeq; reflexivity.
  -
    replace (idx + 32 * Z.min resv 5) with (Z.land (idx + 32 * Z.min resv 5) 255).
    2:{ change 255 with (Z.ones 8). rewrite Z.land_ones by lia. rewrite Z.mod_small; lia. }
    apply stf_known_w; [apply NP'; lia|].
    rewrite SL_eq. destruct (negb (resv =? 0)); destruct (5 <=? resv); cbn [negb lastw app]; repeat aeq; reflexivity.
  -   apply stf_known_old; [apply NP'; lia| | exact K2].
    rewrite SL_eq. destruct (Z.eqb_spec resv 0); destruct (Z.leb_spec 5 resv); cbn [negb lastw app]; try (exfalso; lia); repeat aeq; reflexivity.
  -   apply stf_known_old; [apply NP'; lia| | exact K1].
    rewrite SL_eq. destruct (Z.eqb_spec resv 0); destruct (Z.leb_spec 5 resv); cbn [negb lastw app]; try (exfalso; lia); repeat aeq; reflexivity.
  -   intros R5. unfold byte_of. rewrite Z.mul_0_r, Z.shiftr_0_r, Z.mul_1_r.
    assert (RS : resv < 2 ^ 32) by (rewrite RE; lia).
    assert (E5 : (5 <=? resv) = true) by (apply Z.leb_le; exact R5).
    assert (EZ : (resv =? 0) = false) by (apply Z.eqb_neq; lia).
    split; [| split; [| split; [| split; [| split; [| exact RS]]]]].
    1-4: apply stf_known_w; [apply NP'; rewrite ?RE; unfold IB, UNIT in *; lia|];
         rewrite SL_eq, E5, EZ; cbn [negb lastw app]; repeat aeq; try reflexivity.
    all: try (change (8 * 2) with 16; reflexivity). all: try (change (8 * 3) with 24; reflexivity).
    apply (stf_known_w _ 0); [apply NP'; rewrite ?RE; unfold IB, UNIT in *; lia|].
    rewrite SL_eq, E5, EZ; cbn [negb lastw app]; try (exfalso; lia); repeat aeq; reflexivity.
  -   intros RP.
    replace (snd c + stride - IB - resv) with (snd pp + n) by (rewrite RE, PP; lia).
    apply (stf_known_w _ 0); [apply NP'; lia|].
    assert (EZ : (resv =? 0) = false) by (apply Z.eqb_neq; lia).
    rewrite SL_eq, EZ. destruct (Z.leb_spec 5 resv); cbn [negb lastw app];
      try (destruct (Z.eq_dec resv 5)); try (exfalso; lia); repeat aeq; reflexivity.
  -   intros x Hx. apply stf_unknown. exact Hx.
Qed.

Let X' := mkX (x_idle X1) (x_zomb X1) None (x_orph X1) (x_fresh X1).

Theorem add_resized_INVL : INVL X' stf L (((c, off), n) :: BL1) LS.
Proof.
  destruct stf_ctrl as [CE TK]. pose proof ar_stride as [S16 _].
  assert (REG : exists r, s_regions stA !! fst bg = Some r /\ r_kind r = RKGroup).
  { pose proof Hg as Hg'. destruct Hg' as [ai' Hb]. exact (ig_region _ _ _ IG _ _ Hb). }
  apply (INVL_add_block X1 stA stf L BL1 LS c off n INVA HP CE TK).
  - intros m i Hs q Hq. rewrite ar_slots in Hs. inversion Hs. subst m i.
    assert (NQ : ~ (fst q = fst bg /\ snd pp <= snd q < snd pp + n)).
    { intros [F RG]. apply Hq. unfold inT. rewrite Hc. cbn [fst snd]. split; [exact F|]. unfold pp, aadd in RG. rewrite Hc in RG. cbn [snd] in RG.
      rewrite sstart_succ. fold stride. unfold IB, UNIT in *. lia. }
    rewrite (stf_read_out q NQ). unfold stw. rewrite wrs_read_other; [reflexivity|].
    intros Hin. destruct (SL_addrs q Hin) as (F & RG & _). apply Hq. unfold inT. rewrite Hc. cbn [fst snd]. split; [exact F|].
    rewrite sstart_succ. fold stride. rewrite Hc in RG. cbn [snd] in RG. unfold IB in *. lia.
  - change (DOMS stA stf). unfold stf. destruct (Z.eq_dec n 0) as [N0|NZ].
    + rewrite havoc_le0 by lia. apply wrs_DOMS; [exact (DOMS_of _ _ _ _ _ INVA)|]. intros q Hin. destruct (SL_addrs q Hin) as (F & _). rewrite F. exact REG.
    + apply DOMS_havoc; [lia| | unfold pp; rewrite Hc; cbn [aadd fst]; exact REG]. apply wrs_DOMS; [exact (DOMS_of _ _ _ _ _ INVA)|].
      intros q Hin. destruct (SL_addrs q Hin) as (F & _). rewrite F. exact REG.
  - change (TKS stf (s_tick stA)). unfold stf. destruct (Z.eq_dec n 0) as [N0|NZ].
    + rewrite havoc_le0 by lia. apply stw_TKS.
    + rewrite <- stw_tick. apply TKS_havoc; [apply pp16| lia| rewrite stw_tick; apply stw_TKS].
  - intros m i Hs. rewrite ar_slots in Hs. inversion Hs. subst m i.
    split; [exact Hoff|]. split; [exact Hn|]. split; [exact Hfit|]. apply blk_ok.
Qed.
End ADD_RESIZED.

Section INPLACE.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (c : cptr) (off old n : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hk : In ((c, off), old) BL.
Hypothesis NP : x_pend X = None.
Hypothesis Hn : 0 <= n.
Variables (g bg : aptr) (idx ai : Z) (a : aptr) (ar : area) (ka : Z).
Hypothesis BF : blk_facts st c off old g bg idx ai a ar ka.
Let stride := get_stride (MR st g).
Hypothesis Hfit : UNIT * off + n <= stride - IB.
Hypothesis Hres : stride - IB - UNIT * off - n < 2 ^ 32.

Let IM := proj1 (proj2 (proj2 INV)).
Let st_t := set_tick (N.succ (s_tick st)) st.
Let X1 := mkX (x_idle X) (x_zomb X) (Some c) (x_orph X) (x_fresh X).
Let BL1 := bl_remove c BL.

Lemma ip_hosts : hosts st bg g. Proof. exists ai. exact (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF). Qed.
Lemma INV_t : INVL X st_t L BL LS.
Proof. apply INVL_set_tick; [cbn; lia| exact INV]. Qed.
Lemma INV1 : INVL X1 st_t L BL1 LS.
Proof.
  apply (INVL_remove_block X st_t st_t L BL LS ((c, off), old) INV_t Hk NP).
  - apply ctrl_eq_refl.
  - reflexivity.
  - intros; reflexivity.
  - exact (DOMS_of _ _ _ _ _ INV_t).
  - exact (TKS_of _ _ _ _ _ INV_t).
Qed.

Lemma inplace_full_eq : inplace_full st c off n = stf st_t c off n g idx.
Proof. unfold inplace_full. rewrite (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF). reflexivity. Qed.

Theorem inplace_INVL : INVL X (inplace_full st c off n) L (((c, off), n) :: bl_remove c BL) LS.
Proof.
  rewrite inplace_full_eq.
  assert (EX : mkX (x_idle X1) (x_zomb X1) None (x_orph X1) (x_fresh X1) = X).
  { destruct X as [xi xz xp xo xf]. cbn in NP |- *. rewrite NP. reflexivity. }
  rewrite <- EX.
  pose proof (bf_shadow _ _ _ _ _ _ _ _ _ _ _ BF) as SHB. unfold blk_shadow_ok in SHB. cbn [bslot boff bsize fst snd] in SHB.
  rewrite (gbase_bm _ _ _ _ _ _ _ _ _ _ _ BF) in SHB. destruct SHB as (K4 & K3 & K2 & K1 & Q & _).
  assert (FC : fst c = fst bg) by (rewrite (bf_c _ _ _ _ _ _ _ _ _ _ _ BF); reflexivity).
  apply (add_resized_INVL X1 st_t L BL1 LS c off n g bg idx INV1 eq_refl ip_hosts (bf_i _ _ _ _ _ _ _ _ _ _ _ BF) (bf_c _ _ _ _ _ _ _ _ _ _ _ BF)
           (bf_off _ _ _ _ _ _ _ _ _ _ _ BF) Hn Hfit Hres).
  - rewrite <- FC. exact K4.
  - rewrite <- FC. exact K2.
  - rewrite <- FC. exact K1.
  - exact Q.
  - intros x v t Hc Hx. change (s_tick st_t) with (N.succ (s_tick st)). change (get_shadow st_t (fst bg)) with (get_shadow st (fst bg)) in Hc.
    destruct (get_shadow_cells_some st (fst bg) x (v, t) Hc) as (sh & Hs & Hc').
    destruct (TKS_of _ _ _ _ _ INV (fst bg) sh Hs) as (C & _ & _). destruct (C x v t Hc') as [_ Hle]. lia.
Qed.
End INPLACE.

End CEIL.
