(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.openssl.pem.lib.Spec Require Import STree Malloc KInv MI_Tree MI_Inv MI_Kit MI_Arith MI_Geom MI_List MI_Ext MI_Shadow
  MI_Pres1 MI_Pres2 MI_Read MI_WFree2 MI_WGroup MI_Cnt MI_TF2 MI_WEnframe MI_WEnframe2 MI_WMalloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Definition blk_known (stc stm : mstate) (k : blk) (m : aptr) (i : Z) : Prop :=
  let rid := fst (bslot k) in
  let p := snd (bslot k) + UNIT * boff k in
  let e := snd (bslot k) + get_stride (MR stm m) - IB in
  let res := e - p - bsize k in
  let q := (p - snd (gbase (MR stm m)) - UNIT) / UNIT in
  known stc (rid, p - 4) 0
  /\ known stc (rid, p - 3) (i + 32 * Z.min res 5)
  /\ known stc (rid, p - 2) (byte_of q 0) /\ known stc (rid, p - 1) (byte_of q 1) /\ 0 <= q < 2^16
  /\ (5 <= res -> known stc (rid, e - 4) (byte_of res 0) /\ known stc (rid, e - 3) (byte_of res 1)
                /\ known stc (rid, e - 2) (byte_of res 2) /\ known stc (rid, e - 1) (byte_of res 3)
                /\ known stc (rid, e - 5) 0 /\ res < 2^32)
  /\ (0 < res -> known stc (rid, e - res) 0).

Lemma blk_shadow_ok_known st k m i : blk_shadow_ok st k m i -> blk_known st st k m i.
Proof. unfold blk_shadow_ok, blk_known. cbn zeta. tauto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section GEN.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (g bg : aptr) (idx n off : Z) (l : list (aptr * Z)).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hg : hosts st bg g.
Hypothesis Hidx : 0 <= idx <= m_last_idx (MR st g).
Let c : aptr := (fst bg, sstart (MR st g) idx).
Hypothesis HP : x_pend X = Some c.
Hypothesis Hn : 0 <= n.
Hypothesis Ho : 0 <= off <= 291.
Let stride := get_stride (MR st g).
Hypothesis Hf : UNIT * off + n <= stride - IB.
Hypothesis TF : TF2 st.
Let p : aptr := aadd c (UNIT * off).
Hypothesis HA : forall a, In a (map fst l) ->
  fst a = fst bg /\ snd c - 3 <= snd a < snd c + stride - 4 /\ ~ (snd p <= snd a < snd p + n).
Let stw := wrs l st.
Let stf := havoc p n stw.
Hypothesis HK : blk_known stw st ((c, off), n) g idx.

Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))).

Lemma rg_p16 : snd p mod 16 = 0.
Proof.
  pose proof (ef_c16 X st L BL LS g bg idx 0 INV Hg) as C16. unfold p, aadd. cbn [snd] in *. unfold UNIT.
  rewrite Z.add_mod, C16, Z.mul_comm, Z_mod_mult by lia. reflexivity.
Qed.
Lemma rg_tick : s_tick stw = s_tick st. Proof. exact (proj2 (wrs_ctrl l st)). Qed.
Lemma rg_TKS : TKS stw (s_tick st). Proof. apply wrs_TKS; [lia| exact (TKS_of _ _ _ _ _ INV)]. Qed.
Lemma rg_hav u hl : r_hav (get_shadow stw (fst p)) !! u = Some hl -> hl_ticks hl (s_tick stw).
Proof. intros Hu ch Hch. pose proof rg_TKS as TK. rewrite <- rg_tick in TK. exact (proj1 (sh_ticks_of _ _ TK) u hl ch Hu Hch). Qed.
Lemma rg_ctrl : ctrl_eq st stf /\ s_tick stf = s_tick st.
Proof.
  destruct (havoc_ctrl p n stw) as [C T]. split; [exact (ctrl_eq_trans _ _ _ (proj1 (wrs_ctrl l st)) C)| rewrite T; apply rg_tick].
Qed.
Lemma rg_read_out r : ~ (fst r = fst bg /\ snd p <= snd r < snd p + n) ->
  cell_read (get_shadow stf (fst r)) (snd r) = cell_read (get_shadow stw (fst r)) (snd r).
Proof.
  intros Hr. unfold stf. destruct (Z.eq_dec n 0) as [N0|NZ]; [rewrite havoc_le0 by lia; reflexivity|].
  apply (cell_read_havoc_out p n stw rg_p16 ltac:(lia) rg_hav). exact Hr.
Qed.
Lemma rg_known x v : ~ (snd p <= x < snd p + n) -> known stw (fst bg, x) v -> known stf (fst bg, x) v.
Proof. intros Hx K. unfold known, SHd in *. cbn [fst snd] in *. rewrite (rg_read_out (fst bg, x)) by (cbn [fst snd]; tauto). exact K. Qed.

Lemma rg_unknown a : snd p <= a < snd p + n -> unknown stf (fst bg, a).
Proof.
  intros Ha. unfold unknown, SHd, stf. cbn [fst snd].
  destruct (cell_read_havoc_in p n stw rg_p16 ltac:(lia) rg_hav (fst bg, a) eq_refl Ha) as [h Hh]; [| exists h; exact Hh].
  cbn [snd]. intros v tk Hc. unfold stw in Hc. rewrite wrs_cells_other in Hc.
  2:{ intros Hin. destruct (HA _ Hin) as (_ & _ & NR). apply NR. exact Ha. }
  rewrite rg_tick. change (fst p) with (fst bg) in Hc.
  apply (TF2_interior_old X st L BL LS INV g bg idx Hg Hidx (ef_NH X st L BL LS g bg idx INV Hg Hidx HP) TF a v tk Hc).
  pose proof (ef_stride X st L BL LS g bg INV Hg) as [S16 _]. fold stride in S16.
  unfold p, aadd, c in Ha. cbn [fst snd] in Ha. rewrite sstart_succ. fold stride. unfold IB, UNIT in *. lia.
Qed.

Theorem reframe_INVL : INVL (xpend X None) stf L (((c, off), n) :: BL) LS.
Proof.
  destruct rg_ctrl as [CE TK]. pose proof (ef_stride X st L BL LS g bg INV Hg) as [S16 _]. fold stride in S16.
  pose proof (ef_slots X st L BL LS g bg idx INV Hg Hidx) as SL. fold c in SL.
  assert (REG' : exists r, s_regions st !! fst bg = Some r /\ r_kind r = RKGroup) by (destruct Hg as [ai Hb]; exact (ig_region _ _ _ IG _ _ Hb)).
  apply (INVL_add_block X st stf L BL LS c off n INV HP CE TK).
  - intros m i Hs q Hq. rewrite SL in Hs. inversion Hs. subst m i.
    assert (NQ : ~ (fst q = fst bg /\ snd p <= snd q < snd p + n)).
    { intros [F R]. apply Hq. unfold inT, c. cbn [fst snd]. split; [exact F|]. unfold p, aadd, c in R. cbn [snd] in R. rewrite sstart_succ. fold stride. unfold IB, UNIT in *. lia. }
    rewrite (rg_read_out q NQ). unfold stw. apply wrs_read_other.
    intros Hin. destruct (HA q Hin) as (F & R & _). apply Hq. unfold inT, c. cbn [fst snd]. split; [exact F|].
    rewrite sstart_succ. fold stride. unfold c in R. cbn [snd] in R. unfold IB in *. lia.
  - revert REG'. intros REG' rid sh Hsh. revert rid sh Hsh. change (DOMS st stf). unfold stf. destruct (Z.eq_dec n 0) as [N0|NZ].
    + rewrite havoc_le0 by lia. apply wrs_DOMS; [exact (DOMS_of _ _ _ _ _ INV)|]. intros q Hin. destruct (HA q Hin) as (F & _). rewrite F. exact REG'.
    + apply DOMS_havoc; [lia| | exact REG']. apply wrs_DOMS; [exact (DOMS_of _ _ _ _ _ INV)|]. intros q Hin. destruct (HA q Hin) as (F & _). rewrite F. exact REG'.
  - change (TKS stf (s_tick st)). unfold stf. destruct (Z.eq_dec n 0) as [N0|NZ].
    + rewrite havoc_le0 by lia. apply rg_TKS.
    + rewrite <- rg_tick. apply TKS_havoc; [apply rg_p16| lia| rewrite rg_tick; apply rg_TKS].
  - intros m i Hs. rewrite SL in Hs. inversion Hs. subst m i. split; [exact Ho|]. split; [exact Hn|]. split; [exact Hf|].
    assert (MRE : MR stf g = MR st g) by (apply MR_ext; exact (ce_metas _ _ CE)).
    unfold blk_known in HK. unfold blk_shadow_ok. cbn [bslot boff bsize fst snd] in HK |- *. cbn zeta in HK. rewrite MRE.
    fold stride in HK |- *.
    destruct HK as (K1 & K2 & K3 & K4 & QR & K5 & K6).
    assert (PP : snd p = snd c + UNIT * off) by reflexivity.
    assert (NP : forall x, x < snd p \/ snd p + n <= x -> ~ (snd p <= x < snd p + n)) by (intros; lia).
    split; [apply rg_known; [apply NP; rewrite PP; lia| exact K1]|].
    split; [apply rg_known; [apply NP; rewrite PP; lia| exact K2]|].
    split; [apply rg_known; [apply NP; rewrite PP; lia| exact K3]|].
    split; [apply rg_known; [apply NP; rewrite PP; lia| exact K4]|].
    split; [exact QR|].
    split.
    { intros R5. destruct (K5 R5) as (F1 & F2 & F3 & F4 & F5 & RS).
      split; [apply rg_known; [apply NP; rewrite PP; unfold IB, UNIT in *; lia| exact F1]|].
      split; [apply rg_known; [apply NP; rewrite PP; unfold IB, UNIT in *; lia| exact F2]|].
      split; [apply rg_known; [apply NP; rewrite PP; unfold IB, UNIT in *; lia| exact F3]|].
      split; [apply rg_known; [apply NP; rewrite PP; unfold IB, UNIT in *; lia| exact F4]|].
      split; [apply rg_known; [apply NP; rewrite PP; unfold IB, UNIT in *; lia| exact F5]| exact RS]. }
    split.
    { intros RP. apply rg_known; [apply NP; rewrite PP; unfold IB, UNIT in *; lia| exact (K6 RP)]. }
    intros a Ha. apply rg_unknown. rewrite PP. exact Ha.
Qed.
End GEN.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FULL.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (g bg : aptr) (idx n off : Z) (l : list (aptr * Z)).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hg : hosts st bg g.
Hypothesis Hidx : 0 <= idx <= m_last_idx (MR st g).
Let c : aptr := (fst bg, sstart (MR st g) idx).
Hypothesis HP : x_pend X = Some c.
Hypothesis Hn : 0 <= n.
Hypothesis Ho : 0 <= off <= 291.
Let stride := get_stride (MR st g).
Hypothesis Hf : UNIT * off + n <= stride - IB.
Hypothesis TF : TF2 st.
Hypothesis Hres : stride - IB - n < 2 ^ 32.
Hypothesis HLW : forall q, lastw l q None = lastw (EL st g bg idx n off) q None.
Hypothesis HIN : forall a, In a (map fst l) -> In a (map fst (EL st g bg idx n off)).

Let Hfit : n + IB <= get_stride (MR st g).
Proof. fold stride. unfold UNIT, IB in *. lia. Qed.

Lemma full_known x v : ~ (snd c + UNIT * off <= x < snd c + UNIT * off + n) ->
  known (stf st g bg idx n off) (fst bg, x) v -> known (wrs l st) (fst bg, x) v.
Proof.
  intros Hx K. unfold known, SHd in *. cbn [fst snd] in *.
  rewrite (stf_read_out X st L BL LS g bg idx n INV Hg Hn off (fst bg, x)) in K by (cbn [fst snd]; unfold pp, aadd; cbn [snd]; tauto).
  unfold stw in K. rewrite (wrs_lastw _ st (fst bg, x) (TKS_of _ _ _ _ _ INV)) in K.
  rewrite (wrs_lastw l st (fst bg, x) (TKS_of _ _ _ _ _ INV)), HLW. exact K.
Qed.

Theorem reframe_full_INVL :
  INVL (xpend X None) (havoc (aadd c (UNIT * off)) n (wrs l st)) L (((c, off), n) :: BL) LS.
Proof.
  pose proof (ef_stride X st L BL LS g bg INV Hg) as [S16 _]. fold stride in S16.
  apply (reframe_INVL X st L BL LS g bg idx n off l INV Hg Hidx HP Hn Ho Hf TF).
  - intros a Ha. exact (EL_addrs X st L BL LS g bg idx n INV Hg Hn Hfit off a (proj1 Ho) Hf (HIN a Ha)).
  - pose proof (blk_ok X st L BL LS g bg idx n INV Hg Hidx HP Hn Hfit TF Hres off Ho Hf) as B.
    assert (MRE : MR (stf st g bg idx n off) g = MR st g).
    { apply MR_ext. unfold stf, stw. destruct (havoc_ctrl (pp st g bg idx off) n (wrs (EL st g bg idx n off) st)) as [C _].
      rewrite (ce_metas _ _ C). exact (ce_metas _ _ (proj1 (wrs_ctrl _ st))). }
    unfold blk_shadow_ok in B. unfold blk_known. cbn [bslot boff bsize fst snd] in B |- *. cbn zeta in B. rewrite MRE in B.
    fold c stride in B |- *.
    destruct B as (K1 & K2 & K3 & K4 & QR & K5 & K6 & _).
    assert (NP : forall x, x < sstart (MR st g) idx + UNIT * off \/ sstart (MR st g) idx + UNIT * off + n <= x ->
                 ~ (snd c + UNIT * off <= x < snd c + UNIT * off + n)) by (unfold c; cbn [snd]; intros; lia).
    split; [apply full_known; [apply NP; lia| exact K1]|].
    split; [apply full_known; [apply NP; lia| exact K2]|].
    split; [apply full_known; [apply NP; lia| exact K3]|].
    split; [apply full_known; [apply NP; lia| exact K4]|].
    split; [exact QR|].
    split.
    { intros R5. destruct (K5 R5) as (F1 & F2 & F3 & F4 & F5 & RS).
      split; [apply full_known; [apply NP; unfold IB, UNIT in *; lia| exact F1]|].
      split; [apply full_known; [apply NP; unfold IB, UNIT in *; lia| exact F2]|].
      split; [apply full_known; [apply NP; unfold IB, UNIT in *; lia| exact F3]|].
      split; [apply full_known; [apply NP; unfold IB, UNIT in *; lia| exact F4]|].
      split; [apply full_known; [apply NP; unfold IB, UNIT in *; lia| exact F5]| exact RS]. }
    intros RP. apply full_known; [apply NP; unfold IB, UNIT in *; lia| exact (K6 RP)].
Qed.
End FULL.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ss_list (rid : N) (pz ez n idx : Z) : list (aptr * Z) :=
  let res := ez - pz - n in
  (if negb (res =? 0) then [((rid, ez - res), 0)] else [])
  ++ (if 5 <=? res then [((rid, ez - 5), 0); ((rid, ez - 4), res); ((rid, ez - 4 + 1), Z.shiftr res 8); ((rid, ez - 4 + 2), Z.shiftr res 16);
                          ((rid, ez - 4 + 3), Z.shiftr res 24)] else [])
  ++ [((rid, pz - 3), idx + 32 * Z.min res 5)].

Section SETSIZE.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (g bg : aptr) (idx n off : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hg : hosts st bg g.
Hypothesis Hidx : 0 <= idx <= m_last_idx (MR st g).
Let c : aptr := (fst bg, sstart (MR st g) idx).
Hypothesis HP : x_pend X = Some c.
Hypothesis Hn : 0 <= n.
Hypothesis Ho : 0 <= off <= 291.
Let stride := get_stride (MR st g).
Hypothesis Hf : UNIT * off + n <= stride - IB.
Hypothesis TF : TF2 st.
Hypothesis Hres : stride - IB - n < 2 ^ 32.
Let pz := sstart (MR st g) idx + UNIT * off.
Let ez := sstart (MR st g) idx + stride - IB.
Let q := (pz - snd (gbase (MR st g)) - UNIT) / UNIT.
(* [comment removed for export] *)
Hypothesis K1 : known st (fst bg, pz - 4) 0.
Hypothesis K3 : known st (fst bg, pz - 2) (byte_of q 0).
Hypothesis K4 : known st (fst bg, pz - 1) (byte_of q 1).
Hypothesis QR : 0 <= q < 2 ^ 16.
Let l := ss_list (fst bg) pz ez n idx.
Let res := ez - pz - n.

Local Ltac zeq :=
  match goal with
  | |- context [aptr_eqb (?r, ?a) (?r, ?b)] =>
      first [ rewrite (aptr_eqb_neq (r, a) (r, b)) by (intros E; apply (f_equal snd) in E; cbn [snd] in E; unfold res, ez, pz, IB, UNIT in *; lia)
            | rewrite (proj2 (aptr_eqb_eq (r, a) (r, b))) by (f_equal; unfold res, ez, pz, IB, UNIT in *; lia) ]
  end.

Lemma ss_res : 0 <= res < 2 ^ 32.
Proof. unfold res, ez, pz. fold stride in Hres. unfold IB, UNIT in *. lia. Qed.

Lemma ss_kw x w : lastw l (fst bg, x) None = Some w -> known (wrs l st) (fst bg, x) (Z.land w 255).
Proof. intros HL. unfold known, SHd. cbn [fst snd]. rewrite (wrs_lastw l st (fst bg, x) (TKS_of _ _ _ _ _ INV)), HL. reflexivity. Qed.
Lemma ss_ko x v : lastw l (fst bg, x) None = None -> known st (fst bg, x) v -> known (wrs l st) (fst bg, x) v.
Proof. intros HL K. unfold known, SHd in *. cbn [fst snd] in *. rewrite (wrs_lastw l st (fst bg, x) (TKS_of _ _ _ _ _ INV)), HL. exact K. Qed.

Theorem reframe_setsize_INVL :
  INVL (xpend X None) (havoc (aadd c (UNIT * off)) n (wrs l st)) L (((c, off), n) :: BL) LS.
Proof.
  pose proof (ef_stride X st L BL LS g bg INV Hg) as [S16 _]. fold stride in S16. pose proof ss_res as RR.
  apply (reframe_INVL X st L BL LS g bg idx n off l INV Hg Hidx HP Hn Ho Hf TF).
  - (* [comment removed for export] *)
    intros a Ha. unfold l, ss_list in Ha. fold res in Ha.
    destruct (Z.eqb_spec res 0) as [R0|R0]; destruct (Z.leb_spec 5 res) as [R5|R5]; cbn [negb app map fst In] in Ha;
      repeat match type of Ha with _ \/ _ => destruct Ha as [<-|Ha] | False => destruct Ha end;
      cbn [fst snd aadd]; (split; [reflexivity|]); unfold res, ez, pz, c in *; cbn [fst snd] in *; unfold IB, UNIT in *; lia.
  - unfold blk_known. cbn [bslot boff bsize fst snd]. cbn zeta. fold c stride. fold pz ez. fold res. fold q.
    split; [apply ss_ko; [unfold l, ss_list; fold res; destruct (Z.eqb_spec res 0); destruct (Z.leb_spec 5 res); try (exfalso; lia); cbn [negb app lastw]; repeat zeq; reflexivity| exact K1]|].
    split.
    { replace (idx + 32 * Z.min res 5) with (Z.land (idx + 32 * Z.min res 5) 255).
      2:{ change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. destruct Hg as [ai Hb].
          pose proof (g_li _ _ _ _ _ _ (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) _ _ _ Hb)) as LI. lia. }
      apply ss_kw. unfold l, ss_list; fold res; destruct (Z.eqb_spec res 0); destruct (Z.leb_spec 5 res); try (exfalso; lia); cbn [negb app lastw]; repeat zeq; reflexivity. }
    split; [apply ss_ko; [unfold l, ss_list; fold res; destruct (Z.eqb_spec res 0); destruct (Z.leb_spec 5 res); try (exfalso; lia); cbn [negb app lastw]; repeat zeq; reflexivity| exact K3]|].
    split; [apply ss_ko; [unfold l, ss_list; fold res; destruct (Z.eqb_spec res 0); destruct (Z.leb_spec 5 res); try (exfalso; lia); cbn [negb app lastw]; repeat zeq; reflexivity| exact K4]|].
    split; [exact QR|].
    split.
    { intros R5. assert (E5 : (5 <=? res) = true) by (apply Z.leb_le; exact R5). assert (EZ : (res =? 0) = false) by (apply Z.eqb_neq; lia).
      unfold byte_of. rewrite Z.mul_0_r, Z.shiftr_0_r, Z.mul_1_r. change (8 * 2) with 16. change (8 * 3) with 24.
      split; [apply ss_kw; unfold l, ss_list; fold res; rewrite E5, EZ; cbn [negb app lastw]; repeat zeq; reflexivity|].
      split; [replace (ez - 3) with (ez - 4 + 1) by lia; apply ss_kw; unfold l, ss_list; fold res; rewrite E5, EZ; cbn [negb app lastw]; repeat zeq; reflexivity|].
      split; [replace (ez - 2) with (ez - 4 + 2) by lia; apply ss_kw; unfold l, ss_list; fold res; rewrite E5, EZ; cbn [negb app lastw]; repeat zeq; reflexivity|].
      split; [replace (ez - 1) with (ez - 4 + 3) by lia; apply ss_kw; unfold l, ss_list; fold res; rewrite E5, EZ; cbn [negb app lastw]; repeat zeq; reflexivity|].
      split; [| lia].
      apply (ss_kw (ez - 5) 0). unfold l, ss_list; fold res; rewrite E5, EZ; cbn [negb app lastw]; repeat zeq; reflexivity. }
    intros RP. assert (EZ : (res =? 0) = false) by (apply Z.eqb_neq; lia).
    apply (ss_kw (ez - res) 0). unfold l, ss_list; fold res; rewrite EZ. destruct (Z.leb_spec 5 res); cbn [negb app lastw]; repeat zeq;
      repeat match goal with |- context [if aptr_eqb ?a ?b then _ else _] => destruct (aptr_eqb a b) end; reflexivity.
Qed.
End SETSIZE.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mv_list (rid : N) (cz pz ez n idx q off : Z) : list (aptr * Z) :=
  [((rid, pz - 4), 0); ((rid, pz - 3), idx); ((rid, pz - 2), q); ((rid, pz - 2 + 1), Z.shiftr q 8)]
  ++ ss_list rid pz ez n idx
  ++ [((rid, cz - 3), 224); ((rid, cz - 2), off); ((rid, cz - 2 + 1), Z.shiftr off 8)].

Section MOVE.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (g bg : aptr) (idx n off : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hg : hosts st bg g.
Hypothesis Hidx : 0 <= idx <= m_last_idx (MR st g).
Let c : aptr := (fst bg, sstart (MR st g) idx).
Hypothesis HP : x_pend X = Some c.
Hypothesis Hn : 0 <= n.
Hypothesis Ho : 1 <= off <= 291.
Let stride := get_stride (MR st g).
Hypothesis Hf : UNIT * off + n <= stride - IB.
Hypothesis TF : TF2 st.
Hypothesis Hres : stride - IB - n < 2 ^ 32.
Let cz := sstart (MR st g) idx.
Let pz := sstart (MR st g) idx + UNIT * off.
Let ez := sstart (MR st g) idx + stride - IB.
Let q := (pz - snd (gbase (MR st g)) - UNIT) / UNIT.
Hypothesis QR : 0 <= q < 2 ^ 16.
Let l := mv_list (fst bg) cz pz ez n idx q off.
Let res := ez - pz - n.

Local Ltac zeq :=
  match goal with
  | |- context [aptr_eqb (?r, ?a) (?r, ?b)] =>
      first [ rewrite (aptr_eqb_neq (r, a) (r, b)) by (intros E; apply (f_equal snd) in E; cbn [snd] in E; unfold res, ez, pz, cz, IB, UNIT in *; lia)
            | rewrite (proj2 (aptr_eqb_eq (r, a) (r, b))) by (f_equal; unfold res, ez, pz, cz, IB, UNIT in *; lia) ]
  end.

Lemma mv_res : 0 <= res < 2 ^ 32.
Proof. unfold res, ez, pz. fold stride in Hres. unfold IB, UNIT in *. lia. Qed.

Lemma mv_kw x w : lastw l (fst bg, x) None = Some w -> known (wrs l st) (fst bg, x) (Z.land w 255).
Proof. intros HL. unfold known, SHd. cbn [fst snd]. rewrite (wrs_lastw l st (fst bg, x) (TKS_of _ _ _ _ _ INV)), HL. reflexivity. Qed.

Local Ltac mv_lw := unfold l, mv_list, ss_list; fold res; destruct (Z.eqb_spec res 0); destruct (Z.leb_spec 5 res); try (exfalso; lia);
  cbn [negb app lastw]; repeat zeq; reflexivity.

Theorem reframe_move_INVL :
  INVL (xpend X None) (havoc (aadd c (UNIT * off)) n (wrs l st)) L (((c, off), n) :: BL) LS.
Proof.
  pose proof (ef_stride X st L BL LS g bg INV Hg) as [S16 _]. fold stride in S16. pose proof mv_res as RR.
  assert (LI : 0 <= idx <= 31).
  { destruct Hg as [ai Hb]. pose proof (g_li _ _ _ _ _ _ (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) _ _ _ Hb)) as LI. lia. }
  apply (reframe_INVL X st L BL LS g bg idx n off l INV Hg Hidx HP Hn ltac:(lia) Hf TF).
  - (* [comment removed for export] *)
    intros a Ha. unfold l, mv_list, ss_list in Ha. fold res in Ha.
    destruct (Z.eqb_spec res 0) as [R0|R0]; destruct (Z.leb_spec 5 res) as [R5|R5]; cbn [negb app map fst In] in Ha;
      repeat match type of Ha with _ \/ _ => destruct Ha as [<-|Ha] | False => destruct Ha end;
      cbn [fst snd aadd]; (split; [reflexivity|]); unfold res, ez, pz, cz, c in *; cbn [fst snd] in *; unfold IB, UNIT in *; lia.
  - unfold blk_known. cbn [bslot boff bsize fst snd]. cbn zeta. fold c stride. fold pz ez. fold res. fold q.
    split. { apply (mv_kw (pz - 4) 0). mv_lw. }
    split.
    { replace (idx + 32 * Z.min res 5) with (Z.land (idx + 32 * Z.min res 5) 255).
      2:{ change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia. }
      apply mv_kw. mv_lw. }
    split. { unfold byte_of. rewrite Z.mul_0_r, Z.shiftr_0_r. apply mv_kw. mv_lw. }
    split. { unfold byte_of. rewrite Z.mul_1_r. replace (pz - 1) with (pz - 2 + 1) by lia. apply mv_kw.
             mv_lw. }
    split; [exact QR|].
    split.
    { intros R5. assert (E5 : (5 <=? res) = true) by (apply Z.leb_le; exact R5). assert (EZ : (res =? 0) = false) by (apply Z.eqb_neq; lia).
      unfold byte_of. rewrite Z.mul_0_r, Z.shiftr_0_r, Z.mul_1_r. change (8 * 2) with 16. change (8 * 3) with 24.
      split; [apply mv_kw; unfold l, mv_list, ss_list; fold res; rewrite E5, EZ; cbn [negb app lastw]; repeat zeq; reflexivity|].
      split; [replace (ez - 3) with (ez - 4 + 1) by lia; apply mv_kw; unfold l, mv_list, ss_list; fold res; rewrite E5, EZ; cbn [negb app lastw]; repeat zeq; reflexivity|].
      split; [replace (ez - 2) with (ez - 4 + 2) by lia; apply mv_kw; unfold l, mv_list, ss_list; fold res; rewrite E5, EZ; cbn [negb app lastw]; repeat zeq; reflexivity|].
      split; [replace (ez - 1) with (ez - 4 + 3) by lia; apply mv_kw; unfold l, mv_list, ss_list; fold res; rewrite E5, EZ; cbn [negb app lastw]; repeat zeq; reflexivity|].
      split; [| lia].
      apply (mv_kw (ez - 5) 0). unfold l, mv_list, ss_list; fold res; rewrite E5, EZ; cbn [negb app lastw]; repeat zeq; reflexivity. }
    intros RP. assert (EZ : (res =? 0) = false) by (apply Z.eqb_neq; lia).
    apply (mv_kw (ez - res) 0). unfold l, mv_list, ss_list; fold res; rewrite EZ. destruct (Z.leb_spec 5 res); cbn [negb app lastw]; repeat zeq;
      repeat match goal with |- context [if aptr_eqb ?a ?b then _ else _] => destruct (aptr_eqb a b) end; reflexivity.
Qed.
End MOVE.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rf_tick (st : mstate) : mstate := set_tick (N.succ (s_tick st)) st.

Section WRAP.
Variables (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (k : blk) (g bg : aptr) (idx : Z).
Hypothesis INV : INVL x0 st L BL LS.
Hypothesis Hk : In k BL.
Hypothesis Hs : s_slots st !! bslot k = Some (g, idx).
Hypothesis Hg : hosts st bg g.
Let st1 := rf_tick st.
Let stride := get_stride (MR st g).

Lemma rf_prep :
  0 <= idx <= m_last_idx (MR st g) /\ bslot k = (fst bg, sstart (MR st g) idx)
  /\ INVL (xpend x0 (Some (bslot k))) st1 L (bl_remove (bslot k) BL) LS /\ TF2 st1
  /\ blk_shadow_ok st k g idx /\ 0 <= boff k <= 291.
Proof.
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  destruct (is_valid _ _ _ IS _ _ _ Hs) as (_ & Hi & Ek). rewrite (slot_start'_eq _ _ _ IM _ _ idx Hg) in Ek.
  destruct (is_blocks _ _ _ IS k Hk) as (m' & i' & Hs' & Hoff & _). 
  split; [exact Hi|]. split; [exact Ek|].
  split.
  { apply INVL_set_tick; [lia|].
    exact (INVL_remove_block x0 st st L BL LS k INV Hk eq_refl (ctrl_eq_refl st) eq_refl (fun _ _ _ _ _ => eq_refl)
             (DOMS_of _ _ _ _ _ INV) (TKS_of _ _ _ _ _ INV)). }
  split; [apply TF0_TF2; apply TF0_tick_new; [exact (TKS_of _ _ _ _ _ INV)| lia]|].
  split; [exact (ish_blk _ _ ISH k g idx Hk Hs)| exact Hoff].
Qed.

(* [comment removed for export] *)
Theorem INVL_reframe_full : forall (off' n' : Z) (l : list (aptr * Z)),
  0 <= off' <= 291 -> 0 <= n' -> UNIT * off' + n' <= stride - IB -> stride - IB - n' < 2 ^ 32 ->
  (forall q, lastw l q None = lastw (EL st1 g bg idx n' off') q None) ->
  (forall a, In a (map fst l) -> In a (map fst (EL st1 g bg idx n' off'))) ->
  INVL x0 (havoc (aadd (bslot k) (UNIT * off')) n' (wrs l st1)) L (((bslot k, off'), n') :: bl_remove (bslot k) BL) LS.
Proof.
  intros off' n' l Ho Hn Hf Hres HLW HIN. destruct rf_prep as (Hi & Ek & INV1 & TF1 & _ & _).
  rewrite Ek in INV1 |- *.
  exact (reframe_full_INVL (xpend x0 (Some (fst bg, sstart (MR st g) idx))) st1 L _ LS g bg idx n' off' l INV1 Hg Hi eq_refl Hn Ho Hf TF1 Hres HLW HIN).
Qed.

(* [comment removed for export] *)
Theorem INVL_reframe_move : forall (off' n' : Z),
  1 <= off' <= 291 -> 0 <= n' -> UNIT * off' + n' <= stride - IB -> stride - IB - n' < 2 ^ 32 ->
  0 <= (sstart (MR st g) idx + UNIT * off' - snd (gbase (MR st g)) - UNIT) / UNIT < 2 ^ 16 ->
  INVL x0 (havoc (aadd (bslot k) (UNIT * off')) n'
                 (wrs (mv_list (fst bg) (sstart (MR st g) idx) (sstart (MR st g) idx + UNIT * off') (sstart (MR st g) idx + stride - IB) n' idx
                               ((sstart (MR st g) idx + UNIT * off' - snd (gbase (MR st g)) - UNIT) / UNIT) off') st1))
       L (((bslot k, off'), n') :: bl_remove (bslot k) BL) LS.
Proof.
  intros off' n' Ho Hn Hf Hres QR. destruct rf_prep as (Hi & Ek & INV1 & TF1 & _ & _).
  rewrite Ek in INV1 |- *.
  exact (reframe_move_INVL (xpend x0 (Some (fst bg, sstart (MR st g) idx))) st1 L _ LS g bg idx n' off' INV1 Hg Hi eq_refl Hn Ho Hf TF1 Hres QR).
Qed.

(* [comment removed for export] *)
Theorem INVL_reframe_setsize : forall (n' : Z),
  0 <= n' -> UNIT * boff k + n' <= stride - IB -> stride - IB - n' < 2 ^ 32 ->
  INVL x0 (havoc (aadd (bslot k) (UNIT * boff k)) n'
                 (wrs (ss_list (fst bg) (sstart (MR st g) idx + UNIT * boff k) (sstart (MR st g) idx + stride - IB) n' idx) st1))
       L (((bslot k, boff k), n') :: bl_remove (bslot k) BL) LS.
Proof.
  intros n' Hn Hf Hres. destruct rf_prep as (Hi & Ek & INV1 & TF1 & SHK & Hoff).
  unfold blk_shadow_ok in SHK. cbn zeta in SHK. rewrite Ek in SHK. cbn [fst snd] in SHK.
  destruct SHK as (K1 & _ & K3 & K4 & QR & _).
  rewrite Ek in INV1 |- *.
  exact (reframe_setsize_INVL (xpend x0 (Some (fst bg, sstart (MR st g) idx))) st1 L _ LS g bg idx n' (boff k) INV1 Hg Hi eq_refl Hn Hoff Hf TF1 Hres
           K1 K3 K4 QR).
Qed.
End WRAP.
