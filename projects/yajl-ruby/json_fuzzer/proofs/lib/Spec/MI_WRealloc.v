(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree Malloc MallocCtrl KInv
  MI_Tree MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext MI_Ext2 MI_Shadow MI_Pres1 MI_Pres2 MI_Read
  MI_WFree MI_WFree2 MI_WNtf2 MI_WGroup MI_TF2 MI_WEnframe MI_WEnframe2 MI_WSlot MI_WMalloc MI_Ledger
  Realloc ReallocProto MI_WRemap.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section SS.
Variables (p e : aptr) (n b3 : Z).
Let res := snd e - snd p - n.
Definition ss_list : list (aptr * Z) :=
  (if negb (res =? 0) then [(aadd e (- res), 0)] else [])
  ++ (if 5 <=? res then [(aadd e (-4), res); (aadd (aadd e (-4)) 1, Z.shiftr res 8); (aadd (aadd e (-4)) 2, Z.shiftr res 16);
                         (aadd (aadd e (-4)) 3, Z.shiftr res 24); (aadd e (-5), 0)] else [])
  ++ [(aadd p (-3), Z.land b3 31 + Z.shiftl (if 5 <=? res then 5 else res) 5)].

Lemma set_size_eq st : set_size p e n b3 st = wrs ss_list st.
Proof.
  unfold set_size, ss_list. subst res.
  destruct (snd e - snd p - n =? 0); cbn beta iota delta [wr16 wr32 wrs app negb];
    destruct (5 <=? snd e - snd p - n); cbn beta iota delta [wrs app negb]; reflexivity.
Qed.
End SS.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section HDR.
Variables (st : mstate) (c : cptr) (off n : Z).
Variables (m bm : aptr) (i ai : Z) (a : aptr) (ar : area) (ka : Z).
Hypothesis BF : blk_facts st c off n m bm i ai a ar ka.
Let p : aptr := aadd c (UNIT * off).

Lemma realloc_hdr_eq : realloc_hdr st p = SRet (Some (m, i, n)).
Proof.
  unfold realloc_hdr. rewrite (get_meta_eq st c off n m bm i ai a ar ka BF). cbv beta zeta.
  unfold slot_start. rewrite (bf_mem _ _ _ _ _ _ _ _ _ _ _ BF). cbv beta zeta iota.
  rewrite (get_nominal_size_eq st c off n m bm i ai a ar ka BF). reflexivity.
Qed.
End HDR.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section RESIZE.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (m bm : aptr) (i off n : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hm : hosts st bm m.
Hypothesis Hi : 0 <= i <= m_last_idx (MR st m).
Let c : aptr := (fst bm, sstart (MR st m) i).
Hypothesis HP : x_pend X = Some c.
Hypothesis Hoff : 0 <= off <= 255.
Hypothesis Hn : 0 <= n.
Let stride := get_stride (MR st m).
Hypothesis FIT : UNIT * off + n <= stride - IB.
Hypothesis RES32 : stride - IB - UNIT * off - n < 2 ^ 32.
Let X' := xpend X None.
Let p : aptr := aadd c (UNIT * off).
Let e : aptr := aadd c (stride - IB).
Let res : Z := snd e - snd p - n.
Let q : Z := (snd p - (snd bm + UNIT)) / UNIT.
(* [comment removed for export] *)
Hypothesis K4 : known st (fst bm, snd p - 4) 0.
Hypothesis K2 : known st (fst bm, snd p - 2) (byte_of q 0).
Hypothesis K1 : known st (fst bm, snd p - 1) (byte_of q 1).
Hypothesis Q16 : 0 <= q < 2 ^ 16.
(* [comment removed for export] *)
Hypothesis HT : TW st (fun r => ~ (fst r = fst bm /\ snd p <= snd r < snd p + n)).

Let IM := proj1 (proj2 (proj2 INV)).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))).
Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).
Let ISH := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

Definition SL : list (aptr * Z) := ss_list p e n i.
Definition stw2 : mstate := wrs SL st.
Definition stf2 : mstate := havoc p n stw2.

Lemma rs_set_size : set_size p e n i st = stw2.
Proof. unfold stw2, SL. apply set_size_eq. Qed.

Lemma rs_gbase : gbase (MR st m) = bm. Proof. exact (hosts_gbase _ _ _ IM _ _ Hm). Qed.
Lemma rs_slot : slot_start' (MR st m) i = c. Proof. exact (slot_start'_eq _ _ _ IM _ _ i Hm). Qed.
Lemma rs_slots : s_slots st !! c = Some (m, i). Proof. rewrite <- rs_slot. exact (is_total _ _ _ IS _ _ _ Hm Hi). Qed.
Lemma rs_stride : 16 <= stride /\ stride mod 16 = 0.
Proof. pose proof (stride_ge _ _ _ IG _ _ Hm) as [A B]. unfold UNIT in *. split; assumption. Qed.
Lemma rs_c16 : snd c mod 16 = 0.
Proof.
  pose proof (sstart_res X st L BL LS INV bm m i Hm) as R. unfold c. cbn [snd]. unfold IB in R.
  pose proof (Z.div_mod (sstart (MR st m) i - 4) 16 ltac:(lia)). pose proof (Z.div_mod (sstart (MR st m) i) 16 ltac:(lia)).
  pose proof (Z.mod_pos_bound (sstart (MR st m) i) 16 ltac:(lia)). lia.
Qed.
Lemma rs_p16 : snd p mod 16 = 0.
Proof. unfold p, aadd. cbn [snd]. unfold UNIT. rewrite Z.add_mod, rs_c16, Z.mul_comm, Z_mod_mult by lia. reflexivity. Qed.
Lemma rs_res : res = stride - IB - UNIT * off - n.
Proof. unfold res, e, p, aadd. cbn [snd]. lia. Qed.
Lemma rs_res0 : 0 <= res. Proof. rewrite rs_res. unfold IB, UNIT in *. lia. Qed.

Lemma stw2_TKS : TKS stw2 (s_tick st).
Proof. unfold stw2. apply wrs_TKS; [lia| exact (TKS_of _ _ _ _ _ INV)]. Qed.
Lemma stw2_tick : s_tick stw2 = s_tick st. Proof. exact (proj2 (wrs_ctrl SL st)). Qed.
Lemma stw2_ctrl : ctrl_eq st stw2. Proof. exact (proj1 (wrs_ctrl SL st)). Qed.
Lemma stw2_hav u hl : r_hav (get_shadow stw2 (fst p)) !! u = Some hl -> hl_ticks hl (s_tick stw2).
Proof. intros Hu ch Hch. pose proof stw2_TKS as TK. rewrite <- stw2_tick in TK. exact (proj1 (sh_ticks_of _ _ TK) u hl ch Hu Hch). Qed.
Lemma stf2_ctrl : ctrl_eq st stf2 /\ s_tick stf2 = s_tick st.
Proof.
  destruct (havoc_ctrl p n stw2) as [C T]. split; [exact (ctrl_eq_trans _ _ _ stw2_ctrl C)| rewrite T; apply stw2_tick].
Qed.

Lemma stf2_read_out r : ~ (fst r = fst bm /\ snd p <= snd r < snd p + n) ->
  cell_read (get_shadow stf2 (fst r)) (snd r) = cell_read (get_shadow stw2 (fst r)) (snd r).
Proof.
  intros Hr. unfold stf2. destruct (Z.eq_dec n 0) as [N0|NZ]; [rewrite havoc_le0 by lia; reflexivity|].
  apply (cell_read_havoc_out p n stw2 rs_p16 ltac:(lia) stw2_hav). exact Hr.
Qed.

(* [comment removed for export] *)
Lemma SL_addrs r : In r (map fst SL) ->
  fst r = fst bm /\ (snd r = snd p - 3 \/ snd p + n <= snd r < snd c + stride - 4).
Proof.
  intros Hin. pose proof rs_stride as [S16 _]. pose proof rs_res0 as R0. pose proof rs_res as RE.
  unfold SL, ss_list in Hin. fold e in Hin.
  change (snd e - snd p - n) with res in Hin.
  destruct (Z.eqb_spec res 0) as [Rz|Rz]; destruct (Z.leb_spec 5 res) as [R5|R5];
    cbn [negb app map fst In] in Hin; unfold e, p, aadd in *; cbn [fst snd] in *; unfold IB, UNIT in *;
    repeat match type of Hin with _ \/ _ => destruct Hin as [<-|Hin] | False => destruct Hin end; unfold c; cbn [fst snd]; (split; [reflexivity| lia]).
Qed.

Lemma SL_not_user a : snd p <= a < snd p + n -> ~ In (fst bm, a) (map fst SL).
Proof. intros Ha Hin. pose proof rs_res0 as R0. pose proof rs_res as RE. destruct (SL_addrs _ Hin) as [_ [E|R]]; cbn [snd] in *; unfold e, p, aadd, c in *; cbn [fst snd] in *; unfold IB, UNIT in *; lia. Qed.

Lemma stf2_known_w x w : ~ (snd p <= x < snd p + n) ->
  lastw SL (fst bm, x) None = Some w -> known stf2 (fst bm, x) (Z.land w 255).
Proof.
  intros Hx HL. unfold known, SHd. cbn [fst snd].
  rewrite (stf2_read_out (fst bm, x)) by (cbn [fst snd]; tauto).
  unfold stw2. rewrite (wrs_lastw SL st (fst bm, x) (TKS_of _ _ _ _ _ INV)). rewrite HL. reflexivity.
Qed.

Lemma stf2_known_old x v : ~ (snd p <= x < snd p + n) ->
  lastw SL (fst bm, x) None = None -> known st (fst bm, x) v -> known stf2 (fst bm, x) v.
Proof.
  intros Hx HL K. unfold known, SHd in *. cbn [fst snd] in *.
  rewrite (stf2_read_out (fst bm, x)) by (cbn [fst snd]; tauto).
  unfold stw2. rewrite (wrs_lastw SL st (fst bm, x) (TKS_of _ _ _ _ _ INV)). rewrite HL. exact K.
Qed.

Lemma stf2_unknown a : snd p <= a < snd p + n -> unknown stf2 (fst bm, a).
Proof.
  intros Ha. unfold unknown, SHd, stf2. cbn [fst snd].
  destruct (cell_read_havoc_in p n stw2 rs_p16 ltac:(lia) stw2_hav (fst bm, a) eq_refl Ha) as [h Hh]; [| exists h; exact Hh].
  cbn [snd]. intros v tk Hc. unfold stw2 in Hc. rewrite wrs_cells_other in Hc by (apply SL_not_user; exact Ha).
  rewrite stw2_tick. change (fst p) with (fst bm) in Hc.
  destruct (get_shadow_cells_some st (fst bm) a (v, tk) Hc) as (sh & Hsh & Hc').
  destruct (proj1 (TKS_of _ _ _ _ _ INV (fst bm) sh Hsh) a v tk Hc') as [_ LE].
  destruct (N.eq_dec tk (s_tick st)) as [E|NE]; [| lia].
  exfalso. apply (HT (fst bm) sh a v tk Hsh Hc' E). cbn [fst snd]. split; [reflexivity| exact Ha].
Qed.

Ltac rs_aeq :=
  match goal with
  | |- context [aptr_eqb ?a ?b] =>
      first [ rewrite (aptr_eqb_neq a b) by (unfold e, p, aadd, c; cbn [fst snd]; intros E; apply (f_equal snd) in E; cbn [snd] in E; unfold IB, UNIT in *; lia)
            | rewrite (proj2 (aptr_eqb_eq a b)) by (unfold e, p, aadd, c; cbn [fst snd]; unfold IB, UNIT in *; f_equal; lia) ]
  end.

Lemma rs_blk_ok : blk_shadow_ok stf2 ((c, off), n) m i.
Proof.
  pose proof rs_stride as [S16 SM]. destruct stf2_ctrl as [CE TK].
  assert (MRE : MR stf2 m = MR st m) by (apply MR_ext; exact (ce_metas _ _ CE)).
  pose proof rs_res as RE. pose proof rs_res0 as R0.
  destruct (hosts_ok _ _ _ IG _ _ Hm) as (ai0 & Hb0 & GO0). pose proof (g_li _ _ _ _ _ _ GO0) as LI0.
  unfold blk_shadow_ok. cbn [bslot boff bsize fst snd]. rewrite MRE, rs_gbase. fold stride.
  replace (snd c + stride - IB - (snd c + UNIT * off) - n) with res by (rewrite RE; lia).
  replace ((snd c + UNIT * off - snd bm - UNIT) / UNIT) with q by (unfold q, p, aadd; cbn [snd]; f_equal; lia).
  assert (NP : forall x, x < snd p \/ snd p + n <= x -> ~ (snd p <= x < snd p + n)) by (intros; lia).
  assert (PP : snd p = snd c + UNIT * off) by reflexivity.
  split; [| split; [| split; [| split; [| split; [exact Q16| split; [| split]]]]]].
  - (* [comment removed for export] *) rewrite <- PP. apply stf2_known_old; [apply NP; lia| | exact K4].
    unfold SL, ss_list. fold e. change (snd e - snd p - n) with res.
    destruct (negb (res =? 0)); destruct (5 <=? res); cbn [lastw app]; repeat rs_aeq; reflexivity.
  - (* [comment removed for export] *)
    replace (i + 32 * Z.min res 5) with (Z.land (Z.land i 31 + Z.shiftl (if 5 <=? res then 5 else res) 5) 255).
    2:{ replace (Z.land i 31) with i by (change 31 with (Z.ones 5); rewrite Z.land_ones by lia; rewrite Z.mod_small; lia). rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
        destruct (Z.leb_spec 5 res).
        - rewrite Z.min_r by lia. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. rewrite Z.mod_small; lia.
        - rewrite Z.min_l by lia. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. rewrite Z.mod_small; lia. }
    rewrite <- PP. apply stf2_known_w; [apply NP; lia|].
    unfold SL, ss_list. fold e. change (snd e - snd p - n) with res.
    destruct (negb (res =? 0)); destruct (5 <=? res); cbn [negb lastw app]; repeat rs_aeq; reflexivity.
  - (* [comment removed for export] *) rewrite <- PP. apply stf2_known_old; [apply NP; lia| | exact K2].
    unfold SL, ss_list. fold e. change (snd e - snd p - n) with res.
    destruct (negb (res =? 0)); destruct (Z.leb_spec 5 res); cbn [lastw app]; repeat rs_aeq; reflexivity.
  - (* [comment removed for export] *) rewrite <- PP. apply stf2_known_old; [apply NP; lia| | exact K1].
    unfold SL, ss_list. fold e. change (snd e - snd p - n) with res.
    destruct (negb (res =? 0)); destruct (Z.leb_spec 5 res); cbn [lastw app]; repeat rs_aeq; reflexivity.
  - (* [comment removed for export] *) intros R5. unfold byte_of. rewrite Z.mul_0_r, Z.shiftr_0_r, Z.mul_1_r.
    assert (RS : res < 2 ^ 32) by (rewrite RE; exact RES32).
    assert (E5 : (5 <=? res) = true) by (apply Z.leb_le; exact R5).
    assert (EZ : (res =? 0) = false) by (apply Z.eqb_neq; lia).
    split; [| split; [| split; [| split; [| split; [| exact RS]]]]].
    1-4: apply stf2_known_w; [apply NP; rewrite ?RE; unfold IB, UNIT in *; lia|];
         unfold SL, ss_list; fold e; change (snd e - snd p - n) with res; rewrite E5, EZ; cbn [negb lastw app]; repeat rs_aeq; try reflexivity.
    all: try (change (8 * 2) with 16; reflexivity). all: try (change (8 * 3) with 24; reflexivity).
    apply (stf2_known_w _ 0); [apply NP; rewrite ?RE; unfold IB, UNIT in *; lia|].
    unfold SL, ss_list; fold e; change (snd e - snd p - n) with res; rewrite E5, EZ; cbn [negb lastw app]; try (exfalso; lia); repeat rs_aeq; reflexivity.
  - (* [comment removed for export] *) intros RP.
    replace (snd c + stride - IB - res) with (snd p + n) by (rewrite RE, PP; lia).
    apply (stf2_known_w _ 0); [apply NP; lia|].
    assert (EZ : (res =? 0) = false) by (apply Z.eqb_neq; lia).
    unfold SL, ss_list; fold e; change (snd e - snd p - n) with res; rewrite EZ. destruct (Z.leb_spec 5 res); cbn [negb lastw app];
      try (destruct (Z.eq_dec res 5)); try (exfalso; lia); repeat rs_aeq; reflexivity.
  - (* [comment removed for export] *) intros a Ha. apply stf2_unknown. rewrite PP. exact Ha.
Qed.

Theorem resize_INVL : INVL X' stf2 L (((c, off), n) :: BL) LS /\ ctrl_eq st stf2 /\ s_tick stf2 = s_tick st.
Proof.
  destruct stf2_ctrl as [CE TK]. pose proof rs_stride as [S16 _].
  assert (REG' : exists r, s_regions st !! fst bm = Some r /\ r_kind r = RKGroup) by (destruct Hm as [ai Hb]; exact (ig_region _ _ _ IG _ _ Hb)).
  split; [| split; [exact CE| exact TK]].
  apply (INVL_add_block X st stf2 L BL LS c off n INV HP CE TK).
  - intros m' i' Hs r Hr. rewrite rs_slots in Hs. inversion Hs. subst m' i'.
    assert (NQ : ~ (fst r = fst bm /\ snd p <= snd r < snd p + n)).
    { intros [F R]. apply Hr. unfold inT, c. cbn [fst snd]. split; [exact F|]. unfold p in R. unfold c, aadd in R. cbn [fst snd] in R. rewrite sstart_succ. fold stride. unfold IB, UNIT in *. lia. }
    rewrite (stf2_read_out r NQ). unfold stw2. apply wrs_read_other.
    intros Hin. destruct (SL_addrs r Hin) as (F & R). apply Hr. unfold inT, c. cbn [fst snd]. split; [exact F|].
    rewrite sstart_succ. fold stride. unfold p in R. unfold c, aadd in R. cbn [fst snd] in R. unfold IB, UNIT in *. lia.
  - change (DOMS st stf2). unfold stf2. destruct (Z.eq_dec n 0) as [N0|NZ].
    + rewrite havoc_le0 by lia. unfold stw2. apply wrs_DOMS; [exact (DOMS_of _ _ _ _ _ INV)|]. intros r Hin. destruct (SL_addrs r Hin) as (F & _). rewrite F. exact REG'.
    + apply DOMS_havoc; [lia| | exact REG']. unfold stw2. apply wrs_DOMS; [exact (DOMS_of _ _ _ _ _ INV)|]. intros r Hin. destruct (SL_addrs r Hin) as (F & _). rewrite F. exact REG'.
  - change (TKS stf2 (s_tick st)). unfold stf2. destruct (Z.eq_dec n 0) as [N0|NZ].
    + rewrite havoc_le0 by lia. apply stw2_TKS.
    + rewrite <- stw2_tick. apply TKS_havoc; [apply rs_p16| lia| rewrite stw2_tick; apply stw2_TKS].
  - intros m' i' Hs. rewrite rs_slots in Hs. inversion Hs. subst m' i'. split; [exact Hoff|]. split; [exact Hn|]. split; [exact FIT|].
    apply rs_blk_ok.
Qed.
End RESIZE.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section REMAP.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (g bm : aptr) (r needed : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hg : hosts st bm g.
Hypothesis SC63 : m_sizeclass (MR st g) = 63.
Let rid := fst bm.
Let c : aptr := (rid, sstart (MR st g) 0).
Hypothesis HP : x_pend X = Some c.
Hypothesis HO : x_orph X = None.
Let old := r_base (default (mkRegion RKGroup 0 0) (s_regions st !! rid)).
Let old_len := m_maplen (MR st g) * 4096.
(* [comment removed for export] *)
Hypothesis OK : mremap_answer_ok (live_ranges st) old old_len needed r = true.
Hypothesis NERR : is_err r = false.
Hypothesis HN : 0 < needed < PTRDIFF_MAX.
Hypothesis HNA : needed mod PGSZ = 0.
Hypothesis HNE : needed <> old_len.
(* [comment removed for export] *)
Hypothesis T0 : TF0 st.
Let L' := KInv.set_groups ((r, needed) :: g_remove old (ld_groups L)) L.
Let st' := wr8 (rid, needed - IB) 0 (remap_region rid g r needed st).

(* [comment removed for export] *)
Lemma remap_INVL :
  INVL X st' L' BL LS
  /\ hosts st' bm g /\ MR st' g = m_set_maplen (needed / 4096) (MR st g)
  /\ (forall o v, 0 <= o < needed - IB -> known st (rid, o) v -> known st' (rid, o) v)
  /\ s_secret st' = s_secret st
  /\ (forall rid' x, rid' <> rid -> s_regions st' !! rid' = Some x <-> s_regions st !! rid' = Some x)
  /\ s_regions st' !! rid = Some (mkRegion RKGroup r needed)
  /\ TW st' (fun q => q = (rid, needed - IB)).
Proof. exact (remap_INVL_full X st L BL LS g bm r needed INV Hg SC63 HP HO OK NERR HN HNA HNE T0). Qed.
End REMAP.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition RPOST (BL : list blk) (c : cptr) (n : Z) : mled -> mstate * optr -> Prop :=
  fun L' res =>
    match snd res with
    | None => exists LS', INVL x0 (fst res) L' BL LS'
    | Some p' => exists c' off' LS', p' = aadd c' (UNIT * off') /\ 0 <= off' <= 255
                 /\ INVL x0 (fst res) L' (((c', off'), n) :: bl_remove c BL) LS'
    end.

Lemma bl_remove_cons_ne (k : blk) c BL : bslot k <> c -> bl_remove c (k :: BL) = k :: bl_remove c BL.
Proof. intros H. cbn. rewrite (aptr_eqb_neq _ _ H). reflexivity. Qed.

(* [comment removed for export] *)
Lemma realloc_move_ft st L BL LS c off n0 n :
  INVL x0 st L BL LS -> In ((c, off), n0) BL -> 0 <= n ->
  ftreeX L (realloc_move st (aadd c (UNIT * off)) n) (RPOST BL c n).
Proof.
  intros INV Hk Hn. unfold realloc_move.
  eapply ftreeX_bind.
  { apply (proj1 (ftreeX_xlift _ _ _)). exact (malloc_INVL st L BL LS n INV Hn). }
  intros L1 [st1 r1] (LIVE1 & GP1 & RES). cbn [fst snd] in *.
  destruct r1 as [q|].
  - destruct RES as (c' & off' & LS1 & -> & Ho' & INV1 & NI).
    eapply ftreeX_bind.
    { apply (proj1 (ftreeX_xlift _ _ _)).
      apply (free_INVL_closed st1 L1 (((c', off'), n) :: BL) LS1 c off n0 INV1). right. exact Hk. }
    intros L2 st2 (LS2 & INV2). cbn [ftreeX RPOST fst snd].
    exists c', off', LS2. split; [reflexivity|]. split; [exact Ho'|].
      rewrite bl_remove_cons_ne in INV2; [exact INV2|]. cbn [bslot fst]. intros E. apply NI. rewrite E.
      change c with (bslot ((c, off), n0)). apply in_map. exact Hk.
  - destruct RES as (LS1 & INV1). cbn [ftreeX RPOST fst snd]. exists LS1. exact INV1.
Qed.

End RC__1.
