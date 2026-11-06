(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1ra X1qu X1og X1q8 X1po X1pv X1pf X1pm X1px X1pj X1q4
X1pz X1q0 X1q3 X1qf X1qg X1qh X1ph X1q6 X1qd X1qe X1qn X1qj.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section RESIZE.
Variables (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (c : cptr) (off n n' : Z) (m bm : aptr) (i : Z).
Hypothesis INV : INVL x0 st L BL LS.
Hypothesis Hk : In ((c, off), n) BL.
Hypothesis Hs : s_slots st !! c = Some (m, i).
Hypothesis Hm : hosts st bm m.
Hypothesis Hn' : 0 <= n'.
Let stride := get_stride (MR st m).
Hypothesis Hfit : UNIT * off + n' <= stride - IB.
Hypothesis Hres : stride - IB - UNIT * off - n' < 2 ^ 32.

Let IM := proj1 (proj2 (proj2 INV)).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))).
Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).
Let ISH := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

#[using="L BL LS INV Hs Hm IM IS"] Lemma rs_c : c = (fst bm, sstart (MR st m) i).
Proof. destruct (is_valid _ _ _ IS _ _ _ Hs) as (_ & _ & E). rewrite (slot_start'_eq _ _ _ IM _ _ _ Hm) in E. exact E. Qed.
#[using="L BL LS c INV Hs IS"] Lemma rs_i : 0 <= i <= m_last_idx (MR st m).
Proof. destruct (is_valid _ _ _ IS _ _ _ Hs) as (_ & Hi & _). exact Hi. Qed.
#[using="L BL LS INV Hm IM"] Lemma rs_gbase : gbase (MR st m) = bm. Proof. exact (hosts_gbase _ _ _ IM _ _ Hm). Qed.
#[using="L BL LS bm INV Hm IG"] Lemma rs_stride : 16 <= stride /\ stride mod 16 = 0.
Proof. pose proof (stride_ge _ _ _ IG _ _ Hm) as [A B]. unfold UNIT in *. split; assumption. Qed.
#[using="st L BL LS c n INV Hk IS"] Lemma rs_off : 0 <= off <= 255.
Proof. destruct (is_blocks _ _ _ IS _ Hk) as (m' & i' & Hs' & Ho & _). exact Ho. Qed.
#[using="st L BL LS m bm i INV Hs Hm stride IM IS"] Lemma rs_c16 : snd c mod 16 = 0.
Proof.
pose proof (sstart_res x0 st L BL LS INV bm m i Hm) as R. rewrite rs_c. cbn [snd]. unfold IB in R.
pose proof (Z.div_mod (sstart (MR st m) i - 4) 16 ltac:(lia)). pose proof (Z.div_mod (sstart (MR st m) i) 16 ltac:(lia)).
pose proof (Z.mod_pos_bound (sstart (MR st m) i) 16 ltac:(lia)). lia.
Qed.
#[using="L BL LS off n INV Hk"] Lemma rs_NH : s_groups st !! c = None.
Proof. destruct (block_facts x0 st L BL LS INV c off n Hk) as (m0 & bm0 & i0 & ai0 & a0 & ar0 & ka0 & BF). exact (bf_notH _ _ _ _ _ _ _ _ _ _ _ BF). Qed.

Definition st0 : mstate := set_tick (N.succ (s_tick st)) st.
Definition pp : aptr := aadd c (UNIT * off).
Definition ee : aptr := aadd c (stride - IB).
Definition res : Z := snd ee - snd pp - n'.
Definition RL : list (aptr * Z) :=
(if negb (res =? 0) then [(aadd ee (- res), 0)] else [])
++ (if 5 <=? res then [(aadd ee (-5), 0); (aadd ee (-4), res); (aadd (aadd ee (-4)) 1, Z.shiftr res 8); (aadd (aadd ee (-4)) 2, Z.shiftr res 16); (aadd (aadd ee (-4)) 3, Z.shiftr res 24)] else [])
++ [(aadd pp (-3), Z.land i 31 + Z.shiftl (if 5 <=? res then 5 else res) 5)].
Definition stw : mstate := wrs RL st0.
Definition stf : mstate := havoc pp n' stw.

#[using="Type"] Lemma res_eq : res = stride - IB - UNIT * off - n'.
Proof. unfold res, ee, pp, aadd. cbn [snd]. lia. Qed.

#[using="Type"] Lemma resize_body_eq :
wr8 (aadd pp (-3)) (Z.land i 31 + Z.shiftl (if 5 <=? res then 5 else res) 5)
(if 5 <=? res then wr32 (aadd ee (-4)) res (wr8 (aadd ee (-5)) 0 (if negb (res =? 0) then wr8 (aadd ee (- res)) 0 st0 else st0))
else (if negb (res =? 0) then wr8 (aadd ee (- res)) 0 st0 else st0)) = stw.
Proof.
unfold stw, RL.
destruct (Z.eqb_spec res 0) as [R0|R0]; destruct (Z.leb_spec 5 res) as [R5|R5]; cbn [negb app wrs]; try reflexivity; try (exfalso; lia).
all: unfold wr32; cbn [wrs]; reflexivity.
Qed.

#[using="m INV stride"] Lemma INV0 : INVL x0 st0 L BL LS.
Proof. apply INVL_set_tick; [cbn; lia| exact INV]. Qed.
#[using="L BL LS m INV stride"] Lemma TF00 : TF0 st0.
Proof. apply TF0_tick_new; [exact (TKS_of _ _ _ _ _ INV)| cbn; lia]. Qed.
#[using="Type"] Lemma st0_ctrl : ctrl_eq st st0 /\ s_tick st0 = N.succ (s_tick st).
Proof. split; [constructor; reflexivity| reflexivity]. Qed.
#[using="Type"] Lemma MR0 x : MR st0 x = MR st x. Proof. reflexivity. Qed.

#[using="L BL LS INV"] Lemma stw_TKS : TKS stw (s_tick st0).
Proof. apply wrs_TKS; [lia| exact (TKS_of _ _ _ _ _ INV0)]. Qed.
#[using="Type"] Lemma stw_tick : s_tick stw = s_tick st0. Proof. exact (proj2 (wrs_ctrl RL st0)). Qed.
#[using="Type"] Lemma stw_ctrl : ctrl_eq st0 stw. Proof. exact (proj1 (wrs_ctrl RL st0)). Qed.
#[using="st L BL LS m bm i INV Hs Hm stride IM IS"] Lemma pp16 : snd pp mod 16 = 0.
Proof. unfold pp, aadd. cbn [snd]. unfold UNIT. rewrite Z.add_mod, rs_c16, Z.mul_comm, Z_mod_mult by lia. reflexivity. Qed.
#[using="L BL LS INV"] Lemma stw_hav u hl : r_hav (get_shadow stw (fst pp)) !! u = Some hl -> hl_ticks hl (s_tick stw).
Proof. intros Hu ch Hch. rewrite stw_tick. pose proof stw_TKS as TK. rewrite <- stw_tick in TK. rewrite <- stw_tick. exact (proj1 (sh_ticks_of _ _ TK) u hl ch Hu Hch). Qed.

#[using="Type"] Lemma stf_ctrl : ctrl_eq st stf /\ s_tick stf = N.succ (s_tick st).
Proof.
destruct (havoc_ctrl pp n' stw) as [C T]. destruct st0_ctrl as [C0 T0]. split.
- exact (ctrl_eq_trans _ _ _ C0 (ctrl_eq_trans _ _ _ stw_ctrl C)).
- rewrite T, stw_tick. exact T0.
Qed.

#[using="L BL LS INV Hs Hm Hn' IM IS"] Lemma stf_read_out r : ~ (fst r = fst bm /\ snd pp <= snd r < snd pp + n') ->
cell_read (get_shadow stf (fst r)) (snd r) = cell_read (get_shadow stw (fst r)) (snd r).
Proof.
intros Hr. unfold stf. destruct (Z.eq_dec n' 0) as [N0|NZ]; [rewrite havoc_le0 by lia; reflexivity|].
apply (cell_read_havoc_out pp n' stw pp16 ltac:(lia) stw_hav).
intros [F R]. apply Hr. split; [| exact R]. rewrite F. unfold pp, aadd. cbn [fst]. rewrite rs_c. reflexivity.
Qed.

#[using="L BL LS n INV Hk Hs Hm Hn' Hfit IM IG IS"] Lemma RL_addrs a : In a (map fst RL) ->
fst a = fst bm /\ snd c - 3 <= snd a < snd c + stride - 4 /\ ~ (snd pp <= snd a < snd pp + n').
Proof.
intros Hin. pose proof rs_stride as [S16 _]. pose proof rs_off as Ho.
assert (R : 0 <= res) by (rewrite res_eq; unfold IB, UNIT in *; lia).
unfold RL in Hin.
destruct (Z.eqb_spec res 0) as [R0|R0]; destruct (Z.leb_spec 5 res) as [R5|R5];
cbn [negb app map fst In] in Hin; rewrite ?res_eq in *; unfold ee, pp, aadd in *; cbn [fst snd] in *; unfold IB, UNIT in *;
repeat match type of Hin with _ \/ _ => destruct Hin as [<-|Hin] | False => destruct Hin end; rewrite rs_c; cbn [fst snd]; (split; [reflexivity| rewrite <- ?rs_c; lia]).
Qed.

#[using="L BL LS INV Hs Hm Hn' IM IS"] Lemma stf_known_w x w : ~ (snd pp <= x < snd pp + n') ->
lastw RL (fst bm, x) None = Some w -> known stf (fst bm, x) (Z.land w 255).
Proof.
intros Hx HL. unfold known, SHd. cbn [fst snd].
rewrite (stf_read_out (fst bm, x)) by (cbn [fst snd]; tauto).
unfold stw. rewrite (wrs_lastw RL st0 (fst bm, x) (TKS_of _ _ _ _ _ INV0)). rewrite HL. reflexivity.
Qed.

#[using="L BL LS INV Hs Hm Hn' IM IS"] Lemma stf_known_old x v : ~ (snd pp <= x < snd pp + n') ->
lastw RL (fst bm, x) None = None -> known st (fst bm, x) v -> known stf (fst bm, x) v.
Proof.
intros Hx HL K. unfold known, SHd in *. cbn [fst snd] in *.
rewrite (stf_read_out (fst bm, x)) by (cbn [fst snd]; tauto).
unfold stw. rewrite (wrs_lastw RL st0 (fst bm, x) (TKS_of _ _ _ _ _ INV0)). rewrite HL. exact K.
Qed.

#[using="L BL LS n INV Hk Hs Hm Hn' Hfit IM IG IS"] Lemma RL_not_in a : snd pp <= a < snd pp + n' -> ~ In (fst bm, a) (map fst RL).
Proof. intros Ha Hin. destruct (RL_addrs _ Hin) as (_ & _ & NR). apply NR. exact Ha. Qed.

#[using="L BL LS n INV Hk Hs Hm Hn' Hfit IM IG IS"] Lemma stf_unknown a : snd pp <= a < snd pp + n' -> unknown stf (fst bm, a).
Proof.
intros Ha. unfold unknown, SHd, stf. cbn [fst snd].
assert (Fp : fst bm = fst pp) by (unfold pp, aadd; cbn [fst]; rewrite rs_c; reflexivity).
destruct (cell_read_havoc_in pp n' stw pp16 ltac:(lia) stw_hav (fst bm, a) Fp Ha) as [h Hh]; [| exists h; exact Hh].
cbn [snd]. intros v tk Hc. unfold stw in Hc. rewrite <- Fp in Hc. rewrite wrs_cells_other in Hc by (apply RL_not_in; exact Ha).
rewrite stw_tick. change (get_shadow st0 (fst bm)) with (get_shadow st (fst bm)) in Hc.
destruct (get_shadow_cells_some st (fst bm) a (v, tk) Hc) as (sh & Hsh & Hc').
pose proof (TF00 (fst bm) sh a v tk Hsh Hc') as LT. exact LT.
Qed.

Ltac aeq :=
match goal with
| |- context [aptr_eqb ?a ?b] =>
first [ rewrite (aptr_eqb_neq a b) by (unfold pp, ee, aadd; rewrite ?rs_c; cbn [fst snd]; intros E; apply (f_equal snd) in E; cbn [snd] in E; unfold IB, UNIT in *; lia)
| rewrite (proj2 (aptr_eqb_eq a b)) by (unfold pp, ee, aadd; rewrite ?rs_c; cbn [fst snd]; unfold IB, UNIT in *; f_equal; lia) ]
end.

#[using="L BL LS n bm INV Hk Hs Hm Hn' Hfit Hres IM IG IS ISH"] Lemma blk_ok_resize : blk_shadow_ok stf ((c, off), n') m i.
Proof.
pose proof rs_stride as [S16 SM]. pose proof rs_off as Ho. pose proof rs_i as Hi.
destruct stf_ctrl as [CE TK].
assert (MRE : MR stf m = MR st m) by (apply MR_ext; exact (ce_metas _ _ CE)).
pose proof res_eq as RE.
destruct Hm as [ai Hb] eqn:EHm. pose proof (g_li _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Hb)) as LI.

pose proof (ish_blk _ _ ISH ((c, off), n) m i Hk Hs) as OLD. cbn [bslot boff bsize fst snd] in OLD. rewrite rs_gbase in OLD.
destruct OLD as (K4 & K3 & K2 & K1 & Q & _ & _ & _).
unfold blk_shadow_ok. cbn [bslot boff bsize fst snd]. rewrite MRE, rs_gbase. fold stride.
replace (snd c + stride - IB - (snd c + UNIT * off) - n') with res by (rewrite RE; lia).
set (q := (snd c + UNIT * off - snd bm - UNIT) / UNIT) in *.
assert (R0 : 0 <= res) by (rewrite RE; unfold IB, UNIT in *; lia).
assert (NP : forall x, x < snd pp \/ snd pp + n' <= x -> ~ (snd pp <= x < snd pp + n')) by (intros; lia).
assert (PP : snd pp = snd c + UNIT * off) by reflexivity.
assert (Fc : fst c = fst bm) by (rewrite rs_c; reflexivity).
rewrite Fc.
split; [| split; [| split; [| split; [| split; [exact Q| split; [| split]]]]]].
-   apply stf_known_old; [apply NP; lia| | rewrite <- Fc; exact K4].
unfold RL. destruct (negb (res =? 0)); destruct (5 <=? res); cbn [lastw app]; repeat aeq; reflexivity.
-
replace (i + 32 * Z.min res 5) with (Z.land (Z.land i 31 + Z.shiftl (if 5 <=? res then 5 else res) 5) 255).
2:{ replace (Z.land i 31) with i by (change 31 with (Z.ones 5); rewrite Z.land_ones by lia; rewrite Z.mod_small; lia). rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
destruct (Z.leb_spec 5 res).
- rewrite Z.min_r by lia. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. rewrite Z.mod_small; lia.
- rewrite Z.min_l by lia. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. rewrite Z.mod_small; lia. }
apply stf_known_w; [apply NP; lia|].
unfold RL. destruct (negb (res =? 0)); destruct (5 <=? res); cbn [negb lastw app]; repeat aeq; reflexivity.
-   apply stf_known_old; [apply NP; lia| | rewrite <- Fc; exact K2].
unfold RL. destruct (negb (res =? 0)); destruct (Z.leb_spec 5 res); cbn [lastw app]; try (exfalso; lia); repeat aeq; reflexivity.
-   apply stf_known_old; [apply NP; lia| | rewrite <- Fc; exact K1].
unfold RL. destruct (negb (res =? 0)); destruct (Z.leb_spec 5 res); cbn [lastw app]; try (exfalso; lia); repeat aeq; reflexivity.
-   intros R5. unfold byte_of. rewrite Z.mul_0_r, Z.shiftr_0_r, Z.mul_1_r.
assert (RS : res < 2 ^ 32) by (rewrite RE; exact Hres).
assert (E5 : (5 <=? res) = true) by (apply Z.leb_le; exact R5).
assert (EZ : (res =? 0) = false) by (apply Z.eqb_neq; lia).
split; [| split; [| split; [| split; [| split; [| exact RS]]]]].
1-4: apply stf_known_w; [apply NP; rewrite ?RE; unfold IB, UNIT in *; lia|];
unfold RL; rewrite E5, EZ; cbn [negb lastw app]; repeat aeq; try reflexivity.
all: try (change (8 * 2) with 16; reflexivity). all: try (change (8 * 3) with 24; reflexivity).
apply (stf_known_w _ 0); [apply NP; rewrite ?RE; unfold IB, UNIT in *; lia|].
unfold RL; rewrite E5, EZ; cbn [negb lastw app]; repeat aeq; reflexivity.
-   intros RP.
replace (snd c + stride - IB - res) with (snd pp + n') by (rewrite RE, PP; lia).
apply (stf_known_w _ 0); [apply NP; lia|].
assert (EZ : (res =? 0) = false) by (apply Z.eqb_neq; lia).
unfold RL; rewrite EZ. destruct (Z.leb_spec 5 res); cbn [negb lastw app];
try (destruct (Z.eq_dec res 5)); try (exfalso; lia); repeat aeq; reflexivity.
-   intros a Ha. apply stf_unknown. rewrite PP. exact Ha.
Qed.

#[using="L BL LS n bm INV Hk Hs Hm Hn' Hfit IM IG IS"] Lemma stf_read_T q : ~ inT (fst c) (sstart (MR st m) i - 3) (sstart (MR st m) (i + 1) - 4) q ->
cell_read (get_shadow stf (fst q)) (snd q) = cell_read (get_shadow st0 (fst q)) (snd q).
Proof.
intros Hq. pose proof rs_stride as [S16 _]. pose proof rs_off as Ho.
assert (Fc : fst c = fst bm) by (rewrite rs_c; reflexivity).
assert (NQ : ~ (fst q = fst bm /\ snd pp <= snd q < snd pp + n')).
{ intros [F R]. apply Hq. unfold inT. split; [rewrite Fc; exact F|]. unfold pp, aadd in R. rewrite rs_c in R. cbn [snd] in R.
rewrite sstart_succ. fold stride. unfold IB, UNIT in *. lia. }
rewrite (stf_read_out q NQ). unfold stw. apply wrs_read_other.
intros Hin. destruct (RL_addrs q Hin) as (F & R & _). apply Hq. unfold inT. split; [rewrite Fc; exact F|].
rewrite sstart_succ. fold stride. rewrite rs_c in R. cbn [snd] in R. unfold IB in *. lia.
Qed.

#[using="L BL LS bm INV Hm Hn' Hfit IG"] Lemma RL_addrs_pos a : 0 < off -> In a (map fst RL) -> snd c <= snd a.
Proof.
intros Ho Hin. pose proof rs_stride as [S16 _].
assert (R : 0 <= res) by (rewrite res_eq; unfold IB, UNIT in *; lia).
unfold RL in Hin.
destruct (Z.eqb_spec res 0) as [R0|R0]; destruct (Z.leb_spec 5 res) as [R5|R5];
cbn [negb app map fst In] in Hin; rewrite ?res_eq in *; unfold ee, pp, aadd in *; cbn [fst snd] in *; unfold IB, UNIT in *;
repeat match type of Hin with _ \/ _ => destruct Hin as [<-|Hin] | False => destruct Hin end; cbn [fst snd]; lia.
Qed.
#[using="L BL LS bm INV Hs Hm Hn' Hfit IM IG IS"] Lemma stf_read_chdr k : 0 < off -> 1 <= k <= 3 ->
cell_read (get_shadow stf (fst c)) (snd c - k) = cell_read (get_shadow st (fst c)) (snd c - k).
Proof.
intros Ho Hk3.
rewrite (stf_read_out (fst c, snd c - k)) by (unfold pp, aadd; cbn [fst snd]; unfold UNIT; lia).
unfold stw. rewrite (wrs_read_other RL st0 (fst c, snd c - k)); [reflexivity|].
intros Hin. pose proof (RL_addrs_pos _ Ho Hin) as X. cbn [snd] in X. lia.
Qed.

#[using="L BL LS n bm INV Hk Hs Hm Hn' Hfit IM IG IS"] Lemma stf_DOMS : DOMS st stf.
Proof.
assert (REG' : exists r, s_regions st !! fst bm = Some r /\ r_kind r = RKGroup).
{ destruct Hm as [ai Hb]. exact (ig_region _ _ _ IG _ _ Hb). }
assert (D0 : DOMS st st0) by (intros rid sh Hsh; exact (DOMS_of _ _ _ _ _ INV rid sh Hsh)).
unfold stf. destruct (Z.eq_dec n' 0) as [N0|NZ].
- rewrite havoc_le0 by lia. apply wrs_DOMS; [exact D0|]. intros q Hin. destruct (RL_addrs q Hin) as (F & _). rewrite F. exact REG'.
- apply DOMS_havoc; [lia| |].
+ apply wrs_DOMS; [exact D0|]. intros q Hin. destruct (RL_addrs q Hin) as (F & _). rewrite F. exact REG'.
+ unfold pp, aadd. cbn [fst]. rewrite rs_c. cbn [fst]. exact REG'.
Qed.

#[using="L BL LS bm INV Hs Hm Hn' IM IS"] Lemma stf_TKS : TKS stf (s_tick st0).
Proof.
unfold stf. destruct (Z.eq_dec n' 0) as [N0|NZ].
- rewrite havoc_le0 by lia. apply stw_TKS.
- rewrite <- stw_tick. apply TKS_havoc; [apply pp16| lia| rewrite stw_tick; apply stw_TKS].
Qed.

#[using="n bm INV Hk Hs Hm Hn' Hfit Hres IM IG IS ISH"] Theorem resize_INVL : INVL x0 stf L (((c, off), n') :: bl_remove c BL) LS.
Proof.
destruct stf_ctrl as [CE TK]. destruct st0_ctrl as [CE0 TK0].
assert (CE' : ctrl_eq st0 stf).
{ destruct (havoc_ctrl pp n' stw) as [C T]. exact (ctrl_eq_trans _ _ _ stw_ctrl C). }
assert (TK' : s_tick stf = s_tick st0) by (rewrite TK, TK0; reflexivity).

pose proof (INVL_remove_block x0 st0 stf L BL LS ((c, off), n) INV0 Hk eq_refl CE' TK'
ltac:(intros m' i' Hs'; cbn [bslot fst snd] in Hs' |- *; change (s_slots st0) with (s_slots st) in Hs'; rewrite Hs in Hs'; inversion Hs'; subst m' i'; intros q Hq; apply stf_read_T; exact Hq)
ltac:(intros rid sh Hsh; exact (stf_DOMS rid sh Hsh))
ltac:(intros rid sh Hsh; exact (stf_TKS rid sh Hsh))) as INV1.
cbn [bslot fst snd] in INV1.

pose proof (INVL_add_block (xpend x0 (Some c)) stf stf L (bl_remove c BL) LS c off n' INV1 eq_refl (ctrl_eq_refl stf) eq_refl
ltac:(intros; reflexivity)
ltac:(intros rid sh Hsh; destruct (stf_DOMS rid sh Hsh) as (r & Hr & Kr); exists r; split; [rewrite (ce_regions _ _ CE); exact Hr| exact Kr])
ltac:(intros rid sh Hsh; rewrite TK'; exact (stf_TKS rid sh Hsh))) as INV2.
cbn [xpend x_idle x_zomb x_orph x_fresh x0] in INV2. apply INV2.
intros m' i' Hs'. rewrite (ce_slots _ _ CE) in Hs'. rewrite Hs in Hs'. inversion Hs'; subst m' i'.
split; [exact rs_off|]. split; [exact Hn'|]. split; [| exact blk_ok_resize].
rewrite (MR_ext st stf (ce_metas _ _ CE) m). exact Hfit.
Qed.

#[using="Type"] Lemma resize_GP : GP st stf.
Proof. destruct stf_ctrl as [CE _]. apply GP_eq; [exact (ce_regions _ _ CE)| exact (ce_secret _ _ CE)]. Qed.

#[using="Type"] Lemma resize_ctrl : ctrl_eq st stf /\ s_tick stf = N.succ (s_tick st).
Proof. exact stf_ctrl. Qed.
End RESIZE.
