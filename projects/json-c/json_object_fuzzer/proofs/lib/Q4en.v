(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Bool Lia.
From stdpp Require gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi QUZl Q7S0 Qfya QPiB Qatc QSfG QdBa QpFQ Ql2m QYTG QaiD QLaA Q1am QoCS QQCz QQg5 QlOh QhnL QcV4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import stdpp.gmap.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Q7S0.Mq1 Qfya QPiB.Mq0 Qatc QSfG.Mq2 Q7S0 QdBa.Mq0 QdBa.Mq1 QpFQ QPiB Ql2m.Mq2 QYTG.Mq1 QdBa.Mq2 QaiD QLaA.Mq0 Q1am.Mq1 QSfG QoCS.Mq0 QQCz QQg5.Mq1 QlOh QhnL QcV4.Mq0.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section ADDBACK.
Variables (st : mstate) (L : mled) (BL1 : list blk) (LS : lhead -> list aptr).
Variables (c : cptr) (off n : Z) (m bm : aptr) (i b3 : Z).
Let X1 := xpend x0 (Some c).
Hypothesis INV1 : INVL X1 st L BL1 LS.
Hypothesis Hm : hosts st bm m.
Hypothesis Hidx : 0 <= i <= m_last_idx (MR st m).
Hypothesis Hc : c = (fst bm, sstart (MR st m) i).
Hypothesis TF : TF2 st.
Hypothesis Hn : 0 <= n.
Hypothesis OFF : 0 <= off <= 255.
Let stride := get_stride (MR st m).
Hypothesis Hfit : UNIT * off + n <= stride - IB.
Hypothesis Hres : stride - IB - UNIT * off - n < 2 ^ 32.
Hypothesis Hb3 : Z.land b3 31 = i.
Let qv : Z := (snd c + UNIT * off - snd bm - UNIT) / UNIT.
Hypothesis K4 : known st (fst bm, snd c + UNIT * off - 4) 0.
Hypothesis K2 : known st (fst bm, snd c + UNIT * off - 2) (byte_of qv 0).
Hypothesis K1 : known st (fst bm, snd c + UNIT * off - 1) (byte_of qv 1).
Hypothesis Q : 0 <= qv < 2 ^ 16.

Let IM := proj1 (proj2 (proj2 INV1)).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV1)))).
Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV1))))).
Let ISH := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV1))))).

Definition ip_p : aptr := aadd c (UNIT * off).
Definition ip_e : aptr := aadd c (stride - IB).
Definition ip_res : Z := stride - IB - UNIT * off - n.
Definition RL : list (aptr * Z) :=
(if negb (ip_res =? 0) then [(aadd ip_e (- ip_res), 0)] else [])
++ (if 5 <=? ip_res then [(aadd ip_e (-4), ip_res); (aadd (aadd ip_e (-4)) 1, Z.shiftr ip_res 8); (aadd (aadd ip_e (-4)) 2, Z.shiftr ip_res 16);
(aadd (aadd ip_e (-4)) 3, Z.shiftr ip_res 24); (aadd ip_e (-5), 0)] else [])
++ [(aadd ip_p (-3), Z.land b3 31 + Z.shiftl (if 5 <=? ip_res then 5 else ip_res) 5)].
Definition ip_stw : mstate := wrs RL st.
Definition ip_stf : mstate := havoc ip_p n ip_stw.

#[using="Hc"] Lemma ip_c : c = (fst bm, sstart (MR st m) i). Proof. exact Hc. Qed.
#[using="RC__ L BL1 LS c X1 INV1 Hm IM"] Lemma ip_gbase : gbase (MR st m) = bm. Proof. exact (hosts_gbase _ _ _ IM _ _ Hm). Qed.
#[using="RC__ L BL1 LS bm X1 INV1 Hm Hidx Hc IM IS"] Lemma ip_slots : s_slots st !! c = Some (m, i).
Proof. rewrite Hc, <- ip_gbase, <- slot_start'_sstart. exact (is_total _ _ _ IS _ _ _ Hm Hidx). Qed.
#[using="RC__ L BL1 LS m bm i X1 INV1 Hm Hidx Hc IM IS"] Lemma ip_NH : s_groups st !! c = None.
Proof.
destruct Hm as [ai Hb]. pose proof (is_part _ _ _ IS _ _ _ i Hb Hidx) as P. cbn zeta in P.
rewrite slot_start'_sstart, (hosts_gbase _ _ _ IM _ _ (ex_intro _ ai Hb)), <- Hc in P. unfold X1, xpend in P. cbn [x_pend] in P.
destruct (s_groups st !! c) eqn:E; [| reflexivity]. exfalso. destruct P as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & nDE). apply nDE. split; [rewrite E; discriminate| reflexivity].
Qed.
#[using="RC__ L BL1 LS c bm X1 INV1 Hm IG"] Lemma ip_stride : 16 <= stride /\ stride mod 16 = 0.
Proof. pose proof (stride_ge _ _ _ IG _ _ Hm) as [A B]. unfold UNIT in *. split; assumption. Qed.
#[using="RC__ st L BL1 LS off m bm i X1 INV1 Hm Hc stride qv"] Lemma ip_c16 : snd c mod 16 = 0.
Proof.
pose proof (sstart_res X1 st L BL1 LS INV1 bm m i Hm) as R. rewrite ip_c. cbn [snd]. unfold IB in R.
pose proof (Z.div_mod (sstart (MR st m) i - 4) 16 ltac:(lia)). pose proof (Z.div_mod (sstart (MR st m) i) 16 ltac:(lia)).
pose proof (Z.mod_pos_bound (sstart (MR st m) i) 16 ltac:(lia)). lia.
Qed.
#[using="RC__ st L BL1 LS m bm i X1 INV1 Hm Hc stride qv"] Lemma ip_p16 : snd ip_p mod 16 = 0.
Proof. unfold ip_p, aadd. cbn [snd]. unfold UNIT. rewrite Z.add_mod, ip_c16, Z.mul_comm, Z_mod_mult by lia. reflexivity. Qed.
#[using="OFF"] Lemma ip_off : 0 <= off <= 255. Proof. exact OFF. Qed.
#[using="c bm OFF Hfit qv"] Lemma ip_res_nonneg : 0 <= ip_res. Proof. unfold ip_res. pose proof ip_off. unfold UNIT, IB in *. lia. Qed.

#[using="bm qv"] Lemma set_size_RL : set_size ip_p ip_e n b3 st = ip_stw.
Proof.
unfold set_size, ip_stw, RL. replace (snd ip_e - snd ip_p - n) with ip_res by (unfold ip_e, ip_p, ip_res, aadd; cbn [snd]; lia).
destruct (ip_res =? 0); cbn beta iota delta [wr16 wr32 wrs app negb];
destruct (5 <=? ip_res); cbn beta iota delta [wrs app negb]; reflexivity.
Qed.

#[using="RC__ L BL1 LS bm X1 INV1 qv"] Lemma ip_stw_TKS : TKS ip_stw (s_tick st).
Proof. apply wrs_TKS; [lia| exact (TKS_of _ _ _ _ _ INV1)]. Qed.
#[using="Type"] Lemma ip_stw_tick : s_tick ip_stw = s_tick st. Proof. exact (proj2 (wrs_ctrl RL st)). Qed.
#[using="Type"] Lemma ip_stw_ctrl : ctrl_eq st ip_stw. Proof. exact (proj1 (wrs_ctrl RL st)). Qed.
#[using="RC__ L BL1 LS bm X1 INV1 qv"] Lemma ip_stw_hav u hl : r_hav (get_shadow ip_stw (fst ip_p)) !! u = Some hl -> hl_ticks hl (s_tick ip_stw).
Proof. intros Hu ch Hch. rewrite ip_stw_tick. pose proof ip_stw_TKS as TK. rewrite <- ip_stw_tick in TK. rewrite <- ip_stw_tick. exact (proj1 (sh_ticks_of _ _ TK) u hl ch Hu Hch). Qed.
#[using="Type"] Lemma ip_stf_ctrl : ctrl_eq st ip_stf /\ s_tick ip_stf = s_tick st.
Proof.
destruct (havoc_ctrl ip_p n ip_stw) as [C T]. split; [exact (ctrl_eq_trans _ _ _ ip_stw_ctrl C)| rewrite T; apply ip_stw_tick].
Qed.

#[using="RC__ L BL1 LS i X1 INV1 Hm Hc Hn qv"] Lemma ip_stf_read_out r : ~ (fst r = fst bm /\ snd ip_p <= snd r < snd ip_p + n) ->
cell_read (get_shadow ip_stf (fst r)) (snd r) = cell_read (get_shadow ip_stw (fst r)) (snd r).
Proof.
intros Hr. unfold ip_stf. destruct (Z.eq_dec n 0) as [N0|NZ]; [rewrite havoc_le0 by lia; reflexivity|].
apply (cell_read_havoc_out ip_p n ip_stw ip_p16 ltac:(lia) ip_stw_hav).
intros [F R]. apply Hr. split; [rewrite F; unfold ip_p; rewrite ip_c; reflexivity| exact R].
Qed.

#[using="RC__ L BL1 LS i X1 INV1 Hm Hc Hn OFF Hfit qv IG"] Lemma RL_addrs q : In q (map fst RL) ->
fst q = fst bm /\ snd c - 3 <= snd q < snd c + stride - 4 /\ ~ (snd ip_p <= snd q < snd ip_p + n).
Proof.
intros Hin. pose proof ip_stride as [S16 _]. pose proof ip_res_nonneg as R. pose proof ip_off as OFF'.
unfold RL in Hin.
destruct (Z.eqb_spec ip_res 0) as [R0|R0]; destruct (Z.leb_spec 5 ip_res) as [R5|R5];
cbn [negb app map fst In] in Hin; unfold ip_res, ip_e, ip_p, aadd in *; cbn [fst snd] in *; unfold IB, UNIT in *;
repeat match type of Hin with _ \/ _ => destruct Hin as [<-|Hin] | False => destruct Hin end; rewrite ip_c; cbn [fst snd]; (split; [reflexivity| rewrite <- ?ip_c; lia]).
Qed.

#[using="RC__ L BL1 LS i X1 INV1 Hm Hidx Hc Hn OFF qv Q"] Lemma ip_known_w x w : ~ (snd ip_p <= x < snd ip_p + n) ->
lastw RL (fst bm, x) None = Some w -> known ip_stf (fst bm, x) (Z.land w 255).
Proof.
intros Hx HL. unfold known, SHd. cbn [fst snd].
rewrite (ip_stf_read_out (fst bm, x)) by (cbn [fst snd]; tauto).
unfold ip_stw. rewrite (wrs_lastw RL st (fst bm, x) (TKS_of _ _ _ _ _ INV1)). rewrite HL. reflexivity.
Qed.

#[using="RC__ L BL1 LS i X1 INV1 Hm Hidx Hc Hn OFF qv Q"] Lemma ip_known_old x v : ~ (snd ip_p <= x < snd ip_p + n) ->
lastw RL (fst bm, x) None = None -> known st (fst bm, x) v -> known ip_stf (fst bm, x) v.
Proof.
intros Hx HL K. unfold known, SHd in *. cbn [fst snd] in *.
rewrite (ip_stf_read_out (fst bm, x)) by (cbn [fst snd]; tauto).
unfold ip_stw. rewrite (wrs_lastw RL st (fst bm, x) (TKS_of _ _ _ _ _ INV1)). rewrite HL. exact K.
Qed.

#[using="RC__ L BL1 LS i X1 INV1 Hm Hc Hn OFF Hfit qv IG"] Lemma RL_not_in x : snd ip_p <= x < snd ip_p + n -> ~ In (fst bm, x) (map fst RL).
Proof. intros Hx Hin. destruct (RL_addrs _ Hin) as (_ & _ & NR). apply NR. exact Hx. Qed.

#[using="RC__ L BL1 LS i X1 INV1 Hm Hidx Hc TF Hn OFF Hfit qv IM IG IS"] Lemma ip_unknown x : snd ip_p <= x < snd ip_p + n -> unknown ip_stf (fst bm, x).
Proof.
intros Hx. pose proof ip_off as OFF'. unfold unknown, SHd, ip_stf. cbn [fst snd].
assert (Efst : fst ip_p = fst bm) by (unfold ip_p; rewrite ip_c; reflexivity).
destruct (cell_read_havoc_in ip_p n ip_stw ip_p16 ltac:(lia) ip_stw_hav (fst bm, x) (eq_sym Efst) Hx) as [h Hh]; [| exists h; exact Hh].
cbn [snd]. intros v tk Hcl. unfold ip_stw in Hcl. rewrite Efst in Hcl. rewrite wrs_cells_other in Hcl by (apply RL_not_in; exact Hx).
rewrite ip_stw_tick.
apply (TF2_interior_old X1 st L BL1 LS INV1 m bm i Hm Hidx ltac:(rewrite <- ip_c; exact ip_NH) TF x v tk Hcl).
unfold ip_p, aadd in Hx. rewrite ip_c in Hx. cbn [fst snd] in Hx. rewrite sstart_succ. fold stride. unfold IB, UNIT in *. lia.
Qed.

Ltac ipaeq :=
match goal with
| |- context [aptr_eqb ?a ?b] =>
first [ rewrite (aptr_eqb_neq a b) by (unfold ip_p, ip_e, aadd; rewrite ?ip_c; cbn [fst snd]; intros E; apply (f_equal snd) in E; cbn [snd] in E; unfold IB, UNIT in *; lia)
| rewrite (proj2 (aptr_eqb_eq a b)) by (unfold ip_p, ip_e, aadd; rewrite ?ip_c; cbn [fst snd]; unfold IB, UNIT in *; f_equal; lia) ]
end.

#[using="RC__ L BL1 LS bm X1 INV1 Hm Hidx Hc TF Hn OFF Hfit Hres Hb3 qv K4 K2 K1 Q IM IG IS"] Lemma ip_blk_ok : blk_shadow_ok ip_stf ((c, off), n) m i.
Proof.
pose proof ip_stride as [S16 SM]. pose proof ip_off as OFF'. pose proof ip_res_nonneg as R0. pose proof Hidx as IDX.
assert (LI : m_last_idx (MR st m) <= 31) by (destruct Hm as [ai0 Hb0]; pose proof (g_li _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Hb0)); lia).
destruct ip_stf_ctrl as [CE TK].
assert (RE : ip_res = stride - IB - UNIT * off - n) by reflexivity.
assert (MRE : MR ip_stf m = MR st m) by (apply MR_ext; exact (ce_metas _ _ CE)).
unfold blk_shadow_ok. cbn [bslot boff bsize fst snd]. rewrite MRE, ip_gbase. fold stride.
replace (snd c + stride - IB - (snd c + UNIT * off) - n) with ip_res by (unfold ip_res; lia).
assert (NP : forall x, x < snd ip_p \/ snd ip_p + n <= x -> ~ (snd ip_p <= x < snd ip_p + n)) by (intros; lia).
assert (PP : snd ip_p = snd c + UNIT * off) by reflexivity.
assert (Efc : fst c = fst bm) by (rewrite ip_c; reflexivity).
rewrite Efc. change ((snd c + UNIT * off - snd bm - UNIT) / UNIT) with qv.
split; [| split; [| split; [| split; [| split; [exact Q| split; [| split]]]]]].
-  apply ip_known_old; [apply NP; lia| | exact K4].
unfold RL. destruct (negb (ip_res =? 0)); destruct (5 <=? ip_res); cbn [lastw app]; repeat ipaeq; reflexivity.
-
replace (i + 32 * Z.min ip_res 5) with (Z.land (Z.land b3 31 + Z.shiftl (if 5 <=? ip_res then 5 else ip_res) 5) 255).
2:{ rewrite Hb3. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
destruct (Z.leb_spec 5 ip_res).
- rewrite Z.min_r by lia. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. rewrite Z.mod_small; lia.
- rewrite Z.min_l by lia. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. rewrite Z.mod_small; lia. }
apply ip_known_w; [apply NP; lia|].
unfold RL. destruct (negb (ip_res =? 0)); destruct (5 <=? ip_res); cbn [negb lastw app]; repeat ipaeq; reflexivity.
-  apply ip_known_old; [apply NP; lia| | exact K2].
unfold RL. destruct (Z.eqb_spec ip_res 0); destruct (Z.leb_spec 5 ip_res); cbn [negb lastw app]; try (exfalso; lia); repeat ipaeq; reflexivity.
-  apply ip_known_old; [apply NP; lia| | exact K1].
unfold RL. destruct (Z.eqb_spec ip_res 0); destruct (Z.leb_spec 5 ip_res); cbn [negb lastw app]; try (exfalso; lia); repeat ipaeq; reflexivity.
-  intros R5. unfold byte_of. rewrite Z.mul_0_r, Z.shiftr_0_r, Z.mul_1_r.
assert (RS : ip_res < 2 ^ 32) by (unfold ip_res; exact Hres).
assert (E5 : (5 <=? ip_res) = true) by (apply Z.leb_le; exact R5).
assert (EZ : (ip_res =? 0) = false) by (apply Z.eqb_neq; lia).
split; [| split; [| split; [| split; [| split; [| exact RS]]]]].
1-4: apply ip_known_w; [apply NP; unfold ip_res in *; unfold IB, UNIT in *; lia|];
unfold RL; rewrite E5, EZ; cbn [negb lastw app]; repeat ipaeq; try reflexivity.
all: try (change (8 * 2) with 16; reflexivity). all: try (change (8 * 3) with 24; reflexivity).
apply (ip_known_w _ 0); [apply NP; unfold ip_res in *; unfold IB, UNIT in *; lia|].
unfold RL; rewrite E5, EZ; cbn [negb lastw app]; repeat ipaeq; reflexivity.
-  intros RP.
replace (snd c + stride - IB - ip_res) with (snd ip_p + n) by (unfold ip_res; rewrite PP; lia).
apply (ip_known_w _ 0); [apply NP; lia|].
assert (EZ : (ip_res =? 0) = false) by (apply Z.eqb_neq; lia).
unfold RL; rewrite EZ. destruct (Z.leb_spec 5 ip_res); cbn [negb lastw app];
try (destruct (Z.eq_dec ip_res 5)); try (exfalso; lia); repeat ipaeq; reflexivity.
-  intros x Hx. apply ip_unknown. rewrite PP. exact Hx.
Qed.

#[using="bm i X1 INV1 Hm Hidx Hc TF Hn OFF Hfit Hres Hb3 qv K4 K2 K1 Q IM IG IS"] Theorem addback_INVL : INVL x0 ip_stf L (((c, off), n) :: BL1) LS.
Proof.
destruct ip_stf_ctrl as [CE TK]. pose proof ip_stride as [S16 _]. pose proof ip_off as OFF'.
assert (REG : exists r, s_regions st !! fst bm = Some r /\ r_kind r = RKGroup) by (destruct Hm as [ai Hb]; exact (ig_region _ _ _ IG _ _ Hb)).
change x0 with (mkX (x_idle X1) (x_zomb X1) None (x_orph X1) (x_fresh X1)).
apply (INVL_add_block X1 st ip_stf L BL1 LS c off n INV1 eq_refl CE TK).
- intros m' i' Hs q Hq. rewrite ip_slots in Hs. inversion Hs. subst m' i'.
assert (NQ : ~ (fst q = fst bm /\ snd ip_p <= snd q < snd ip_p + n)).
{ intros [F R]. apply Hq. unfold inT. rewrite ip_c. cbn [fst snd]. split; [exact F|]. unfold ip_p, aadd in R. rewrite ip_c in R. cbn [snd] in R.
rewrite sstart_succ. fold stride. unfold IB, UNIT in *. lia. }
rewrite (ip_stf_read_out q NQ). unfold ip_stw. apply wrs_read_other.
intros Hin. destruct (RL_addrs q Hin) as (F & R & _). apply Hq. unfold inT.
assert (E2 : snd c = sstart (MR st m) i) by (rewrite ip_c; reflexivity). split; [rewrite F, ip_c; reflexivity|].
rewrite sstart_succ. fold stride. unfold IB in *. lia.
- change (DOMS st ip_stf). unfold ip_stf. destruct (Z.eq_dec n 0) as [N0|NZ].
+ rewrite havoc_le0 by lia. apply wrs_DOMS; [exact (DOMS_of _ _ _ _ _ INV1)|]. intros q Hin. destruct (RL_addrs q Hin) as (F & _). rewrite F. exact REG.
+ apply DOMS_havoc; [lia| | unfold ip_p; rewrite ip_c; exact REG]. apply wrs_DOMS; [exact (DOMS_of _ _ _ _ _ INV1)|]. intros q Hin. destruct (RL_addrs q Hin) as (F & _). rewrite F. exact REG.
- change (TKS ip_stf (s_tick st)). unfold ip_stf. destruct (Z.eq_dec n 0) as [N0|NZ].
+ rewrite havoc_le0 by lia. apply ip_stw_TKS.
+ rewrite <- ip_stw_tick. apply TKS_havoc; [apply ip_p16| lia| rewrite ip_stw_tick; apply ip_stw_TKS].
- intros m' i' Hs. rewrite ip_slots in Hs. inversion Hs. subst m' i'. split; [exact OFF'|]. split; [exact Hn|]. split; [exact Hfit|].
apply ip_blk_ok.
Qed.

#[using="Type"] Lemma addback_ctrl : ctrl_eq st ip_stf /\ s_tick ip_stf = s_tick st.
Proof. exact ip_stf_ctrl. Qed.
End ADDBACK.

Section INPLACE.
Variables (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (c : cptr) (off n0 n : Z).
Variables (m bm : aptr) (i ai : Z) (a : aptr) (ar : area) (ka : Z).
Hypothesis INV : INVL x0 st L BL LS.
Hypothesis Hk : In ((c, off), n0) BL.
Hypothesis BF : blk_facts st c off n0 m bm i ai a ar ka.
Hypothesis TF : TF2 st.
Hypothesis Hn : 0 <= n.
Let stride := get_stride (MR st m).
Hypothesis Hfit : UNIT * off + n <= stride - IB.
Hypothesis Hres : stride - IB - UNIT * off - n < 2 ^ 32.

Definition ip_b3 : Z := i + 32 * Z.min (stride - IB - UNIT * off - n0) 5.

#[using="off n0 INV Hk"] Lemma inplace_INV1 : INVL (xpend x0 (Some c)) st L (bl_remove c BL) LS.
Proof.
change c with (bslot ((c, off), n0)) at 1 2.
apply (INVL_remove_block x0 st st L BL LS ((c, off), n0) INV Hk eq_refl (ctrl_eq_refl st) eq_refl).
- intros; reflexivity.
- exact (DOMS_of _ _ _ _ _ INV).
- exact (TKS_of _ _ _ _ _ INV).
Qed.

#[using="c bm ai a ar ka BF"] Lemma ip_b3_land : Z.land ip_b3 31 = i.
Proof.
unfold ip_b3. pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF). pose proof (bf_li _ _ _ _ _ _ _ _ _ _ _ BF).
change 31 with (Z.ones 5). rewrite Z.land_ones by lia. change (2 ^ 5) with 32.
rewrite (Z.mul_comm 32), Z.mod_add by lia. rewrite Z.mod_small; lia.
Qed.

#[using="bm ai a ar ka INV Hk BF TF Hn Hfit Hres"] Theorem inplace_INVL :
INVL x0 (ip_stf st c off n m ip_b3) L (((c, off), n) :: bl_remove c BL) LS.
Proof.
pose proof (bf_shadow _ _ _ _ _ _ _ _ _ _ _ BF) as SH0. unfold blk_shadow_ok in SH0. cbn [bslot boff bsize fst snd] in SH0.
rewrite (hosts_gbase _ _ _ (proj1 (proj2 (proj2 INV))) _ _ (ex_intro _ ai (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF))) in SH0.
destruct SH0 as (K4 & K3 & K2 & K1 & Q & _ & _ & _).
assert (Efc : fst c = fst bm) by (rewrite (bf_c _ _ _ _ _ _ _ _ _ _ _ BF); reflexivity). rewrite Efc in K4, K2, K1.
apply (addback_INVL st L (bl_remove c BL) LS c off n m bm i ip_b3 inplace_INV1 (ex_intro _ ai (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF))
(bf_i _ _ _ _ _ _ _ _ _ _ _ BF) (bf_c _ _ _ _ _ _ _ _ _ _ _ BF) TF Hn (bf_off _ _ _ _ _ _ _ _ _ _ _ BF) Hfit Hres ip_b3_land K4 K2 K1 Q).
Qed.

#[using="Type"] Lemma inplace_ctrl : ctrl_eq st (ip_stf st c off n m ip_b3) /\ s_tick (ip_stf st c off n m ip_b3) = s_tick st.
Proof. apply addback_ctrl. Qed.
#[using="bm"] Lemma inplace_eq : havoc (ip_p c off) n (set_size (ip_p c off) (ip_e st c m) n ip_b3 st) = ip_stf st c off n m ip_b3.
Proof. unfold ip_stf. rewrite (set_size_RL st c off n m bm ip_b3). reflexivity. Qed.
End INPLACE.

Section REMAP2.
Variables (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (c : cptr) (off n0 n : Z).
Variables (m bm : aptr) (i ai : Z) (a : aptr) (ar : area) (ka : Z).
Variables (z nl : Z).
Hypothesis INV : INVL x0 st L BL LS.
Hypothesis Hk : In ((c, off), n0) BL.
Hypothesis BF : blk_facts st c off n0 m bm i ai a ar ka.
Hypothesis T0 : TF0 st.
Hypothesis Hn : 0 <= n.
Hypothesis SC : m_sizeclass (MR st m) = 63.
Hypothesis Hz : 0 < z /\ z mod PGSZ = 0.
Hypothesis Hnl : 0 < nl < LEN_MAX /\ nl mod PGSZ = 0.
Hypothesis Hceil : z + nl <= alloc_ceiling.
Hypothesis DISJ : forall rid2 r2, rid2 <> fst bm -> s_regions st !! rid2 = Some r2 ->
let '(b2, l2) := region_live_range r2 in z + nl <= b2 \/ b2 + l2 <= z.
Hypothesis ND : n + UNIT * off + UNIT + IB <= nl.
Hypothesis Hres : nl - UNIT - IB - UNIT * off - n < 2 ^ 32.

Definition rm_st4 : mstate := st4 st m bm z nl.
Definition rm_L' : mled := L' st L bm z nl.
Definition rm_b3 : Z := ip_b3 st off n0 m i.
Definition rm_stf : mstate := ip_stf rm_st4 c off n m rm_b3.

#[using="RC__ L BL LS off n0 ai a ar ka z nl INV BF SC Hz Hnl"] Lemma rm_facts : i = 0 /\ m_last_idx (MR st m) = 0 /\ m_maplen (MR st m) <> 0 /\ snd bm = 0 /\ c = aadd bm UNIT.
Proof.
pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
pose proof (ig_ok _ _ _ IG _ _ _ (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF)) as GO.
assert (LI0 : m_last_idx (MR st m) = 0 /\ m_maplen (MR st m) <> 0).
{ destruct (g_sc _ _ _ _ _ _ GO) as [[Hsc _]|(_ & A1 & A2 & _)]; [unfold MR in *; lia| auto]. }
destruct LI0 as [LI0 ML].
assert (I0 : i = 0) by (pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF); lia).
destruct (bf_top _ _ _ _ _ _ _ _ _ _ _ BF ML) as [B0 _].
repeat split; auto.
rewrite (bf_c _ _ _ _ _ _ _ _ _ _ _ BF). unfold sstart, gbase. rewrite (bf_mem _ _ _ _ _ _ _ _ _ _ _ BF), I0. unfold aadd. cbn [fst snd default id]. f_equal. lia.
Qed.

#[using="off n0 INV Hk"] Lemma rm_INV1 : INVL (xpend x0 (Some c)) st L (bl_remove c BL) LS.
Proof. exact (inplace_INV1 st L BL LS c off n0 INV Hk). Qed.

#[using="off n0 i ai a ar ka INV Hk BF SC Hz Hnl Hceil DISJ"] Lemma rm_INV4 : INVL (xpend x0 (Some c)) rm_st4 rm_L' (bl_remove c BL) LS.
Proof.
destruct rm_facts as (I0 & LI0 & ML & B0 & Ec).
apply (remap_core_INVL (xpend x0 (Some c)) st L (bl_remove c BL) LS m bm ai z nl rm_INV1 (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF) SC);
try reflexivity; try assumption.
cbn. f_equal. rewrite (bf_c _ _ _ _ _ _ _ _ _ _ _ BF), I0. reflexivity.
Qed.

#[using="ai a ar ka INV Hk BF T0 Hn SC Hz Hnl Hceil DISJ ND Hres"] Theorem remap_INVL : INVL x0 rm_stf rm_L' (((c, off), n) :: bl_remove c BL) LS.
Proof.
destruct rm_facts as (I0 & LI0 & ML & B0 & Ec).
pose proof (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF) as Hb.
pose proof (bf_shadow _ _ _ _ _ _ _ _ _ _ _ BF) as SH0. unfold blk_shadow_ok in SH0. cbn [bslot boff bsize fst snd] in SH0.
rewrite (hosts_gbase _ _ _ (proj1 (proj2 (proj2 INV))) _ _ (ex_intro _ ai Hb)) in SH0.
destruct SH0 as (K4 & K3 & K2 & K1 & Q & _ & _ & _).
assert (Efc : fst c = fst bm) by (rewrite Ec; reflexivity). assert (Esc : snd c = UNIT) by (rewrite Ec; cbn; lia). rewrite Efc in K4, K2, K1.
pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF) as OFF.
assert (KT : forall k v, 1 <= k <= 4 -> known st (fst bm, snd c + UNIT * off - k) v -> known rm_st4 (fst bm, snd c + UNIT * off - k) v).
{ intros k v Hk0 K. apply (known4 (xpend x0 (Some c)) st L (bl_remove c BL) LS m bm ai z nl rm_INV1 Hb SC); [| exact K].
cbn [fst snd]. intros _. rewrite (rm_B_eq (xpend x0 (Some c)) st L (bl_remove c BL) LS m bm ai z nl rm_INV1 Hb SC).
pose proof (bf_fit _ _ _ _ _ _ _ _ _ _ _ BF) as FIT. pose proof (bf_n _ _ _ _ _ _ _ _ _ _ _ BF) as N0.
assert (STR : get_stride (MR st m) = m_maplen (MR st m) * 4096 - UNIT).
{ unfold get_stride. fold (MR st m). unfold MR in *. rewrite LI0. cbn [Z.eqb andb]. destruct (Z.eqb_spec (m_maplen (get_meta_rec st m)) 0) as [E0|E0]; [clear - ML E0; lia| reflexivity].    }
unfold MR in *. rewrite STR in FIT. clear -Hk0 ND OFF Hn Esc FIT N0. unfold UNIT, IB in *. lia. }
unfold rm_stf.
apply (addback_INVL rm_st4 rm_L' (bl_remove c BL) LS c off n m bm 0 rm_b3 rm_INV4).
- apply hosts'. exists ai. exact Hb.
- unfold rm_st4. rewrite R'_last. lia.
- unfold rm_st4. rewrite R'_sstart0. rewrite (bf_c _ _ _ _ _ _ _ _ _ _ _ BF), I0. reflexivity.
- apply (TF2_4 (xpend x0 (Some c)) st L (bl_remove c BL) LS m bm ai z nl rm_INV1 Hb SC Hz Hnl T0).
- exact Hn.
- exact OFF.
- unfold rm_st4. rewrite (stride' (xpend x0 (Some c)) st L (bl_remove c BL) LS m bm ai z nl rm_INV1 Hb SC Hz Hnl). clear -ND Hn OFF. unfold UNIT, IB in *. lia.
- unfold rm_st4. rewrite (stride' (xpend x0 (Some c)) st L (bl_remove c BL) LS m bm ai z nl rm_INV1 Hb SC Hz Hnl). clear -Hres. unfold UNIT, IB in *. lia.
- unfold rm_b3. rewrite <- I0. apply (ip_b3_land st c off n0 m bm i ai a ar ka BF).
- apply KT; [lia| exact K4].
- apply KT; [lia| exact K2].
- apply KT; [lia| exact K1].
- exact Q.
Qed.

#[using="RC__ L BL LS ai a ar ka INV Hk BF SC Hz Hnl"] Lemma remap_eq :
rm_stf = havoc (aadd c (UNIT * off)) n
(set_size (aadd c (UNIT * off)) (aadd bm (UNIT + (nl - UNIT) - IB)) n rm_b3
(wr8 (aadd bm (UNIT + (nl - UNIT) - IB)) 0 (remap_region (fst bm) z nl m st))).
Proof.
destruct rm_facts as (I0 & LI0 & ML & B0 & Ec). pose proof (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF) as Hb.
unfold rm_stf, ip_stf. rewrite <- (set_size_RL rm_st4 c off n m bm rm_b3). unfold ip_p, ip_e.
unfold rm_st4 at 2. rewrite (stride' (xpend x0 (Some c)) st L (bl_remove c BL) LS m bm ai z nl rm_INV1 Hb SC Hz Hnl).
assert (Ee : aadd c (nl - UNIT - IB) = aadd bm (UNIT + (nl - UNIT) - IB)) by (rewrite Ec; unfold aadd; cbn [fst snd]; f_equal; lia).
rewrite Ee. unfold rm_st4, st4. rewrite (remap_region_st3 (xpend x0 (Some c)) st L (bl_remove c BL) LS m bm ai z nl rm_INV1 Hb SC).
unfold rm_e. replace (fst bm, nl - IB) with (aadd bm (UNIT + (nl - UNIT) - IB)) by (unfold aadd; rewrite B0; f_equal; lia). reflexivity.
Qed.

#[using="RC__ L BL LS ai a ar ka INV Hk BF SC"] Lemma remap_regions_kept rid r : s_regions st !! rid = Some r -> r_kind r = RKGroup -> rid <> fst bm -> s_regions rm_stf !! rid = Some r.
Proof.
intros Hr Kr NE. unfold rm_stf. destruct (addback_ctrl rm_st4 c off n m rm_b3) as [CE _]. rewrite (ce_regions _ _ CE).
unfold rm_st4. apply (st4_keep (xpend x0 (Some c)) st L (bl_remove c BL) LS m bm ai z nl rm_INV1 (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF) SC); assumption.
Qed.
End REMAP2.

End RC__1.
End Mq0.

From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfya.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfya. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPiB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPiB.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qatc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qatc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSfG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSfG.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdBa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdBa.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdBa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdBa.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpFQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpFQ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPiB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPiB. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYTG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYTG.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdBa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdBa.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QaiD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QaiD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLaA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLaA.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQg5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQg5.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1am.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1am.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSfG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSfG. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QoCS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QoCS.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQCz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQCz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QcV4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QcV4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7RC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7RC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQg5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQg5.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlOh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlOh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QhnL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QhnL.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Set Implicit Arguments.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Fixpoint lafter {R} (L : mled) (t : M R) (ans : list Z) {struct t} : mled :=
match t, ans with
| SRet _, _ => L
| SVis (EUndef _) _, _ => L
| SVis e k, a :: ans' => lafter (event_post L e a) (k a) ans'
| SVis _ _, [] => L
end.

Fixpoint followk {R} (t : M R) (ans : list Z) {struct t} : option (R * list Z) :=
match t, ans with
| SRet r, _ => Some (r, ans)
| SVis (EUndef _) _, _ => None
| SVis _ k, a :: ans' => followk (k a) ans'
| SVis _ _, [] => None
end.

#[using="Type"] Lemma ptree_follow_lafter {R} : forall (t : M R) L Post ans r,
ptree L t Post -> follow t ans = Some r -> cpath L t (lafter L t ans) r /\ Post (lafter L t ans) r.
Proof.
induction t as [r0|e k IH]; intros L Post ans r H Hf; cbn [ptree follow lafter] in *.
- inversion Hf; subst. split; [constructor| exact H].
- destruct e; try (destruct H; fail); try contradiction.
all: destruct H as [He Hk]; destruct ans as [|a ans']; [discriminate|];
specialize (Hk a); case_ans;
[ destruct (IH a _ _ _ _ Hk Hf) as [Hp HP]; split; [econstructor; eauto| exact HP]
| destruct (rejects_inv _ Hk) as (w & k' & E); rewrite E in Hf; cbn in Hf; discriminate ].
Qed.

#[using="Type"] Lemma followk_follow {R} : forall (t : M R) ans x rest, followk t ans = Some (x, rest) -> follow t ans = Some x.
Proof.
induction t as [r0|e k IH]; intros ans x rest H; cbn [followk follow] in *.
- inversion H. reflexivity.
- destruct e; try discriminate; destruct ans as [|a ans']; try discriminate; eapply IH; exact H.
Qed.

#[using="Type"] Lemma follow_sbind {R S} : forall (t : M R) (k : R -> M S) ans,
follow (sbind t k) ans = match followk t ans with Some (x, rest) => follow (k x) rest | None => None end.
Proof.
induction t as [r0|e k0 IH]; intros k ans; cbn [sbind followk follow]; [reflexivity|].
destruct e; destruct ans as [|a ans']; cbn [follow]; try reflexivity; apply IH.
Qed.

#[using="Type"] Lemma lafter_sbind {R S} : forall (t : M R) (k : R -> M S) L ans x rest,
followk t ans = Some (x, rest) -> lafter L (sbind t k) ans = lafter (lafter L t ans) (k x) rest.
Proof.
induction t as [r0|e k0 IH]; intros k L ans x rest H; cbn [sbind followk lafter] in *.
- inversion H. reflexivity.
- destruct e; try discriminate; destruct ans as [|a ans']; try discriminate; cbn [lafter]; apply IH; exact H.
Qed.

#[using="Type"] Lemma strel_followk {R1 R2} (RR : R1 -> R2 -> Prop) (t1 : M R1) (t2 : M R2) :
strel RR t1 t2 -> forall ans x1 rest, followk t1 ans = Some (x1, rest) ->
exists x2, followk t2 ans = Some (x2, rest) /\ RR x1 x2.
Proof.
induction 1 as [r1 r2 Hr|e k1 k2 Hk IH]; intros ans x1 rest H; cbn [followk] in *.
- inversion H. subst. eauto.
- destruct e; try discriminate; destruct ans as [|a ans']; try discriminate; eapply IH; exact H.
Qed.

#[using="Type"] Lemma strel_lafter {R1 R2} (RR : R1 -> R2 -> Prop) (t1 : M R1) (t2 : M R2) :
strel RR t1 t2 -> forall L ans, lafter L t1 ans = lafter L t2 ans.
Proof.
induction 1 as [r1 r2 Hr|e k1 k2 Hk IH]; intros L ans; cbn [lafter]; [reflexivity|].
destruct e; destruct ans; try reflexivity; apply IH.
Qed.

#[using="Type"] Lemma strel_follow_some {R1 R2} (RR : R1 -> R2 -> Prop) (t1 : M R1) (t2 : M R2) ans r1 :
strel RR t1 t2 -> follow t1 ans = Some r1 -> exists r2, follow t2 ans = Some r2 /\ RR r1 r2.
Proof.
intros H Hf. pose proof (strel_follow H ans) as F. rewrite Hf in F.
destruct (follow t2 ans) as [r2|]; [exists r2; auto| destruct F].
Qed.

#[using="Type"] Lemma steq_follow {R} (t1 t2 : M R) ans : steq t1 t2 -> follow t1 ans = follow t2 ans.
Proof.
intros H. apply strel_eq_steq in H. pose proof (strel_follow H ans) as F.
destruct (follow t1 ans), (follow t2 ans); cbn in F; try reflexivity; [congruence| destruct F| destruct F].
Qed.

#[using="Type"] Lemma steq_followk {R} (t1 t2 : M R) : steq t1 t2 -> forall ans, followk t1 ans = followk t2 ans.
Proof.
induction 1 as [r|e k1 k2 Hk IH]; intros ans; cbn [followk]; [reflexivity|].
destruct e; destruct ans; try reflexivity; apply IH.
Qed.

#[using="Type"] Lemma steq_lafter {R} (t1 t2 : M R) : steq t1 t2 -> forall L ans, lafter L t1 ans = lafter L t2 ans.
Proof. intros H. apply strel_eq_steq in H. apply (strel_lafter H). Qed.

#[using="Type"] Lemma ptree_followk {R} (t : M R) L Post ans x rest :
ptree L t Post -> followk t ans = Some (x, rest) -> Post (lafter L t ans) x.
Proof. intros HP Hf. exact (proj2 (ptree_follow_lafter t L Post ans HP (followk_follow _ _ Hf))). Qed.

#[using="Type"] Lemma event_post_live L e z : ld_live (event_post L e z) = ld_live L.
Proof.
destruct e as [rq|a len prot flags|a len|a len prot|p c h|w|a ol nl fl]; cbn; try reflexivity.
- destruct (rq =? 0); [reflexivity|]. destruct (z =? rq); [| reflexivity]. destruct (ld_brk L); try reflexivity; destruct (ld_brkreg L) as [[b l]|]; reflexivity.
- destruct (Z.land flags MAP_FIXED =? 0); [| reflexivity]. destruct (is_err z); [reflexivity|]. destruct (prot =? PROT_NONE); reflexivity.
- destruct ((z =? 0) || (z =? TWO64 - ENOSYS)); reflexivity.
- destruct (is_errno_form z); reflexivity.
Qed.

#[using="Type"] Lemma cpath_live {R} L (t : M R) L' r : cpath L t L' r -> ld_live L' = ld_live L.
Proof. induction 1; [reflexivity|]. rewrite IHcpath. apply event_post_live. Qed.
End RC__1.

Unset Implicit Arguments.
Section RC__2. Context {RC__ : Q6q3.RunConsts}.

Section SIM.
Context {O : Type} (pans : O -> aptr -> Z -> Z -> Z) (pupd : O -> ev -> Z -> O).
Hypothesis Hpans : forall o p c h, 0 <= pans o p c h < 256.
Local Notation PRUN := (prun pans pupd).

#[using="Type"] Lemma prun_ret {R} o (x : R) : PRUN o (SRet x) = SRet (o, x).
Proof. reflexivity. Qed.

#[using="Type"] Lemma free_prefix st L BL LS c off n :
INVL x0 st L BL LS -> In ((c, off), n) BL ->
exists m bm i,
let p := aadd c (UNIT * off) in
let st1 := wr16 (aadd p (-2)) 0 (wr8 (aadd p (-3)) 255 st) in
free_hdr st p = SRet (Some (st1, m, i))
/\ ctrl_eq st st1 /\ strip st1 = strip st /\ s_slots st !! c = Some (m, i)
/\ INVL (xpend x0 (Some c)) st1 L (bl_remove c BL) LS /\ hosts st1 bm m
/\ 0 <= i <= m_last_idx (MR st1 m) /\ c = (fst bm, sstart (MR st1 m) i)
/\ tbit (m_avail (MR st1 m)) i = false /\ tbit (m_freed (MR st1 m)) i = false
/\ (0 <= m_sizeclass (MR st1 m) < 48 \/ m_sizeclass (MR st1 m) = 63)
/\ free_tail dec_hdr st1 m i = free_tail dec_slots st1 m i.
Proof.
intros INV Hk.
destruct (block_facts x0 st L BL LS INV c off n Hk) as (m & bm & i & ai & a & ar & ka & BF).
pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
exists m, bm, i. cbn zeta.
set (p := aadd c (UNIT * off)).
set (st1 := wr16 (aadd p (-2)) 0 (wr8 (aadd p (-3)) 255 st)).
pose proof (free_hdr_eq st c off n m bm i ai a ar ka BF) as FH. fold p in FH. fold st1 in FH.
assert (CE1 : ctrl_eq st st1) by (eapply ctrl_eq_trans; [apply ctrl_eq_wr8| apply ctrl_eq_wr16]).
assert (TK1 : s_tick st1 = s_tick st) by reflexivity.
pose proof (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF) as Hs. pose proof (bf_c _ _ _ _ _ _ _ _ _ _ _ BF) as Ec.
pose proof (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF) as Hm. pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF) as Hi.
assert (STR1 : strip st1 = strip st).
{ destruct CE1 as [C1 C2 C3 C4 C5 C6 C7 C8 C9]. unfold strip. rewrite C1, C2, C3, C4, C5, C6, C7, C8, C9. reflexivity. }
assert (INV1 : INVL (xpend x0 (Some c)) st1 L (bl_remove c BL) LS).
{ change c with (bslot ((c, off), n)) at 1 2.
apply (INVL_remove_block x0 st st1 L BL LS ((c, off), n) INV Hk eq_refl CE1 TK1).
- intros m' i' Hs' q Hq. cbn [bslot fst snd] in Hs', Hq. rewrite Hs in Hs'. inversion Hs'. subst m' i'.
subst st1. unfold wr16. rewrite !cell_read_wr8_other; [reflexivity| | |];
intros ->; apply Hq; unfold inT; subst p; rewrite Ec; cbn [fst snd aadd]; rewrite sstart_succ;
pose proof (bf_stride _ _ _ _ _ _ _ _ _ _ _ BF) as [SG _]; pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF); pose proof (bf_fit _ _ _ _ _ _ _ _ _ _ _ BF);
pose proof (bf_n _ _ _ _ _ _ _ _ _ _ _ BF); unfold UNIT, IB in *; lia.
- subst st1. unfold wr16. set (P := fun rid : N => exists r, s_regions st !! rid = Some r /\ r_kind r = RKGroup).
change (forall rid sh, s_shadow (wr8 (aadd (aadd p (-2)) 1) (Z.shiftr 0 8) (wr8 (aadd p (-2)) 0 (wr8 (aadd p (-3)) 255 st))) !! rid = Some sh -> P rid).
assert (HP : P (fst bm)) by (destruct (ig_region _ _ _ IG _ _ Hm) as (r & Hr & Hkr); exists r; auto).
assert (Efst : forall d1 d2, fst (aadd (aadd p d1) d2) = fst bm) by (intros; subst p; rewrite Ec; reflexivity).
assert (Efst1 : forall d1, fst (aadd p d1) = fst bm) by (intros; subst p; rewrite Ec; reflexivity).
apply (wr8_dom _ _ _ P); [apply (wr8_dom _ _ _ P); [apply (wr8_dom _ _ _ P); [exact (ish_dom _ _ ISH)|]|]|]; rewrite ?Efst, ?Efst1; exact HP.
- subst st1. unfold wr16. apply wr8_tks; [cbn; lia|]. apply wr8_tks; [cbn; lia|]. apply wr8_tks; [cbn; lia|]. exact (ish_ticks _ _ ISH). }
assert (Hm1 : hosts st1 bm m). { exists ai. rewrite (ce_groups _ _ CE1). exact Hm. }
assert (MR1 : forall x, MR st1 x = MR st x) by (intros; apply MR_ext; exact (ce_metas _ _ CE1)).
assert (SC : 0 <= m_sizeclass (MR st1 m) < 48 \/ m_sizeclass (MR st1 m) = 63).
{ rewrite MR1. destruct (g_sc _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Hm)) as [[? ?]|[? ?]]; lia. }
split; [exact FH|]. split; [exact CE1|]. split; [exact STR1|]. split; [exact Hs|]. split; [exact INV1|]. split; [exact Hm1|].
rewrite !MR1. split; [exact Hi|]. split; [exact Ec|].
split; [exact (bf_notA _ _ _ _ _ _ _ _ _ _ _ BF)|]. split; [exact (bf_notF _ _ _ _ _ _ _ _ _ _ _ BF)|]. split; [rewrite <- MR1; exact SC|].
unfold free_tail.
rewrite (ntf_slots_agree mstate FUEL (xpend x0 (Some c)) st1 L (bl_remove c BL) LS m bm i _ (ret st1) INV1 Hm1); [reflexivity| | | | | |].
- rewrite MR1. exact Hi.
- cbn. rewrite MR1, Ec. reflexivity.
- reflexivity.
- reflexivity.
- unfold FUEL. lia.
- unfold FUEL. lia.
Qed.

#[using="Type"] Theorem INVL_hdr_ok st L BL LS c off n :
INVL x0 st L BL LS -> In ((c, off), n) BL -> hdr_ok pans pupd st (aadd c (UNIT * off)) c.
Proof.
intros INV Hk. destruct (free_prefix st L BL LS c off n INV Hk) as (m & bm & i & FH & CE1 & STR1 & Hs & INV1 & Hm1 & Hi & Ec & NA & NF & SC & AGREE).
cbn zeta in FH, AGREE, STR1.
eexists _, m, i. split; [| split; [exact STR1| split; [exact Hs|]]].
- intros o. rewrite FH. reflexivity.
- intros o. rewrite AGREE, <- STR1. apply free_tail_slots_control.
Qed.

#[using="Type"] Theorem free_leaf_facts st L BL LS c off n o ans o' st' :
INVL x0 st L BL LS -> In ((c, off), n) BL ->
follow (PRUN o (free st (Some (aadd c (UNIT * off))))) ans = Some (o', st') ->
(forall rid r, s_regions st' !! rid = Some r -> s_regions st !! rid = Some r) /\ s_secret st' = s_secret st
/\ c_init_done (s_ctx st') = c_init_done (s_ctx st)
/\ c_meta_alloc_shift (s_ctx st') = c_meta_alloc_shift (s_ctx st).
Proof.
intros INV Hk Hf. destruct (free_prefix st L BL LS c off n INV Hk) as (m & bm & i & FH & CE1 & STR1 & Hs & INV1 & Hm1 & Hi & Ec & NA & NF & SC & AGREE).
cbn zeta in *.
set (st1 := wr16 (aadd (aadd c (UNIT * off)) (-2)) 0 (wr8 (aadd (aadd c (UNIT * off)) (-3)) 255 st)) in *.
unfold free in Hf. rewrite FH in Hf. cbn [sbind] in Hf. unfold free_tail in Hf.
rewrite (guard_true 60) in Hf by (unfold testbit; rewrite Z.lor_spec; fold (MR st1 m); unfold tbit in NA, NF; rewrite NA, NF; reflexivity).
fold (MR st1 m) in Hf.
pose proof (ce_regions _ _ CE1) as RG1. pose proof (ce_secret _ _ CE1) as SE1. pose proof (ce_ctx _ _ CE1) as CX1.
destruct (negb ((m_freed (MR st1 m) =? 0) || (Z.lor (m_freed (MR st1 m)) (m_avail (MR st1 m)) + bit i =? mask_upto (m_last_idx (MR st1 m))))).
- rewrite prun_ret in Hf. cbn [follow] in Hf. inversion Hf. subst st'. split; [intros rid r H; rewrite <- RG1; exact H| split; [rewrite <- SE1; reflexivity| cbn; rewrite ?CX1; split; reflexivity]].
- destruct (ntf_spec2 mstate FUEL dec_hdr dec_hdr (dec_hdr_ok _) (dec_hdr_ok _) (xpend x0 (Some c)) st1 L (bl_remove c BL) LS m bm i
(fun st2 mi => match mi with
| Some (base, len) => if negb (len =? 0)
then SVis (EMunmap (conc st2 base) len) (fun ru => if munmap_answer_ok ru then ret (drop_region (fst base) st2) else bad_answer (ret st1))
else ret st2
| None => ret st2 end) (ret st1) INV1 Hm1 Hi ltac:(cbn; rewrite Ec; reflexivity) eq_refl eq_refl ltac:(unfold FUEL; lia) ltac:(unfold FUEL; lia))
as (st2 & mi & LS2 & EQ & _ & (RG2 & SE2 & ID2 & SH2) & _).
rewrite EQ in Hf.
assert (K2 : (forall rid r, s_regions st2 !! rid = Some r -> s_regions st !! rid = Some r) /\ s_secret st2 = s_secret st
/\ c_init_done (s_ctx st2) = c_init_done (s_ctx st) /\ c_meta_alloc_shift (s_ctx st2) = c_meta_alloc_shift (s_ctx st)).
{ split; [intros rid r H; rewrite <- RG1, <- RG2; exact H| split; [rewrite <- SE1, <- SE2; reflexivity| rewrite ID2, SH2, CX1; split; reflexivity]]. }
destruct mi as [[base len]|].
+ destruct (negb (len =? 0)).
* unfold prun in Hf. rewrite (eruns_vis_keep) in Hf by reflexivity. destruct ans as [|a ans']; [cbn [follow] in Hf; discriminate Hf|]. cbn [follow] in Hf.
destruct (munmap_answer_ok a).
-- change (eruns (psel pans) pupd (pupd o (EMunmap (conc st2 base) len) a) (ret (drop_region (fst base) st2))) with
(PRUN (pupd o (EMunmap (conc st2 base) len) a) (SRet (drop_region (fst base) st2))) in Hf.
rewrite prun_ret in Hf. cbn [follow] in Hf. inversion Hf. subst st'.
split; [| exact (proj2 K2)]. intros rid r H. unfold drop_region in H. cbn in H.
destruct (N.eq_dec rid (fst base)) as [->|NE]; [rewrite lookup_delete_eq in H; discriminate H|]. rewrite lookup_delete_ne in H by congruence. apply (proj1 K2). exact H.
-- unfold bad_answer in Hf. rewrite eruns_vis_keep in Hf by reflexivity. cbn [follow] in Hf. discriminate Hf.
* rewrite prun_ret in Hf. cbn [follow] in Hf. inversion Hf. subst st'. exact K2.
+ rewrite prun_ret in Hf. cbn [follow] in Hf. inversion Hf. subst st'. exact K2.
Qed.

#[using="Hpans"] Theorem free_sim st L BL LS c off n o ans o' st' :
INVL x0 st L BL LS -> In ((c, off), n) BL ->
follow (PRUN o (free st (Some (aadd c (UNIT * off))))) ans = Some (o', st') ->
let t := cfree (strip st) (Some c) in
let L' := lafter L t ans in
follow t ans = Some (strip st') /\ cpath L t L' (strip st') /\ ld_live L' = ld_live L
/\ exists LS', INVL x0 st' L' (bl_remove c BL) LS'.
Proof.
intros INV Hk Hf. cbn zeta.
pose proof (free_control pans pupd st (aadd c (UNIT * off)) c o (INVL_hdr_ok st L BL LS c off n INV Hk)) as REL.
pose proof (ftree_prun pans pupd Hpans (free st (Some (aadd c (UNIT * off)))) L _ o (free_INVL_closed st L BL LS c off n INV Hk)) as PT.
destruct (strel_follow_some ans REL Hf) as (cs' & Hf2 & FR). unfold FREL in FR. cbn in FR. subst cs'.
split; [exact Hf2|].
pose proof (ptree_strel REL L _ (fun _ _ => True) ltac:(intros; exact I) PT) as PT2.
destruct (ptree_follow_lafter _ L _ ans PT2 Hf2) as [CP _].
split; [exact CP|]. split; [exact (cpath_live CP)|].
destruct (ptree_follow_lafter _ L _ ans PT Hf) as [_ POST]. cbn in POST.
rewrite <- (strel_lafter REL L ans). exact POST.
Qed.

#[using="Hpans"] Theorem malloc_sim st L BL LS n o ans o' st' r :
INVL x0 st L BL LS -> 0 <= n ->
follow (PRUN o (malloc st n)) ans = Some (o', (st', r)) ->
let t := cmalloc (strip st) n in
let L' := lafter L t ans in
exists rc, follow t ans = Some (strip st', rc) /\ cpath L t L' (strip st', rc) /\ ld_live L' = ld_live L /\ GP st st' /\
match r, rc with
| None, None => exists LS', INVL x0 st' L' BL LS'
| Some pf, Some c => exists off LS', pf = aadd c (UNIT * off) /\ 0 <= off <= 255
/\ INVL x0 st' L' (((c, off), n) :: BL) LS' /\ ~ In c (map bslot BL)
| _, _ => False
end.
Proof.
intros INV Hn Hf. cbn zeta.
set (st0 := set_tick (N.succ (s_tick st)) st).
assert (INV0 : INVL x0 st0 L BL LS) by (apply INVL_set_tick; [cbn; lia| exact INV]).
assert (TF0' : TF0 st0) by (apply TF0_tick_new; [exact (TKS_of _ _ _ _ _ INV)| cbn; lia]).
set (K := fun x : mstate * option (aptr * Z) => let '(st1, r) := x in
match r with
| None => ret (st1, @None aptr)
| Some (g, idx) => enframe_full st1 g idx n (c_mmap_counter (ctx st1)) (fun st2 p => ret (havoc p n st2, Some p))
end).
assert (E1 : steq (PRUN o (malloc st n)) (sbind (PRUN o (malloc_core full_lay st0 n)) (fun x => PRUN (fst x) (K (snd x))))).
{ unfold malloc, prun. apply eruns_sbind. }
rewrite (steq_follow ans E1) in Hf. rewrite follow_sbind in Hf.
destruct (followk (PRUN o (malloc_core full_lay st0 n)) ans) as [[[o1 [st1 rg]] rest]|] eqn:FK; [| discriminate].

pose proof (ftree_prun pans pupd Hpans (malloc_core full_lay st0 n) L _ o (malloc_core_ft st0 L BL LS n INV0 TF0' Hn)) as PTC.
pose proof (ptree_followk _ L _ ans PTC FK) as CP. cbn [snd fst] in CP.
set (L1 := lafter L (PRUN o (malloc_core full_lay st0 n)) ans) in *.
destruct CP as (LIVE1 & GP1 & CP).

pose proof (malloc_core_ctrl pans pupd n o st0 (strip st) ltac:(unfold st0; rewrite strip_set_tick; reflexivity)) as RELC.
destruct (strel_followk RELC ans FK) as ([cst1 rg'] & FK2 & [CR1 CR2]). cbn in CR1, CR2. subst rg'.
assert (FT : follow (cmalloc (strip st) n) ans
= Some (strip cst1, match rg with Some (g, idx) => Some (slot_of cst1 g idx) | None => None end)).
{ unfold cmalloc. rewrite follow_sbind, FK2. reflexivity. }
assert (LT : lafter L (cmalloc (strip st) n) ans = L1).
{ unfold cmalloc. rewrite (lafter_sbind _ _ L ans FK2). cbn [lafter]. unfold L1. symmetry. apply (strel_lafter RELC). }
rewrite LT.

assert (PT2 : ptree L (cmalloc (strip st) n) (fun _ _ => True)).
{ eapply (ptree_strel (malloc_control pans pupd Hpans st n o)); [intros; exact I|].
eapply ptree_mono; [intros; exact I|]. exact (ftree_prun pans pupd Hpans (malloc st n) L _ o (malloc_INVL st L BL LS n INV Hn)). }
assert (SS1 : strip cst1 = strip st1) by (rewrite <- CR1; apply strip_strip).
assert (GP0 : GP st st1) by (eapply GP_trans; [apply GP_eq; reflexivity| exact GP1]).
destruct rg as [[g idx]|].
- destruct CP as (LS1 & bg & Hg & Hidx & INV1 & FIT & TF1 & RES32 & _).
set (c0 := (fst bg, sstart (MR st1 g) idx)) in *.
assert (Ec0 : slot_of cst1 g idx = c0).
{ rewrite <- CR1, slot_of_strip. unfold slot_of. exact (slot_start'_eq _ _ _ (proj1 (proj2 (proj2 INV1))) _ _ idx Hg). }
rewrite Ec0 in FT.

pose proof (enframe_ft (xpend x0 (Some c0)) st1 L1 BL LS1 g bg idx n INV1 Hg Hidx eq_refl Hn FIT TF1 RES32 (c_mmap_counter (ctx st1))
(fun _ res => exists off, 0 <= off <= 255 /\ snd res = Some (aadd c0 (UNIT * off))
/\ INVL x0 (fst res) L1 (((c0, off), n) :: BL) LS1 /\ strip (fst res) = strip st1 /\ GP st1 (fst res))) as EF.
cbn [fst snd] in EF.
specialize (EF ltac:(intros off st2 Ho Hf2 INV2 CE TK; exists off; split; [exact Ho|]; split; [reflexivity|]; split; [exact INV2|];
split; [destruct CE as [C1 C2 C3 C4 C5 C6 C7 C8 C9]; unfold strip; rewrite C1, C2, C3, C4, C5, C6, C7, C8, C9; reflexivity| apply GP_eq; [exact (ce_regions _ _ CE)| exact (ce_secret _ _ CE)| rewrite (ce_ctx _ _ CE); reflexivity]])).
pose proof (ftree_prun pans pupd Hpans _ L1 _ o1 EF) as PTE.
cbn [K fst snd] in Hf.
destruct (ptree_follow_lafter _ L1 _ rest PTE Hf) as [_ (off & Ho & Er & INV2 & SS2 & GP2)]. cbn [fst snd] in Er, INV2, SS2, GP2. subst r.
exists (Some c0). split; [rewrite FT, SS1, SS2; reflexivity|].
split; [rewrite <- LT; pose proof (ptree_follow_lafter _ L _ ans PT2 ltac:(rewrite FT, SS1; reflexivity)) as [C _]; rewrite SS2; exact C|].
split; [exact LIVE1|]. split; [exact (GP_trans _ _ _ GP0 GP2)|].
exists off, LS1. split; [reflexivity|]. split; [exact Ho|]. split; [exact INV2|].
pose proof (is_nodup _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV2))))))) as ND. cbn [map bslot fst] in ND.
apply NoDup_cons in ND as [NI _]. intros Hin. apply NI. apply list_elem_of_In. exact Hin.
- destruct CP as (LS1 & INV1). cbn [K fst snd] in Hf. rewrite prun_ret in Hf. cbn [follow] in Hf. inversion Hf. subst o' st' r.
exists None. split; [rewrite FT, SS1; reflexivity|].
split; [rewrite <- LT; pose proof (ptree_follow_lafter _ L _ ans PT2 ltac:(rewrite FT, SS1; reflexivity)) as [C _]; exact C|].
split; [exact LIVE1|]. split; [exact GP0|]. exists LS1. exact INV1.
Qed.

#[using="Hpans"] Theorem malloc_core_allzero st L BL LS n o ans o' st1 g idx :
INVL x0 st L BL LS -> 0 <= n ->
follow (PRUN o (malloc_core full_lay (set_tick (N.succ (s_tick st)) st) n)) ans = Some (o', (st1, Some (g, idx))) ->
(48 <= m_sizeclass (MR st1 g) \/ get_stride (MR st1 g) < UNIT * size_class (m_sizeclass (MR st1 g))) ->
exists bg, m_mem (MR st1 g) = Some bg /\
forall k, 0 <= k < get_stride (MR st1 g) - IB ->
cell_read (get_shadow st1 (fst bg)) (sstart (MR st1 g) idx + k) = Known 0.
Proof.
intros INV Hn Hf U.
set (st0 := set_tick (N.succ (s_tick st)) st) in *.
assert (INV0 : INVL x0 st0 L BL LS) by (apply INVL_set_tick; [cbn; lia| exact INV]).
assert (TF0' : TF0 st0) by (apply TF0_tick_new; [exact (TKS_of _ _ _ _ _ INV)| cbn; lia]).
pose proof (ftree_prun pans pupd Hpans (malloc_core full_lay st0 n) L _ o (malloc_core_ft st0 L BL LS n INV0 TF0' Hn)) as PTC.
destruct (ptree_follow_lafter _ L _ ans PTC Hf) as [_ CP]. cbn [snd fst] in CP.
destruct CP as (LIVE1 & GP1 & LS1 & bg & Hg & Hidx & INV1 & FIT & TF1 & RES32 & AZ).
pose proof (hosts_mem _ _ _ (proj1 (proj2 (proj2 INV1))) _ _ Hg) as HM.
pose proof (stride_ge _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV1))))) _ _ Hg) as [SG _].
exists bg. split; [exact HM|].
cbn [fst snd] in SG, Hidx. intros k Hk. apply (AZ U). unfold sstart, gbase. rewrite HM. cbn [default fst snd]. unfold id. unfold UNIT in *. nia.
Qed.

End SIM.

End RC__2.
