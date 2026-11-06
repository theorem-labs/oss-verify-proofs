(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation Classical_Prop.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep Bytes Walk Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MRep MRepAux.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require W_rejt8.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallmv3.Mallm24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.W_rejt8.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require STree Malloc Mall7vg KInv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_List.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Inv MI_Kit MI_Arith MI_Geom MI_List MI_Ext MI_S421.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_WFree.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_WFree MI_Ws22 MI_Wp9i MI_Cnt.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Ccma.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Ccma.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Ccma.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Ccma.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.STree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malloc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall7vg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_List.MI_Tree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Kit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Arith OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Geom OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_List OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ext OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_S421 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres2.MI_Pres1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WFree.MI_Read OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WFree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ws22 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Wp9i OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Cnt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_TF2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_Wj0q OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_W9kq OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_Wkfj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma one5_iff3 A B C C' D E : (C <-> C') -> one5 A B C D E -> one5 A B C' D E.
Proof. unfold one5. intros HC H. tauto. Qed.

Section CEIL.
Context {Clg : Ceiling} {Rr : MRep.RunRandom}.  (* [comment removed for export] *)

Lemma INVL_perm X st L BL BL' LS : Permutation BL BL' -> INVL X st L BL LS -> INVL X st L BL' LS.
Proof.
  intros P (IR & IA & IM & IL & IG & IS & ISH).
  assert (PM : Permutation (map bslot BL) (map bslot BL')) by (apply Permutation_map; exact P).
  assert (INP : forall k, In k BL' <-> In k BL).
  { intros k. split; intros H; [eapply Permutation_in; [apply Permutation_sym; exact P| exact H]| eapply Permutation_in; [exact P| exact H]]. }
  assert (INS : forall s, In s (map bslot BL) <-> In s (map bslot BL')).
  { intros s. split; intros H; [eapply Permutation_in; [exact PM| exact H]| eapply Permutation_in; [apply Permutation_sym; exact PM| exact H]]. }
  split; [exact IR|]. split; [exact IA|]. split; [exact IM|]. split; [exact IL|]. split; [exact IG|]. split.
  - destruct IS as [S1 S2 S3 S4 S5 S6]. constructor.
    + exact S1.
    + exact S2.
    + intros b m ai i Hb Hi. apply (one5_iff3 _ _ _ _ _ _ (INS _)). exact (S3 b m ai i Hb Hi).
    + exact S4.
    + apply NoDup_ListNoDup. eapply Permutation_NoDup; [exact PM|]. apply NoDup_ListNoDup. exact S5.
    + intros k Hk. apply S6. apply INP. exact Hk.
  - apply (inv_SH_incl st BL); [intros k Hk; apply INP; exact Hk| exact ISH].
Qed.

End CEIL.

(* [comment removed for export] *)
Definition bl_resize (c : cptr) (n' : Z) (BL : list blk) : list blk :=
  map (fun k => if aptr_eqb (bslot k) c then ((bslot k, boff k), n') else k) BL.

Lemma bl_resize_slots c n' BL : map bslot (bl_resize c n' BL) = map bslot BL.
Proof. unfold bl_resize. rewrite map_map. apply map_ext. intros [[s o] z]. cbn. destruct (aptr_eqb s c); reflexivity. Qed.

Lemma bl_resize_perm BL (c : cptr) off old n' :
  NoDup (map bslot BL) -> In ((c, off), old) BL ->
  Permutation (((c, off), n') :: bl_remove c BL) (bl_resize c n' BL).
Proof.
  intros ND Hk.
  destruct (bl_remove_split BL ((c, off), old) ND Hk) as (l1 & l2 & EBL & EBL' & M1 & M2). cbn [bslot fst] in EBL', M1, M2.
  rewrite EBL', EBL. unfold bl_resize. rewrite map_app. cbn [map bslot fst]. rewrite aptr_eqb_refl. cbn [boff fst snd].
  assert (ID : forall l, ~ In c (map bslot l) -> map (fun k : blk => if aptr_eqb (bslot k) c then ((bslot k, boff k), n') else k) l = l).
  { intros l Hl. induction l as [|x l IH]; [reflexivity|]. cbn. cbn in Hl.
    destruct (aptr_eqb_spec (bslot x) c) as [E|NE]; [exfalso; apply Hl; left; exact E|]. rewrite IH by tauto. reflexivity. }
  rewrite (ID l1 M1), (ID l2 M2). apply Permutation_middle.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section INPLACE.
Context {Clg : Ceiling} {Rr : MRep.RunRandom}.  (* [comment removed for export] *)
Variables (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (c : cptr) (off old : Z) (g bm : aptr) (i : Z) (n' b3 : Z).
Let k : blk := ((c, off), old).
Hypothesis INV : INVL x0 st L BL LS.
Hypothesis Hk : In k BL.
Hypothesis SL : s_slots st !! c = Some (g, i).
Hypothesis Hg : hosts st bm g.
Hypothesis Hi : 0 <= i <= m_last_idx (MR st g).
Hypothesis Ec : c = (fst bm, sstart (MR st g) i).
Hypothesis Hoff : 0 <= off <= 255.
Hypothesis Hn : 0 <= n'.
Let stride := get_stride (MR st g).
Hypothesis Hfit : UNIT * off + n' <= stride - IB.
Hypothesis Hres : stride - IB - UNIT * off - n' < 2 ^ 32.
Hypothesis B3 : Z.land b3 31 = i.
Hypothesis B3R : 0 <= b3 < 256.
(* [comment removed for export] *)
Let pp : aptr := aadd c (UNIT * off).
Let ee : aptr := aadd c (stride - IB).
Let q : Z := (snd pp - (snd bm + UNIT)) / UNIT.
Hypothesis K4 : known st (fst c, snd pp - 4) 0.
Hypothesis K2 : known st (fst c, snd pp - 2) (byte_of q 0).
Hypothesis K1 : known st (fst c, snd pp - 1) (byte_of q 1).
Hypothesis QR : 0 <= q < 2 ^ 16.

Let IM := proj1 (proj2 (proj2 INV)).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))).
Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).
Let ISH := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

Definition st0 : mstate := set_tick (N.succ (s_tick st)) st.
Definition resv : Z := snd ee - snd pp - n'.
Definition r5 : Z := if 5 <=? resv then 5 else resv.
(* [comment removed for export] *)
Definition RL : list (aptr * Z) :=
  (if negb (resv =? 0) then [(aadd ee (- resv), 0)] else [])
  ++ (if 5 <=? resv then [(aadd ee (-5), 0); (aadd ee (-4), resv); (aadd (aadd ee (-4)) 1, Z.shiftr resv 8);
                         (aadd (aadd ee (-4)) 2, Z.shiftr resv 16); (aadd (aadd ee (-4)) 3, Z.shiftr resv 24)] else [])
  ++ [(aadd pp (-3), Z.land b3 31 + Z.shiftl r5 5)].
Definition stw : mstate := wrs RL st0.
Definition stf : mstate := havoc pp n' stw.

Lemma ip_stride : 16 <= stride /\ stride mod 16 = 0.
Proof. pose proof (stride_ge _ _ _ IG _ _ Hg) as [A B]. unfold UNIT in *. split; assumption. Qed.
Lemma ip_gbase : gbase (MR st g) = bm. Proof. exact (hosts_gbase _ _ _ IM _ _ Hg). Qed.
Lemma resv_eq : resv = stride - IB - UNIT * off - n'.
Proof. unfold resv, ee, pp, aadd. cbn [snd]. lia. Qed.
Lemma resv_nonneg : 0 <= resv. Proof. rewrite resv_eq. unfold UNIT, IB in *. lia. Qed.
Lemma pp16 : snd pp mod 16 = 0.
Proof.
  pose proof (sstart_res x0 st L BL LS INV bm g i Hg) as R. unfold pp, aadd. rewrite Ec. cbn [snd]. unfold IB, UNIT in *.
  pose proof (Z.div_mod (sstart (MR st g) i - 4) 16 ltac:(lia)). pose proof (Z.div_mod (sstart (MR st g) i) 16 ltac:(lia)).
  pose proof (Z.mod_pos_bound (sstart (MR st g) i) 16 ltac:(lia)).
  replace (sstart (MR st g) i + 16 * off) with ((sstart (MR st g) i / 16 + off) * 16) by lia. apply Z_mod_mult.
Qed.
Lemma ip_NH : s_groups st !! c = None.
Proof.
  destruct Hg as [ai Hb]. pose proof (is_part _ _ _ IS _ _ _ i Hb Hi) as P5. cbn zeta in P5.
  rewrite (slot_start'_eq _ _ _ IM _ _ i (ex_intro _ ai Hb)), <- Ec in P5.
  destruct (s_groups st !! c) eqn:E; [| reflexivity]. exfalso.
  assert (U : In c (map bslot BL)) by (change c with (bslot k); apply in_map; exact Hk).
  assert (H : s_groups st !! c <> None) by congruence. unfold one5 in P5. tauto.
Qed.

Lemma st0_INVL : INVL x0 st0 L BL LS.
Proof. apply INVL_set_tick; [cbn; lia| exact INV]. Qed.
Lemma st0_TF0 : TF0 st0.
Proof. apply TF0_tick_new; [exact (TKS_of _ _ _ _ _ INV)| cbn; lia]. Qed.
(* [comment removed for export] *)
Lemma st0_ctrl : ctrl_eq st st0. Proof. apply ctrl_eq_set_tick. Qed.
Lemma st0_read r : cell_read (get_shadow st0 (fst r)) (snd r) = cell_read (get_shadow st (fst r)) (snd r).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition X1 : extras := mkX [] [] (Some c) None None.
Lemma st0_INVL1 : INVL X1 st0 L (bl_remove c BL) LS.
Proof.
  pose proof st0_INVL as I0.
  apply (INVL_remove_block x0 st0 st0 L BL LS k I0 Hk eq_refl (ctrl_eq_refl _) eq_refl).
  - intros; reflexivity.
  - exact (DOMS_of _ _ _ _ _ I0).
  - exact (TKS_of _ _ _ _ _ I0).
Qed.

Lemma stw_TKS : TKS stw (s_tick st0).
Proof. unfold stw. apply wrs_TKS; [lia| exact (TKS_of _ _ _ _ _ st0_INVL)]. Qed.
Lemma stw_tick : s_tick stw = s_tick st0. Proof. exact (proj2 (wrs_ctrl RL st0)). Qed.
Lemma stw_ctrl : ctrl_eq st0 stw. Proof. exact (proj1 (wrs_ctrl RL st0)). Qed.
Lemma stw_hav u hl : r_hav (get_shadow stw (fst pp)) !! u = Some hl -> hl_ticks hl (s_tick stw).
Proof. intros Hu ch Hch. rewrite stw_tick. pose proof stw_TKS as TK. rewrite <- stw_tick in TK. rewrite <- stw_tick. exact (proj1 (sh_ticks_of _ _ TK) u hl ch Hu Hch). Qed.
Lemma stf_ctrl : ctrl_eq st0 stf /\ s_tick stf = s_tick st0.
Proof.
  destruct (havoc_ctrl pp n' stw) as [C T]. split; [exact (ctrl_eq_trans _ _ _ stw_ctrl C)| rewrite T; apply stw_tick].
Qed.
Lemma stf_read_out r : ~ (fst r = fst c /\ snd pp <= snd r < snd pp + n') ->
  cell_read (get_shadow stf (fst r)) (snd r) = cell_read (get_shadow stw (fst r)) (snd r).
Proof.
  intros Hr. unfold stf. destruct (Z.eq_dec n' 0) as [N0|NZ]; [rewrite havoc_le0 by lia; reflexivity|].
  apply (cell_read_havoc_out pp n' stw pp16 ltac:(lia) stw_hav). exact Hr.
Qed.

(* [comment removed for export] *)
Lemma RL_addrs a : In a (map fst RL) ->
  fst a = fst c /\ snd c - 3 <= snd a < snd c + stride - 4 /\ ~ (snd pp <= snd a < snd pp + n').
Proof.
  intros Hin. pose proof ip_stride as [S16 _]. pose proof resv_nonneg as R.
  unfold RL in Hin.
  destruct (Z.eqb_spec resv 0) as [R0|R0]; destruct (Z.leb_spec 5 resv) as [R5|R5];
    cbn [negb app map fst In] in Hin; unfold resv, ee, pp, aadd in *; cbn [fst snd] in *; unfold IB, UNIT in *;
    repeat match type of Hin with _ \/ _ => destruct Hin as [<-|Hin] | False => destruct Hin end; cbn [fst snd]; (split; [reflexivity| lia]).
Qed.

Lemma stf_known_w x w : ~ (snd pp <= x < snd pp + n') ->
  lastw RL (fst c, x) None = Some w -> known stf (fst c, x) (Z.land w 255).
Proof.
  intros Hx HL. unfold known, SHd. cbn [fst snd].
  rewrite (stf_read_out (fst c, x)) by (cbn [fst snd]; tauto).
  unfold stw. rewrite (wrs_lastw RL st0 (fst c, x) (TKS_of _ _ _ _ _ st0_INVL)). rewrite HL. reflexivity.
Qed.

Lemma stf_known_old x v : ~ (snd pp <= x < snd pp + n') ->
  lastw RL (fst c, x) None = None -> known st (fst c, x) v -> known stf (fst c, x) v.
Proof.
  intros Hx HL K. unfold known, SHd in *. cbn [fst snd] in *.
  rewrite (stf_read_out (fst c, x)) by (cbn [fst snd]; tauto).
  unfold stw. rewrite (wrs_lastw RL st0 (fst c, x) (TKS_of _ _ _ _ _ st0_INVL)). rewrite HL. rewrite st0_read. exact K.
Qed.

Lemma RL_not_in a : snd pp <= a < snd pp + n' -> ~ In (fst c, a) (map fst RL).
Proof. intros Ha Hin. destruct (RL_addrs _ Hin) as (_ & _ & NR). apply NR. exact Ha. Qed.

Lemma stf_unknown a : snd pp <= a < snd pp + n' -> unknown stf (fst c, a).
Proof.
  intros Ha. unfold unknown, SHd, stf. cbn [fst snd].
  destruct (cell_read_havoc_in pp n' stw pp16 ltac:(lia) stw_hav (fst c, a) eq_refl Ha) as [h Hh]; [| exists h; exact Hh].
  cbn [snd]. intros v tk Hc. unfold stw in Hc. change (fst pp) with (fst c) in Hc. rewrite wrs_cells_other in Hc by (apply RL_not_in; exact Ha).
  rewrite stw_tick.
  destruct (get_shadow_cells_some st0 (fst c) a (v, tk) Hc) as (sh & Hs & Hc').
  exact (st0_TF0 _ _ _ _ _ Hs Hc').
Qed.

(* [comment removed for export] *)
Ltac aeq :=
  match goal with
  | |- context [aptr_eqb ?a ?b] =>
      first [ rewrite (aptr_eqb_neq a b) by (unfold pp, ee, aadd; cbn [fst snd]; intros E; apply (f_equal snd) in E; cbn [snd] in E; unfold IB, UNIT in *; lia)
            | rewrite (proj2 (aptr_eqb_eq a b)) by (unfold pp, ee, aadd; cbn [fst snd]; unfold IB, UNIT in *; f_equal; lia) ]
  end.

Lemma blk_ok : blk_shadow_ok stf ((c, off), n') g i.
Proof.
  pose proof ip_stride as [S16 SM]. pose proof resv_eq as RE. pose proof resv_nonneg as R0.
  pose proof (Z.div_mod stride 16 ltac:(lia)) as SD. rewrite SM, Z.add_0_r in SD.
  destruct stf_ctrl as [CE TK].
  assert (MRE : MR stf g = MR st g).
  { rewrite (MR_ext st0 stf (ce_metas _ _ CE)). reflexivity. }
  destruct Hg as [ai Hb]. pose proof (g_li _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Hb)) as LI.
  unfold blk_shadow_ok. cbn [bslot boff bsize fst snd]. rewrite MRE, ip_gbase. fold stride.
  replace (snd c + stride - IB - (snd c + UNIT * off) - n') with resv by (rewrite RE; lia).
  replace ((snd c + UNIT * off - snd bm - UNIT) / UNIT) with q by (unfold q, pp, aadd; cbn [snd]; f_equal; lia).
  assert (NP : forall x, x < snd pp \/ snd pp + n' <= x -> ~ (snd pp <= x < snd pp + n')) by (intros; lia).
  assert (PP : snd pp = snd c + UNIT * off) by reflexivity.
  assert (EE : snd ee = snd c + stride - IB) by (unfold ee, aadd; cbn [snd]; lia).
  split; [| split; [| split; [| split; [| split; [exact QR| split; [| split]]]]]].
  - (* [comment removed for export] *) rewrite <- PP. replace (snd pp - 4) with (snd pp - 4) by lia.
    apply stf_known_old; [apply NP; lia| | exact K4].
    unfold RL. destruct (Z.eqb_spec resv 0); destruct (Z.leb_spec 5 resv); cbn [negb lastw app]; try (exfalso; lia); repeat aeq; reflexivity.
  - (* [comment removed for export] *)
    replace (i + 32 * Z.min resv 5) with (Z.land (Z.land b3 31 + Z.shiftl r5 5) 255).
    2:{ rewrite B3. unfold r5. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
        destruct (Z.leb_spec 5 resv).
        - rewrite Z.min_r by lia. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. rewrite Z.mod_small; lia.
        - rewrite Z.min_l by lia. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. rewrite Z.mod_small; lia. }
    rewrite <- PP. apply stf_known_w; [apply NP; lia|].
    unfold RL. destruct (Z.eqb_spec resv 0); destruct (Z.leb_spec 5 resv); cbn [negb lastw app]; try (exfalso; lia); repeat aeq; reflexivity.
  - (* [comment removed for export] *) rewrite <- PP. apply stf_known_old; [apply NP; lia| | exact K2].
    unfold RL. destruct (Z.eqb_spec resv 0); destruct (Z.leb_spec 5 resv); cbn [negb lastw app]; try (exfalso; lia); repeat aeq; reflexivity.
  - (* [comment removed for export] *) rewrite <- PP. apply stf_known_old; [apply NP; lia| | exact K1].
    unfold RL. destruct (Z.eqb_spec resv 0); destruct (Z.leb_spec 5 resv); cbn [negb lastw app]; try (exfalso; lia); repeat aeq; reflexivity.
  - (* [comment removed for export] *) intros R5. unfold byte_of. rewrite Z.mul_0_r, Z.shiftr_0_r, Z.mul_1_r.
    assert (RS : resv < 2 ^ 32) by (rewrite RE; exact Hres).
    assert (E5 : (5 <=? resv) = true) by (apply Z.leb_le; exact R5).
    assert (EZ : (resv =? 0) = false) by (apply Z.eqb_neq; lia).
    rewrite <- EE.
    split; [| split; [| split; [| split; [| split; [| exact RS]]]]].
    1-4: apply stf_known_w; [apply NP; rewrite ?EE, ?PP, ?RE; unfold IB, UNIT in *; lia|];
         unfold RL; rewrite E5, EZ; cbn [negb lastw app]; repeat aeq; try reflexivity.
    all: try (change (8 * 2) with 16; reflexivity). all: try (change (8 * 3) with 24; reflexivity).
    apply (stf_known_w _ 0); [apply NP; rewrite ?EE, ?PP, ?RE; unfold IB, UNIT in *; lia|].
    unfold RL; rewrite E5, EZ; cbn [negb lastw app]; repeat aeq; reflexivity.
  - (* [comment removed for export] *) intros RP.
    replace (snd c + stride - IB - resv) with (snd pp + n') by (rewrite RE, PP; lia).
    apply (stf_known_w _ 0); [apply NP; lia|].
    assert (EZ : (resv =? 0) = false) by (apply Z.eqb_neq; lia).
    unfold RL; rewrite EZ. destruct (Z.leb_spec 5 resv); cbn [negb lastw app];
      try (destruct (Z.eq_dec resv 5)); try (exfalso; lia); repeat aeq; reflexivity.
  - (* [comment removed for export] *) intros a Ha. apply stf_unknown. rewrite PP. exact Ha.
Qed.

(* [comment removed for export] *)
Theorem ip_INVL : INVL x0 stf L (bl_resize c n' BL) LS.
Proof.
  destruct stf_ctrl as [CE TK]. pose proof ip_stride as [S16 _].
  pose proof st0_INVL1 as I1.
  assert (SL0 : s_slots st0 !! c = Some (g, i)) by exact SL.
  assert (I2 : INVL x0 stf L (((c, off), n') :: bl_remove c BL) LS).
  { apply (INVL_add_block X1 st0 stf L (bl_remove c BL) LS c off n' I1 eq_refl CE TK).
    - intros m j Hs r Hr. rewrite SL0 in Hs. inversion Hs. subst m j.
      assert (SC : snd c = sstart (MR st g) i) by (rewrite Ec; reflexivity).
      change (MR st0 g) with (MR st g) in Hr. rewrite sstart_succ in Hr. fold stride in Hr. rewrite <- SC in Hr.
      assert (NQ : ~ (fst r = fst c /\ snd pp <= snd r < snd pp + n')).
      { intros [F R]. apply Hr. unfold inT. split; [exact F|]. unfold pp, aadd in R. cbn [snd] in R. try (generalize alloc_ceiling_val); clear - R Hfit Hn Hoff S16; try pose proof alloc_ceiling_val. unfold IB, UNIT in *. lia. }
      rewrite (stf_read_out r NQ). unfold stw. rewrite wrs_read_other; [reflexivity|].
      intros Hin. destruct (RL_addrs r Hin) as (F & R & _). apply Hr. unfold inT. split; [exact F|]. try (generalize alloc_ceiling_val); clear - R; try pose proof alloc_ceiling_val. unfold IB in *. lia.
    - intros rid sh Hsh. assert (REG' : exists r, s_regions st0 !! fst c = Some r /\ r_kind r = RKGroup).
      { rewrite Ec. cbn [fst]. destruct Hg as [ai Hb]. exact (ig_region _ _ _ IG _ _ Hb). }
      revert rid sh Hsh. change (DOMS st0 stf). unfold stf. destruct (Z.eq_dec n' 0) as [N0|NZ].
      + rewrite havoc_le0 by lia. apply wrs_DOMS; [exact (DOMS_of _ _ _ _ _ st0_INVL)|]. intros r Hin. destruct (RL_addrs r Hin) as (F & _). rewrite F. exact REG'.
      + apply DOMS_havoc; [lia| | exact REG']. apply wrs_DOMS; [exact (DOMS_of _ _ _ _ _ st0_INVL)|]. intros r Hin. destruct (RL_addrs r Hin) as (F & _). rewrite F. exact REG'.
    - change (TKS stf (s_tick st0)). unfold stf. destruct (Z.eq_dec n' 0) as [N0|NZ].
      + rewrite havoc_le0 by lia. apply stw_TKS.
      + rewrite <- stw_tick. apply TKS_havoc; [apply pp16| lia| rewrite stw_tick; apply stw_TKS].
    - intros m j Hs. rewrite SL0 in Hs. inversion Hs. subst m j. split; [exact Hoff|]. split; [exact Hn|]. split; [exact Hfit|].
      apply blk_ok. }
  eapply INVL_perm; [| exact I2].
  apply (bl_resize_perm BL c off old n' (is_nodup _ _ _ IS) Hk).
Qed.

Lemma stf_ctrl_st : ctrl_eq st stf /\ s_tick stf = N.succ (s_tick st).
Proof. destruct stf_ctrl as [C T]. split; [exact (ctrl_eq_trans _ _ _ st0_ctrl C)| rewrite T; reflexivity]. Qed.

(* [comment removed for export] *)
Variables (m : word -> option byte) (r : region).
Hypothesis MRP : mrep st m.
Hypothesis TKst : ticks_ok st.
Hypothesis Hr : s_regions st !! (fst bm) = Some r.
Hypothesis Hkr : r_kind r = RKGroup.
Hypothesis B0 : 0 <= snd bm.
Hypothesis SPAN : snd bm + UNIT + stride * (m_last_idx (MR st g) + 1) <= round_up_pg (r_len r).

Lemma ip_NOGRP b' gh : s_groups st !! b' = Some gh -> fst b' = fst bm ->
  snd b' + 16 <= snd c \/ snd c + stride <= snd b' + 4.
Proof.
  intros Hb' Hf.
  assert (HO : exists m', hosts st b' m').
  { destruct gh as [[m'|] ai']; [exists m'; exists ai'; exact Hb'| exfalso; exact (ig_nometa _ _ _ IG _ _ Hb')]. }
  destruct HO as [m' Hm'].
  assert (NH : s_groups st !! (fst bm, sstart (MR st g) i) = None) by (rewrite <- Ec; apply ip_NH).
  pose proof (sep_ghdr x0 st BL LS IM IG IS g bm i Hg Hi NH m' b' Hm' Hf) as SG.
  rewrite sstart_succ in SG. fold stride in SG. rewrite Ec. cbn [snd]. exact SG.
Qed.

Lemma ip_mrep :
  mrep stf (set_size_mem m (r_base r + snd pp) (r_base r + snd ee) n' b3) /\ ticks_ok stf.
Proof.
  pose proof ip_stride as [S16 SM]. pose proof resv_eq as RE. pose proof resv_nonneg as R0.
  pose proof (Z.div_mod stride 16 ltac:(lia)) as SD. rewrite SM, Z.add_0_r in SD.
  assert (SC : snd c = snd bm + 16 + stride * i) by (rewrite Ec; cbn [snd]; unfold sstart; rewrite ip_gbase; reflexivity).
  assert (FC : fst c = fst bm) by (rewrite Ec; reflexivity).
  assert (SI0 : 0 <= stride * i) by (apply Z.mul_nonneg_nonneg; lia).
  assert (SIL : stride * (i + 1) <= stride * (m_last_idx (MR st g) + 1)) by (apply Z.mul_le_mono_nonneg_l; lia).
  assert (EHI : snd c + stride <= round_up_pg (r_len r)) by (rewrite SC; unfold UNIT in SPAN; lia).
  assert (MR0 : mrep st0 m) by (apply mrep_set_tick; exact MRP).
  assert (TK0 : ticks_ok st0) by (apply ticks_ok_set_tick; [cbn; lia| exact TKst]).
  (* [comment removed for export] *)
  assert (W8 : forall stx mx o v, mrep stx mx -> ticks_ok stx -> s_regions stx = s_regions st -> s_groups stx = s_groups st ->
            snd c - 4 <= o < snd c + stride - 4 -> 0 <= v < 256 ->
            mrep (wr8 (fst c, o) v stx) (write_to_mem mx (wa (r_base r + o)) [b8 v]) /\ ticks_ok (wr8 (fst c, o) v stx)).
  { intros stx mx o v MX TX ER EG Ho Hv. split; [| apply ticks_ok_wr8; exact TX].
    apply (mrep_wr8 stx mx (fst c, o) v r MX TX); cbn [fst snd]; [rewrite ER, FC; exact Hr| exact Hkr| lia| | exact Hv].
    intros b' gh Hb' Hf. rewrite EG in Hb'. rewrite FC in Hf. destruct (ip_NOGRP b' gh Hb' Hf); lia. }
  assert (W32 : forall stx mx o v, mrep stx mx -> ticks_ok stx -> s_regions stx = s_regions st -> s_groups stx = s_groups st ->
            snd c - 4 <= o -> o + 4 <= snd c + stride - 4 -> 0 <= v < 2^32 ->
            mrep (wr32 (fst c, o) v stx) (write_to_mem mx (wa (r_base r + o)) (le4 (wz v))) /\ ticks_ok (wr32 (fst c, o) v stx)).
  { intros stx mx o v MX TX ER EG Ho Ho4 Hv.
    apply (mrep_wr32 stx mx (fst c, o) v r MX TX); cbn [fst snd]; [rewrite ER, FC; exact Hr| exact Hkr| lia| lia| | exact Hv].
    intros b' gh Hb' Hf. rewrite EG in Hb'. rewrite FC in Hf. destruct (ip_NOGRP b' gh Hb' Hf); lia. }
  unfold set_size_mem. cbv zeta.
  replace (r_base r + snd ee - (r_base r + snd pp) - n') with resv by (unfold resv; lia).
  unfold stf, stw, RL.
  assert (PPE : snd pp = snd c + UNIT * off) by reflexivity.
  assert (EEE : snd ee = snd c + (stride - IB)) by reflexivity.
  (* [comment removed for export] *)
  replace (aadd ee (- resv)) with (fst c, snd ee - resv) by (unfold ee, aadd; cbn [fst snd]; f_equal; lia).
  replace (aadd ee (-5)) with (fst c, snd ee - 5) by (unfold ee, aadd; cbn [fst snd]; f_equal; lia).
  replace (aadd ee (-4)) with (fst c, snd ee - 4) by (unfold ee, aadd; cbn [fst snd]; f_equal; lia).
  replace (aadd pp (-3)) with (fst c, snd pp - 3) by (unfold pp, aadd; cbn [fst snd]; f_equal; lia).
  replace (r_base r + snd ee - resv) with (r_base r + (snd ee - resv)) by lia.
  replace (r_base r + snd ee - 5) with (r_base r + (snd ee - 5)) by lia.
  replace (r_base r + snd ee - 4) with (r_base r + (snd ee - 4)) by lia.
  replace (r_base r + snd pp - 3) with (r_base r + (snd pp - 3)) by lia.
  assert (LI : 0 <= m_last_idx (MR st g) <= 31).
  { destruct Hg as [ai Hb]. exact (g_li _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Hb)). }
  assert (V3 : forall r5v, 0 <= r5v <= 5 -> 0 <= Z.land b3 31 + Z.shiftl r5v 5 < 256).
  { intros r5v Hr5. rewrite B3, Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32. try (generalize alloc_ceiling_val); clear - Hr5 Hi LI; try pose proof alloc_ceiling_val. lia. }
  assert (FIN : forall stx mx, mrep stx mx -> ticks_ok stx ->
            mrep (havoc pp n' stx) mx /\ ticks_ok (havoc pp n' stx)).
  { intros stx mx MX TX. destruct (Z.eq_dec n' 0) as [N0|NZ]; [rewrite havoc_le0 by lia; split; assumption| exact (mrep_havoc _ _ pp n' MX TX)]. }
  destruct (Z.eqb_spec resv 0) as [RZ|RZ]; destruct (Z.leb_spec 5 resv) as [R5|R5]; try (exfalso; lia); cbn [negb app wrs]; unfold r5.
  - (* [comment removed for export] *)
    rewrite (proj2 (Z.leb_gt 5 resv) ltac:(try (generalize alloc_ceiling_val); clear - RZ R5; try pose proof alloc_ceiling_val; lia)).
    destruct (W8 st0 m (snd pp - 3) (Z.land b3 31 + Z.shiftl resv 5) MR0 TK0 eq_refl eq_refl ltac:(rewrite PPE; unfold IB, UNIT in *; lia) ltac:(apply V3; lia)) as [M3 T3].
    exact (FIN _ _ M3 T3).
  - (* [comment removed for export] *)
    rewrite (proj2 (Z.leb_le 5 resv) R5).
    assert (RS : resv < 2 ^ 32) by (rewrite RE; exact Hres).
    destruct (W8 st0 m (snd ee - resv) 0 MR0 TK0 eq_refl eq_refl ltac:(rewrite EEE; unfold IB, UNIT in *; lia) ltac:(lia)) as [M1 T1].
    destruct (W8 _ _ (snd ee - 5) 0 M1 T1 ltac:(reflexivity) ltac:(reflexivity) ltac:(rewrite EEE; unfold IB, UNIT in *; lia) ltac:(lia)) as [M2 T2].
    destruct (W32 _ _ (snd ee - 4) resv M2 T2 ltac:(reflexivity) ltac:(reflexivity)
                ltac:(rewrite EEE; unfold IB, UNIT in *; lia) ltac:(rewrite EEE; unfold IB; lia) ltac:(lia)) as [M4 T4].
    set (stX := wr8 (fst c, snd ee - 5) 0 (wr8 (fst c, snd ee - resv) 0 st0)) in *.
    change (wr8 (aadd (fst c, snd ee - 4) 3) (Z.shiftr resv 24) (wr8 (aadd (fst c, snd ee - 4) 2) (Z.shiftr resv 16)
              (wr8 (aadd (fst c, snd ee - 4) 1) (Z.shiftr resv 8) (wr8 (fst c, snd ee - 4) resv stX))))
      with (wr32 (fst c, snd ee - 4) resv stX).
    destruct (W8 _ _ (snd pp - 3) (Z.land b3 31 + Z.shiftl 5 5) M4 T4 ltac:(reflexivity) ltac:(reflexivity) ltac:(rewrite PPE; unfold IB, UNIT in *; lia) ltac:(apply V3; lia)) as [M3 T3].
    exact (FIN _ _ M3 T3).
  - (* [comment removed for export] *)
    rewrite (proj2 (Z.leb_gt 5 resv) ltac:(try (generalize alloc_ceiling_val); clear - RZ R5; try pose proof alloc_ceiling_val; lia)).
    destruct (W8 st0 m (snd ee - resv) 0 MR0 TK0 eq_refl eq_refl ltac:(rewrite EEE; unfold IB, UNIT in *; lia) ltac:(lia)) as [M1 T1].
    destruct (W8 _ _ (snd pp - 3) (Z.land b3 31 + Z.shiftl resv 5) M1 T1 ltac:(reflexivity) ltac:(reflexivity) ltac:(rewrite PPE; unfold IB, UNIT in *; lia) ltac:(apply V3; lia)) as [M3 T3].
    exact (FIN _ _ M3 T3).
Qed.

End INPLACE.
