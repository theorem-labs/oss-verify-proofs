(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Bool.
From Stdlib Require Lia.
From Stdlib Require Permutation.
From stdpp Require gmap.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require STree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Malloc.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MallocCtrl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require KInv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require KStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MEX_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Inv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Cnt.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Ext.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Pres1.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Pres4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_WFree2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_WEnframe2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Contracts.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_WSlot2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Realloc.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_WRemap.
Module MI_WRemap2.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KInv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_defs.MI_Tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Inv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Cnt.MI_Arith OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Ext.MI_List OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres1.MI_Geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Ext OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4.MI_Ext2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4.MI_Shadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4.MI_Pres2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WFree2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WEnframe2.MI_WGroup OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WEnframe2.MI_TF2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Contracts.MI_WMalloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WEnframe2.MI_WEnframe OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WEnframe2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WSlot2.MI_Ledger OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Contracts.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WRemap.MI_WRealloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WRemap.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Local Open Scope Z_scope.
Import Realloc.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma inv_S_perm X st BL BL' : Permutation BL BL' -> inv_S X st BL -> inv_S X st BL'.
Proof.
  intros P I. destruct I as [S1 S2 S3 S4 S5 S6]; constructor; auto.
  - intros b m ai i Hb Hi. pose proof (S3 b m ai i Hb Hi) as O. cbv zeta in O |- *.
    assert (E : forall s, In s (map bslot BL') <-> In s (map bslot BL)).
    { intros s. split; intros H; [eapply Permutation_in; [apply Permutation_map; apply Permutation_sym; exact P| exact H]
                                  | eapply Permutation_in; [apply Permutation_map; exact P| exact H]]. }
    unfold one5 in O |- *. rewrite !E. exact O.
  - assert (HP : Permutation (map bslot BL) (map bslot BL')) by (apply Permutation_map; exact P). rewrite <- HP. exact S5.
  - intros k Hk. apply S6. eapply Permutation_in; [apply Permutation_sym; exact P| exact Hk].
Qed.

Lemma inv_SH_perm st BL BL' : Permutation BL BL' -> inv_SH st BL -> inv_SH st BL'.
Proof.
  intros P I. destruct I as [H1 H2 H3 H4 H5 H6]; constructor; auto.
  intros k m i Hk Hs. apply (H6 k m i); [| exact Hs]. eapply Permutation_in; [apply Permutation_sym; exact P| exact Hk].
Qed.

Lemma INVL_perm X st L BL BL' LS : Permutation BL BL' -> INVL X st L BL LS -> INVL X st L BL' LS.
Proof.
  intros P (IR & IA & IM & IL & IG & IS & ISH).
  split; [exact IR|]. split; [exact IA|]. split; [exact IM|]. split; [exact IL|]. split; [exact IG|].
  split; [exact (inv_S_perm _ _ _ _ P IS)| exact (inv_SH_perm _ _ _ P ISH)].
Qed.

(* [comment removed for export] *)
Fixpoint bl_replace (c : cptr) (k : blk) (l : list blk) : list blk :=
  match l with
  | [] => []
  | b :: l' => if aptr_eqb (bslot b) c then k :: l' else b :: bl_replace c k l'
  end.

Lemma bl_replace_map c k l : bslot k = c -> In c (map bslot l) -> map bslot (bl_replace c k l) = map bslot l.
Proof.
  intros Ek. induction l as [|b l IH]; intros Hin; [destruct Hin|]. cbn.
  destruct (aptr_eqb_spec (bslot b) c) as [E|NE]; cbn; [rewrite Ek, E; reflexivity|].
  f_equal. apply IH. destruct Hin as [H|H]; [exfalso; exact (NE H)| exact H].
Qed.

Lemma bl_replace_perm c k l : In c (map bslot l) -> Permutation (k :: bl_remove c l) (bl_replace c k l).
Proof.
  induction l as [|b l IH]; intros Hin; [destruct Hin|]. cbn.
  destruct (aptr_eqb_spec (bslot b) c) as [E|NE]; [apply Permutation_refl|].
  eapply Permutation_trans; [apply perm_swap|]. apply perm_skip. apply IH. destruct Hin as [H|H]; [exfalso; exact (NE H)| exact H].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition L_remapR (L : mled) (base d nn : Z) : mled := set_groups ((d, nn) :: g_remove base (ld_groups L)) L.

Section REMAP.
Variables (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (c : cptr) (off sz n : Z) (g : aptr) (idx : Z) (d nn : Z).
Hypothesis INV : INVL x0 st L BL LS.
Hypothesis Hk : In ((c, off), sz) BL.
Hypothesis Hn : 0 <= n.
Hypothesis Hs : s_slots st !! c = Some (g, idx).
Hypothesis Hsc : 48 <= m_sizeclass (MR st g).
Hypothesis Hd : 0 < d.
Hypothesis Hda : d mod PGSZ = 0.
Hypothesis Hnn2 : 2 * PGSZ <= nn.
Hypothesis Hnna : nn mod PGSZ = 0.
Hypothesis HnnM : nn < LEN_MAX.
Hypothesis Hce : d + nn <= alloc_ceiling.
Hypothesis Hfree : forall q rq, s_regions st !! q = Some rq -> q <> fst c ->
  d + nn <= fst (region_live_range rq) \/ fst (region_live_range rq) + snd (region_live_range rq) <= d.
Hypothesis Hfit : UNIT * off + n <= nn - UNIT - IB.
Hypothesis RS : nn - UNIT - IB - UNIT * off - n < 2^32.

Let up : aptr := aadd c (UNIT * off).
Let rid := fst c.
Let b : aptr := (rid, 0).

Let IR := proj1 INV.
Let IM := proj1 (proj2 (proj2 INV)).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))).
Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).
Let ISH := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

Let st1 := set_tick (N.succ (s_tick st)) st.
Let X1 := mkX [] [] (Some c) None None.
Let BL1 := bl_remove c BL.

Lemma rm_INV1 : INVL x0 st1 L BL LS.
Proof. apply INVL_set_tick; [cbn; lia| exact INV]. Qed.

Lemma rm_TF0 : TF0 st1.
Proof. apply TF0_tick_new; [exact (TKS_of _ _ _ _ _ INV)| cbn; lia]. Qed.

Lemma rm_INV_removed : INVL X1 st1 L BL1 LS.
Proof.
  apply (INVL_remove_block x0 st1 st1 L BL LS ((c, off), sz) rm_INV1 Hk eq_refl (ctrl_eq_refl _) eq_refl).
  - intros; reflexivity.
  - exact (DOMS_of _ _ _ _ _ rm_INV1).
  - exact (TKS_of _ _ _ _ _ rm_INV1).
Qed.

(* [comment removed for export] *)
Lemma rm_group : exists ai, s_groups st !! b = Some (mkGhdr (Some g) ai) /\ idx = 0 /\ m_mem (MR st g) = Some b
  /\ exists r, s_regions st !! rid = Some r /\ r_kind r = RKGroup /\ conc st b = r_base r.
Proof.
  clear Hn Hd Hda Hnn2 Hnna HnnM Hce Hfree Hfit RS.
  destruct (is_valid _ _ _ IS _ _ _ Hs) as ([b' Hb'] & Hi & Ec).
  destruct (g63 x0 st L BL LS INV g b' Hb' Hsc) as (E63 & L0 & ML & NL).
  destruct (hosts_ok _ _ _ IG _ _ Hb') as (ai & Hg & GO).
  destruct (g_top _ _ _ _ _ _ GO ML) as (Hsnd & r & Hr & Kr & _).
  rewrite (slot_start'_eq _ _ _ IM _ _ _ Hb') in Ec.
  assert (Eb : b' = b).
  { unfold b, rid. rewrite Ec. cbn [fst]. destruct b' as [q o]. cbn [fst snd] in Hsnd |- *. rewrite Hsnd. reflexivity. }
  subst b'. exists ai. split; [exact Hg|]. split; [lia|]. split; [exact (hosts_mem _ _ _ IM _ _ Hb')|].
  exists r. split; [exact Hr|]. split; [exact Kr|]. unfold conc, get_region. unfold b in Hr |- *. cbn [fst snd] in Hr |- *. rewrite Hr. lia.
Qed.

Theorem rr_remap_INVL : exists r,
  s_regions st !! rid = Some r /\ r_kind r = RKGroup /\ conc st b = r_base r /\ m_mem (MR st g) = Some b /\ idx = 0
  /\ INVL x0 (rr_remap_full st c up n d nn) (L_remapR L (r_base r) d nn) (((c, off), n) :: bl_remove c BL) LS.
Proof.
  destruct rm_group as (ai & Hg & -> & Hmem & r & Hr & Kr & Hconc).
  exists r. split; [exact Hr|]. split; [exact Kr|]. split; [exact Hconc|]. split; [exact Hmem|]. split; [reflexivity|].
  pose proof rm_INV_removed as INV1. pose proof rm_TF0 as TF.
  assert (Hgb1 : s_groups st1 !! b = Some (mkGhdr (Some g) ai)) by exact Hg.
  assert (Hs1 : s_slots st1 !! c = Some (g, 0)) by exact Hs.
  assert (Hsc1 : 48 <= m_sizeclass (MR st1 g)) by exact Hsc.
  assert (Hr1 : s_regions st1 !! rid = Some r) by exact Hr.
  assert (Hnn : PGSZ <= nn) by (unfold PGSZ in *; lia).
  assert (Hfree1 : forall q rq, s_regions st1 !! q = Some rq -> q <> rid ->
            d + nn <= fst (region_live_range rq) \/ fst (region_live_range rq) + snd (region_live_range rq) <= d) by exact Hfree.
  pose proof (pa_facts st1 L BL1 LS c g ai r d nn INV1 TF Hgb1 Hs1 Hsc1 Hr1 Hd Hda Hnn Hnn2 Hnna HnnM Hce Hfree1)
    as (INVA & MRg & STR & SST & GBR & F6 & Ec & PL & SL5 & GR5 & TK5 & KLOW & COLD & E63 & L0).
  fold rid in Ec, GBR, KLOW, COLD.
  set (s5 := pa_s5 st1 c g d nn) in *.
  assert (Hs5 : s_slots s5 !! c = Some (g, 0)) by (rewrite SL5; exact Hs1).
  assert (Hg5 : s_groups s5 !! b = Some (mkGhdr (Some g) ai)) by (rewrite GR5; exact Hgb1).
  assert (Hi5 : 0 <= 0 <= m_last_idx (MR s5 g)) by (rewrite MRg, F6, L0; lia).
  assert (Ec5 : c = (fst b, sstart (MR s5 g) 0)).
  { rewrite MRg, SST. unfold b. cbn [fst]. replace (UNIT + (nn - UNIT) * 0) with UNIT by lia. exact Ec. }
  destruct (is_blocks _ _ _ IS _ Hk) as (m' & i' & Hs' & Ho & Hsz & _). cbn [bslot boff bsize fst snd] in Hs', Ho, Hsz.
  assert (Hfit5 : UNIT * off + n <= get_stride (MR s5 g) - IB) by (rewrite MRg, STR; lia).
  assert (S16 : 16 <= get_stride (MR s5 g)) by (rewrite MRg, STR; unfold PGSZ, UNIT in *; lia).
  assert (SM : get_stride (MR s5 g) mod 16 = 0).
  { rewrite MRg, STR. unfold PGSZ, UNIT in *. rewrite <- Zminus_mod_idemp_l.
    replace (nn mod 16) with 0; [reflexivity|]. symmetry.
    pose proof (Z_div_mod_eq_full nn 4096). replace nn with ((nn / 4096) * 256 * 16) by lia. apply Z_mod_mult. }
  assert (RS5 : get_stride (MR s5 g) - IB - UNIT * off - n < 2^32) by (rewrite MRg, STR; lia).
  (* [comment removed for export] *)
  destruct (ish_blk _ _ ISH ((c, off), sz) g 0 Hk Hs) as (K4 & _ & K2 & K1 & HQ & _). cbn [bslot boff bsize fst snd] in K4, K2, K1, HQ.
  fold rid in K4, K2, K1.
  pose proof (hosts_gbase _ _ _ IM _ _ (ex_intro _ ai Hg)) as GB. rewrite GB in K2, K1, HQ. unfold b in K2, K1, HQ. cbn [snd] in K2, K1, HQ.
  assert (GB5 : snd (gbase (MR s5 g)) = 0) by (rewrite MRg, GBR; reflexivity).
  assert (Ec2 : snd c = UNIT) by (rewrite Ec; reflexivity).
  assert (LOW : forall x, snd c + UNIT * off - 4 <= x <= snd c + UNIT * off - 1 -> 0 <= x < pa_len st1 g nn /\ x <> nn - IB).
  { intros x Hx. rewrite Ec2 in Hx. unfold PGSZ, UNIT, IB in *. lia. }
  assert (K4' : known s5 (rid, snd c + UNIT * off - 4) 0).
  { apply KLOW; [apply LOW; lia| apply LOW; lia| exact K4]. }
  assert (K2' : known s5 (rid, snd c + UNIT * off - 2) (byte_of ((snd c + UNIT * off - snd (gbase (MR s5 g)) - UNIT) / UNIT) 0)).
  { rewrite GB5. apply KLOW; [apply LOW; lia| apply LOW; lia| exact K2]. }
  assert (K1' : known s5 (rid, snd c + UNIT * off - 1) (byte_of ((snd c + UNIT * off - snd (gbase (MR s5 g)) - UNIT) / UNIT) 1)).
  { rewrite GB5. apply KLOW; [apply LOW; lia| apply LOW; lia| exact K1]. }
  assert (HQ5 : 0 <= (snd c + UNIT * off - snd (gbase (MR s5 g)) - UNIT) / UNIT < 2^16) by (rewrite GB5; exact HQ).
  assert (OLD : forall o v t, r_cells (get_shadow s5 (fst c)) !! o = Some (v, t) ->
                snd (aadd c (UNIT * off)) <= o < snd (aadd c (UNIT * off)) + n -> (t < s_tick s5)%N).
  { intros o v t Hc Ho'. unfold aadd in Ho'. cbn [snd] in Ho'. fold rid in Hc. rewrite TK5.
    apply (COLD o v t Hc). rewrite Ec2 in Ho'. unfold UNIT, IB in *. lia. }
  pose proof (ss_INVL s5 (L_remapR L (r_base r) d nn) BL1 LS c off n g b 0 ai INVA Hs5 Hg5 Hi5 Ec5 Ho Hn Hfit5 S16 SM RS5 OLD K4' K2' K1' HQ5) as FIN.
  (* [comment removed for export] *)
  assert (E : rr_remap_full st c up n d nn = ss_final s5 c off n g 0).
  { unfold rr_remap_full. rewrite Hs. cbv zeta. rewrite Hmem. cbn [default from_option id].
    unfold ss_final. rewrite set_size_i_eq. fold rid. fold st1.
    assert (EE : aadd b (nn - IB) = aadd c (get_stride (MR s5 g) - IB)).
    { rewrite MRg, STR. unfold aadd, b. rewrite Ec. cbn [fst snd]. f_equal. lia. }
    rewrite <- EE. subst s5. unfold pa_s5, pa_s4, pa_s3, pa_s2, pa_len. reflexivity. }
  rewrite E. exact FIN.
Qed.
End REMAP.


End CeilWrap.
(* [comment removed for export] *)
Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).
End MI_WRemap2.

(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import State.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Decode NodesSound.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require KRaw.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KRaw.ImplSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import STree Malloc MallocCtrl Prog KInv KStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MEX_defs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_defs.MI_Tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import MI_Inv MI_Kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Pres1.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres1.MI_Geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Ext.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Ext.MI_List.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import MI_Ext MI_Contracts.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Realloc.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import KRaw.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require KB_ReallocM.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KB_ReallocM.KB_Realloc.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require KB_ReallocM.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KB_ReallocM.KRawR.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import KB_ReallocM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_WRemap.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WRemap.MI_WRealloc.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import MI_WRemap.
Import MI_WRemap2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Local Open Scope Z_scope.
Import Realloc.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).

Lemma ranges_free_regions st a n q rq :
  ranges_free (live_ranges st) a n = true -> s_regions st !! q = Some rq ->
  a + n <= fst (region_live_range rq) \/ fst (region_live_range rq) + snd (region_live_range rq) <= a.
Proof.
  intros RF Hq. unfold ranges_free in RF. rewrite forallb_forall in RF.
  specialize (RF (region_live_range rq)).
  assert (Hin : In (region_live_range rq) (live_ranges st)).
  { unfold live_ranges. apply in_or_app. right. apply in_map_iff. exists (q, rq). split; [reflexivity|].
    apply (proj1 (list_elem_of_In _ _)). apply elem_of_map_to_list. exact Hq. }
  specialize (RF Hin). unfold iv_disjoint in RF. apply Bool.orb_true_iff in RF.
  destruct RF as [RF|RF]; apply Z.leb_le in RF; lia.
Qed.

Lemma live_range_pos X st L BL LS q rq : INVL X st L BL LS -> s_regions st !! q = Some rq -> 0 < snd (region_live_range rq).
Proof.
  intros INV Hq. pose proof (ir_shape _ _ _ (proj1 INV) _ _ Hq) as (S1 & S2 & S3 & S4 & S5 & S6).
  pose proof (MI_WFree2.round_up_ge (r_len rq)).
  unfold region_live_range. destruct (r_kind rq) eqn:K; cbn [fst snd]; try lia.
  destruct (S6 ltac:(left; exact K)) as [_ H2]. unfold PGSZ in *. lia.
Qed.

Theorem rr_remap_facts_proof : rr_remap_facts.
Proof.
  intros cs L c A n rid g base on nn d SR Hc Hn HA EP Hne Hd Hda Hce HF.
  pose proof (rr_plan_facts_proof cs L c A n SR Hc Hn HA) as PF. rewrite EP in PF. destruct PF as (_ & HnnM & Hnna).
  destruct SR as (st & BL & LS & <- & INV & LIVE).
  rewrite LIVE in Hc. destruct (In_bslot _ _ Hc) as (off & sz & Hk).
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  destruct (is_blocks _ _ _ IS _ Hk) as (g0 & idx & Hs & Ho & Hsz & Hfit0). cbn [bslot boff bsize fst snd] in Hs, Ho, Hsz, Hfit0.
  (* [comment removed for export] *)
  unfold rplan_of in EP. rewrite s_slots_strip, Hs, !get_meta_rec_strip, !conc_strip in EP. fold (MR st g0) in EP.
  destruct ((n <=? get_stride (MR st g0) - IB - (A - conc st c)) && (n <? MMAP_THRESHOLD) && (m_sizeclass (MR st g0) <=? size_to_class n + 1)); [discriminate|].
  destruct (Z.leb_spec 48 (m_sizeclass (MR st g0))) as [Hsc|Hsc]; [| discriminate].
  destruct (Z.leb_spec MMAP_THRESHOLD n) as [Hth|Hth]; [| discriminate]. cbn [andb] in EP.
  destruct (m_sizeclass (MR st g0) =? 63); [| discriminate]. cbn [negb] in EP.
  destruct (m_mem (MR st g0)) as [b0|] eqn:Hmem; [| discriminate].
  injection EP as Erid Eg Ebase Eon Enn. subst g0. subst rid base on.
  specialize (HA g idx ltac:(rewrite s_slots_strip; exact Hs)). rewrite get_meta_rec_strip, conc_strip in HA. fold (MR st g) in HA.
  destruct (rr_needed_facts n (A - conc st c) ltac:(lia) ltac:(lia)) as (N1 & N2 & N3). rewrite Enn in N1, N2, N3.
  (* [comment removed for export] *)
  set (n' := nn - UNIT - IB - UNIT * off).
  assert (Hn' : 0 <= n') by (subst n'; unfold MMAP_THRESHOLD, UNIT, IB in *; lia).
  assert (Hnn2 : 2 * PGSZ <= nn) by (unfold MMAP_THRESHOLD, PGSZ, UNIT, IB in *; lia).
  assert (Hfree : forall q rq, s_regions st !! q = Some rq -> q <> fst c ->
            d + nn <= fst (region_live_range rq) \/ fst (region_live_range rq) + snd (region_live_range rq) <= d).
  { intros q rq Hq NE. pose proof (live_range_pos _ _ _ _ _ q rq INV Hq) as LP.
    destruct HF as [[-> HG]|HM].
    - (* [comment removed for export] *)
      destruct (rm_group st L BL LS c g idx INV Hs Hsc) as (ai & Hg & _ & HmemX & r & Hr & Kr & Hconc). rename HmemX into Hmem'.
      rewrite Hmem in Hmem'. injection Hmem' as ->. rewrite conc_strip in *. rewrite Hconc in *.
      destruct (g63 x0 st L BL LS INV g (fst c, 0) (ex_intro _ ai Hg) Hsc) as (E63 & L0 & ML & NL).
      destruct (g_top _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Hg) ML) as (_ & r' & Hr' & _ & Hlen & _). cbn [fst] in Hr'.
      rewrite Hr in Hr'. injection Hr' as <-.
      pose proof (ir_disj _ _ _ IR q (fst c) rq r Hq Hr NE) as D. unfold region_live_range in D at 2. rewrite Kr in D.
      rewrite <- Hlen in D.
      destruct (Z.lt_ge_cases (m_maplen (MR st g) * 4096) nn) as [Hlt|Hge].
      + pose proof (ranges_free_regions st _ _ q rq (HG Hlt) Hq) as D2.
        destruct (region_live_range rq) as [x l]. cbn [fst snd] in *. lia.
      + destruct (region_live_range rq) as [x l]. cbn [fst snd] in *. lia.
    - exact (ranges_free_regions st d nn q rq HM Hq). }
  assert (Hfit : UNIT * off + n' <= nn - UNIT - IB) by (subst n'; lia).
  assert (RS : nn - UNIT - IB - UNIT * off - n' < 2^32) by (subst n'; lia).
  destruct (rr_remap_INVL st L BL LS c off sz n' g idx d nn INV Hk Hn' Hs Hsc Hd Hda Hnn2 ltac:(unfold PGSZ; exact Hnna) (proj2 HnnM) Hce Hfree Hfit RS)
    as (r & Hr & Kr & Hconc & Hmem' & -> & INV').
  rewrite Hmem in Hmem'. injection Hmem' as ->. cbn [fst].
  rewrite conc_strip, Hconc.
  exists (rr_remap_full st c (aadd c (UNIT * off)) n' d nn), (bl_replace c ((c, off), n') BL), LS.
  split; [| split].
  - rewrite strip_rr_remap_full, Hs. reflexivity.
  - apply (INVL_perm x0 _ _ (((c, off), n') :: bl_remove c BL)).
    + apply bl_replace_perm. rewrite <- LIVE. rewrite LIVE. apply in_map_iff. exists ((c, off), sz). split; [reflexivity| exact Hk].
    + exact INV'.
  - rewrite ld_live_L_remap, LIVE. symmetry. apply bl_replace_map; [reflexivity|]. apply in_map_iff. exists ((c, off), sz). split; [reflexivity| exact Hk].
Qed.

(* [comment removed for export] *)
Theorem raw_realloc_etwf_closed : forall X s mo (p : bptr) A n,
  AOWN X s mo -> In (fst p) X -> 0 <= n < 2^32 -> addr_in_slot (ps_m s) (fst p) A ->
  etwf (raw_realloc p A n s) mo (fun q mo' => raw_realloc_post X s mo (fst p) (fst q) (snd q) mo').
Proof. exact (raw_realloc_etwf rr_plan_facts_proof rr_remap_facts_proof). Qed.


End CeilWrap.
(* [comment removed for export] *)
Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).
