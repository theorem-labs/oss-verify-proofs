(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require STree Malloc Mall7vg KInv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_List.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Inv MI_Kit MI_Arith MI_Geom MI_List MI_Ext MI_WFree MI_Pres4 MI_Ws22 MI_WNtf2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Ccma.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Ccma.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Ccma.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Ccma.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Ccma.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.STree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malloc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall7vg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_List.MI_Tree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Kit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Arith OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Geom OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_List OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ext OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WFree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ws22 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WNtf2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_TF2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_WSlot OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_Wkfj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_Sim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require MRep MRepAux MTree Mall5lv Mallwlb.

Module Mallttr.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require STree Malloc Mall7vg KInv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_List.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Inv MI_Kit MI_Geom MI_Ext MI_Ws22 MI_WNtf2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Ccma.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Ccma.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Ccma.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Ccma.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Ccma.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.STree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malloc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall7vg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_List.MI_Tree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Kit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Geom OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ext OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ws22 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WNtf2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_TF2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_WSlot OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_Wkfj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_Sim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Import MRep MRepAux MTree Mall5lv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.  (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section CEIL.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Theorem areach_inv resv st LB : AREACH_from resv st LB ->
  exists L LS BL, INVL x0 st L BL LS /\ ld_live L = map bslot BL /\ ld_resv L = resv /\ s_secret st = run_secret /\ CORR st LB BL.
Proof. intros H. exact H. Qed.


(* [comment removed for export] *)
Lemma areach_hdr_ok_proof : forall {resv} st LB (blk : block) (off : Z),
  AREACH_from resv st LB -> In blk LB -> 0 <= off -> blk_addr blk = conc st (blk_slot blk) + UNIT * off ->
  hdr_ok pans_mem pupd_mem st (aadd (blk_slot blk) (UNIT * off)) (blk_slot blk).
Proof.
  intros resv st LB blk off AR Hb Ho Ha.
  destruct (areach_inv resv st LB AR) as (L & LS & BL & INV & _ & _ & _ & CR).
  destruct (Forall2_In_l _ _ _ _ CR Hb) as (k & Hk & (C1 & C2 & C3)).
  destruct k as [[c bo] n]. cbn [bslot boff bsize fst snd] in C1, C2, C3. rewrite C1 in Ha |- *.
  assert (off = bo) by (unfold UNIT in *; lia). subst off.
  exact (INVL_hdr_ok pans_mem pupd_mem st L BL LS c bo n INV Hk).
Qed.

End CEIL.
End Mallttr.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mall5lv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallwlb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Malls6g.Mallttr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.  (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma NoDup_map_on {A B} (f : A -> B) (l : list A) :
  (forall x y, In x l -> In y l -> f x = f y -> x = y) -> List.NoDup l -> List.NoDup (map f l).
Proof.
  induction l as [|a l IH]; intros Hinj ND; cbn; [constructor|].
  inversion ND; subst. constructor.
  - intros Hin. apply in_map_iff in Hin. (first [ dex1 Hin as y; destruct Hin as [Ey Hy] | dand3 Hin as y Ey Hy | destruct Hin as (y & Ey & Hy) ]).
    rewrite (Hinj a y ltac:(now left) ltac:(now right) (eq_sym Ey)) in H1. exact (H1 Hy).
  - apply IH; [| assumption]. intros x y Hx Hy. apply Hinj; now right.
Qed.

Lemma NoDup_Z_length (l : list Z) (N : Z) : 0 <= N -> List.NoDup l -> (forall x, In x l -> 0 <= x < N) -> Z.of_nat (length l) <= N.
Proof.
  intros Hn ND HB.
  assert (INCL : incl l (map Z.of_nat (seq 0 (Z.to_nat N)))).
  { intros x Hx. apply in_map_iff. exists (Z.to_nat x). pose proof (HB x Hx). split; [lia|]. apply in_seq. lia. }
  pose proof (NoDup_incl_length ND INCL) as Hlen. rewrite length_map, length_seq in Hlen. lia.
Qed.

Lemma zsum_bound (l : list Z) (K : Z) : (forall x, In x l -> 0 <= x <= K) -> 0 <= zsum l <= K * Z.of_nat (length l).
Proof.
  induction l as [|a l IH]; intros HB; cbn -[Z.of_nat]; [lia|].
  pose proof (HB a ltac:(now left)). specialize (IH ltac:(intros x Hx; apply HB; now right)).
  unfold zsum in IH. rewrite Nat2Z.inj_succ. lia.
Qed.

Section MF.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis INV : INVL X st L BL LS.
Hypothesis ZB : x_zomb X = [].
Hypothesis NFR : x_fresh X = None.

Let IR := proj1 INV. Let IA := proj1 (proj2 INV). Let IM := proj1 (proj2 (proj2 INV)). Let IL := proj1 (proj2 (proj2 (proj2 INV))).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))). Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).
Let ISH := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

(* [comment removed for export] *)
Lemma mem_hosts g b : m_mem (MR st g) = Some b -> hosts st b g.
Proof. intros H. destruct (im_group _ _ _ IM g b H) as [Hh|Hz]; [exact Hh|]. rewrite ZB in Hz. destruct Hz. Qed.

Lemma hosts_GO b g : hosts st b g -> exists ai, s_groups st !! b = Some (mkGhdr (Some g) ai) /\ group_ok X st LS g b ai.
Proof. intros H. exact (hosts_ok _ _ _ IG _ _ H). Qed.

Lemma sstart_of_eq r i : sstart_of r i = sstart r i.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma group_in_region b m : hosts st b m ->
  exists r, s_regions st !! fst b = Some r /\ r_kind r = RKGroup /\ 0 <= snd b /\ gend (MR st m) <= round_up_pg (r_len r).
Proof.
  intros Hm. (first [ pose proof ((hosts_GO _ _ Hm)) as dR_2; dex1 dR_2 as ai; destruct dR_2 as [Hb GO] | pose proof ((hosts_GO _ _ Hm)) as dR_2; dand3 dR_2 as ai Hb GO | destruct (hosts_GO _ _ Hm) as (ai & Hb & GO) ]). pose proof (g_align _ _ _ _ _ _ GO) as [A0 _].
  destruct (Z.eq_dec (m_maplen (MR st m)) 0) as [Z0|NZ].
  - (first [ pose proof ((top_chain _ _ _ _ IM IG IS m b Hm Z0)) as dR_3; dex4 dR_3 as t i c bt; dand4 dR_3 as Ha Ht Htl Hf | pose proof ((top_chain _ _ _ _ IM IG IS m b Hm Z0)) as dR_3; dand8 dR_3 as t i c bt Ha Ht Htl Hf | destruct (top_chain _ _ _ _ IM IG IS m b Hm Z0) as (t & i & c & bt & Ha & Ht & Htl & Hf) ]).
    (first [ pose proof ((anc_box _ _ _ _ IM IG IS m t i c b Ha Hm)) as dR_4; dand3 dR_4 as B1 B2 B3 | destruct (anc_box _ _ _ _ IM IG IS m t i c b Ha Hm) as (B1 & B2 & B3) ]).
    (first [ pose proof ((anc_facts _ _ _ _ IM IG IS m t i c Ha)) as dR_5; dex2 dR_5 as bm bp; dand5 dR_5 as Hm' Hp' _ Hi _ | pose proof ((anc_facts _ _ _ _ IM IG IS m t i c Ha)) as dR_5; dand7 dR_5 as bm bp Hm' Hp' _ Hi _ | destruct (anc_facts _ _ _ _ IM IG IS m t i c Ha) as (bm & bp & Hm' & Hp' & _ & Hi & _) ]).
    pose proof (hosts_inj _ _ _ IM _ _ _ Ht Hp'); subst bp.
    (first [ pose proof ((hosts_GO _ _ Ht)) as dR_6; dex1 dR_6 as ait; destruct dR_6 as [Hbt GOt] | pose proof ((hosts_GO _ _ Ht)) as dR_6; dand3 dR_6 as ait Hbt GOt | destruct (hosts_GO _ _ Ht) as (ait & Hbt & GOt) ]).
    (first [ pose proof ((g_top _ _ _ _ _ _ GOt Htl)) as dR_7; dand6 dR_7 as S0 r Hr Kr ML GE | destruct (g_top _ _ _ _ _ _ GOt Htl) as (S0 & r & Hr & Kr & ML & GE) ]).
    rewrite <- Hf. exists r. split; [exact Hr|]. split; [exact Kr|]. split; [exact A0|].
    pose proof (sstart_mono _ _ _ IG _ _ (i + 1) (m_last_idx (MR st t) + 1) Ht ltac:(lia)) as SM. rewrite <- gend_eq in SM. lia.
  - (first [ pose proof ((g_top _ _ _ _ _ _ GO NZ)) as dR_8; dand6 dR_8 as S0 r Hr Kr ML GE | destruct (g_top _ _ _ _ _ _ GO NZ) as (S0 & r & Hr & Kr & ML & GE) ]). exists r. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; auto. lia.
Qed.

Lemma conc_group b m : hosts st b m -> exists r, s_regions st !! fst b = Some r /\ r_kind r = RKGroup /\
  conc st b = r_base r + snd b /\ r_base r <= conc st b /\ conc st b + 32 <= r_base r + round_up_pg (r_len r).
Proof.
  intros Hm. (first [ pose proof ((group_in_region _ _ Hm)) as dR_9; dex1 dR_9 as r; dand4 dR_9 as Hr Kr A0 GE | pose proof ((group_in_region _ _ Hm)) as dR_9; dand5 dR_9 as r Hr Kr A0 GE | destruct (group_in_region _ _ Hm) as (r & Hr & Kr & A0 & GE) ]). pose proof (gend_ge _ _ _ IM IG _ _ Hm) as G32.
  exists r. unfold conc, get_region. rewrite Hr. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; auto; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma f_ctx : fact_ctx (strip st).
Proof.
  (first [ pose proof ((ia_ctx _ IA)) as dR_10; dand4 dR_10 as C1 C2 C3 C4 | pose proof (ia_ctx _ IA) as (C1 & C2 & C3 & C4) ]). pose proof (ia_secret _ IA) as [S1 S2].
  unfold fact_ctx. rewrite ctx_strip. unfold ctx.
  split; [exact C1|]. split; [destruct S2 as [(_ & E & _)|[_ E]]; rewrite E; lia|].
  split; [destruct S2 as [(E & _)|[E _]]; rewrite E; auto|]. split; [exact C2|].
  split.
  - intros i. unfold bounces, ctx. cbn. destruct (c_bounces (s_ctx st) !! i) as [v|] eqn:E; cbn; [| lia]. exact (proj2 (C3 i v E)).
  - intros i. unfold unmap_seq, ctx. cbn. destruct (c_unmap_seq (s_ctx st) !! i) as [v|] eqn:E; cbn; [| lia]. exact (proj2 (C4 i v E)).
Qed.

Lemma f_active : fact_active (strip st).
Proof.
  intros sc g H. rewrite active_strip in H. rewrite !get_meta_rec_strip. fold (MR st g).
  pose proof (head_listed _ _ _ _ _ INV (LActive sc) g H) as Hin.
  (first [ pose proof ((il_active _ _ IL sc g Hin)) as dR_11; dand3 dR_11 as Hsc [b Hb] Esc | destruct (il_active _ _ IL sc g Hin) as (Hsc & [b Hb] & Esc) ]). split; [exact Hsc|]. split; [exact Esc|].
  rewrite (hosts_mem _ _ _ IM _ _ Hb). discriminate.
Qed.

Lemma f_masks : fact_masks (strip st).
Proof.
  intros g b H. rewrite !get_meta_rec_strip in *. fold (MR st g) in *. cbn zeta.
  (first [ pose proof ((hosts_GO _ _ (mem_hosts _ _ H))) as dR_12; dex1 dR_12 as ai; destruct dR_12 as [Hb GO] | pose proof ((hosts_GO _ _ (mem_hosts _ _ H))) as dR_12; dand3 dR_12 as ai Hb GO | destruct (hosts_GO _ _ (mem_hosts _ _ H)) as (ai & Hb & GO) ]).
  (first [ pose proof ((g_masks _ _ _ _ _ _ GO)) as dR_13; dand6 dR_13 as M1 M2 M3 M4 M5 M6 | pose proof (g_masks _ _ _ _ _ _ GO) as (M1 & M2 & M3 & M4 & M5 & M6) ]). pose proof (g_ai _ _ _ _ _ _ GO) as AI.
  split; [intros i Hi Ha; pose proof (M3 i Hi Ha); lia|]. split; [exact M4|].
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.testbit (m_avail (MR st g)) i) eqn:Ea; destruct (Z.testbit (m_freed (MR st g)) i) eqn:Ef; try reflexivity.
  exfalso. exact (M5 i Hi Ea Ef).
Qed.

Lemma f_maplen : fact_maplen (strip st).
Proof.
  intros g b H. rewrite !get_meta_rec_strip in *. fold (MR st g) in *.
  pose proof (mem_hosts _ _ H) as Hm. (first [ pose proof ((hosts_GO _ _ Hm)) as dR_14; dex1 dR_14 as ai; destruct dR_14 as [Hb GO] | pose proof ((hosts_GO _ _ Hm)) as dR_14; dand3 dR_14 as ai Hb GO | destruct (hosts_GO _ _ Hm) as (ai & Hb & GO) ]).
  destruct (Z.eq_dec (m_maplen (MR st g)) 0) as [->|NZ]; [lia|].
  (first [ pose proof ((g_top _ _ _ _ _ _ GO NZ)) as dR_15; dand6 dR_15 as S0 r Hr Kr ML GE | destruct (g_top _ _ _ _ _ _ GO NZ) as (S0 & r & Hr & Kr & ML & GE) ]).
  (first [ pose proof ((ir_shape _ _ _ IR _ _ Hr)) as dR_16; dand6 dR_16 as B0 _ _ _ CEIL _ | destruct (ir_shape _ _ _ IR _ _ Hr) as (B0 & _ & _ & _ & CEIL & _) ]). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). lia.
Qed.

Lemma f_slots : fact_slots (strip st).
Proof.
  intros p g idx H. rewrite s_slots_strip in H. rewrite !get_meta_rec_strip. fold (MR st g).
  (first [ pose proof ((is_valid _ _ _ IS _ _ _ H)) as dR_17; dand3 dR_17 as [b Hb] Hi Ep | destruct (is_valid _ _ _ IS _ _ _ H) as ([b Hb] & Hi & Ep) ]). exists b. split; [exact (hosts_mem _ _ _ IM _ _ Hb)|].
  rewrite (slot_start'_eq _ _ _ IM _ _ idx Hb) in Ep. rewrite Ep. cbn. rewrite sstart_of_eq. auto.
Qed.

Lemma f_slots_complete : fact_slots_complete (strip st).
Proof.
  intros g b i H Hi. rewrite s_slots_strip. rewrite !get_meta_rec_strip in *. fold (MR st g) in *.
  pose proof (mem_hosts _ _ H) as Hm. rewrite sstart_of_eq, <- (slot_start'_eq _ _ _ IM _ _ i Hm). exact (is_total _ _ _ IS _ _ _ Hm Hi).
Qed.

Lemma f_hdr0 : fact_hdr0 st.
Proof.
  intros g b i H Hi. fold (MR st g) in *. rewrite sstart_of_eq. exact (ish_hdr0 _ _ ISH b g i (mem_hosts _ _ H) ltac:(unfold cnt_of; lia)).
Qed.

Lemma f_cell_ticks : fact_cell_ticks st.
Proof. intros rid sh o v t Hs Hc. exact (proj2 (proj1 (ish_ticks _ _ ISH rid sh Hs) o v t Hc)). Qed.

Lemma f_ticks : ticks_ok st.
Proof.
  split.
  - intros rid sh u hl ch Hs Hu Hin. exact (proj1 (proj2 (ish_ticks _ _ ISH rid sh Hs)) u hl ch Hu Hin).
  - intros rid sh pg t Hs Hp. exact (proj2 (proj2 (ish_ticks _ _ ISH rid sh Hs)) pg t Hp).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma f_gmeta : fact_gmeta (strip st).
Proof.
  intros g b H. rewrite !get_meta_rec_strip in *. fold (MR st g) in *. cbn zeta.
  pose proof (mem_hosts _ _ H) as Hm. (first [ pose proof ((hosts_GO _ _ Hm)) as dR_18; dex1 dR_18 as ai; destruct dR_18 as [Hb GO] | pose proof ((hosts_GO _ _ Hm)) as dR_18; dand3 dR_18 as ai Hb GO | destruct (hosts_GO _ _ Hm) as (ai & Hb & GO) ]).
  (first [ pose proof ((g_masks _ _ _ _ _ _ GO)) as dR_19; dand6 dR_19 as M1 M2 M3 M4 M5 M6 | pose proof (g_masks _ _ _ _ _ _ GO) as (M1 & M2 & M3 & M4 & M5 & M6) ]). pose proof (g_ai _ _ _ _ _ _ GO) as AI.
  pose proof (g_li _ _ _ _ _ _ GO) as LI.
  assert (AV : m_avail (MR st g) < 2 ^ 32).
  { apply bits_below_bound; [exact M1| lia|]. intros i Hi Ht. pose proof (M3 i Hi Ht). lia. }
  assert (FR : m_freed (MR st g) < 2 ^ 32).
  { apply bits_below_bound; [exact M2| lia|]. intros i Hi Ht. pose proof (M4 i Hi Ht). lia. }
  split.
  { (* [comment removed for export] *) pose proof (g_present _ _ _ _ _ _ GO) as Pr. destruct (s_metas st !! g) as [mr|] eqn:Em; [| congruence].
    (first [ pose proof ((ia_metas _ IA _ _ Em)) as dR_20; dex3 dR_20 as a ar ka; dand3 dR_20 as Ha Hka Emk | pose proof ((ia_metas _ IA _ _ Em)) as dR_20; dand6 dR_20 as a ar ka Ha Hka Emk | destruct (ia_metas _ IA _ _ Em) as (a & ar & ka & Ha & Hka & Emk) ]). exists a, ar, ka. rewrite s_areas_strip. split; [exact Ha|]. split; [exact Hka|]. exact Emk. }
  split; [lia|]. split; [lia|]. split; [exact LI|]. split; [exact (g_freeable _ _ _ _ _ _ GO)|].
  pose proof (g_maplen _ _ _ _ _ _ GO) as ML.
  split. { destruct (g_sc _ _ _ _ _ _ GO) as [[S1 S2]|(S1 & S2 & S3 & _)]; [left; lia| right; lia]. }
  split; [exact ML|].
  split. { exists ai. rewrite s_groups_strip. split; [exact Hb|]. split; [exact AI|]. exact M3. }
  split. { (first [ pose proof ((group_in_region _ _ Hm)) as dR_21; dex1 dR_21 as r; dand4 dR_21 as Hr Kr A0 GE | pose proof ((group_in_region _ _ Hm)) as dR_21; dand5 dR_21 as r Hr Kr A0 GE | destruct (group_in_region _ _ Hm) as (r & Hr & Kr & A0 & GE) ]). exists r. rewrite s_regions_strip.
           pose proof (g_align _ _ _ _ _ _ GO) as [_ A16]. split; [exact Hr|]. split; [exact Kr|]. split; [exact A0|]. split; [exact A16|]. rewrite sstart_of_eq. rewrite gend_eq in GE. exact GE. }
  pose proof (stride_ge _ _ _ IG _ _ Hm) as [SG SM].
  split; [exact SG|]. split; [exact SM|].
  pose proof (g_stride _ _ _ _ _ _ GO) as GS.
  split. { intros Hsc. (first [ pose proof ((GS Hsc)) as dR_22; dand3 dR_22 as _ _ LT | destruct (GS Hsc) as (_ & _ & LT) ]). unfold cnt_of in LT. nia. }
  split. { intros Hsc i Hi Ht. destruct (Z.lt_ge_cases (get_stride (MR st g)) (UNIT * size_class (m_sizeclass (MR st g)))) as [LT|GE]; [| lia].
           exfalso. destruct (g_under _ _ _ _ _ _ GO ltac:(rewrite NFR; discriminate) Hsc LT) as [A0 _]. rewrite A0 in Ht. rewrite Z.bits_0 in Ht. discriminate. }
  intros Hsc. (first [ pose proof ((GS Hsc)) as dR_23; dand3 dR_23 as _ _ LT | destruct (GS Hsc) as (_ & _ & LT) ]). unfold cnt_of in LT. lia.
Qed.

(* [comment removed for export] *)
Lemma bit_slot_nonH g b ai i : s_groups st !! b = Some (mkGhdr (Some g) ai) -> 0 <= i <= m_last_idx (MR st g) ->
  (Z.testbit (m_avail (MR st g)) i = true \/ Z.testbit (m_freed (MR st g)) i = true) ->
  s_groups st !! (fst b, sstart (MR st g) i) = None /\ ~ In (fst b, sstart (MR st g) i) (map bslot BL).
Proof.
  intros Hb Hil Hbits. assert (Hm : hosts st b g) by (exists ai; exact Hb).
  pose proof (is_part _ _ _ IS b g ai i Hb Hil) as P. rewrite (slot_start'_eq _ _ _ IM _ _ i Hm) in P.
  unfold one5, tbit in P. (first [ dand8 P as _ nAB nAC nAD _ nBC nBD _ | destruct P as (_ & nAB & nAC & nAD & _ & nBC & nBD & _) ]).
  split.
  - destruct (s_groups st !! (fst b, sstart (MR st g) i)) eqn:E; [| reflexivity]. exfalso.
    destruct Hbits as [A|F]; [apply nAD| apply nBD]; split; auto; intros Y; rewrite Y in E; discriminate E.
  - intros C. destruct Hbits as [A|F]; [apply nAC| apply nBC]; split; auto.
Qed.

Lemma hdr_hosts b gh : s_groups st !! b = Some gh -> exists m, hosts st b m.
Proof.
  intros Hb. (first [ pose proof ((im_hdr _ _ _ IM _ _ Hb)) as dR_25; dex1 dR_25 as m; destruct dR_25 as [Eg _] | pose proof ((im_hdr _ _ _ IM _ _ Hb)) as dR_25; dand3 dR_25 as m Eg _ | destruct (im_hdr _ _ _ IM _ _ Hb) as (m & Eg & _) ]). exists m. destruct gh as [gm gai]; cbn in Eg; subst gm. exists gai. exact Hb.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Variable LB : list block.
Hypothesis CR : CORR st LB BL.

Lemma LB_blk blk : In blk LB -> exists c off n, In ((c, off), n) BL /\ blk_slot blk = c /\ blk_size blk = n /\ blk_addr blk = conc st c + UNIT * off.
Proof.
  intros Hb. (first [ pose proof ((Forall2_In_l _ _ _ _ CR Hb)) as dR_26; dex1 dR_26 as k; destruct dR_26 as [Hk (C1 & C2 & C3)] | pose proof ((Forall2_In_l _ _ _ _ CR Hb)) as dR_26; dand3 dR_26 as k Hk (C1 & C2 & C3) | destruct (Forall2_In_l _ _ _ _ CR Hb) as (k & Hk & (C1 & C2 & C3)) ]). destruct k as [[c off] n].
  exists c, off, n. cbn [bslot boff bsize fst snd] in C1, C2, C3. auto.
Qed.

(* [comment removed for export] *)
Lemma LB_geo blk : In blk LB -> exists c off n m bm i r,
  In ((c, off), n) BL /\ blk_slot blk = c /\ blk_size blk = n /\
  hosts st bm m /\ 0 <= i <= m_last_idx (MR st m) /\ c = (fst bm, sstart (MR st m) i) /\ s_groups st !! c = None /\
  s_regions st !! (fst bm) = Some r /\ r_kind r = RKGroup /\
  blk_addr blk = r_base r + sstart (MR st m) i + UNIT * off /\ 0 <= off /\ 0 <= n /\ UNIT * off + n <= get_stride (MR st m) - IB.
Proof.
  intros Hb. (first [ pose proof ((LB_blk _ Hb)) as dR_27; dex3 dR_27 as c off n; dand4 dR_27 as Hk C1 C2 C3 | pose proof ((LB_blk _ Hb)) as dR_27; dand7 dR_27 as c off n Hk C1 C2 C3 | destruct (LB_blk _ Hb) as (c & off & n & Hk & C1 & C2 & C3) ]).
  (first [ pose proof ((block_facts _ _ _ _ _ INV c off n Hk)) as dR_28; dex7 dR_28 as m bm i ai a ar ka; rename dR_28 into BF | pose proof ((block_facts _ _ _ _ _ INV c off n Hk)) as dR_28; dand8 dR_28 as m bm i ai a ar ka BF | destruct (block_facts _ _ _ _ _ INV c off n Hk) as (m & bm & i & ai & a & ar & ka & BF) ]).
  pose proof (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF) as Hh. assert (Hm : hosts st bm m) by (exists ai; exact Hh).
  (first [ pose proof ((ig_region _ _ _ IG _ _ Hh)) as dR_29; dex1 dR_29 as r; destruct dR_29 as [Hr Kr] | pose proof ((ig_region _ _ _ IG _ _ Hh)) as dR_29; dand3 dR_29 as r Hr Kr | destruct (ig_region _ _ _ IG _ _ Hh) as (r & Hr & Kr) ]).
  exists c, off, n, m, bm, i, r.
  pose proof (bf_c _ _ _ _ _ _ _ _ _ _ _ BF) as Ec. pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF) as Hi.
  pose proof (bf_notH _ _ _ _ _ _ _ _ _ _ _ BF) as NH. pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF) as Ho.
  pose proof (bf_n _ _ _ _ _ _ _ _ _ _ _ BF) as Hn. pose proof (bf_fit _ _ _ _ _ _ _ _ _ _ _ BF) as Hf.
  OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; auto; try lia.
  rewrite C3, Ec. unfold conc, get_region. cbn [fst snd]. rewrite Hr. lia.
Qed.

Lemma f_free_clear : fact_free_clear (strip st) LB.
Proof.
  change (fact_free_clear st LB). intros g b i H Hi Hbits. fold (MR st g) in *. cbn zeta. rewrite !sstart_of_eq.
  pose proof (mem_hosts _ _ H) as Hm. (first [ pose proof ((hosts_GO _ _ Hm)) as dR_30; dex1 dR_30 as ai; destruct dR_30 as [Hb GO] | pose proof ((hosts_GO _ _ Hm)) as dR_30; dand3 dR_30 as ai Hb GO | destruct (hosts_GO _ _ Hm) as (ai & Hb & GO) ]).
  (first [ pose proof ((g_masks _ _ _ _ _ _ GO)) as dR_31; dand6 dR_31 as M1 M2 M3 M4 M5 M6 | pose proof (g_masks _ _ _ _ _ _ GO) as (M1 & M2 & M3 & M4 & M5 & M6) ]). pose proof (g_ai _ _ _ _ _ _ GO) as AI.
  assert (Hil : 0 <= i <= m_last_idx (MR st g)). { destruct Hbits as [A|F]; [pose proof (M3 i Hi A); lia | pose proof (M4 i Hi F); lia]. }
  destruct (bit_slot_nonH _ _ _ _ Hb Hil Hbits) as [NH NB].
  pose proof (sstart_succ st g i) as SS.
  split.
  - intros b' gh Hb' Hf. destruct (hdr_hosts _ _ Hb') as [m' Hm'].
    destruct (sep_ghdr _ _ _ _ IM IG IS g b i Hm Hil NH m' b' Hm' Hf) as [A|A]; unfold IB; lia.
  - intros blk Hblk Hf. (first [ pose proof ((LB_geo _ Hblk)) as dR_32; dex7 dR_32 as c off n m2 b2 i2 r; dand13 dR_32 as Hk C1 C2 Hm2 Hi2 Ec NH2 Hr Kr Ea Ho Hn Fit | pose proof ((LB_geo _ Hblk)) as dR_32; dand20 dR_32 as c off n m2 b2 i2 r Hk C1 C2 Hm2 Hi2 Ec NH2 Hr Kr Ea Ho Hn Fit | destruct (LB_geo _ Hblk) as (c & off & n & m2 & b2 & i2 & r & Hk & C1 & C2 & Hm2 & Hi2 & Ec & NH2 & Hr & Kr & Ea & Ho & Hn & Fit) ]).
    rewrite C1, Ec in Hf. cbn [fst] in Hf. rewrite <- Hf, Hr. exists r. split; [reflexivity|].
    rewrite Ea, C2. pose proof (sstart_succ st m2 i2) as SS2.
    assert (NE : m2 <> g \/ i2 <> i). { destruct (aptr_eq_dec m2 g) as [->|]; [right| now left]. intros ->. apply NB. rewrite <- Hf, <- Ec, <- C1.
      (first [ pose proof ((Forall2_In_l _ _ _ _ CR Hblk)) as dR_33; dex1 dR_33 as k; destruct dR_33 as [HkB (Ek & _)] | pose proof ((Forall2_In_l _ _ _ _ CR Hblk)) as dR_33; dand3 dR_33 as k HkB (Ek & _) | destruct (Forall2_In_l _ _ _ _ CR Hblk) as (k & HkB & (Ek & _)) ]). rewrite Ek. apply in_map. exact HkB. }
    destruct (sep_ext _ _ _ _ IM IG IS g b i Hm Hil NH m2 b2 i2 Hm2 Hf Hi2 NE ltac:(rewrite Ec in NH2; exact NH2)) as [A|A]; unfold UNIT, IB in *; lia.
Qed.

Lemma f_avail_clear : fact_avail_clear (strip st) LB.
Proof. intros g b i H Hi Ha. exact (f_free_clear g b i H Hi (or_introl Ha)). Qed.

Lemma f_hdr_clear : fact_hdr_clear (strip st) LB.
Proof.
  change (fact_hdr_clear st LB). intros b gh blk r Hb Hblk Hf Hr.
  (first [ pose proof ((LB_geo _ Hblk)) as dR_34; dex7 dR_34 as c off n m2 b2 i2 r'; dand13 dR_34 as Hk C1 C2 Hm2 Hi2 Ec NH2 Hr' Kr Ea Ho Hn Fit | pose proof ((LB_geo _ Hblk)) as dR_34; dand20 dR_34 as c off n m2 b2 i2 r' Hk C1 C2 Hm2 Hi2 Ec NH2 Hr' Kr Ea Ho Hn Fit | destruct (LB_geo _ Hblk) as (c & off & n & m2 & b2 & i2 & r' & Hk & C1 & C2 & Hm2 & Hi2 & Ec & NH2 & Hr' & Kr & Ea & Ho & Hn & Fit) ]).
  rewrite C1, Ec in Hf. cbn [fst] in Hf. rewrite <- Hf, Hr' in Hr. inversion Hr; subst r'.
  destruct (hdr_hosts _ _ Hb) as [m' Hm']. rewrite Ea, C2. pose proof (sstart_succ st m2 i2).
  rewrite Ec in NH2. destruct (sep_ghdr _ _ _ _ IM IG IS m2 b2 i2 Hm2 Hi2 NH2 m' b Hm' (eq_sym Hf)) as [A|A]; unfold UNIT, IB in *; lia.
Qed.

Lemma f_blk_unknown : fact_blk_unknown st LB.
Proof.
  intros blk r Hblk Hr a Ha. (first [ pose proof ((LB_blk _ Hblk)) as dR_35; dex3 dR_35 as c off n; dand4 dR_35 as Hk C1 C2 C3 | pose proof ((LB_blk _ Hblk)) as dR_35; dand7 dR_35 as c off n Hk C1 C2 C3 | destruct (LB_blk _ Hblk) as (c & off & n & Hk & C1 & C2 & C3) ]).
  (first [ pose proof ((is_blocks _ _ _ IS _ Hk)) as dR_36; dex2 dR_36 as m i; destruct dR_36 as [Hs _] | pose proof ((is_blocks _ _ _ IS _ Hk)) as dR_36; dand4 dR_36 as m i Hs _ | destruct (is_blocks _ _ _ IS _ Hk) as (m & i & Hs & _) ]). cbn [bslot fst snd] in Hs.
  (first [ pose proof ((ish_blk _ _ ISH ((c, off), n) m i Hk Hs)) as dR_37; dand8 dR_37 as _ _ _ _ _ _ _ U | pose proof (ish_blk _ _ ISH ((c, off), n) m i Hk Hs) as (_ & _ & _ & _ & _ & _ & _ & U) ]). cbn [bslot boff bsize fst snd] in U.
  rewrite C1 in Hr |- *. rewrite C3, C2 in Ha. unfold conc, get_region in Ha. rewrite Hr in Ha.
  destruct (U (a - r_base r) ltac:(lia)) as [h Hh]. exists h. exact Hh.
Qed.

Lemma f_blocks_disjoint : fact_blocks_disjoint st LB.
Proof.
  intros b1 b2 H1 H2 Hf NE.
  (first [ pose proof ((LB_geo _ H1)) as dR_38; dex7 dR_38 as c1 o1 n1 m1 bm1 i1 r1; dand13 dR_38 as K1 C1 S1 Hm1 Hi1 E1 N1 R1 _ A1 O1 P1 F1 | pose proof ((LB_geo _ H1)) as dR_38; dand20 dR_38 as c1 o1 n1 m1 bm1 i1 r1 K1 C1 S1 Hm1 Hi1 E1 N1 R1 _ A1 O1 P1 F1 | destruct (LB_geo _ H1) as (c1 & o1 & n1 & m1 & bm1 & i1 & r1 & K1 & C1 & S1 & Hm1 & Hi1 & E1 & N1 & R1 & _ & A1 & O1 & P1 & F1) ]).
  (first [ pose proof ((LB_geo _ H2)) as dR_39; dex7 dR_39 as c2 o2 n2 m2 bm2 i2 r2; dand13 dR_39 as K2 C2 S2 Hm2 Hi2 E2 N2 R2 _ A2 O2 P2 F2 | pose proof ((LB_geo _ H2)) as dR_39; dand20 dR_39 as c2 o2 n2 m2 bm2 i2 r2 K2 C2 S2 Hm2 Hi2 E2 N2 R2 _ A2 O2 P2 F2 | destruct (LB_geo _ H2) as (c2 & o2 & n2 & m2 & bm2 & i2 & r2 & K2 & C2 & S2 & Hm2 & Hi2 & E2 & N2 & R2 & _ & A2 & O2 & P2 & F2) ]).
  rewrite C1, C2, E1, E2 in Hf. cbn [fst] in Hf. rewrite Hf, R2 in R1. inversion R1; subst r2.
  rewrite A1, A2, S1, S2. pose proof (sstart_succ st m1 i1). pose proof (sstart_succ st m2 i2).
  assert (NE' : m2 <> m1 \/ i2 <> i1). { destruct (aptr_eq_dec m2 m1) as [->|]; [right| now left]. intros ->. apply NE. rewrite C1, C2, E1, E2, Hf. reflexivity. }
  rewrite E1 in N1. rewrite E2 in N2.
  destruct (sep_ext _ _ _ _ IM IG IS m1 bm1 i1 Hm1 Hi1 N1 m2 bm2 i2 Hm2 ltac:(symmetry; exact Hf) Hi2 NE' N2) as [A|A]; unfold UNIT, IB in *; lia.
Qed.

(* [comment removed for export] *)
Lemma f_blocks_apart : forall b1 b2, In b1 LB -> In b2 LB -> fst (blk_slot b1) = fst (blk_slot b2) -> blk_slot b1 <> blk_slot b2 ->
    blk_addr b1 + blk_size b1 < blk_addr b2 \/ blk_addr b2 + blk_size b2 < blk_addr b1.
Proof.
  intros b1 b2 H1 H2 Hf NE.
  (first [ pose proof ((LB_geo _ H1)) as dR_40; dex7 dR_40 as c1 o1 n1 m1 bm1 i1 r1; dand13 dR_40 as K1 C1 S1 Hm1 Hi1 E1 N1 R1 _ A1 O1 P1 F1 | pose proof ((LB_geo _ H1)) as dR_40; dand20 dR_40 as c1 o1 n1 m1 bm1 i1 r1 K1 C1 S1 Hm1 Hi1 E1 N1 R1 _ A1 O1 P1 F1 | destruct (LB_geo _ H1) as (c1 & o1 & n1 & m1 & bm1 & i1 & r1 & K1 & C1 & S1 & Hm1 & Hi1 & E1 & N1 & R1 & _ & A1 & O1 & P1 & F1) ]).
  (first [ pose proof ((LB_geo _ H2)) as dR_41; dex7 dR_41 as c2 o2 n2 m2 bm2 i2 r2; dand13 dR_41 as K2 C2 S2 Hm2 Hi2 E2 N2 R2 _ A2 O2 P2 F2 | pose proof ((LB_geo _ H2)) as dR_41; dand20 dR_41 as c2 o2 n2 m2 bm2 i2 r2 K2 C2 S2 Hm2 Hi2 E2 N2 R2 _ A2 O2 P2 F2 | destruct (LB_geo _ H2) as (c2 & o2 & n2 & m2 & bm2 & i2 & r2 & K2 & C2 & S2 & Hm2 & Hi2 & E2 & N2 & R2 & _ & A2 & O2 & P2 & F2) ]).
  rewrite C1, C2, E1, E2 in Hf. cbn [fst] in Hf. rewrite Hf, R2 in R1. inversion R1; subst r2.
  rewrite A1, A2, S1, S2. pose proof (sstart_succ st m1 i1). pose proof (sstart_succ st m2 i2).
  assert (NE' : m2 <> m1 \/ i2 <> i1). { destruct (aptr_eq_dec m2 m1) as [->|]; [right| now left]. intros ->. apply NE. rewrite C1, C2, E1, E2, Hf. reflexivity. }
  rewrite E1 in N1. rewrite E2 in N2.
  destruct (sep_ext _ _ _ _ IM IG IS m1 bm1 i1 Hm1 Hi1 N1 m2 bm2 i2 Hm2 ltac:(symmetry; exact Hf) Hi2 NE' N2) as [A|A]; unfold UNIT, IB in *; lia.
Qed.

Lemma LB_blocks_ok : Forall (block_ok st) LB.
Proof.
  apply List.Forall_forall. intros blk Hblk. (first [ pose proof ((LB_blk _ Hblk)) as dR_42; dex3 dR_42 as c off n; dand4 dR_42 as Hk C1 C2 C3 | pose proof ((LB_blk _ Hblk)) as dR_42; dand7 dR_42 as c off n Hk C1 C2 C3 | destruct (LB_blk _ Hblk) as (c & off & n & Hk & C1 & C2 & C3) ]).
  (first [ pose proof ((block_facts _ _ _ _ _ INV c off n Hk)) as dR_43; dex7 dR_43 as m bm i ai a ar ka; rename dR_43 into BF | pose proof ((block_facts _ _ _ _ _ INV c off n Hk)) as dR_43; dand8 dR_43 as m bm i ai a ar ka BF | destruct (block_facts _ _ _ _ _ INV c off n Hk) as (m & bm & i & ai & a & ar & ka & BF) ]).
  pose proof (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF) as Hh.
  constructor.
  - exists m, i. rewrite C1. split; [exact (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF)|]. fold (MR st m).
    split; [exact (bf_notA _ _ _ _ _ _ _ _ _ _ _ BF)|]. split; [exact (bf_notF _ _ _ _ _ _ _ _ _ _ _ BF)|].
    split; [exact (bf_i _ _ _ _ _ _ _ _ _ _ _ BF)|].
    exists off. pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF). pose proof (bf_fit _ _ _ _ _ _ _ _ _ _ _ BF). rewrite C2, C3. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia.
  - rewrite C1. (first [ pose proof ((ig_region _ _ _ IG _ _ Hh)) as dR_44; dex1 dR_44 as r; destruct dR_44 as [Hr Kr] | pose proof ((ig_region _ _ _ IG _ _ Hh)) as dR_44; dand3 dR_44 as r Hr Kr | destruct (ig_region _ _ _ IG _ _ Hh) as (r & Hr & Kr) ]). rewrite (bf_c _ _ _ _ _ _ _ _ _ _ _ BF). cbn [fst]. exists r. auto.
  - rewrite C2. exact (bf_n _ _ _ _ _ _ _ _ _ _ _ BF).
Qed.

Lemma LB_nodup : List.NoDup (map blk_slot LB).
Proof.
  rewrite (Forall2_map_eq (corr1 st) blk_slot bslot LB BL CR ltac:(intros a b (E & _); exact E)).
  apply NoDup_ListNoDup. exact (is_nodup _ _ _ IS).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma region_rid rid r : s_regions st !! rid = Some r -> (rid < s_next_rid st)%N.
Proof. exact (ir_ids _ _ _ IR rid r). Qed.
Lemma area_rid a ar : s_areas st !! a = Some ar -> (fst a < s_next_rid st)%N.
Proof. intros Ha. destruct (ia_areas _ IA _ _ Ha) as ((r & Hr & _) & _). exact (region_rid _ _ Hr). Qed.
Lemma area_rid' a : s_areas st !! a <> None -> (fst a < s_next_rid st)%N.
Proof. intros Ha. destruct (s_areas st !! a) as [ar|] eqn:E; [exact (area_rid _ _ E)| congruence]. Qed.
Lemma present_rid m : s_metas st !! m <> None -> (fst m < s_next_rid st)%N.
Proof.
  intros Hm. destruct (s_metas st !! m) as [mr|] eqn:E; [| congruence].
  (first [ pose proof ((ia_metas _ IA _ _ E)) as dR_45; dex3 dR_45 as a ar k; dand3 dR_45 as Ha Hk -> | pose proof ((ia_metas _ IA _ _ E)) as dR_45; dand6 dR_45 as a ar k Ha Hk -> | destruct (ia_metas _ IA _ _ E) as (a & ar & k & Ha & Hk & ->) ]). unfold mslot, aadd. cbn [fst]. exact (area_rid _ _ Ha).
Qed.
Lemma nonzero_present m : MR st m <> meta0 -> s_metas st !! m <> None.
Proof. unfold MR, get_meta_rec. destruct (s_metas st !! m); cbn; congruence. Qed.
Lemma listed_rid m h : In m (LS h) -> (fst m < s_next_rid st)%N.
Proof. intros H. apply present_rid. exact (listed_present _ _ _ _ _ INV m h H). Qed.
Lemma hosts_rid b m : hosts st b m -> (fst b < s_next_rid st)%N.
Proof. intros [ai Hb]. (first [ pose proof ((ig_region _ _ _ IG _ _ Hb)) as dR_46; dex1 dR_46 as r; destruct dR_46 as [Hr _] | pose proof ((ig_region _ _ _ IG _ _ Hb)) as dR_46; dand3 dR_46 as r Hr _ | destruct (ig_region _ _ _ IG _ _ Hb) as (r & Hr & _) ]). exact (region_rid _ _ Hr). Qed.

Lemma f_ptrs : fact_ptrs st.
Proof.
  split.
  - unfold ptrs_in. cbn zeta.
    assert (HD : forall h, optr_in (fun rid => (rid < s_next_rid st)%N) (get_head st h)).
    { intros h. destruct (get_head st h) as [a|] eqn:E; cbn; [| exact I]. exact (listed_rid _ _ (head_listed _ _ _ _ _ INV h a E)). }
    split; [exact (HD LFree)|].
    split. { destruct (c_avail_meta (ctx st)) as [q|] eqn:E; cbn; [| exact I]. (first [ pose proof ((ia_availptr _ IA q E)) as dR_47; dex1 dR_47 as r; destruct dR_47 as [Hr _] | pose proof ((ia_availptr _ IA q E)) as dR_47; dand3 dR_47 as r Hr _ | destruct (ia_availptr _ IA q E) as (r & Hr & _) ]). exact (region_rid _ _ Hr). }
    split. { destruct (c_meta_area_head (ctx st)) as [q|] eqn:E; cbn; [| exact I]. exact (area_rid' _ (ia_head _ IA q E)). }
    split. { destruct (c_meta_area_tail (ctx st)) as [q|] eqn:E; cbn; [| exact I]. exact (area_rid' _ (ia_tail _ IA q E)). }
    split. { destruct (c_avail_meta_areas (ctx st)) as [[rid off]|] eqn:E; cbn; [| exact I].
             (first [ pose proof ((ir_cursor _ _ _ IR)) as dR_48; dand3 dR_48 as _ _ CU | destruct (ir_cursor _ _ _ IR) as (_ & _ & CU) ]). (first [ pose proof ((CU rid off E)) as dR_49; dex1 dR_49 as r; destruct dR_49 as [Hr _] | pose proof ((CU rid off E)) as dR_49; dand3 dR_49 as r Hr _ | destruct (CU rid off E) as (r & Hr & _) ]). exact (region_rid _ _ Hr). }
    split; [intros sc; exact (HD (LActive sc))|].
    split. { pose proof (ir_brk _ _ _ IR) as BR. unfold ctx. destruct (c_brk (s_ctx st)) as [| |rid off]; try exact I.
             (first [ dand4 BR as _ r Hr _ | destruct BR as (_ & r & Hr & _) ]). exact (region_rid _ _ Hr). }
    split.
    { intros g. fold (MR st g). pose proof (il_link _ _ IL g) as [[L1 L2] L3].
      assert (NX : forall x, m_next (MR st g) = Some x -> (fst x < s_next_rid st)%N).
      { intros x Hx. destruct (L2 ltac:(rewrite Hx; discriminate)) as [h Hh]. exact (listed_rid _ _ (next_listed _ _ _ _ _ INV h g x Hh Hx)). }
      split. { destruct (m_prev (MR st g)) as [p|] eqn:Ep; cbn; [| exact I].
               destruct (m_next (MR st g)) as [x|] eqn:Ex; [| discriminate (L3 eq_refl)].
               destruct (L2 ltac:(discriminate)) as [h Hh]. exact (listed_rid _ _ (prev_listed _ _ _ _ _ INV h g p Hh Ep)). }
      split. { destruct (m_next (MR st g)) as [x|] eqn:Ex; cbn; [| exact I]. exact (NX x eq_refl). }
      destruct (m_mem (MR st g)) as [b|] eqn:Eb; cbn; [| exact I]. exact (hosts_rid _ _ (mem_hosts _ _ Eb)). }
    split.
    { intros a ar Ha. split; [exact (area_rid _ _ Ha)|]. destruct (a_next ar) as [a'|] eqn:E; cbn; [| exact I].
      (first [ pose proof ((ia_areas _ IA _ _ Ha)) as dR_51; dand4 dR_51 as _ _ _ NXT | destruct (ia_areas _ IA _ _ Ha) as (_ & _ & _ & NXT) ]). exact (area_rid' _ (NXT a' E)). }
    intros b gh Hb. destruct (hdr_hosts _ _ Hb) as [m Hm]. split; [exact (hosts_rid _ _ Hm)|].
    (first [ pose proof ((im_hdr _ _ _ IM _ _ Hb)) as dR_52; dex1 dR_52 as m'; dand3 dR_52 as Eg Hmem _ | pose proof ((im_hdr _ _ _ IM _ _ Hb)) as dR_52; dand4 dR_52 as m' Eg Hmem _ | destruct (im_hdr _ _ _ IM _ _ Hb) as (m' & Eg & Hmem & _) ]). rewrite Eg. cbn. apply present_rid. apply nonzero_present. intros E. rewrite E in Hmem. cbn in Hmem. discriminate.
  - intros rid Hrid. split.
    + destruct (s_regions st !! rid) as [r|] eqn:E; [| reflexivity]. pose proof (region_rid _ _ E). lia.
    + destruct (s_shadow st !! rid) as [sh|] eqn:E; [| reflexivity]. (first [ pose proof ((ish_dom _ _ ISH _ _ E)) as dR_53; dex1 dR_53 as r; destruct dR_53 as [Hr _] | pose proof ((ish_dom _ _ ISH _ _ E)) as dR_53; dand3 dR_53 as r Hr _ | destruct (ish_dom _ _ ISH _ _ E) as (r & Hr & _) ]). pose proof (region_rid _ _ Hr). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma conc_group_inj b1 b2 m1 m2 : hosts st b1 m1 -> hosts st b2 m2 -> conc st b1 = conc st b2 -> b1 = b2.
Proof.
  intros H1 H2 E.
  (first [ pose proof ((conc_group _ _ H1)) as dR_54; dex1 dR_54 as r1; dand5 dR_54 as R1 K1 C1 LO1 HI1 | pose proof ((conc_group _ _ H1)) as dR_54; dand6 dR_54 as r1 R1 K1 C1 LO1 HI1 | destruct (conc_group _ _ H1) as (r1 & R1 & K1 & C1 & LO1 & HI1) ]). (first [ pose proof ((conc_group _ _ H2)) as dR_55; dex1 dR_55 as r2; dand5 dR_55 as R2 K2 C2 LO2 HI2 | pose proof ((conc_group _ _ H2)) as dR_55; dand6 dR_55 as r2 R2 K2 C2 LO2 HI2 | destruct (conc_group _ _ H2) as (r2 & R2 & K2 & C2 & LO2 & HI2) ]).
  destruct (N.eq_dec (fst b1) (fst b2)) as [Ef|NEf].
  - rewrite Ef, R2 in R1. inversion R1; subst r1. apply injective_projections; [exact Ef| lia].
  - exfalso. pose proof (ir_disj _ _ _ IR _ _ _ _ R1 R2 NEf) as D. unfold region_live_range in D. rewrite K1, K2 in D. lia.
Qed.

Lemma groups_count : Z.of_nat (length (map_to_list (s_groups st))) <= alloc_ceiling.
Proof.
  rewrite <- (length_map (fun bh : aptr * ghdr => conc st (fst bh))).
  assert (HIN : forall bh, In bh (map_to_list (s_groups st)) -> s_groups st !! (fst bh) = Some (snd bh)).
  { intros [b h] Hin. apply elem_of_map_to_list. apply list_elem_of_In. exact Hin. }
  apply NoDup_Z_length; [(let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia| |].
  - apply NoDup_map_on.
    + intros [b1 h1] [b2 h2] I1 I2 E. cbn in E. pose proof (HIN _ I1) as G1. pose proof (HIN _ I2) as G2. cbn in G1, G2.
      destruct (hdr_hosts _ _ G1) as [m1 Hm1]. destruct (hdr_hosts _ _ G2) as [m2 Hm2].
      pose proof (conc_group_inj _ _ _ _ Hm1 Hm2 E) as Eb. subst b2. rewrite G1 in G2. inversion G2. reflexivity.
    + pose proof (NoDup_fst_map_to_list (s_groups st)) as ND. apply NoDup_ListNoDup in ND.
      apply (NoDup_map_inv fst). exact ND.
  - intros x Hx. apply in_map_iff in Hx. (first [ dand3 Hx as [b h] <- Hin | destruct Hx as ([b h] & <- & Hin) ]). cbn. pose proof (HIN _ Hin) as G. cbn in G.
    destruct (hdr_hosts _ _ G) as [m Hm]. (first [ pose proof ((conc_group _ _ Hm)) as dR_57; dex1 dR_57 as r; dand5 dR_57 as Hr Kr C LO HI | pose proof ((conc_group _ _ Hm)) as dR_57; dand6 dR_57 as r Hr Kr C LO HI | destruct (conc_group _ _ Hm) as (r & Hr & Kr & C & LO & HI) ]).
    (first [ pose proof ((ir_shape _ _ _ IR _ _ Hr)) as dR_58; dand6 dR_58 as B0 _ _ _ CE _ | destruct (ir_shape _ _ _ IR _ _ Hr) as (B0 & _ & _ & _ & CE & _) ]). lia.
Qed.

Lemma gcnt_bound sc : 0 <= gcnt st sc < 2 ^ 60.
Proof.
  unfold gcnt.
  pose proof (zsum_bound (map (fun bh : aptr * ghdr => match g_meta (snd bh) with
     | Some m => if m_sizeclass (MR st m) =? sc then cnt_of (MR st m) else 0 | None => 0 end) (map_to_list (s_groups st))) 32) as ZS.
  rewrite length_map in ZS. pose proof groups_count as GC. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
  eassert (H : _); [| specialize (ZS H); lia].
  intros x Hx. apply in_map_iff in Hx. (first [ dand3 Hx as [b h] <- Hin | destruct Hx as ([b h] & <- & Hin) ]). cbn.
  assert (G : s_groups st !! b = Some h). { apply elem_of_map_to_list. apply list_elem_of_In. exact Hin. }
  (first [ pose proof ((im_hdr _ _ _ IM _ _ G)) as dR_60; dex1 dR_60 as m; dand3 dR_60 as Eg Hmem AI | pose proof ((im_hdr _ _ _ IM _ _ G)) as dR_60; dand4 dR_60 as m Eg Hmem AI | destruct (im_hdr _ _ _ IM _ _ G) as (m & Eg & Hmem & AI) ]). rewrite Eg.
  (first [ pose proof ((hosts_GO _ _ (mem_hosts _ _ Hmem))) as dR_61; dex1 dR_61 as ai; destruct dR_61 as [_ GO] | pose proof ((hosts_GO _ _ (mem_hosts _ _ Hmem))) as dR_61; dand3 dR_61 as ai _ GO | destruct (hosts_GO _ _ (mem_hosts _ _ Hmem)) as (ai & _ & GO) ]). pose proof (g_li _ _ _ _ _ _ GO). unfold cnt_of.
  destruct (m_sizeclass (MR st m) =? sc); lia.
Qed.

Lemma f_usage : fact_usage (strip st).
Proof.
  intros i. rewrite usage_strip. destruct (c_usage (s_ctx st) !! i) as [v|] eqn:E.
  - pose proof (ia_usage_keys _ IA i v E) as Hi. rewrite (ia_usage _ IA i Hi). apply gcnt_bound.
  - unfold usage, ctx. rewrite E. cbn. lia.
Qed.
End MF.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac inst f INV CR :=
  first [ exact (f _ _ _ _ _ INV) | exact (f _ _ _ _ _ INV eq_refl) | exact (f _ _ _ _ _ INV eq_refl eq_refl)
        | exact (f _ _ _ _ _ INV _ CR) | exact (f _ _ _ _ _ INV eq_refl _ CR) | exact (f _ _ _ _ _ INV eq_refl eq_refl _ CR) ].

Section CEIL.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Theorem areach_facts_proof : forall {resv} st LB, AREACH_from resv st LB -> @MFACTS_g resv st LB.
Proof.
  intros resv st LB AR. (first [ pose proof ((areach_inv resv st LB AR)) as dR_62; dand8 dR_62 as L LS BL INV LIVE RESV SEC CR | destruct (areach_inv resv st LB AR) as (L & LS & BL & INV & LIVE & RESV & SEC & CR) ]).
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  constructor.
  - inst LB_blocks_ok INV CR.
  - inst LB_nodup INV CR.
  - inst f_ticks INV CR.
  - rewrite <- RESV. symmetry. exact (ir_resv _ _ _ IR).
  - inst f_ctx INV CR.
  - inst f_active INV CR.
  - inst f_gmeta INV CR.
  - inst f_avail_clear INV CR.
  - inst f_hdr0 INV CR.
  - inst f_free_clear INV CR.
  - inst f_hdr_clear INV CR.
  - inst f_usage INV CR.
  - inst f_masks INV CR.
  - inst f_maplen INV CR.
  - inst f_slots INV CR.
  - inst f_slots_complete INV CR.
  - inst f_ptrs INV CR.
  - inst f_blk_unknown INV CR.
  - inst f_blocks_disjoint INV CR.
  - inst f_cell_ticks INV CR.
Qed.

Theorem areach_blocks_apart_proof : forall {resv} st LB, AREACH_from resv st LB ->
  forall b1 b2, In b1 LB -> In b2 LB -> fst (blk_slot b1) = fst (blk_slot b2) -> blk_slot b1 <> blk_slot b2 ->
    blk_addr b1 + blk_size b1 < blk_addr b2 \/ blk_addr b2 + blk_size b2 < blk_addr b1.
Proof.
  intros resv st LB AR. (first [ pose proof ((areach_inv resv st LB AR)) as dR_63; dand8 dR_63 as L LS BL INV LIVE RESV SEC CR | destruct (areach_inv resv st LB AR) as (L & LS & BL & INV & LIVE & RESV & SEC & CR) ]).
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  inst f_blocks_apart INV CR.
Qed.

End CEIL.
