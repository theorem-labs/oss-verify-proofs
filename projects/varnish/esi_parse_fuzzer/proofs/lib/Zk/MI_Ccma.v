(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require STree Malloc Mall7vg KInv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_List.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Inv MI_Kit MI_Geom MI_List MI_Ext MI_Pres2 MI_Ws22 MI_WNtf2.

Module MI_TF2.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc KInv MI_Inv MI_Kit MI_Arith MI_Geom MI_Ext MI_S421 MI_Ws22 MI_Wp9i.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.  (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition TW (st : mstate) (P : aptr -> Prop) : Prop :=
  forall rid sh o v t, s_shadow st !! rid = Some sh -> r_cells sh !! o = Some (v, t) -> t = s_tick st -> P (rid, o).

Definition TF0 (st : mstate) : Prop :=
  forall rid sh o v t, s_shadow st !! rid = Some sh -> r_cells sh !! o = Some (v, t) -> (t < s_tick st)%N.

(* [comment removed for export] *)
Definition PS (st : mstate) (q : aptr) : Prop :=
  exists b m, hosts st b m /\ fst b = fst q /\
    ((exists i, 0 <= i <= cnt_of (MR st m) /\ snd q = sstart (MR st m) i - IB)
     \/ (m_maplen (MR st m) = 0 /\ snd b - 3 <= snd q <= snd b - 1)).

Definition TF2 (st : mstate) : Prop := TW st (PS st).

Lemma TF0_TW st P : TF0 st -> TW st P.
Proof. intros H rid sh o v t Hs Hc Ht. exfalso. pose proof (H rid sh o v t Hs Hc). lia. Qed.
Lemma TF0_TF2 st : TF0 st -> TF2 st. Proof. apply TF0_TW. Qed.
(* [comment removed for export] *)

Lemma TW_mono st (P P' : aptr -> Prop) : (forall q, P q -> P' q) -> TW st P -> TW st P'.
Proof. intros HP H rid sh o v t Hs Hc Ht. apply HP. eapply H; eassumption. Qed.

Lemma TW_ctrl st st' P : s_shadow st' = s_shadow st -> s_tick st' = s_tick st -> TW st P -> TW st' P.
Proof. intros E1 E2 H rid sh o v t Hs Hc Ht. rewrite E1 in Hs. rewrite E2 in Ht. eapply H; eassumption. Qed.

Lemma TF0_ctrl st st' : s_shadow st' = s_shadow st -> s_tick st' = s_tick st -> TF0 st -> TF0 st'.
Proof. intros E1 E2 H rid sh o v t Hs Hc. rewrite E1 in Hs. rewrite E2. eapply H; eassumption. Qed.

(* [comment removed for export] *)
Lemma TF0_tick_new st t : TKS st (s_tick st) -> (s_tick st < t)%N -> TF0 (set_tick t st).
Proof.
  intros TK Ht rid sh o v tk Hs Hc. cbn in Hs |- *. (first [ pose proof ((TK rid sh Hs)) as dR_1; dand3 dR_1 as C _ _ | destruct (TK rid sh Hs) as (C & _ & _) ]). destruct (C o v tk Hc) as [_ Hle]. lia.
Qed.

Lemma TF0_hdr_havoc st b : TF0 st -> TF0 (hdr_havoc b st).
Proof.
  intros H rid sh o v t Hs Hc. unfold hdr_havoc, upd_shadow in Hs. cbn in Hs.
  change (s_tick (hdr_havoc b st)) with (s_tick st).
  destruct (N.eq_dec rid (fst b)) as [->|NE].
  - rewrite lookup_insert_eq in Hs. inversion Hs; subst; clear Hs. cbn in Hc.
    unfold get_shadow in Hc. destruct (s_shadow st !! fst b) as [sh0|] eqn:E0; cbn in Hc.
    + eapply H; eassumption.
    + rewrite lookup_empty in Hc. discriminate.
  - rewrite lookup_insert_ne in Hs by congruence. eapply H; eassumption.
Qed.

Lemma TW_hdr_havoc st b P : TW st P -> TW (hdr_havoc b st) P.
Proof.
  intros H rid sh o v t Hs Hc Ht. unfold hdr_havoc, upd_shadow in Hs. cbn in Hs.
  change (s_tick (hdr_havoc b st)) with (s_tick st) in Ht.
  destruct (N.eq_dec rid (fst b)) as [->|NE].
  - rewrite lookup_insert_eq in Hs. inversion Hs; subst; clear Hs. cbn in Hc.
    unfold get_shadow in Hc. destruct (s_shadow st !! fst b) as [sh0|] eqn:E0; cbn in Hc.
    + eapply H; [eassumption| eassumption| first [reflexivity| exact Ht]].
    + rewrite lookup_empty in Hc. discriminate.
  - rewrite lookup_insert_ne in Hs by congruence. eapply H; [eassumption| eassumption| first [reflexivity| exact Ht]].
Qed.

Lemma TW_wr8' st q v P : TW st P -> P q -> TW (wr8 q v st) P.
Proof.
  intros H Hq rid sh o w t Hs Hc Ht. change (s_tick (wr8 q v st)) with (s_tick st) in Ht.
  unfold wr8, upd_shadow in Hs. cbn in Hs.
  destruct (N.eq_dec rid (fst q)) as [->|NE].
  - rewrite lookup_insert_eq in Hs. inversion Hs; subst; clear Hs. cbn in Hc.
    destruct (Z.eq_dec o (snd q)) as [->|NEo].
    + replace (fst q, snd q) with q by (destruct q; reflexivity). exact Hq.
    + rewrite lookup_insert_ne in Hc by congruence. unfold get_shadow in Hc.
      destruct (s_shadow st !! fst q) as [sh0|] eqn:E0; cbn in Hc; [| rewrite lookup_empty in Hc; discriminate].
      eapply H; [exact E0| exact Hc| first [reflexivity| exact Ht]].
  - rewrite lookup_insert_ne in Hs by congruence. eapply H; [exact Hs| exact Hc| first [reflexivity| exact Ht]].
Qed.

Lemma TW_wrs l : forall st P, TW st P -> (forall q, In q (map fst l) -> P q) -> TW (wrs l st) P.
Proof.
  induction l as [|[q v] l IH]; intros st P H HP; cbn [wrs]; [exact H|].
  apply IH.
  - apply TW_wr8'; [exact H| apply HP; left; reflexivity].
  - intros q' Hq'. apply HP. right. exact Hq'.
Qed.

(* [comment removed for export] *)
Definition geom_kept (st st' : mstate) : Prop :=
  forall b m, hosts st b m -> hosts st' b m /\ (forall i, sstart (MR st' m) i = sstart (MR st m) i)
                              /\ cnt_of (MR st' m) = cnt_of (MR st m) /\ m_maplen (MR st' m) = m_maplen (MR st m).

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma PS_mono st st' q : geom_kept st st' -> PS st q -> PS st' q.
Proof.
  (intros GK; (first [ intro dR_17; dex2 dR_17 as b m; dand3 dR_17 as Hm Hf ALT | intro dR_17; dand5 dR_17 as b m Hm Hf ALT | intros (b & m & Hm & Hf & ALT) ])). (first [ pose proof ((GK _ _ Hm)) as dR_4; dand4 dR_4 as Hm' S C ML | destruct (GK _ _ Hm) as (Hm' & S & C & ML) ]).
  exists b, m. split; [exact Hm'|]. split; [exact Hf|].
  destruct ALT as [(i & Hi & E)|(Z0 & R0)].
  - left. exists i. rewrite C, S. auto.
  - right. rewrite ML. auto.
Qed.

Lemma TF2_kept st st' : s_shadow st' = s_shadow st -> s_tick st' = s_tick st -> geom_kept st st' -> TF2 st -> TF2 st'.
Proof.
  intros E1 E2 GK H. unfold TF2. eapply TW_mono; [intros q; apply (PS_mono st st' q GK)|]. exact (TW_ctrl st st' _ E1 E2 H).
Qed.

(* [comment removed for export] *)
Lemma geom_kept_of st st' :
  (forall b h, s_groups st !! b = Some h -> s_groups st' !! b = Some h) ->
  (forall b m, hosts st b m -> MR st' m = MR st m) ->
  geom_kept st st'.
Proof.
  intros HG HM b m Hm. pose proof Hm as [ai Hb]. split; [exists ai; apply HG; exact Hb|].
  rewrite (HM _ _ Hm). auto.
Qed.

(* [comment removed for export] *)
Lemma wr8_cells_other st q v rid o : (rid, o) <> q ->
  r_cells (get_shadow (wr8 q v st) rid) !! o = r_cells (get_shadow st rid) !! o.
Proof.
  intros NE. unfold get_shadow at 1. rewrite (wr8_shadow_lookup st q v rid).
  destruct (N.eqb_spec rid (fst q)) as [->|NR]; [| reflexivity]. cbn.
  rewrite lookup_insert_ne; [reflexivity|]. intros E. apply NE. rewrite <- E. destruct q; reflexivity.
Qed.

Lemma wrs_cells_other l : forall st rid o, ~ In (rid, o) (map fst l) ->
  r_cells (get_shadow (wrs l st) rid) !! o = r_cells (get_shadow st rid) !! o.
Proof.
  induction l as [|[q v] l IH]; intros st rid o Hn; cbn [wrs]; [reflexivity|].
  rewrite IH by (cbn in Hn; tauto). apply wr8_cells_other. cbn in Hn. intros E. apply Hn. left. symmetry. exact E.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section INTERIOR.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis INV : INVL X st L BL LS.

Lemma sstart_res b x i : hosts st b x -> (sstart (MR st x) i - IB) mod 16 = 12.
Proof.
  intros Hx. pose proof INV as (_ & _ & IM0 & _ & IG0 & _).
  pose proof (stride_ge X st LS IG0 _ _ Hx) as [SG SM]. (first [ pose proof ((hosts_ok X st LS IG0 _ _ Hx)) as dR_5; dex1 dR_5 as a; destruct dR_5 as [Hb GO] | pose proof ((hosts_ok X st LS IG0 _ _ Hx)) as dR_5; dand3 dR_5 as a Hb GO | destruct (hosts_ok X st LS IG0 _ _ Hx) as (a & Hb & GO) ]). pose proof (g_align _ _ _ _ _ _ GO) as [A0 A16].
  unfold sstart, IB, UNIT in *. rewrite (hosts_gbase X st LS IM0 _ _ Hx).
  pose proof (Z.div_mod (snd b) 16 ltac:(lia)) as D1. rewrite A16 in D1. pose proof (Z.div_mod (get_stride (MR st x)) 16 ltac:(lia)) as D2. rewrite SM in D2.
  replace (snd b + 16 + get_stride (MR st x) * i - 4) with (12 + (snd b / 16 + get_stride (MR st x) / 16 * i) * 16) by nia.
  rewrite Z_mod_plus_full. reflexivity.
Qed.
Variables (g bg : aptr) (idx : Z).
Hypothesis Hg : hosts st bg g.
Hypothesis Hidx : 0 <= idx <= m_last_idx (MR st g).
Hypothesis NH : s_groups st !! (fst bg, sstart (MR st g) idx) = None.

Let IM := proj1 (proj2 (proj2 INV)).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))).
Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

Lemma PS_not_interior q :
  PS st q -> fst q = fst bg -> ~ (sstart (MR st g) idx <= snd q < sstart (MR st g) (idx + 1) - IB).
Proof.
  ((first [ intro dR_18; dex2 dR_18 as b m; dand3 dR_18 as Hm Hf ALT | intro dR_18; dand5 dR_18 as b m Hm Hf ALT | intros (b & m & Hm & Hf & ALT) ]); intros Hq HI). rewrite Hq in Hf.
  destruct ALT as [(i & Hi & E)|(Z0 & R0)].
  - destruct (Z.eq_dec i (cnt_of (MR st m))) as [Ei|NEi].
    + (* [comment removed for export] *)
      assert (Hi' : 0 <= i <= m_last_idx (MR st m) + 1) by (unfold cnt_of in *; lia).
      destruct (aptr_eq_dec m g) as [->|NEm].
      * pose proof (sstart_mono X st LS IG _ _ (idx + 1) i Hg ltac:(unfold cnt_of in *; lia)). unfold IB in *. lia.
      * destruct (sep_hdr0 _ _ _ _ IM IG IS g bg idx Hg Hidx NH m b i Hm Hf Hi' ltac:(left; exact NEm)); unfold IB in *; lia.
    + assert (Hi' : 0 <= i <= m_last_idx (MR st m) + 1) by (unfold cnt_of in *; lia).
      destruct (aptr_eq_dec m g) as [->|NEm].
      * destruct (Z.eq_dec i idx) as [->|NEi2]; [unfold IB in *; lia|].
        destruct (sep_hdr0 _ _ _ _ IM IG IS g bg idx Hg Hidx NH g b i Hm Hf Hi' ltac:(right; exact NEi2)); unfold IB in *; lia.
      * destruct (sep_hdr0 _ _ _ _ IM IG IS g bg idx Hg Hidx NH m b i Hm Hf Hi' ltac:(left; exact NEm)); unfold IB in *; lia.
  - (* [comment removed for export] *)
    (first [ pose proof ((hosts_ok X st LS IG _ _ Hm)) as dR_6; dex1 dR_6 as ai; destruct dR_6 as [Hb GO] | pose proof ((hosts_ok X st LS IG _ _ Hm)) as dR_6; dand3 dR_6 as ai Hb GO | destruct (hosts_ok X st LS IG _ _ Hm) as (ai & Hb & GO) ]).
    (first [ pose proof ((g_nest _ _ _ _ _ _ GO Z0)) as dR_7; dex2 dR_7 as p ip; dand5 dR_7 as Hsl Hfp _ _ _ | pose proof ((g_nest _ _ _ _ _ _ GO Z0)) as dR_7; dand7 dR_7 as p ip Hsl Hfp _ _ _ | destruct (g_nest _ _ _ _ _ _ GO Z0) as (p & ip & Hsl & Hfp & _ & _ & _) ]).
    (first [ pose proof ((is_valid _ _ _ IS _ _ _ Hsl)) as dR_8; dand3 dR_8 as LVp Hip Eb | destruct (is_valid _ _ _ IS _ _ _ Hsl) as (LVp & Hip & Eb) ]).
    destruct LVp as [bp Hp].
    rewrite (slot_start'_eq _ _ _ IM _ _ _ Hp) in Eb.
    assert (Hfb : fst bp = fst bg) by (rewrite Eb in Hf; exact Hf).
    assert (Esnd : snd b = sstart (MR st p) ip) by (rewrite Eb; reflexivity).
    assert (NE : p <> g \/ ip <> idx).
    { destruct (aptr_eq_dec p g) as [->|]; [| left; assumption]. right. intros ->.
      pose proof (hosts_inj _ _ _ IM _ _ _ Hp Hg) as Ebp. rewrite Ebp in Eb. rewrite Eb in Hb. rewrite NH in Hb. discriminate. }
    destruct (sep_h3 _ _ _ _ IM IG IS g bg idx Hg Hidx NH p bp ip Hp Hfb Hip NE); unfold IB in *; lia.
Qed.

(* [comment removed for export] *)
Lemma TF2_interior_old :
  TF2 st -> forall o v t, r_cells (get_shadow st (fst bg)) !! o = Some (v, t) ->
  sstart (MR st g) idx <= o < sstart (MR st g) (idx + 1) - IB -> (t < s_tick st)%N.
Proof.
  intros TF o v t Hc Ho. (first [ pose proof ((get_shadow_cells_some st (fst bg) o (v, t) Hc)) as dR_9; dex1 dR_9 as sh; destruct dR_9 as [Hs Hc'] | pose proof ((get_shadow_cells_some st (fst bg) o (v, t) Hc)) as dR_9; dand3 dR_9 as sh Hs Hc' | destruct (get_shadow_cells_some st (fst bg) o (v, t) Hc) as (sh & Hs & Hc') ]).
  (first [ pose proof ((TKS_of _ _ _ _ _ INV (fst bg) sh Hs)) as dR_10; dand3 dR_10 as C _ _ | destruct (TKS_of _ _ _ _ _ INV (fst bg) sh Hs) as (C & _ & _) ]). destruct (C o v t Hc') as [_ Hle].
  destruct (N.eq_dec t (s_tick st)) as [Et|]; [| lia]. exfalso.
  exact (PS_not_interior (fst bg, o) (TF _ _ _ _ _ Hs Hc' Et) eq_refl Ho).
Qed.

(* [comment removed for export] *)
Lemma TF2_ghdr_old (p : aptr) :
  TF2 st -> snd p mod 16 = 0 ->
  forall o v t, snd p <= o < snd p + 12 -> r_cells (get_shadow st (fst p)) !! o = Some (v, t) -> (t < s_tick st)%N.
Proof.
  intros TF Al o v t Ho Hc. (first [ pose proof ((get_shadow_cells_some st (fst p) o (v, t) Hc)) as dR_11; dex1 dR_11 as sh; destruct dR_11 as [Hs Hc'] | pose proof ((get_shadow_cells_some st (fst p) o (v, t) Hc)) as dR_11; dand3 dR_11 as sh Hs Hc' | destruct (get_shadow_cells_some st (fst p) o (v, t) Hc) as (sh & Hs & Hc') ]).
  (first [ pose proof ((TKS_of _ _ _ _ _ INV (fst p) sh Hs)) as dR_12; dand3 dR_12 as C _ _ | destruct (TKS_of _ _ _ _ _ INV (fst p) sh Hs) as (C & _ & _) ]). destruct (C o v t Hc') as [_ Hle].
  destruct (N.eq_dec t (s_tick st)) as [Et|]; [| lia]. exfalso.
  (first [ pose proof ((TF _ _ _ _ _ Hs Hc' Et)) as dR_13; dex2 dR_13 as b m; dand3 dR_13 as Hm Hf ALT | pose proof ((TF _ _ _ _ _ Hs Hc' Et)) as dR_13; dand5 dR_13 as b m Hm Hf ALT | destruct (TF _ _ _ _ _ Hs Hc' Et) as (b & m & Hm & Hf & ALT) ]). cbn in Hf.
  destruct ALT as [(i & Hi & E)|(Z0 & R0)]; cbn in *.
  - pose proof (sstart_res b m i Hm) as RS. rewrite <- E in RS.
    pose proof (Z.div_mod o 16 ltac:(lia)). pose proof (Z.div_mod (snd p) 16 ltac:(lia)). lia.
  - (first [ pose proof ((hosts_ok X st LS IG _ _ Hm)) as dR_14; dex1 dR_14 as ai; destruct dR_14 as [Hb GO] | pose proof ((hosts_ok X st LS IG _ _ Hm)) as dR_14; dand3 dR_14 as ai Hb GO | destruct (hosts_ok X st LS IG _ _ Hm) as (ai & Hb & GO) ]). pose proof (g_align _ _ _ _ _ _ GO) as [_ A16]. unfold UNIT in A16.
    pose proof (Z.div_mod o 16 ltac:(lia)). pose proof (Z.div_mod (snd p) 16 ltac:(lia)). pose proof (Z.div_mod (snd b) 16 ltac:(lia)).
    pose proof (Z.mod_pos_bound o 16 ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma TF2_TF : TF2 st -> TF st.
Proof.
  intros TF rid sh o v t Hs Hc Ht. (first [ pose proof ((TF _ _ _ _ _ Hs Hc Ht)) as dR_15; dex2 dR_15 as b m; dand3 dR_15 as Hm Hf ALT | pose proof ((TF _ _ _ _ _ Hs Hc Ht)) as dR_15; dand5 dR_15 as b m Hm Hf ALT | destruct (TF _ _ _ _ _ Hs Hc Ht) as (b & m & Hm & Hf & ALT) ]). cbn in Hf.
  destruct ALT as [(i & Hi & E)|(Z0 & R0)]; cbn in *.
  - pose proof (sstart_res b m i Hm) as RS. rewrite <- E in RS. pose proof (Z.mod_pos_bound o 16 ltac:(lia)). lia.
  - (first [ pose proof ((hosts_ok X st LS IG _ _ Hm)) as dR_16; dex1 dR_16 as ai; destruct dR_16 as [Hb GO] | pose proof ((hosts_ok X st LS IG _ _ Hm)) as dR_16; dand3 dR_16 as ai Hb GO | destruct (hosts_ok X st LS IG _ _ Hm) as (ai & Hb & GO) ]). pose proof (g_align _ _ _ _ _ _ GO) as [_ A16]. unfold UNIT in A16.
    pose proof (Z.div_mod o 16 ltac:(lia)). pose proof (Z.div_mod (snd b) 16 ltac:(lia)).
    pose proof (Z.mod_pos_bound o 16 ltac:(lia)). lia.
Qed.
End INTERIOR.
End MI_TF2.


Module MI_Wm9j.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require STree Malloc KInv MI_Inv MI_Kit MI_Arith MI_Geom MI_List MI_Ext MI_S421.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_WFree.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Ws22 MI_Wp9i MI_Wgyo MI_Cnt.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.STree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malloc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Kit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Arith OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Geom OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_List OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ext OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_S421 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres2.MI_Pres1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres4.MI_Pres3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WFree.MI_Read OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ws22 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Wp9i OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Wgyo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Cnt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_TF2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.  (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma land31_id x : 0 <= x <= 31 -> Z.land x 31 = x.
Proof. intros. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
Lemma land63_id x : 0 <= x <= 63 -> Z.land x 63 = x.
Proof. intros. change 63 with (Z.ones 6). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
Lemma land52_id x : 0 <= x < 2 ^ 52 -> Z.land x (2 ^ 52 - 1) = x.
Proof. intros. change (2 ^ 52 - 1) with (Z.ones 52). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

Lemma one5_A (A B E : Prop) : A -> ~ B -> ~ E -> one5 A B False False E.
Proof. intros. unfold one5. tauto. Qed.
Lemma one5_B (A B E : Prop) : ~ A -> B -> ~ E -> one5 A B False False E.
Proof. intros. unfold one5. tauto. Qed.
Lemma one5_E (A B E : Prop) : ~ A -> ~ B -> E -> one5 A B False False E.
Proof. intros. unfold one5. tauto. Qed.

Lemma cell_read_shadow0 o : cell_read shadow0 o = Known 0.
Proof. unfold cell_read. cbn. rewrite !lookup_empty. reflexivity. Qed.

Lemma known_noshadow st rid o : s_shadow st !! rid = None -> known st (rid, o) 0.
Proof. intros H. unfold known, SHd, get_shadow. cbn. rewrite H. cbn. apply cell_read_shadow0. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition agG (sc : Z) (p : aptr) (cnt ai : Z) (r : meta) : meta :=
  m_set_sizeclass sc (m_set_freeable 1 (m_set_last_idx (cnt - 1)
    (m_set_mem (Some p) (m_set_freed (mask_upto (cnt - 1) - mask_upto ai) (m_set_avail (mask_upto ai) r))))).

Definition agt (st : mstate) (sc : Z) (m p : aptr) (cnt ai : Z) : mstate :=
  let st0 := hdr_havoc p st in
  let st1 := set_usage sc (usage st0 sc + cnt) st0 in
  let st2 := upd_meta m (agG sc p cnt ai) st1 in
  let st3 := put_group p (Some m) ai st2 in
  add_slots m p (get_stride (get_meta_rec st3 m)) cnt st3.

Lemma ag_tail_eq {T} st sc m p cnt ai (k : mstate -> optr -> M T) :
  ag_tail full_lay st sc m p cnt ai k = k (agt st sc m p cnt ai) (Some m).
Proof. reflexivity. Qed.

Section AGT.
Variables (st : mstate) (sc : Z) (m p : aptr) (cnt ai : Z).
Let st' := agt st sc m p cnt ai.
Let mr' := agG sc p cnt ai (MR st m).

Lemma agt_metas : s_metas st' = <[m := mr']> (s_metas st).
Proof. reflexivity. Qed.
Lemma agt_MR_m : MR st' m = mr'.
Proof. unfold MR, get_meta_rec. rewrite agt_metas, lookup_insert_eq. reflexivity. Qed.
#[using="mr'"] Lemma agt_MR_other x : x <> m -> MR st' x = MR st x.
Proof. intros NE. unfold MR, get_meta_rec. rewrite agt_metas, lookup_insert_ne by congruence. reflexivity. Qed.
Lemma agt_groups : s_groups st' = <[p := mkGhdr (Some m) (Z.land ai 31)]> (s_groups st).
Proof. reflexivity. Qed.
Lemma agt_rec3 :
  get_meta_rec (put_group p (Some m) ai (upd_meta m (agG sc p cnt ai) (set_usage sc (usage (hdr_havoc p st) sc + cnt) (hdr_havoc p st)))) m = mr'.
Proof. unfold get_meta_rec. cbn -[agG get_meta_rec]. rewrite lookup_insert_eq. reflexivity. Qed.
Lemma agt_slots s : 0 <= cnt -> 0 < get_stride mr' ->
  s_slots st' !! s =
  if (fst s =? fst p)%N && (0 <=? snd s - snd p - UNIT) && ((snd s - snd p - UNIT) mod get_stride mr' =? 0) && ((snd s - snd p - UNIT) / get_stride mr' <? cnt)
  then Some (m, (snd s - snd p - UNIT) / get_stride mr') else s_slots st !! s.
Proof. intros Hc Hs. unfold st', agt. cbn zeta. rewrite agt_rec3. rewrite lookup_add_slots by assumption. reflexivity. Qed.
Lemma agt_shadow : s_shadow st' = s_shadow (hdr_havoc p st). Proof. reflexivity. Qed.
Lemma agt_regions : s_regions st' = s_regions st. Proof. reflexivity. Qed.
Lemma agt_areas : s_areas st' = s_areas st. Proof. reflexivity. Qed.
Lemma agt_next_rid : s_next_rid st' = s_next_rid st. Proof. reflexivity. Qed.
Lemma agt_tick : s_tick st' = s_tick st. Proof. reflexivity. Qed.
Lemma agt_secret : s_secret st' = s_secret st. Proof. reflexivity. Qed.
Lemma agt_reserved : s_reserved st' = s_reserved st. Proof. reflexivity. Qed.
Lemma agt_ctx : s_ctx st' = set_usage_map (<[sc := usage st sc + cnt]> (c_usage (s_ctx st))) (s_ctx st). Proof. reflexivity. Qed.
Lemma agt_usage sc0 : usage st' sc0 = usage st sc0 + (if sc0 =? sc then cnt else 0).
Proof.
  unfold usage at 1. unfold ctx. rewrite agt_ctx. cbn -[usage]. destruct (Z.eqb_spec sc0 sc) as [->|NE].
  - rewrite lookup_insert_eq. reflexivity.
  - rewrite lookup_insert_ne by congruence. unfold usage, ctx. lia.
Qed.
Lemma agt_active sc0 : active st' sc0 = active st sc0. Proof. reflexivity. Qed.
Lemma agt_get_head h : get_head st' h = get_head st h. Proof. destruct h; reflexivity. Qed.

Lemma agt_TF0 : TF0 st -> TF0 st'.
Proof. intros H. apply (TF0_ctrl (hdr_havoc p st)); [reflexivity| reflexivity|]. apply TF0_hdr_havoc. exact H. Qed.
Lemma agt_TW P : TW st P -> TW st' P.
Proof. intros H. apply (TW_ctrl (hdr_havoc p st)); [reflexivity| reflexivity|]. apply TW_hdr_havoc. exact H. Qed.
End AGT.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section AG_TOP.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
Variables (idle0 : list aptr) (st2 : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (m : aptr) (rid : N) (r : region) (sc cnt needed ai : Z).
Let X := mkX (m :: idle0) [] None (Some rid) None.
Let X' := mkX idle0 [] None None (Some m).
Hypothesis INV : INVL X st2 L BL LS.
Hypothesis Hr : s_regions st2 !! rid = Some r.
Hypothesis Kr : r_kind r = RKGroup.
Hypothesis Lr : r_len r = needed.
Hypothesis NS : s_shadow st2 !! rid = None.
Hypothesis GRP : grp_ok sc cnt needed = true.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis Hai : 0 <= ai <= cnt - 1.
Hypothesis Hai0 : sc = 0 -> ai = cnt - 1.
Hypothesis EMP : LS (LActive sc) = [].
Hypothesis TF : TF0 st2.
Hypothesis NIm : ~ In m idle0.
Let p : aptr := (rid, 0).
Let ml := Z.shiftr needed 12.
Let MC := fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c.
Let st3 := upd_ctx MC st2.
Let st4 := upd_meta m (m_set_maplen ml) st3.
Let st' := agt st4 sc m p cnt ai.
Let mr' := agG sc p cnt ai (m_set_maplen ml meta0).

Let IM := proj1 (proj2 (proj2 INV)).
#[using="IM INV X rid LS BL L idle0 Clg"] Lemma top_MRm : MR st2 m = meta0.
Proof. unfold MR, get_meta_rec. rewrite (proj1 (im_idle _ _ _ IM m ltac:(left; reflexivity))). reflexivity. Qed.

#[using="INV"] Lemma top_INV3 : INVL X st3 L BL LS.
Proof. exact (INVL_mmap_counter X st2 L BL LS INV). Qed.

#[using="IM INV X rid LS BL L idle0 Clg"] Lemma top_MR4 : MR st4 m = m_set_maplen ml meta0.
Proof. unfold st4, MR. rewrite get_meta_rec_upd_same. f_equal. exact top_MRm. Qed.

#[using="Hsc GRP"] Lemma top_facts :
  let size := UNIT * size_class sc in
  let stride := get_stride mr' in
  1 <= cnt <= 32 /\ ml = needed / 4096 /\ 1 <= ml <= 256 /\ UNIT + stride * cnt <= ml * 4096
  /\ (stride <= size \/ 28 <= sc) /\ (cnt - 1 = 0 -> 27 <= sc) /\ stride * cnt < 2 ^ 20 /\ 16 <= stride /\ stride mod 16 = 0
  /\ ml * 4096 = round_up_pg needed /\ 0 < needed
  /\ mr' = mkMeta None None (Some p) (mask_upto ai) (mask_upto (cnt - 1) - mask_upto ai) (cnt - 1) 1 sc ml.
Proof.
  unfold ml in *. pose proof (grp_ok_sound sc cnt needed GRP) as G. cbn zeta in G.
  (first [ dand11 G as G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 | destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11) ]).
  assert (Emr : mr' = mkMeta None None (Some p) (mask_upto ai) (mask_upto (cnt - 1) - mask_upto ai) (cnt - 1) 1 sc ml).
  { (* [comment removed for export] *)
    cbv beta iota delta [mr' agG m_set_sizeclass m_set_freeable m_set_last_idx m_set_mem m_set_freed m_set_avail m_set_maplen m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen meta0].
    rewrite land31_id by lia. rewrite land63_id by lia. rewrite land52_id by lia. reflexivity. }
  assert (Es : get_stride mr' = (if (cnt - 1 =? 0) && negb (ml =? 0) then ml * 4096 - UNIT else UNIT * size_class sc)).
  { rewrite Emr. unfold get_stride. cbn. reflexivity. }
  cbn zeta. unfold ml in *.
  assert (RU : needed / 4096 * 4096 = round_up_pg needed).
  { destruct (round_up_pg_spec needed) as [A B]. pose proof (Z.div_mod needed 4096 ltac:(lia)). rewrite G2 in H.
    pose proof (Z.div_mod (round_up_pg needed) 4096 ltac:(lia)). rewrite B in H0. nia. }
  rewrite Es. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try assumption; try lia.
Qed.

#[using="IM NIm TF EMP Hai0 Hai Hsc GRP NS Lr Kr Hr INV X r"] Theorem ag_top_ok :
  INVL X' st' L BL LS /\ TF0 st' /\ MR st' m = mr'
  /\ s_groups st' !! p = Some (mkGhdr (Some m) ai)
  /\ (forall sc0, active st' sc0 = active st2 sc0) /\ (forall h, get_head st' h = get_head st2 h)
  /\ s_tick st' = s_tick st2.
Proof.
  pose proof top_facts as TFX. cbn zeta in TFX. (first [ dand12 TFX as F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 Emr | destruct TFX as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & Emr) ]).
  pose proof top_INV3 as INV3. (first [ pose proof (INV3) as dR_3; dand7 dR_3 as IR IA IM3 IL IG IS ISH | pose proof INV3 as (IR & IA & IM3 & IL & IG & IS & ISH) ]).
  assert (MR'm : MR st' m = mr') by (unfold st'; rewrite agt_MR_m; unfold mr'; rewrite top_MR4; reflexivity).
  pose proof (created_masks ai (cnt - 1) Hai ltac:(lia)) as CM. cbn zeta in CM. (first [ dand8 CM as M1 M2 M3 M4 M5 M6 M7 _ | destruct CM as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & _) ]).
  assert (Sp : get_stride mr' > 0) by lia.
  assert (INV' : INVL X' st' L BL LS).
  { apply (INVL_create X X' st3 st' L BL LS m p ai mr' INV3 ltac:(left; reflexivity)).
    all: try (rewrite Emr; cbn [m_prev m_next m_mem m_freeable m_maplen m_last_idx m_sizeclass m_avail m_freed]).
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - lia.
    - lia.
    - lia.
    - exact Hai0.
    - left. lia.
    - unfold tbit. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try lia; assumption.
    - intros _. rewrite <- Emr. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia.
    - rewrite <- Emr. lia.
    - cbn. unfold UNIT. split; [lia| reflexivity].
    - left. reflexivity.
    - reflexivity.
    - intros x Hx. cbn in Hx |- *. split; [right; exact Hx|]. intros ->. exact (NIm Hx).
    - reflexivity.
    - reflexivity.
    - intros i Hi. unfold tbit. cbn [x_pend X'].
      destruct (Z.le_gt_cases i ai).
      + apply one5_A; [apply M7; lia| intros Hf; exact (M5 i ltac:(lia) (M7 i ltac:(lia)) Hf)| discriminate].
      + apply one5_B; [intros Ha; pose proof (M3 i ltac:(lia) Ha); lia| apply M6; lia| discriminate].
    - intros s Hs. discriminate.
    - intros _. exact EMP.
    - left. rewrite <- Emr. cbn [snd fst x_orph x_pend X X' p]. split; [lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      exists r. split; [exact Hr|]. split; [exact Kr|]. rewrite Lr. replace (m_maplen mr') with ml by (rewrite Emr; reflexivity).
      split; [exact F10|]. unfold cnt_of. replace (m_last_idx mr') with (cnt - 1) by (rewrite Emr; reflexivity). lia.
    - intros i Hi. apply known_noshadow. exact NS.
    - intros o v tk Ho Hc. exfalso. unfold get_shadow in Hc. cbn in Hc. rewrite NS in Hc. cbn in Hc. rewrite lookup_empty in Hc. discriminate.
    - unfold st'. rewrite agt_metas. unfold st4. rewrite s_metas_upd_meta. apply map_eq. intros kk. destruct (decide (kk = m)) as [->|NE].
      + rewrite !lookup_insert_eq. f_equal. fold st4. first [rewrite top_MR4; exact Emr| unfold mr'; f_equal; exact top_MR4].
      + rewrite !lookup_insert_ne by congruence. reflexivity.
    - unfold st'. rewrite agt_groups. rewrite land31_id by lia. reflexivity.
    - intros s. unfold st'. rewrite (agt_slots st4 sc m p cnt ai s); [| lia| rewrite top_MR4; fold mr'; lia].
      rewrite top_MR4. fold mr'. rewrite Emr. replace (cnt - 1 + 1) with cnt by lia. reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - cbn. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity.
    - pose proof (ia_ctx _ IA) as (C & _). exact C.
    - intros sc0 Hsc0. unfold st'. rewrite agt_usage. replace (cnt - 1 + 1) with cnt by lia. reflexivity.
    - intros sc0 v Hv. unfold st' in Hv. rewrite agt_ctx in Hv. cbn in Hv.
      destruct (Z.eq_dec sc0 sc) as [->|NE]; [lia|]. rewrite lookup_insert_ne in Hv by congruence. exact (ia_usage_keys _ IA sc0 v Hv). }
  split; [exact INV'|]. split.
  { unfold st'. apply agt_TF0. apply (TF0_ctrl st2); [reflexivity| reflexivity| exact TF]. }
  split; [exact MR'm|]. split; [unfold st'; rewrite agt_groups, lookup_insert_eq, land31_id by lia; reflexivity|].
  split; [intros; reflexivity|]. split; [intros h; destruct h; reflexivity| reflexivity].
Qed.
End AG_TOP.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma set_metas_id st v : v = s_metas st -> Malloc.set_metas v st = st.
Proof. destruct st; cbn; intros ->; reflexivity. Qed.

Definition hdr3_f (i : Z) : bool := (Z.land (Z.lor (Z.land i 31) 192) 255 =? i + 192) && (Z.land (i + 192) 31 =? i).
Lemma hdr3_all : forallb hdr3_f (zrange 0 32) = true. Proof. vm_compute. reflexivity. Qed.
Lemma hdr3_facts i : 0 <= i <= 31 -> Z.land (Z.lor (Z.land i 31) 192) 255 = i + 192 /\ Z.land (i + 192) 31 = i.
Proof.
  intros Hi. pose proof (forallb_zrange hdr3_f 0 32 i hdr3_all ltac:(lia) ltac:(lia)) as H. unfold hdr3_f in H.
  apply andb_true_iff in H as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. auto.
Qed.

Section AG_NESTED.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
Variables (idle0 : list aptr) (st1 : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (m g bg : aptr) (aig idx sc cnt : Z).
Let size := UNIT * size_class sc.
Let j := size_to_class (UNIT + cnt * size - IB).
Let p : aptr := (fst bg, sstart (MR st1 g) idx).
Let X := mkX (m :: idle0) [] (Some p) None None.
Let X' := mkX idle0 [] None None (Some m).
Hypothesis INV : INVL X st1 L BL LS.
Hypothesis Hg : s_groups st1 !! bg = Some (mkGhdr (Some g) aig).
Hypothesis Hidx : 0 <= idx <= m_last_idx (MR st1 g).
Hypothesis SCg : m_sizeclass (MR st1 g) = j.
Hypothesis STR : get_stride (MR st1 g) = UNIT * size_class j.
Hypothesis NEST : nest_ok sc cnt = true.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis EMP : LS (LActive sc) = [].
Hypothesis TF : TF2 st1.
Hypothesis NIm : ~ In m idle0.
Let st2 := nest_layout st1 g idx j size cnt.
Let st3 := upd_meta m (m_set_maplen 0) st2.
Let st' := agt st3 sc m p cnt (cnt - 1).
Let mr' := agG sc p cnt (cnt - 1) meta0.

Let IM := proj1 (proj2 (proj2 INV)).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))).
Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

#[using="IM INV X p idx bg g LS BL L idle0 Clg"] Lemma nst_MRm : MR st1 m = meta0.
Proof. unfold MR, get_meta_rec. rewrite (proj1 (im_idle _ _ _ IM m ltac:(left; reflexivity))). reflexivity. Qed.
#[using="Hg aig"] Lemma nst_hosts : hosts st1 bg g. Proof. exists aig. exact Hg. Qed.

#[using="Hsc NEST"] Lemma nst_facts :
  2 <= cnt <= 32 /\ sc < j <= 23 /\ UNIT + cnt * size <= UNIT * size_class j /\ size * cnt < 2 ^ 20
  /\ 16 <= size /\ size mod 16 = 0 /\ size_class j <= 127
  /\ mr' = mkMeta None None (Some p) (mask_upto (cnt - 1)) 0 (cnt - 1) 1 sc 0
  /\ get_stride mr' = size.
Proof.
  pose proof (nest_ok_sound sc cnt NEST) as N0. cbn zeta in N0. fold size in N0. fold j in N0.
  (first [ dand6 N0 as N1 N2 N3 N4 N5 N6 | destruct N0 as (N1 & N2 & N3 & N4 & N5 & N6) ]).
  pose proof (size_class_bound sc Hsc) as SB.
  assert (Emr : mr' = mkMeta None None (Some p) (mask_upto (cnt - 1)) 0 (cnt - 1) 1 sc 0).
  { cbv beta iota delta [mr' agG m_set_sizeclass m_set_freeable m_set_last_idx m_set_mem m_set_freed m_set_avail m_set_maplen m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen meta0].
    rewrite land31_id by lia. rewrite land63_id by lia. rewrite Z.sub_diag. reflexivity. }
  assert (SJ : size_class j <= 127) by (change 127 with (size_class 23); apply size_class_le; lia).
  OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try lia.
  - unfold size, UNIT. lia.
  - unfold size, UNIT. rewrite Z.mul_comm. apply Z_mod_mult.
  - exact Emr.
  - rewrite Emr. unfold get_stride. cbn -[Z.eqb size_class Z.mul]. replace (cnt - 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
Qed.

(* [comment removed for export] *)
#[using="mr' TF Hsc NEST STR Hidx Hg INV aig"] Lemma nst_layout :
  INVL X st2 L BL LS /\ ctrl_eq st1 st2 /\ s_tick st2 = s_tick st1
  /\ known st2 (aadd p (-3)) (Z.land (Z.lor (Z.land idx 31) 192) 255)
  /\ known st2 (aadd p (-2)) (Z.land ((snd p - (snd bg + UNIT)) / UNIT) 255)
  /\ known st2 (aadd (aadd p (-2)) 1) (Z.land (Z.shiftr ((snd p - (snd bg + UNIT)) / UNIT) 8) 255)
  /\ (forall k, 0 <= k <= cnt -> known st2 (aadd p (UNIT + k * size - 4)) 0)
  /\ st2 = wrs (nl_list st1 g bg idx size cnt) st1.
Proof.
  (first [ pose proof (nst_facts) as dR_6; dand9 dR_6 as N1 N2 N3 N4 N5 N6 N7 _ _ | pose proof nst_facts as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & _ & _) ]).
  (first [ pose proof ((nest_layout_ok X st1 L BL LS g bg aig idx j size cnt INV Hg Hidx eq_refl STR N6 N5 ltac:(lia) ltac:(rewrite STR; exact N3)
                (TF2_TF X st1 L BL LS INV TF))) as dR_7; dand9 dR_7 as A _ C D E F G H _ | pose proof (nest_layout_ok X st1 L BL LS g bg aig idx j size cnt INV Hg Hidx eq_refl STR N6 N5 ltac:(lia) ltac:(rewrite STR; exact N3)
                (TF2_TF X st1 L BL LS INV TF)) as (A & _ & C & D & E & F & G & H & _) ]).
  refine (conj A (conj C (conj D (conj E (conj F (conj G (conj H _))))))). apply (nl_eq X st1 L BL LS g bg aig idx j size cnt INV Hg STR).
Qed.

#[using="IM mr' TF Hsc NEST STR Hidx Hg INV X p aig bg LS BL L idle0 Clg"] Lemma nst_st3 : st3 = st2.
Proof.
  (first [ pose proof (nst_layout) as dR_8; dand3 dR_8 as INV2 CE _ | pose proof nst_layout as (INV2 & CE & _) ]).
  unfold st3, upd_meta, put_meta. apply set_metas_id.
  assert (E : get_meta_rec st2 m = meta0) by (rewrite (get_meta_rec_ext st1 st2 m (ce_metas _ _ CE)); exact nst_MRm).
  rewrite E. change (m_set_maplen 0 meta0) with meta0. apply insert_id. rewrite (ce_metas _ _ CE). exact (proj1 (im_idle _ _ _ IM m ltac:(left; reflexivity))).
Qed.

#[using="IM NIm TF EMP Hsc NEST STR SCg Hidx Hg INV X aig"] Theorem ag_nested_ok :
  INVL X' st' L BL LS /\ TF2 st' /\ MR st' m = mr'
  /\ s_groups st' !! p = Some (mkGhdr (Some m) (cnt - 1))
  /\ (forall sc0, active st' sc0 = active st1 sc0) /\ (forall h, get_head st' h = get_head st1 h)
  /\ s_tick st' = s_tick st1.
Proof.
  (first [ pose proof (nst_facts) as dR_9; dand9 dR_9 as N1 N2 N3 N4 N5 N6 N7 Emr Es | pose proof nst_facts as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & Emr & Es) ]).
  (first [ pose proof (nst_layout) as dR_10; dand8 dR_10 as INV2 CE TK2 K3 K2 K1 KZ Ewrs | pose proof nst_layout as (INV2 & CE & TK2 & K3 & K2 & K1 & KZ & Ewrs) ]).
  pose proof INV as (IR1 & IA1 & IM1 & IL1 & IG1 & IS1 & ISH1).
  (first [ pose proof (INV2) as dR_11; dand7 dR_11 as IR IA IM2 IL IG2 IS2 ISH | pose proof INV2 as (IR & IA & IM2 & IL & IG2 & IS2 & ISH) ]).
  pose proof nst_st3 as E3.
  assert (MR2 : forall x, MR st2 x = MR st1 x) by (intros x; apply MR_ext; exact (ce_metas _ _ CE)).
  assert (MR'm : MR st' m = mr') by (unfold st'; rewrite agt_MR_m; unfold mr'; rewrite E3, MR2, nst_MRm; reflexivity).
  pose proof (created_masks (cnt - 1) (cnt - 1) ltac:(lia) ltac:(lia)) as CM. cbn zeta in CM. (first [ dand8 CM as M1 M2 M3 M4 M5 M6 M7 _ | destruct CM as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & _) ]).
  rewrite Z.sub_diag in *.
  pose proof (g_li _ _ _ _ _ _ (ig_ok _ _ _ IG1 _ _ _ Hg)) as LI31.
  pose proof (hdr3_facts idx ltac:(lia)) as [H3a H3b].
  pose proof (sstart_res X st1 L BL LS INV bg g idx nst_hosts) as PR. fold p in PR.
  assert (P16 : snd p mod 16 = 0).
  { unfold p. cbn [snd]. unfold IB in PR. pose proof (Z.div_mod (sstart (MR st1 g) idx - 4) 16 ltac:(lia)). pose proof (Z.div_mod (sstart (MR st1 g) idx) 16 ltac:(lia)).
    pose proof (Z.mod_pos_bound (sstart (MR st1 g) idx) 16 ltac:(lia)). lia. }
  pose proof (hosts_gbase _ _ _ IM1 _ _ nst_hosts) as GB.
  assert (S0 : sstart (MR st1 g) idx = snd bg + UNIT + get_stride (MR st1 g) * idx) by (unfold sstart; rewrite GB; reflexivity).
  assert (Q : (snd p - snd bg - UNIT) / UNIT = size_class j * idx).
  { unfold p. cbn [snd]. rewrite S0, STR. unfold UNIT. replace (snd bg + 16 + 16 * size_class j * idx - snd bg - 16) with ((size_class j * idx) * 16) by lia. apply Z.div_mul. lia. }
  assert (Qr : 0 <= size_class j * idx < 2 ^ 16).
  { pose proof (size_class_bound j ltac:(clear - N2 Hsc; lia)) as SB.
    (first [ pose proof ((g_stride _ _ _ _ _ _ (ig_ok _ _ _ IG1 _ _ _ Hg) ltac:(rewrite SCg; clear - N2; lia))) as dR_13; dand3 dR_13 as _ _ LT | destruct (g_stride _ _ _ _ _ _ (ig_ok _ _ _ IG1 _ _ _ Hg) ltac:(rewrite SCg; clear - N2; lia)) as (_ & _ & LT) ]).
    rewrite STR in LT. unfold cnt_of in LT. clear - SB LT Hidx. unfold UNIT in LT. nia. }
  assert (NH : s_groups st1 !! p = None).
  { pose proof (is_part _ _ _ IS1 _ _ _ idx Hg Hidx) as P5. cbn zeta in P5. rewrite (slot_start'_eq _ _ _ IM1 _ _ _ nst_hosts) in P5. fold p in P5.
    destruct (s_groups st1 !! p) eqn:E; [| reflexivity]. exfalso. (first [ dand11 P5 as _ _ _ _ _ _ _ _ _ _ nDE | destruct P5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & nDE) ]). apply nDE. split; [congruence| reflexivity]. }
  assert (INV' : INVL X' st' L BL LS).
  { apply (INVL_create X X' st2 st' L BL LS m p (cnt - 1) mr' INV2 ltac:(left; reflexivity)).
    all: try (rewrite Emr; cbn [m_prev m_next m_mem m_freeable m_maplen m_last_idx m_sizeclass m_avail m_freed]).
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - lia.
    - lia.
    - lia.
    - intros _. reflexivity.
    - left. lia.
    - unfold tbit. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try lia; try assumption; try (intros i Hi Hb; rewrite Z.bits_0 in Hb; discriminate).
    - intros _. rewrite <- Emr, Es. unfold size. clear - N1 N4. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia.
    - rewrite <- Emr, Es. lia.
    - unfold UNIT. split; [| exact P16]. unfold p. cbn [snd]. pose proof (sstart0 _ _ _ IM1 _ _ nst_hosts). pose proof (sstart_mono _ _ _ IG1 _ _ 0 idx nst_hosts ltac:(lia)).
      (first [ pose proof ((hosts_ok _ _ _ IG1 _ _ nst_hosts)) as dR_15; dex1 dR_15 as a0; destruct dR_15 as [_ GO] | pose proof ((hosts_ok _ _ _ IG1 _ _ nst_hosts)) as dR_15; dand3 dR_15 as a0 _ GO | destruct (hosts_ok _ _ _ IG1 _ _ nst_hosts) as (a0 & _ & GO) ]). pose proof (g_align _ _ _ _ _ _ GO). unfold UNIT in *. lia.
    - left. reflexivity.
    - reflexivity.
    - intros x Hx. cbn [x_idle X X'] in Hx |- *. split; [right; exact Hx|]. intros ->. exact (NIm Hx).
    - reflexivity.
    - reflexivity.
    - intros i Hi. unfold tbit. cbn [x_pend X']. apply one5_A; [apply M7; lia| rewrite Z.bits_0; discriminate| discriminate].
    - intros s Hs. discriminate.
    - intros _. exact EMP.
    - right. rewrite <- Emr. cbn [x_pend x_orph X X']. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      exists g, idx, bg. rewrite !MR2.
      split; [rewrite (ce_slots _ _ CE); unfold p; rewrite <- (slot_start'_eq _ _ _ IM1 _ _ idx nst_hosts); exact (is_total _ _ _ IS1 _ _ _ nst_hosts Hidx)|].
      split; [apply (proj2 (hosts_ext st1 st2 (ce_groups _ _ CE) bg g)); exact nst_hosts|].
      split; [reflexivity|]. split; [exact Hidx|]. split; [reflexivity|].
      split; [rewrite Es; unfold p; cbn [snd]; rewrite STR; unfold cnt_of; replace (m_last_idx mr') with (cnt - 1) by (rewrite Emr; reflexivity); unfold size in N3 |- *; lia|].
      split; [rewrite SCg; replace (m_sizeclass mr') with sc by (rewrite Emr; reflexivity); lia|].
      split; [rewrite STR, SCg; reflexivity|].
      split; [exists (idx + 192); split; [| split; [exact H3b| clear - Hidx LI31; lia]]; rewrite <- H3a; exact K3|].
      rewrite Q. unfold byte_of. rewrite Z.mul_0_r, Z.shiftr_0_r, Z.mul_1_r. rewrite <- Q.
      replace (snd p - snd bg - UNIT) with (snd p - (snd bg + UNIT)) by lia.
      split; [exact K2|]. split; [replace (fst p, snd p - 1) with (aadd (aadd p (-2)) 1) by (unfold aadd; cbn [fst snd]; f_equal; lia); exact K1|].
      replace ((snd p - (snd bg + UNIT)) / UNIT) with (size_class j * idx) by (rewrite <- Q; f_equal; lia). exact Qr.
    - rewrite <- Emr. intros i Hi. rewrite Es. replace (fst p, snd p + UNIT + size * i - IB) with (aadd p (UNIT + i * size - 4)) by (unfold aadd, IB; f_equal; lia).
      apply KZ. unfold cnt_of in Hi. rewrite ?Emr in Hi. cbn [m_last_idx] in Hi. lia.
    - intros o v tk Ho Hc. rewrite Ewrs in Hc. rewrite wrs_cells_other in Hc.
      + rewrite TK2. exact (TF2_ghdr_old X st1 L BL LS INV p TF P16 o v tk Ho Hc).
      + unfold nl_list. rewrite map_app. intros Hin. apply in_app_iff in Hin. unfold p in Ho. cbn [snd] in Ho. destruct Hin as [Hin|Hin].
        * cbn [map fst In] in Hin. destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; apply (f_equal snd) in E; unfold aadd in E; cbn [fst snd] in E; clear - E Ho N1 N5; lia.
        * apply in_zlist in Hin as (k & Hk & E). apply (f_equal snd) in E. unfold aadd in E. cbn [fst snd] in E. unfold UNIT in E.
          assert (0 <= k * size) by (apply Z.mul_nonneg_nonneg; clear - Hk N5; lia). clear - E Ho H Hk N5. lia.
    - unfold st'. rewrite agt_metas. rewrite E3. apply map_eq. intros kk. destruct (decide (kk = m)) as [->|NE].
      + rewrite !lookup_insert_eq. f_equal. rewrite MR2, nst_MRm. first [exact Emr| reflexivity].
      + rewrite !lookup_insert_ne by congruence. reflexivity.
    - unfold st'. rewrite agt_groups, E3. rewrite land31_id by lia. reflexivity.
    - intros s. unfold st'. rewrite (agt_slots st3 sc m p cnt (cnt - 1) s); [| lia| rewrite E3, MR2, nst_MRm; fold mr'; rewrite Es; lia].
      rewrite E3, MR2, nst_MRm. fold mr'. rewrite Emr. replace (cnt - 1 + 1) with cnt by lia. reflexivity.
    - unfold st'. rewrite agt_shadow, E3. reflexivity.
    - unfold st'. rewrite agt_regions, E3. reflexivity.
    - unfold st'. rewrite agt_areas, E3. reflexivity.
    - unfold st'. rewrite agt_next_rid, E3. reflexivity.
    - unfold st'. rewrite agt_tick, E3. reflexivity.
    - unfold st'. rewrite agt_secret, E3. reflexivity.
    - unfold st'. rewrite agt_reserved, E3. reflexivity.
    - unfold st'. rewrite agt_ctx, E3. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity.
    - unfold st'. rewrite agt_ctx, E3. cbn [c_mmap_counter set_usage_map]. rewrite (ce_ctx _ _ CE). pose proof (ia_ctx _ IA1) as (C & _). exact C.
    - intros sc0 Hsc0. unfold st'. rewrite agt_usage, E3. replace (cnt - 1 + 1) with cnt by lia. reflexivity.
    - intros sc0 v Hv. unfold st' in Hv. rewrite agt_ctx, E3 in Hv. cbn [c_usage set_usage_map] in Hv.
      destruct (Z.eq_dec sc0 sc) as [->|NE]; [lia|]. rewrite lookup_insert_ne in Hv by congruence. rewrite (ce_ctx _ _ CE) in Hv. exact (ia_usage_keys _ IA1 sc0 v Hv). }
  split; [exact INV'|]. split.
  { (* [comment removed for export] *)
    unfold TF2. unfold st'. rewrite E3.
    apply (TW_mono _ (fun q => PS st1 q \/ In q (map fst (nl_list st1 g bg idx size cnt)))).
    2:{ apply agt_TW. rewrite Ewrs. apply TW_wrs; [| intros q Hq; right; exact Hq]. apply (TW_mono _ (PS st1)); [intros q Hq; left; exact Hq| exact TF]. }
    intros q [Hq|Hq].
    - apply (PS_mono st1); [| exact Hq]. apply geom_kept_of.
      + intros b h Hb. rewrite <- E3. fold st'. unfold st'. rewrite agt_groups, E3, (ce_groups _ _ CE).
        rewrite lookup_insert_ne; [exact Hb|]. intros ->. rewrite NH in Hb. discriminate.
      + intros b x Hx. rewrite <- E3. fold st'. rewrite (agt_MR_other st3 sc m p cnt (cnt - 1) x), E3, MR2; [reflexivity|].
        intros ->. exact (idle_not_live _ _ _ _ _ INV m ltac:(left; reflexivity) (ex_intro _ b Hx)).
    - assert (Hm' : hosts (agt st2 sc m p cnt (cnt - 1)) p m) by (exists (Z.land (cnt - 1) 31); rewrite agt_groups, lookup_insert_eq; reflexivity).
      assert (R' : MR (agt st2 sc m p cnt (cnt - 1)) m = mr') by (rewrite <- E3; exact MR'm).
      exists p, m. split; [exact Hm'|]. rewrite R'.
      unfold nl_list in Hq. rewrite map_app in Hq. apply in_app_iff in Hq. destruct Hq as [Hq|Hq].
      + cbn [map fst In app] in Hq. assert (E : fst q = fst p /\ snd p - 3 <= snd q <= snd p - 1).
        { destruct Hq as [E|[E|[E|[E|[E|[]]]]]]; subst q; unfold aadd, p; cbn [fst snd]; split; first [reflexivity| lia]. }
        destruct E as [E1 E2]. split; [symmetry; exact E1|]. right. split; [rewrite Emr; reflexivity| exact E2].
      + apply in_zlist in Hq as (k & Hk & ->). unfold aadd. cbn [fst snd]. split; [reflexivity|]. left. exists k.
        split; [unfold cnt_of; rewrite Emr; cbn [m_last_idx]; clear - Hk; lia|].
        unfold sstart. replace (gbase mr') with p by (rewrite Emr; reflexivity). rewrite Es. unfold p. cbn [snd]. unfold sstart, UNIT, IB. lia. }
  split; [exact MR'm|].
  split; [unfold st'; rewrite agt_groups, E3, lookup_insert_eq, land31_id by lia; reflexivity|].
  split; [intros sc0; unfold st'; rewrite agt_active, E3; unfold active, ctx; rewrite (ce_ctx _ _ CE); reflexivity|].
  split; [intros h; unfold st'; rewrite agt_get_head, E3; unfold get_head, active, ctx; rewrite (ce_ctx _ _ CE); reflexivity|].
  unfold st'. rewrite agt_tick, E3. exact TK2.
Qed.
End AG_NESTED.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma round_up_pg_div x : 0 < x -> (x + 4095) / 4096 * 4096 = round_up_pg x.
Proof.
  intros Hx. destruct (round_up_pg_spec x) as [A B].
  pose proof (Z.div_mod (x + 4095) 4096 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (x + 4095) 4096 ltac:(lia)) as M1.
  pose proof (Z.div_mod (round_up_pg x) 4096 ltac:(lia)) as D2. rewrite B in D2. nia.
Qed.

Definition F63 (rid : N) (ml : Z) (mr : meta) : meta :=
  m_set_freed 0 (m_set_avail 0 (m_set_maplen ml (m_set_sizeclass 63 (m_set_freeable 1 (m_set_last_idx 0 (m_set_mem (Some (rid, 0)) mr)))))).

Section CREATE63.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
Variables (st3 : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (g : aptr) (rid : N) (r : region) (needed : Z).
Let X := mkX [g] [] None (Some rid) None.
Let p : aptr := (rid, 0).
Let X' := mkX [] [] (Some (rid, 16)) None None.
Hypothesis INV : INVL X st3 L BL LS.
Hypothesis Hr : s_regions st3 !! rid = Some r.
Hypothesis Kr : r_kind r = RKGroup.
Hypothesis Lr : r_len r = needed.
Hypothesis NS : s_shadow st3 !! rid = None.
Hypothesis Hn : 0 < needed < 2 ^ 63.
Hypothesis TF : TF0 st3.
Let ml := (needed + 4095) / 4096.
Let st4 := upd_meta g (F63 rid ml) st3.
Let st5 := put_group p (Some g) (group_active_idx st4 p) (hdr_havoc p st4).
Let st6 := add_slots g p (get_stride (get_meta_rec st5 g)) 1 st5.
Let mr' := mkMeta None None (Some p) 0 0 0 1 63 ml.

Let IR := proj1 INV.
Let IM := proj1 (proj2 (proj2 INV)).

#[using="IM INV X rid LS BL L Clg"] Lemma c63_MRg : MR st3 g = meta0.
Proof. unfold MR, get_meta_rec. rewrite (proj1 (im_idle _ _ _ IM g ltac:(left; reflexivity))). reflexivity. Qed.

#[using="Hn"] Lemma c63_ml : 1 <= ml < 2 ^ 52 /\ ml * 4096 = round_up_pg needed.
Proof.
  unfold ml. split; [| apply round_up_pg_div; lia].
  split; [apply Z.div_le_lower_bound; lia| apply Z.div_lt_upper_bound; lia].
Qed.

#[using="Hn"] Lemma c63_F : F63 rid ml meta0 = mr'.
Proof.
  pose proof c63_ml as [M _]. cbv beta iota delta [mr' agG F63 m_set_sizeclass m_set_freeable m_set_last_idx m_set_mem m_set_freed m_set_avail m_set_maplen m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen meta0].
  rewrite land52_id by lia. reflexivity.
Qed.

#[using="Hn"] Lemma c63_stride : get_stride mr' = ml * 4096 - UNIT.
Proof. pose proof c63_ml as [M _]. unfold get_stride, mr'. cbn -[Z.mul Z.sub Z.eqb]. replace (ml =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. Qed.

#[using="IR INV X g LS BL L Clg"] Lemma c63_nogroup : s_groups st3 !! p = None.
Proof. (first [ pose proof ((ir_orph _ _ _ IR rid eq_refl)) as dR_16; dex1 dR_16 as r0; dand3 dR_16 as _ _ NG | pose proof ((ir_orph _ _ _ IR rid eq_refl)) as dR_16; dand4 dR_16 as r0 _ _ NG | destruct (ir_orph _ _ _ IR rid eq_refl) as (r0 & _ & _ & NG) ]). apply NG. reflexivity. Qed.

#[using="IM Hn INV X LS BL L Clg"] Lemma c63_rec5 : get_meta_rec st5 g = mr'.
Proof. unfold get_meta_rec. cbn -[F63 get_meta_rec]. rewrite lookup_insert_eq. fold (MR st3 g). rewrite c63_MRg. exact c63_F. Qed.

#[using="IM IR TF Hn NS Lr Kr Hr INV X r"] Theorem create63_ok :
  INVL X' st6 L BL LS /\ TF0 st6 /\ MR st6 g = mr' /\ s_groups st6 !! p = Some (mkGhdr (Some g) 0)
  /\ s_ctx st6 = s_ctx st3 /\ s_tick st6 = s_tick st3 /\ s_regions st6 = s_regions st3
  /\ get_stride mr' = ml * 4096 - UNIT /\ ml * 4096 = round_up_pg needed.
Proof.
  pose proof c63_ml as [M RU]. pose proof c63_stride as Es.
  pose proof INV as (IR0 & IA & IM0 & IL & IG & IS & ISH).
  assert (Emetas : s_metas st6 = <[g := mr']> (s_metas st3)).
  { change (s_metas st6) with (s_metas st4). unfold st4. rewrite s_metas_upd_meta. fold (MR st3 g). rewrite c63_MRg, c63_F. reflexivity. }
  assert (MR'g : MR st6 g = mr') by (unfold MR, get_meta_rec; rewrite Emetas, lookup_insert_eq; reflexivity).
  assert (GAI : group_active_idx st4 p = 0).
  { unfold group_active_idx, get_group. change (s_groups st4) with (s_groups st3). rewrite c63_nogroup. reflexivity. }
  assert (Egroups : s_groups st6 = <[p := mkGhdr (Some g) 0]> (s_groups st3)).
  { change (s_groups st6) with (s_groups st5). unfold st5. rewrite GAI. reflexivity. }
  assert (INV' : INVL X' st6 L BL LS).
  { apply (INVL_create X X' st3 st6 L BL LS g p 0 mr' INV ltac:(left; reflexivity)).
    all: cbn [m_prev m_next m_mem m_freeable m_maplen m_last_idx m_sizeclass m_avail m_freed mr'].
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - lia.
    - lia.
    - lia.
    - intros _. reflexivity.
    - right. lia.
    - unfold tbit. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try lia; intros i Hi Hb; rewrite Z.testbit_0_l in Hb; discriminate.
    - lia.
    - fold mr'. rewrite Es. unfold UNIT. split; [lia|]. replace (ml * 4096 - 16) with ((ml * 256 - 1) * 16) by lia. apply Z_mod_mult.
    - cbn. unfold UNIT. split; [lia| reflexivity].
    - right. split; reflexivity.
    - reflexivity.
    - intros x Hx. destruct Hx.
    - reflexivity.
    - reflexivity.
    - intros i Hi. unfold tbit. cbn [x_pend X' fst snd p]. apply one5_E; [rewrite Z.testbit_0_l; discriminate| rewrite Z.testbit_0_l; discriminate|].
      assert (i = 0) by lia. subst i. rewrite Z.mul_0_r. reflexivity.
    - intros s Hs. cbn [x_pend X'] in Hs. inversion Hs. subst s. exists 0. split; [lia|]. cbn [fst snd p]. rewrite Z.mul_0_r. reflexivity.
    - intros H. lia.
    - left. cbn [x_orph x_pend X X' fst snd p]. split; [lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      exists r. split; [exact Hr|]. split; [exact Kr|]. rewrite Lr. split; [exact RU|]. fold mr'. rewrite Es. unfold UNIT. lia.
    - intros i Hi. apply known_noshadow. exact NS.
    - intros o v tk Ho Hc. exfalso. unfold get_shadow in Hc. cbn [fst p] in Hc. rewrite NS in Hc. cbn in Hc. rewrite lookup_empty in Hc. discriminate.
    - exact Emetas.
    - exact Egroups.
    - intros s. unfold st6. rewrite c63_rec5. rewrite lookup_add_slots; [| lia| rewrite Es; unfold UNIT; lia]. fold mr'. reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity.
    - pose proof (ia_ctx _ IA) as (C & _). exact C.
    - intros sc0 Hsc0. replace (sc0 =? 63) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Z.add_0_r. reflexivity.
    - intros sc0 v Hv. exact (ia_usage_keys _ IA sc0 v Hv). }
  split; [exact INV'|]. split.
  { apply (TF0_ctrl (hdr_havoc p st4)); [reflexivity| reflexivity|]. apply TF0_hdr_havoc. apply (TF0_ctrl st3); [reflexivity| reflexivity| exact TF]. }
  split; [exact MR'g|]. split; [rewrite Egroups, lookup_insert_eq; reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact Es| exact RU].
Qed.
End CREATE63.
End MI_Wm9j.

Module MI_WSlot.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require STree Malloc KInv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_List.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Inv MI_Kit MI_Arith MI_Geom MI_List MI_Ext MI_S421.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_WFree.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Ws22.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_W2ig.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_W2ig MI_W3do.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_WTry2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_WTry2 MI_Wp9i MI_Wgyo MI_Cnt.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.STree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malloc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_List.MI_Tree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Kit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Arith OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Geom OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_List OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ext OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_S421 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres2.MI_Pres1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres4.MI_Pres3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WFree.MI_Read OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ws22 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_W2ig.MI_Lsjc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_W2ig OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_W3do OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WTry2.MI_WTry OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WTry2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Wp9i OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Wgyo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Cnt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_TF2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_Wm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.  (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Definition X_as (idle : list aptr) : extras := mkX idle [] None None None.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition GP (st st' : mstate) : Prop :=
  (forall rid r, s_regions st !! rid = Some r -> r_kind r = RKGroup -> s_regions st' !! rid = Some r)
  /\ s_secret st' = s_secret st.
Lemma GP_refl st : GP st st. Proof. split; [intros rid r H _; exact H| reflexivity]. Qed.
Lemma GP_trans a b c : GP a b -> GP b c -> GP a c.
Proof. intros [H1 S1] [H2 S2]. split; [intros rid r H K; exact (H2 rid r (H1 rid r H K) K)| congruence]. Qed.
Lemma GP_eq st st' : s_regions st' = s_regions st -> s_secret st' = s_secret st -> GP st st'.
Proof. intros E S. split; [intros rid r H _; rewrite E; exact H| exact S]. Qed.
Lemma GP_amf st st' : AM_frame st st' -> GP st st'.
Proof. intros AF. split; [exact (amf_regions _ _ AF)| exact (amf_ssec _ _ AF)]. Qed.
Lemma GP_taf st st' sc : TA_frame st st' sc -> GP st st'.
Proof. intros TF. apply GP_eq; [exact (taf_regions _ _ _ TF)| exact (taf_ssec _ _ _ TF)]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition geo_of (r : meta) : (optr * Z * Z * Z)%type := (m_mem r, m_last_idx r, m_maplen r, m_sizeclass r).

Lemma geo_facts r r' : geo_of r' = geo_of r ->
  (forall i, sstart r' i = sstart r i) /\ cnt_of r' = cnt_of r /\ m_maplen r' = m_maplen r /\ get_stride r' = get_stride r.
Proof.
  unfold geo_of. intros H. injection H. intros E1 E2 E3 E4.
  assert (ES : get_stride r' = get_stride r) by (unfold get_stride; rewrite E2, E3, E1; reflexivity).
  unfold sstart, cnt_of, gbase. rewrite ES, E4, E3, E2. auto.
Qed.

Lemma geom_kept_geo st st' :
  (forall b h, s_groups st !! b = Some h -> s_groups st' !! b = Some h) ->
  (forall x, geo_of (MR st' x) = geo_of (MR st x)) ->
  geom_kept st st'.
Proof.
  intros HG HM b m Hm. pose proof Hm as [ai Hb]. split; [exists ai; apply HG; exact Hb|].
  (first [ pose proof ((geo_facts _ _ (HM m))) as dR_1; dand4 dR_1 as A B C _ | destruct (geo_facts _ _ (HM m)) as (A & B & C & _) ]). auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma INVL_idle_sub X idle' st L BL LS :
  (forall x, In x idle' -> In x (x_idle X)) -> INVL X st L BL LS -> INVL (xidle X idle') st L BL LS.
Proof.
  (intros SUB; (first [ intro dR_10; dand7 dR_10 as IR IA IM IL IG IS ISH | intros (IR & IA & IM & IL & IG & IS & ISH) ])).
  split; [exact (inv_R_X X (xidle X idle') st L eq_refl IR)|]. split; [exact IA|].
  split.
  { destruct IM as [Q1 Q2 Q3 Q4 Q5]; constructor; cbn; auto. }
  split; [exact IL|]. split; [exact (inv_G_X X (xidle X idle') st LS eq_refl eq_refl IG)|]. split; [exact (inv_S_X X (xidle X idle') st BL eq_refl IS)| exact ISH].
Qed.

End CEIL.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FREE_IDLE.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
Variables (idle : list aptr) (m : aptr) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis INV : INVL (X_as (m :: idle)) st L BL LS.
Hypothesis NIm : ~ In m idle.
Let st' := fm_st st m.
Let LS' := fupd LS LFree (LS LFree ++ [m]).

Let IM := proj1 (proj2 (proj2 INV)).
Lemma fi_metas : s_metas st !! m = Some meta0.
Proof. exact (proj1 (im_idle _ _ _ IM m ltac:(left; reflexivity))). Qed.
Lemma fi_put : put_meta m meta0 st = st.
Proof. unfold put_meta. apply set_metas_id. apply insert_id. exact fi_metas. Qed.

Lemma free_idle_ok :
  INVL (X_as idle) st' L BL LS'
  /\ s_shadow st' = s_shadow st /\ s_tick st' = s_tick st /\ s_groups st' = s_groups st /\ s_slots st' = s_slots st
  /\ s_regions st' = s_regions st /\ s_next_rid st' = s_next_rid st
  /\ (forall sc, active st' sc = active st sc) /\ (forall sc, usage st' sc = usage st sc)
  /\ c_mmap_counter (s_ctx st') = c_mmap_counter (s_ctx st)
  /\ c_bounces (s_ctx st') = c_bounces (s_ctx st) /\ c_seq (s_ctx st') = c_seq (s_ctx st).
Proof.
  pose proof (INVL_idle_sub (X_as (m :: idle)) idle st L BL LS ltac:(intros x Hx; right; exact Hx) INV) as INV1.
  assert (MRm : MR st m = meta0) by (unfold MR, get_meta_rec; rewrite fi_metas; reflexivity).
  unfold st', fm_st. rewrite fi_put.
  pose proof (INVL_queue (xidle (X_as (m :: idle)) idle) st L BL LS m LFree INV1 ltac:(rewrite MRm; reflexivity)
                ltac:(rewrite fi_metas; discriminate) ltac:(cbn; rewrite MRm; split; [reflexivity| tauto])) as INV2.
  (first [ pose proof ((queue_frame LFree m st)) as dR_2; dand10 dR_2 as F1 F2 F3 F4 F5 F6 F7 F8 F9 FC | destruct (queue_frame LFree m st) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & FC) ]).
  split; [exact INV2|]. split; [exact F2|]. split; [exact F7|]. split; [exact F5|]. split; [exact F6|]. split; [exact F1|]. split; [exact F3|].
  split; [intros sc; change (active ?s sc) with (get_head s (LActive sc)); rewrite queue_head; destruct (decide (LActive sc = LFree)); [discriminate| reflexivity]|].
  split; [intros sc; unfold usage, ctx; rewrite (cb_usage _ _ FC); reflexivity|].
  split; [exact (cb_mc _ _ FC)|]. split; [exact (cb_bounces _ _ FC)| exact (cb_seq _ _ FC)].
Qed.
End FREE_IDLE.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FINISH.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
Variables (T : Type) (idle : list aptr) (st2 : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (m b : aptr) (ai last sc ml : Z) (k : mstate -> M T) (bail : M T).
Let X2 := mkX idle [] None None (Some m).
Hypothesis INV : INVL X2 st2 L BL LS.
Hypothesis Hb : s_groups st2 !! b = Some (mkGhdr (Some m) ai).
Hypothesis Em : MR st2 m = mkMeta None None (Some b) (mask_upto ai) (mask_upto last - mask_upto ai) last 1 sc ml.
Hypothesis Hai : 0 <= ai <= last.
Hypothesis Hl : last <= 31.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis HA : active st2 sc = None.
Hypothesis UND : get_stride (MR st2 m) < UNIT * size_class sc -> ai = 0 /\ last = 0.
Hypothesis TF : TF2 st2.

Let st3 := upd_meta m (fun r => m_set_avail (m_avail r - 1) r) st2.
Let st4 := queue_st (LActive sc) m st3.
Let LS4 := fupd LS (LActive sc) (LS (LActive sc) ++ [m]).
Let s0 : aptr := (fst b, sstart (MR st2 m) 0).

Lemma fin_hosts : hosts st2 b m. Proof. exists ai. exact Hb. Qed.
Lemma fin_empty : LS (LActive sc) = [].
Proof.
  pose proof (il_head _ _ (proj1 (proj2 (proj2 (proj2 INV)))) (LActive sc)) as HH. cbn in HH. rewrite HA in HH.
  destruct (LS (LActive sc)); [reflexivity| discriminate].
Qed.

Lemma mask_upto_pred a : 0 <= a -> mask_upto a - 1 = Z.ldiff (mask_upto a) 1.
Proof.
  intros Ha. apply Z.sub_nocarry_ldiff. apply Z.bits_inj'. intros i Hi. rewrite Z.ldiff_spec, Z.bits_0, testbit_mask_upto by lia.
  destruct (Z.eq_dec i 0) as [->|NZ].
  - cbn. replace (0 <=? a) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
  - replace (Z.testbit 1 i) with false; [reflexivity|]. symmetry. change 1 with (2 ^ 0). rewrite Z.pow2_bits_eqb by lia. apply Z.eqb_neq. lia.
Qed.

Lemma testbit_avail' i : 0 <= i -> Z.testbit (mask_upto ai - 1) i = ((1 <=? i) && (i <=? ai)).
Proof.
  intros Hi. rewrite mask_upto_pred by lia. rewrite Z.ldiff_spec, testbit_mask_upto by lia.
  change 1 with (2 ^ 0) at 1. rewrite Z.pow2_bits_eqb by lia.
  destruct (Z.leb_spec i ai); destruct (Z.leb_spec 1 i); destruct (Z.eqb_spec 0 i); cbn; try reflexivity; lia.
Qed.

Lemma st3_eq : st3 = upd_meta m (fun r => m_set_avail (mask_upto ai - 1) (m_set_freed (mask_upto last - mask_upto ai) r)) st2.
Proof.
  unfold st3, upd_meta. f_equal. fold (MR st2 m). rewrite Em. reflexivity.
Qed.

Lemma fin_INV3 : INVL (mkX idle [] (Some s0) None (Some m)) st3 L BL LS.
Proof.
  rewrite st3_eq.
  pose proof (created_masks ai last Hai Hl) as CM. cbn zeta in CM. (first [ dand8 CM as M1 M2 M3 M4 M5 M6 M7 _ | destruct CM as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & _) ]).
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  assert (Elast : m_last_idx (MR st2 m) = last) by (rewrite Em; reflexivity).
  apply (INVL_mask_change X2 st2 L BL LS m b ai (mask_upto ai - 1) (mask_upto last - mask_upto ai) (Some s0) INV Hb).
  - rewrite Elast. unfold tbit. split; [unfold mask_upto; assert (P2 : 2 ^ 1 <= 2 ^ (ai + 1)) by (apply Z.pow_le_mono_r; lia); change (2 ^ 1) with 2 in P2; lia|].
    split; [exact M2|]. split; [intros i Hi Hb'; rewrite testbit_avail' in Hb' by lia; apply andb_true_iff in Hb' as [_ Hb']; apply Z.leb_le in Hb'; exact Hb'|].
    split; [exact M4|]. split; [| exact M6].
    intros i Hi Ha Hf. rewrite testbit_avail' in Ha by lia. apply andb_true_iff in Ha as [_ Ha]. apply Z.leb_le in Ha. exact (M5 i Hi (M7 i ltac:(lia)) Hf).
  - rewrite Elast. intros i Hi. cbn zeta. unfold tbit.
    pose proof (is_part _ _ _ IS _ _ _ i Hb ltac:(rewrite Elast; exact Hi)) as P5. cbn zeta in P5. rewrite Em in P5. cbn [m_avail m_freed x_pend X2] in P5.
    rewrite <- Em in P5.
    (first [ dand11 P5 as _ _ nAC nAD _ nBC nBD _ _ _ _ | destruct P5 as (_ & _ & nAC & nAD & _ & nBC & nBD & _ & _ & _ & _) ]).
    rewrite testbit_avail' by lia.
    destruct (Z.eq_dec i 0) as [->|NZ].
    + assert (A0 : Z.testbit (mask_upto ai) 0 = true) by (apply M7; lia).
      apply one5_iff_create; [apply one5_E| intros C; exact (nAC (conj A0 C))| intros D; exact (nAD (conj A0 D))].
      * cbn. discriminate.
      * intros F. exact (M5 0 ltac:(lia) A0 F).
      * unfold s0. rewrite (slot_start'_eq _ _ _ IM _ _ 0 fin_hosts). reflexivity.
    + destruct (Z.le_gt_cases i ai) as [Hle|Hgt].
      * assert (A : Z.testbit (mask_upto ai) i = true) by (apply M7; lia).
        apply one5_iff_create; [apply one5_A| intros C; exact (nAC (conj A C))| intros D; exact (nAD (conj A D))].
        -- replace (1 <=? i) with true by (symmetry; apply Z.leb_le; lia). replace (i <=? ai) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
        -- intros F. exact (M5 i ltac:(lia) A F).
        -- unfold s0. rewrite (slot_start'_eq _ _ _ IM _ _ i fin_hosts). intros E. injection E. intros E2.
           pose proof (sstart_lt _ _ _ IG _ _ 0 i fin_hosts ltac:(lia)). pose proof (stride_ge _ _ _ IG _ _ fin_hosts). unfold UNIT in *. lia.
      * assert (F : Z.testbit (mask_upto last - mask_upto ai) i = true) by (apply M6; lia).
        apply one5_iff_create; [apply one5_B| intros C; exact (nBC (conj F C))| intros D; exact (nBD (conj F D))].
        -- replace (i <=? ai) with false by (symmetry; apply Z.leb_gt; lia). rewrite andb_false_r. discriminate.
        -- exact F.
        -- unfold s0. rewrite (slot_start'_eq _ _ _ IM _ _ i fin_hosts). intros E. injection E. intros E2.
           pose proof (sstart_lt _ _ _ IG _ _ 0 i fin_hosts ltac:(lia)). pose proof (stride_ge _ _ _ IG _ _ fin_hosts). unfold UNIT in *. lia.
  - right. split; [intros s Hs; discriminate|]. intros s Hs. inversion Hs. exists 0. rewrite Elast. split; [lia|].
    rewrite (slot_start'_eq _ _ _ IM _ _ 0 fin_hosts). reflexivity.
  - intros NF. exfalso. apply NF. reflexivity.
  - intros NF. exfalso. apply NF. reflexivity.
  - intros NF. exfalso. apply NF. reflexivity.
Qed.

Lemma fin_MR3 : MR st3 m = mkMeta None None (Some b) (mask_upto ai - 1) (mask_upto last - mask_upto ai) last 1 sc ml.
Proof. unfold st3, MR. rewrite get_meta_rec_upd_same. fold (MR st2 m). rewrite Em. reflexivity. Qed.
Lemma fin_MR3_other x : x <> m -> MR st3 x = MR st2 x.
Proof. intros NE. unfold st3, MR. apply get_meta_rec_upd_other. exact NE. Qed.

Lemma fin_queue_eq : queue (LActive sc) m st3 k bail = k st4.
Proof. apply queue_eq; fold (MR st3 m); rewrite fin_MR3; reflexivity. Qed.

Lemma fin_head3 : get_head st3 (LActive sc) = None.
Proof. unfold st3. rewrite get_head_upd_meta. cbn. exact HA. Qed.

Lemma fin_INV4 : INVL (mkX idle [] (Some s0) None (Some m)) st4 L BL LS4.
Proof.
  apply (INVL_queue (mkX idle [] (Some s0) None (Some m)) st3 L BL LS m (LActive sc) fin_INV3).
  - rewrite fin_MR3. reflexivity.
  - unfold st3. rewrite s_metas_upd_meta, lookup_insert_eq. discriminate.
  - cbn. split; [exact Hsc|]. split; [exists b; exists ai; exact Hb|]. split; [rewrite fin_MR3; reflexivity| reflexivity].
Qed.

Lemma fin_LS4 : LS4 (LActive sc) = [m].
Proof. unfold LS4. rewrite fupd_eq, fin_empty. reflexivity. Qed.

Lemma fin_MR4 : geo_of (MR st4 m) = geo_of (MR st3 m) /\ m_avail (MR st4 m) = m_avail (MR st3 m) /\ m_freed (MR st4 m) = m_freed (MR st3 m).
Proof.
  pose proof (queue_data (LActive sc) m st3 m) as D. apply data_of_eq in D. (first [ dand7 D as D1 D2 D3 D4 D5 D6 D7 | destruct D as (D1 & D2 & D3 & D4 & D5 & D6 & D7) ]).
  unfold geo_of. fold st4 in D1, D2, D3, D4, D5, D6, D7. rewrite D1, D4, D7, D6, D2, D3. auto.
Qed.

Lemma fin_geo x : geo_of (MR st4 x) = geo_of (MR st2 x).
Proof.
  pose proof (queue_data (LActive sc) m st3 x) as D. apply data_of_eq in D. (first [ dand7 D as D1 D2 D3 D4 D5 D6 D7 | destruct D as (D1 & D2 & D3 & D4 & D5 & D6 & D7) ]).
  fold st4 in D1, D2, D3, D4, D5, D6, D7. unfold geo_of. rewrite D1, D4, D6, D7.
  destruct (aptr_eq_dec x m) as [->|NE].
  - rewrite fin_MR3, Em. reflexivity.
  - rewrite (fin_MR3_other x NE). reflexivity.
Qed.

Theorem slot_finish_ok :
  exists LS',
    queue (LActive sc) m st3 k bail = k st4
    /\ INVL (xpend (X_as idle) (Some s0)) st4 L BL LS'
    /\ TF2 st4
    /\ active st4 sc = Some m /\ (forall sc', sc' <> sc -> active st4 sc' = active st2 sc')
    /\ s_groups st4 = s_groups st2 /\ s_tick st4 = s_tick st2 /\ s_shadow st4 = s_shadow st2
    /\ m_last_idx (MR st4 m) = last /\ m_sizeclass (MR st4 m) = sc /\ get_stride (MR st4 m) = get_stride (MR st2 m)
    /\ (forall i, sstart (MR st4 m) i = sstart (MR st2 m) i) /\ s_regions st4 = s_regions st2 /\ s_secret st4 = s_secret st2.
Proof.
  exists LS4. (first [ pose proof ((queue_frame (LActive sc) m st3)) as dR_7; dand10 dR_7 as F1 F2 F3 F4 F5 F6 F7 F8 F9 FC | destruct (queue_frame (LActive sc) m st3) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & FC) ]). fold st4 in F1, F2, F3, F4, F5, F6, F7, F8, F9, FC.
  pose proof fin_INV4 as INV4.
  assert (G4 : s_groups st4 = s_groups st2) by (rewrite F5; reflexivity).
  (first [ pose proof ((geo_facts _ _ (fin_geo m))) as dR_8; dand4 dR_8 as S1 S2 S3 S4 | destruct (geo_facts _ _ (fin_geo m)) as (S1 & S2 & S3 & S4) ]).
  split; [exact fin_queue_eq|].
  split.
  { (* [comment removed for export] *)
    apply (INVL_clear_fresh (mkX idle [] (Some s0) None (Some m)) st4 L BL LS4 m INV4 eq_refl).
    intros b' ai' Hb'. rewrite G4 in Hb'.
    assert (Eb : b' = b /\ ai' = ai).
    { pose proof (hosts_inj _ _ _ (proj1 (proj2 (proj2 INV))) _ _ _ fin_hosts (ex_intro _ ai' Hb')) as <-. rewrite Hb in Hb'. inversion Hb'. auto. }
    destruct Eb as [-> ->].
    assert (Esc : m_sizeclass (MR st4 m) = sc) by (pose proof (fin_geo m) as G; unfold geo_of in G; rewrite Em in G; injection G; intros; congruence).
    rewrite Esc. split; [| split; [| split]].
    - intros _. rewrite fin_LS4. left. reflexivity.
    - intros _ NI. exfalso. apply NI. exists (LActive sc). rewrite fin_LS4. left. reflexivity.
    - intros sc0 Hin Hh. exfalso.
      pose proof (il_disj _ _ (proj1 (proj2 (proj2 (proj2 INV4)))) (LActive sc0) (LActive sc) m Hin ltac:(rewrite fin_LS4; left; reflexivity)) as E.
      inversion E. subst sc0. rewrite fin_LS4 in Hh. apply Hh. reflexivity.
    - intros _ HU. (first [ dand3 fin_MR4 as _ EA EF | destruct fin_MR4 as (_ & EA & EF) ]). rewrite EA, EF, fin_MR3. cbn. rewrite S4 in HU.
      destruct (UND HU) as [-> ->]. cbn. split; reflexivity. }
  split.
  { apply (TF2_kept st2 st4); [rewrite F2; reflexivity| rewrite F7; reflexivity| | exact TF].
    apply geom_kept_geo; [intros bb h Hh; rewrite G4; exact Hh| apply fin_geo]. }
  split; [change (active st4 sc) with (get_head st4 (LActive sc)); unfold st4; rewrite queue_head; destruct (decide (LActive sc = LActive sc)); [rewrite fin_head3; reflexivity| congruence]|].
  split; [intros sc' NE; change (active st4 sc') with (get_head st4 (LActive sc')); change (active st2 sc') with (get_head st2 (LActive sc')); unfold st4; rewrite queue_head; destruct (decide (LActive sc' = LActive sc)); [congruence|]; unfold st3; rewrite get_head_upd_meta; reflexivity|].
  split; [exact G4|]. split; [rewrite F7; reflexivity|]. split; [rewrite F2; reflexivity|].
  pose proof (fin_geo m) as G. unfold geo_of in G. rewrite Em in G. injection G. intros E4 E3 E2 E1.
  split; [exact E2|]. split; [exact E4|]. split; [exact S4|]. split; [exact S1|]. split; [rewrite F1; reflexivity| rewrite F8; reflexivity].
Qed.
End FINISH.
End MI_WSlot.


Module MI_Wvdb.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require STree Malloc Mall7vg KInv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_List.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Inv MI_Kit MI_Arith MI_Geom MI_List MI_Ext MI_S421.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_WFree.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Ws22.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_W2ig.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_W2ig MI_W3do.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_WTry2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_WTry2 MI_Wp9i MI_Wgyo MI_Cnt.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.STree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malloc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall7vg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_List.MI_Tree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Kit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Arith OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Geom OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_List OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ext OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_S421 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres2.MI_Pres1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres4.MI_Pres3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WFree.MI_Read OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ws22 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_W2ig.MI_Lsjc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_W2ig OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_W3do OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WTry2.MI_WTry OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WTry2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Wp9i OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Wgyo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Cnt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_TF2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_Wm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_WSlot.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.  (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
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
(* [comment removed for export] *)

(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Definition SLOT_POST (idle : list aptr) (sc req : Z) (st : mstate) (L : mled) (BL : list blk)
   (st1 : mstate) (idx : Z) (L1 : mled) (LS1 : lhead -> list aptr) : Prop :=
  (forall sc', sc' < sc -> active st1 sc' = active st sc') /\ ld_live L1 = ld_live L /\ GP st st1 /\
  ((idx = -1 /\ INVL (X_as idle) st1 L1 BL LS1 /\ TF0 st1)
   \/ (exists g bg ai, 0 <= idx <= m_last_idx (MR st1 g) /\ active st1 sc = Some g
         /\ s_groups st1 !! bg = Some (mkGhdr (Some g) ai) /\ m_sizeclass (MR st1 g) = sc
         /\ req + IB <= get_stride (MR st1 g)
         /\ (sc < 28 -> get_stride (MR st1 g) = UNIT * size_class sc)
         /\ INVL (xpend (X_as idle) (Some (fst bg, sstart (MR st1 g) idx))) st1 L1 BL LS1
         /\ TF2 st1)).

(* [comment removed for export] *)
Definition AG_POST (idle : list aptr) (sc req : Z) (st : mstate) (L : mled) (BL : list blk)
   (st2 : mstate) (go : optr) (L2 : mled) (LS2 : lhead -> list aptr) : Prop :=
  (forall sc', sc' <= sc -> active st2 sc' = active st sc') /\ ld_live L2 = ld_live L /\ GP st st2 /\
  match go with
  | None => INVL (X_as idle) st2 L2 BL LS2 /\ TF0 st2
  | Some m => exists b ai last ml,
      s_groups st2 !! b = Some (mkGhdr (Some m) ai)
      /\ MR st2 m = mkMeta None None (Some b) (mask_upto ai) (mask_upto last - mask_upto ai) last 1 sc ml
      /\ 0 <= ai <= last /\ last <= 31
      /\ req + IB <= get_stride (MR st2 m)
      /\ (sc < 28 -> get_stride (MR st2 m) = UNIT * size_class sc)
      /\ (get_stride (MR st2 m) < UNIT * size_class sc -> ai = 0 /\ last = 0)
      /\ INVL (mkX idle [] None None (Some m)) st2 L2 BL LS2 /\ TF2 st2
  end.

(* [comment removed for export] *)
Definition REC_OK (T : Type) (rec : mstate -> Z -> Z -> (mstate -> Z -> M T) -> M T -> M T) (sc : Z) (Post : mled -> T -> Prop) : Prop :=
  forall j idle st L BL LS req (k : mstate -> Z -> M T) bail,
  sc < j < 48 ->
  INVL (X_as idle) st L BL LS -> TF0 st -> NoDup idle -> 0 <= req -> req + IB <= UNIT * size_class j ->
  (forall st1 idx L1 LS1, SLOT_POST idle j req st L BL st1 idx L1 LS1 -> ftree L1 (k st1 idx) Post) ->
  ftree L (rec st j req k bail) Post.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ag_cnt1 (sc u0 : Z) : Z :=
  let size := UNIT * size_class sc in
  let cnt := cnt0_of sc u0 in
  if (cnt =? 1) && (size * cnt + UNIT <=? PGSZ / 2) then 2 else cnt.

Definition ag_cnt2 (sc cnt1 u1 : Z) (nosmall : bool) : Z :=
  if (u1 <? 4 * cnt1) && negb nosmall then adj sc (UNIT * size_class sc) cnt1 else cnt1.

Definition ag_cn3 (sc req cnt2 u1 : Z) (nosmall : bool) : Z * Z :=
  let size := UNIT * size_class sc in
  let needed := round_up_pg (size * cnt2 + UNIT) in
  if negb nosmall && (cnt2 <=? 7) then
    let req' := round_up_pg (req + IB + UNIT) in
    if (req' <? size + UNIT) || ((4 * PGSZ <=? req') && (u1 <? 2 * cnt2)) then (1, req') else (cnt2, needed)
  else (cnt2, needed).

Lemma ag_arith sc req u0 u1 ns c3 n3 :
  0 <= sc < 48 -> 0 <= req -> req + IB <= UNIT * size_class sc ->
  let size := UNIT * size_class sc in
  (PGSZ / 2 < size * ag_cnt1 sc u0 + UNIT ->
   ag_cn3 sc req (ag_cnt2 sc (ag_cnt1 sc u0) u1 ns) u1 ns = (c3, n3) ->
   grp_ok sc c3 n3 = true /\ ((c3 = 1 /\ n3 = round_up_pg (req + IB + UNIT) /\ 28 <= sc) \/ (size * c3 + UNIT <= n3)))
  /\ (size * ag_cnt1 sc u0 + UNIT <= PGSZ / 2 -> nest_ok sc (ag_cnt1 sc u0) = true).
Proof.
  intros Hsc Hreq Hfit. pose proof (alloc_group_arith sc req u0 u1 ns Hsc Hreq Hfit) as AR. cbn zeta in AR.
  change (if (cnt0_of sc u0 =? 1) && (UNIT * size_class sc * cnt0_of sc u0 + UNIT <=? PGSZ / 2) then 2 else cnt0_of sc u0) with (ag_cnt1 sc u0) in AR.
  destruct AR as [AR1 AR2]. cbn zeta. split; [| exact AR2].
  intros HB E. specialize (AR1 HB).
  change (if (u1 <? 4 * ag_cnt1 sc u0) && negb ns
          then if (Z.land sc 3 =? 1) && (8 * PGSZ <? UNIT * size_class sc * ag_cnt1 sc u0) then 2
               else if (Z.land sc 3 =? 2) && (4 * PGSZ <? UNIT * size_class sc * ag_cnt1 sc u0) then 3
               else if (Z.land sc 3 =? 0) && (8 * PGSZ <? UNIT * size_class sc * ag_cnt1 sc u0) then 3
               else if (Z.land sc 3 =? 0) && (2 * PGSZ <? UNIT * size_class sc * ag_cnt1 sc u0) then 5
               else ag_cnt1 sc u0
          else ag_cnt1 sc u0) with (ag_cnt2 sc (ag_cnt1 sc u0) u1 ns) in AR1.
  set (c2 := ag_cnt2 sc (ag_cnt1 sc u0) u1 ns) in *. clearbody c2.
  unfold ag_cn3 in E. cbn zeta in E.
  destruct (negb ns && (c2 <=? 7)).
  - destruct ((round_up_pg (req + IB + UNIT) <? UNIT * size_class sc + UNIT) || ((4 * PGSZ <=? round_up_pg (req + IB + UNIT)) && (u1 <? 2 * c2))).
    + inversion E; subst. destruct AR1 as [G R]. split; [exact G|]. destruct R as [R|(R1 & R2 & R3)]; [left; exact R| right; rewrite R2 at 1; lia].
    + inversion E; subst. destruct AR1 as [G R]. split; [exact G|]. destruct R as [(R1 & R2 & R3)|(R1 & R2 & R3)]; [| right; exact R3].
      right. rewrite R1. pose proof (proj1 (round_up_pg_spec (UNIT * size_class sc * 1 + UNIT))). lia.
  - inversion E; subst. destruct AR1 as [G R]. split; [exact G|]. destruct R as [(R1 & R2 & R3)|(R1 & R2 & R3)]; [| right; exact R3].
    right. rewrite R1. pose proof (proj1 (round_up_pg_spec (UNIT * size_class sc * 1 + UNIT))). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma shadow_next_rid_none X st L BL LS : INVL X st L BL LS -> s_shadow st !! s_next_rid st = None.
Proof.
  intros INV. destruct (s_shadow st !! s_next_rid st) as [sh|] eqn:E; [| reflexivity]. exfalso.
  (first [ pose proof ((ish_dom _ _ (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV)))))) _ _ E)) as dR_1; dex1 dR_1 as r; destruct dR_1 as [Hr _] | pose proof ((ish_dom _ _ (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV)))))) _ _ E)) as dR_1; dand3 dR_1 as r Hr _ | destruct (ish_dom _ _ (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV)))))) _ _ E) as (r & Hr & _) ]).
  pose proof (ir_ids _ _ _ (proj1 INV) _ _ Hr). lia.
Qed.

Lemma LS_empty_of X st L BL LS sc : INVL X st L BL LS -> active st sc = None -> LS (LActive sc) = [].
Proof.
  intros INV HA. pose proof (il_head _ _ (proj1 (proj2 (proj2 (proj2 INV)))) (LActive sc)) as HH. cbn in HH. rewrite HA in HH.
  destruct (LS (LActive sc)); [reflexivity| discriminate].
Qed.

End CEIL.

Lemma step_seq_fields st : let st' := step_seq st in
  s_shadow st' = s_shadow st /\ s_tick st' = s_tick st /\ (forall sc, active st' sc = active st sc) /\ s_regions st' = s_regions st
  /\ s_next_rid st' = s_next_rid st /\ s_metas st' = s_metas st /\ s_groups st' = s_groups st /\ (forall sc, usage st' sc = usage st sc).
Proof. unfold step_seq. destruct (c_seq (ctx st) =? 255); cbn; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity. Qed.

Lemma account_bounce_fields sc0 st : let st' := account_bounce sc0 st in
  s_shadow st' = s_shadow st /\ s_tick st' = s_tick st /\ (forall sc, active st' sc = active st sc) /\ s_regions st' = s_regions st
  /\ s_next_rid st' = s_next_rid st /\ s_metas st' = s_metas st /\ s_groups st' = s_groups st /\ (forall sc, usage st' sc = usage st sc).
Proof.
  unfold account_bounce. destruct (sc_in_seq_range sc0); [| cbn; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity].
  destruct (negb (unmap_seq st (sc0 - 7) =? 0) && (c_seq (ctx st) - unmap_seq st (sc0 - 7) <? 10)); [| cbn; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity].
  destruct (bounces st (sc0 - 7) + 1 <? 100); cbn; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section MMAP_BRANCH.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
Variables (T : Type) (idle : list aptr) (st0 st1 : mstate) (L0 L1 : mled) (BL : list blk) (LS1 : lhead -> list aptr).
Variables (m : aptr) (sc req cnt needed : Z) (k : mstate -> optr -> M T) (bail : M T) (Post : mled -> T -> Prop).
Hypothesis INV1 : INVL (X_as (m :: idle)) st1 L1 BL LS1.
Hypothesis NIm : ~ In m idle.
Hypothesis TF1 : TF0 st1.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis Hreq : 0 <= req.
Hypothesis Hfit : req + IB <= UNIT * size_class sc.
Hypothesis HA1 : forall sc', active st1 sc' = active st0 sc'.
Hypothesis HA0 : active st0 sc = None.
Hypothesis HL1 : ld_live L1 = ld_live L0.
Hypothesis HG1 : GP st0 st1.
Hypothesis GRP : grp_ok sc cnt needed = true.
Hypothesis RED : (cnt = 1 /\ needed = round_up_pg (req + IB + UNIT) /\ 28 <= sc) \/ (UNIT * size_class sc * cnt + UNIT <= needed).
Hypothesis HK : forall st2 go L2 LS2, AG_POST idle sc req st0 L0 BL st2 go L2 LS2 -> ftree L2 (k st2 go) Post.
Let st1' := step_seq (account_bounce sc st1).
Let MC := fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c.
Let AI := let ai := (4096 - UNIT) / (UNIT * size_class sc) - 1 in let ai := if cnt - 1 <? ai then cnt - 1 else ai in if ai <? 0 then 0 else ai.

Lemma st1'_facts :
  INVL (X_as (m :: idle)) st1' L1 BL LS1 /\ s_shadow st1' = s_shadow st1 /\ s_tick st1' = s_tick st1
  /\ (forall sc', active st1' sc' = active st1 sc') /\ TF0 st1' /\ s_regions st1' = s_regions st1 /\ s_secret st1' = s_secret st1.
Proof.
  (first [ pose proof ((account_bounce_fields sc st1)) as dR_2; dand5 dR_2 as A1 A2 A3 A4 _ | destruct (account_bounce_fields sc st1) as (A1 & A2 & A3 & A4 & _) ]). (first [ pose proof ((step_seq_fields (account_bounce sc st1))) as dR_3; dand5 dR_3 as B1 B2 B3 B4 _ | destruct (step_seq_fields (account_bounce sc st1)) as (B1 & B2 & B3 & B4 & _) ]).
  assert (SH : s_shadow st1' = s_shadow st1) by (unfold st1'; rewrite B1, A1; reflexivity).
  assert (TK : s_tick st1' = s_tick st1) by (unfold st1'; rewrite B2, A2; reflexivity).
  split; [apply INVL_step_seq; apply INVL_account_bounce; exact INV1|].
  split; [exact SH|]. split; [exact TK|]. split; [intros sc'; unfold st1'; rewrite B3, A3; reflexivity|].
  split; [exact (TF0_ctrl st1 st1' SH TK TF1)|]. split; [unfold st1'; rewrite B4, A4; reflexivity|].
  unfold st1', step_seq, account_bounce. destruct (sc_in_seq_range sc); [destruct (negb _ && _); [destruct (_ <? 100)|]|]; destruct (c_seq _ =? 255); reflexivity.
Qed.

Theorem ag_mmap_ft :
  ftree L1 (SVis (EMmap 0 needed PROT_RW (MAP_PRIVATE + MAP_ANON)) (fun r =>
    if negb (mmap_answer_ok (live_ranges st1') needed r) then bad_answer bail
    else if is_err r then free_meta m st1' (fun st2 => k st2 None) bail
    else let '(st2, rid) := new_region RKGroup r needed st1' in
         ag_tail full_lay (upd_ctx MC (upd_meta m (m_set_maplen (Z.shiftr needed 12)) st2)) sc m (rid, 0) cnt AI k)) Post.
Proof.
  (first [ dand7 st1'_facts as INV1' SH1 TK1 ACT1 TF1' RG1 SS1' | destruct st1'_facts as (INV1' & SH1 & TK1 & ACT1 & TF1' & RG1 & SS1') ]).
  pose proof (grp_ok_sound sc cnt needed GRP) as G. cbn zeta in G. (first [ dand11 G as G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 | destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11) ]).
  apply ftree_vis; [reflexivity| reflexivity| | |].
  - (* [comment removed for export] *) cbn. left. split; [exact (brk_quiet_of _ _ _ (proj1 INV1'))|]. split; [reflexivity|]. split; [reflexivity|].
    split; [right; reflexivity|]. unfold LEN_MAX. lia.
  - intros a Ha. cbn [answer_ok] in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn [negb] in Ha |- *.
    change (event_post L1 (EMmap 0 needed PROT_RW (MAP_PRIVATE + MAP_ANON)) a)
      with (if Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0 then if is_err a then L1 else if PROT_RW =? PROT_NONE then KInv.set_metas ((a, needed, 0) :: ld_metas L1) L1 else KInv.set_groups ((a, needed) :: ld_groups L1) L1 else set_brkph BPLive (set_brkreg (Some (0, 2 * PGSZ)) L1)).
    change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true. change (PROT_RW =? PROT_NONE) with false. cbn iota.
    rewrite (mmap_answer_ok_eq _ _ _ (proj1 INV1')) in Ha. rewrite Ha. cbn [negb].
    destruct (is_err a) eqn:ER.
    + (* [comment removed for export] *)
      rewrite free_meta_eq.
      (first [ pose proof ((free_idle_ok idle m st1' L1 BL LS1 INV1' NIm)) as dR_6; dand9 dR_6 as INV2 F1 F2 F3 F4 F5 F6 F7 _ | destruct (free_idle_ok idle m st1' L1 BL LS1 INV1' NIm) as (INV2 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & _) ]).
      eapply HK. split; [intros sc' _; rewrite F7, ACT1; apply HA1|]. split; [exact HL1|].
      split.
      { eapply GP_trans; [exact HG1| apply GP_eq; [rewrite F5, RG1; reflexivity|]].
        unfold fm_st. (first [ pose proof ((queue_frame LFree m (put_meta m meta0 st1'))) as dR_7; dand9 dR_7 as _ _ _ _ _ _ _ Q8 _ | destruct (queue_frame LFree m (put_meta m meta0 st1')) as (_ & _ & _ & _ & _ & _ & _ & Q8 & _) ]). rewrite Q8. cbn. exact SS1'. }
      split; [exact INV2|]. exact (TF0_ctrl st1' _ F1 F2 TF1').
    + (* [comment removed for export] *)
      destruct (new_region RKGroup a needed st1') as [st2 rid] eqn:EN.
      assert (Erid : rid = s_next_rid st1') by (unfold new_region in EN; inversion EN; reflexivity).
      assert (Est2 : st2 = fst (new_region RKGroup a needed st1')) by (rewrite EN; reflexivity).
      pose proof (INVL_new_group_region (X_as (m :: idle)) st1' L1 BL LS1 a needed INV1' eq_refl Ha ER ltac:(unfold LEN_MAX; lia)) as INV2.
      rewrite <- Est2, <- Erid in INV2. cbn [xorph X_as x_idle x_zomb x_pend x_fresh] in INV2.
      assert (Hr : s_regions st2 !! rid = Some (mkRegion RKGroup a needed)).
      { rewrite Est2, ng_lookup, Erid, N.eqb_refl. reflexivity. }
      assert (NS : s_shadow st2 !! rid = None).
      { rewrite Est2, Erid. change (s_shadow (fst (new_region RKGroup a needed st1'))) with (s_shadow st1'). exact (shadow_next_rid_none _ _ _ _ _ INV1'). }
      assert (ACT2 : forall sc', active st2 sc' = active st0 sc') by (intros sc'; rewrite Est2; change (active (fst (new_region RKGroup a needed st1')) sc') with (active st1' sc'); rewrite ACT1; apply HA1).
      assert (EMP : LS1 (LActive sc) = []) by (apply (LS_empty_of _ _ _ _ _ _ INV2); rewrite ACT2; exact HA0).
      assert (TF2' : TF0 st2) by (apply (TF0_ctrl st1'); [rewrite Est2; reflexivity| rewrite Est2; reflexivity| exact TF1']).
      pose proof (clamp_ai (UNIT * size_class sc) cnt ltac:(lia)) as HAI. cbn zeta in HAI. fold AI in HAI.
      assert (HAI0 : sc = 0 -> AI = cnt - 1).
      { intros Hsc0. unfold AI. rewrite Hsc0. change (UNIT * size_class 0) with 16. change ((4096 - UNIT) / 16 - 1) with 254.
        pose proof (grp_ok_sound sc cnt needed GRP) as (Gc & _).
        replace (cnt - 1 <? 254) with true by (symmetry; apply Z.ltb_lt; lia). replace (cnt - 1 <? 0) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
      rewrite ag_tail_eq.
      change (upd_ctx MC (upd_meta m (m_set_maplen (Z.shiftr needed 12)) st2)) with (upd_meta m (m_set_maplen (Z.shiftr needed 12)) (upd_ctx MC st2)).
      (first [ pose proof ((ag_top_ok idle st2 (KInv.set_groups ((a, needed) :: ld_groups L1) L1) BL LS1 m rid (mkRegion RKGroup a needed) sc cnt needed AI
                  INV2 Hr eq_refl eq_refl NS GRP Hsc HAI HAI0 EMP TF2' NIm)) as dR_8; dand7 dR_8 as INV' TF' MR' GR' ACT' HD' TK' | destruct (ag_top_ok idle st2 (KInv.set_groups ((a, needed) :: ld_groups L1) L1) BL LS1 m rid (mkRegion RKGroup a needed) sc cnt needed AI
                  INV2 Hr eq_refl eq_refl NS GRP Hsc HAI HAI0 EMP TF2' NIm) as (INV' & TF' & MR' & GR' & ACT' & HD' & TK') ]).
      pose proof (top_facts rid sc cnt needed AI GRP Hsc) as TFX. cbn zeta in TFX.
      (first [ dand12 TFX as F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 Emr | destruct TFX as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & Emr) ]).
      rewrite Emr in MR', F4, F5, F7, F8, F9. rewrite <- MR' in F4, F5, F7, F8, F9.
      eapply HK. split; [intros sc' _; rewrite ACT'; apply ACT2|]. split; [cbn; exact HL1|].
      split.
      { eapply GP_trans; [exact HG1|]. split.
        - intros q rq Hq Kq. rewrite agt_regions. cbn. rewrite Est2. apply (ng_keep _ _ _ _ _ _ _ INV1'). rewrite RG1. exact Hq.
        - rewrite agt_secret. cbn. rewrite Est2. cbn. exact SS1'. }
      exists (rid, 0), AI, (cnt - 1), (Z.shiftr needed 12).
      split; [exact GR'|]. split; [exact MR'|]. split; [exact HAI|]. split; [lia|].
      assert (STR : get_stride (MR (agt (upd_meta m (m_set_maplen (Z.shiftr needed 12)) (upd_ctx MC st2)) sc m (rid, 0) cnt AI) m)
                    = if (cnt - 1 =? 0) && negb (Z.shiftr needed 12 =? 0) then Z.shiftr needed 12 * 4096 - UNIT else UNIT * size_class sc).
      { rewrite MR'. unfold get_stride. cbn. reflexivity. }
      assert (NZ : (Z.shiftr needed 12 =? 0) = false) by (apply Z.eqb_neq; lia).
      rewrite NZ in STR. cbn [negb] in STR. rewrite andb_true_r in STR.
      assert (E12 : Z.shiftr needed 12 * 4096 = needed) by (rewrite F2; pose proof (Z.div_mod needed 4096 ltac:(lia)); lia).
      split; [| split; [| split; [| split; [exact INV'| apply TF0_TF2; exact TF']]]].
      * destruct RED as [(C1 & Nd & S28)|NR].
        -- rewrite STR. replace (cnt - 1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia). rewrite E12, Nd.
           pose proof (proj1 (round_up_pg_spec (req + IB + UNIT))). unfold UNIT, IB in *. lia.
        -- rewrite STR. destruct (Z.eqb_spec (cnt - 1) 0); [rewrite E12; unfold UNIT in *; nia| lia].
      * intros S28. destruct RED as [(C1 & Nd & S28')|NR]; [lia|].
        rewrite STR in F5 |- *. destruct (Z.eqb_spec (cnt - 1) 0) as [C1|]; [| reflexivity].
        destruct F5 as [F5|]; [| lia]. rewrite E12 in F5 |- *. assert (cnt = 1) by lia. subst cnt. lia.
      * intros UNDER. rewrite STR in UNDER. destruct RED as [(C1 & Nd & S28)|NR].
        -- clear - HAI C1. lia.
        -- exfalso. destruct (Z.eqb_spec (cnt - 1) 0) as [C1|]; [| lia]. rewrite E12 in UNDER. assert (cnt = 1) by lia. subst cnt. lia.
  - intros a Ha. cbn [answer_ok] in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn iota in Ha.
    rewrite (mmap_answer_ok_eq _ _ _ (proj1 INV1')) in Ha. rewrite Ha. exact I.
Qed.
End MMAP_BRANCH.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section NEST_BRANCH.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
Variables (T : Type) (rec : mstate -> Z -> Z -> (mstate -> Z -> M T) -> M T -> M T).
Variables (idle : list aptr) (st0 st1 : mstate) (L0 L1 : mled) (BL : list blk) (LS1 : lhead -> list aptr).
Variables (m : aptr) (sc req cnt : Z) (k : mstate -> optr -> M T) (bail : M T) (Post : mled -> T -> Prop).
Hypothesis REC : REC_OK T rec sc Post.
Hypothesis INV1 : INVL (X_as (m :: idle)) st1 L1 BL LS1.
Hypothesis NIm : ~ In m idle.
Hypothesis ND : NoDup idle.
Hypothesis TF1 : TF0 st1.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis Hreq : 0 <= req.
Hypothesis Hfit : req + IB <= UNIT * size_class sc.
Hypothesis HA1 : forall sc', active st1 sc' = active st0 sc'.
Hypothesis HA0 : active st0 sc = None.
Hypothesis HL1 : ld_live L1 = ld_live L0.
Hypothesis HG1 : GP st0 st1.
Hypothesis NEST : nest_ok sc cnt = true.
Hypothesis HK : forall st2 go L2 LS2, AG_POST idle sc req st0 L0 BL st2 go L2 LS2 -> ftree L2 (k st2 go) Post.
Let size := UNIT * size_class sc.
Let j := size_to_class (UNIT + cnt * size - IB).

Theorem ag_nest_ft :
  ftree L1 (rec st1 j (UNIT + cnt * size - IB) (fun st2 idx =>
     if idx <? 0 then free_meta m st2 (fun st3 => k st3 None) bail
     else match active st2 j with
          | None => SVis (EUndef UBadPtr) (fun _ => bail)
          | Some g => ag_tail full_lay (upd_meta m (m_set_maplen 0) (nest_layout st2 g idx j size cnt)) sc m (slot_of st2 g idx) cnt (cnt - 1) k
          end) bail) Post.
Proof.
  pose proof (nest_ok_sound sc cnt NEST) as N0. cbn zeta in N0. fold size in N0. fold j in N0. (first [ dand6 N0 as N1 N2 N3 N4 N5 N6 | destruct N0 as (N1 & N2 & N3 & N4 & N5 & N6) ]).
  apply (REC j (m :: idle) st1 L1 BL LS1 (UNIT + cnt * size - IB) _ bail ltac:(lia) INV1 TF1).
  - apply NoDup_cons. split; [intros Hin; apply NIm; apply list_elem_of_In; exact Hin| exact ND].
  - exact N5.
  - lia.
  - (intros st2 idx L2 LS2; (first [ intro dR_15; dand4 dR_15 as ACT LIVE GP2 RES | intros (ACT & LIVE & GP2 & RES) ])). destruct RES as [(-> & INV2 & TF2')|(g & bg & aig & Hidx & HAj & Hg & SCg & FIT & STR & INV2 & TF2')].
    + (* [comment removed for export] *)
      change (-1 <? 0) with true. cbn iota. rewrite free_meta_eq.
      (first [ pose proof ((free_idle_ok idle m st2 L2 BL LS2 INV2 NIm)) as dR_11; dand9 dR_11 as INV3 F1 F2 F3 F4 F5 F6 F7 _ | destruct (free_idle_ok idle m st2 L2 BL LS2 INV2 NIm) as (INV3 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & _) ]).
      eapply HK. split; [intros sc' Hs; rewrite F7, ACT by lia; apply HA1|]. split; [rewrite LIVE; exact HL1|].
      split.
      { eapply GP_trans; [exact HG1| eapply GP_trans; [exact GP2| apply GP_eq; [exact F5|]]].
        unfold fm_st. (first [ pose proof ((queue_frame LFree m (put_meta m meta0 st2))) as dR_12; dand9 dR_12 as _ _ _ _ _ _ _ Q8 _ | destruct (queue_frame LFree m (put_meta m meta0 st2)) as (_ & _ & _ & _ & _ & _ & _ & Q8 & _) ]). rewrite Q8. reflexivity. }
      split; [exact INV3|]. exact (TF0_ctrl st2 _ F1 F2 TF2').
    + replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia). rewrite HAj.
      assert (Hgh : hosts st2 bg g) by (exists aig; exact Hg).
      assert (Ep : slot_of st2 g idx = (fst bg, sstart (MR st2 g) idx)).
      { unfold slot_of. fold (MR st2 g). exact (slot_start'_eq _ _ _ (proj1 (proj2 (proj2 INV2))) _ _ idx Hgh). }
      rewrite Ep. rewrite ag_tail_eq.
      specialize (STR ltac:(lia)).
      assert (EMP : LS2 (LActive sc) = []) by (apply (LS_empty_of _ _ _ _ _ _ INV2); rewrite ACT by lia; rewrite HA1; exact HA0).
      (first [ pose proof ((ag_nested_ok idle st2 L2 BL LS2 m g bg aig idx sc cnt INV2 Hg Hidx SCg STR NEST Hsc EMP TF2' NIm)) as dR_13; dand7 dR_13 as INV' TF' MR' GR' ACT' HD' TK' | destruct (ag_nested_ok idle st2 L2 BL LS2 m g bg aig idx sc cnt INV2 Hg Hidx SCg STR NEST Hsc EMP TF2' NIm)
        as (INV' & TF' & MR' & GR' & ACT' & HD' & TK') ]).
      pose proof (nst_facts st2 g bg idx sc cnt NEST Hsc) as NF. cbn zeta in NF.
      (first [ dand9 NF as _ _ _ _ _ _ _ Emr Es | destruct NF as (_ & _ & _ & _ & _ & _ & _ & Emr & Es) ]).
      fold size in MR', GR', ACT', INV', TF', Emr, Es |- *. fold j in MR', GR', ACT', INV', TF' |- *.
      rewrite Emr in MR'. rewrite Emr in Es.
      eapply HK. split; [intros sc' Hs; rewrite ACT', ACT by lia; apply HA1|]. split; [rewrite LIVE; exact HL1|].
      split.
      { eapply GP_trans; [exact HG1| eapply GP_trans; [exact GP2| apply GP_eq]].
        - rewrite agt_regions. change (s_regions (nest_layout st2 g idx j size cnt) = s_regions st2).
          rewrite <- (s_regions_strip (nest_layout st2 g idx j size cnt)), strip_nest_layout. reflexivity.
        - rewrite agt_secret. change (s_secret (nest_layout st2 g idx j size cnt) = s_secret st2).
          rewrite <- (s_secret_strip (nest_layout st2 g idx j size cnt)), strip_nest_layout. reflexivity. }
      exists (fst bg, sstart (MR st2 g) idx), (cnt - 1), (cnt - 1), 0.
      rewrite Z.sub_diag. split; [exact GR'|]. split; [exact MR'|]. split; [lia|]. split; [lia|].
      rewrite MR', Es. split; [unfold size; lia|]. split; [intros _; reflexivity|]. split; [unfold size; intros; lia|].
      split; [exact INV'| exact TF'].
Qed.
End NEST_BRANCH.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section AG.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
Variables (T : Type) (rec : mstate -> Z -> Z -> (mstate -> Z -> M T) -> M T -> M T) (sc : Z) (Post : mled -> T -> Prop).
Hypothesis REC : REC_OK T rec sc Post.

Theorem alloc_group_ft idle st L BL LS req (k : mstate -> optr -> M T) bail :
  INVL (X_as idle) st L BL LS -> TF0 st -> NoDup idle -> 0 <= sc < 48 -> 0 <= req -> req + IB <= UNIT * size_class sc ->
  active st sc = None ->
  (forall st2 go L2 LS2, AG_POST idle sc req st L BL st2 go L2 LS2 -> ftree L2 (k st2 go) Post) ->
  ftree L (alloc_group T full_lay rec st sc req k bail) Post.
Proof.
  intros INV TF ND Hsc Hreq Hfit HA HK. unfold alloc_group.
  eapply (alloc_meta_ft T BL Post _ bail (X_as idle) st L); [ | | exact INV| apply amf_refl| apply lf_refl].
  - (* [comment removed for export] *)
    intros st1 L1 LS1 INV1 AF LF. cbn beta iota. eapply HK.
    split; [intros sc' _; apply (amf_active _ _ AF)|]. split; [exact (lf_live _ _ LF)|]. split; [exact (GP_amf _ _ AF)|]. split; [exact INV1|].
    exact (TF0_ctrl st st1 (amf_shadow _ _ AF) (amf_tick _ _ AF) TF).
  - (* [comment removed for export] *)
    intros st1 L1 LS1 m INV1 NIm AF LF. cbn beta iota zeta.
    change (if sc <? 9 then small_cnt_pick sc (usage st1 sc) else halve_big 8 (halve_even 8 (med_cnt (Z.land sc 3)) (usage st1 sc)) (UNIT * size_class sc))
      with (cnt0_of sc (usage st1 sc)).
    change (if (cnt0_of sc (usage st1 sc) =? 1) && (UNIT * size_class sc * cnt0_of sc (usage st1 sc) + UNIT <=? PGSZ / 2) then 2 else cnt0_of sc (usage st1 sc))
      with (ag_cnt1 sc (usage st1 sc)).
    change (lh_nest full_lay) with nest_layout.
    assert (HA1 : forall sc', active st1 sc' = active st sc') by (intros; apply (amf_active _ _ AF)).
    assert (TF1 : TF0 st1) by exact (TF0_ctrl st st1 (amf_shadow _ _ AF) (amf_tick _ _ AF) TF).
    pose proof (ag_arith sc req (usage st1 sc)) as AR.
    set (c1 := ag_cnt1 sc (usage st1 sc)) in *.
    destruct (Z.ltb_spec (PGSZ / 2) (UNIT * size_class sc * c1 + UNIT)) as [HB|HB].
    + (* [comment removed for export] *)
      set (ns := is_bouncing sc st1).
      set (st1' := step_seq (account_bounce sc st1)).
      set (u1 := if Z.even sc && (sc <? 32) then usage st1 sc + usage st1' (sc + 1) else usage st1 sc).
      change (if (u1 <? 4 * c1) && negb ns
              then if (Z.land sc 3 =? 1) && (8 * PGSZ <? UNIT * size_class sc * c1) then 2
                   else if (Z.land sc 3 =? 2) && (4 * PGSZ <? UNIT * size_class sc * c1) then 3
                   else if (Z.land sc 3 =? 0) && (8 * PGSZ <? UNIT * size_class sc * c1) then 3
                   else if (Z.land sc 3 =? 0) && (2 * PGSZ <? UNIT * size_class sc * c1) then 5
                   else c1
              else c1) with (ag_cnt2 sc c1 u1 ns).
      set (c2 := ag_cnt2 sc c1 u1 ns).
      specialize (AR u1 ns). 
      assert (GO : forall c3 n3, ag_cn3 sc req c2 u1 ns = (c3, n3) ->
        ftree L1 (SVis (EMmap 0 n3 PROT_RW (MAP_PRIVATE + MAP_ANON)) (fun r =>
          if negb (mmap_answer_ok (live_ranges st1') n3 r) then bad_answer bail
          else if is_err r then free_meta m st1' (fun st2 => k st2 None) bail
          else let '(st2, rid) := new_region RKGroup r n3 st1' in
               ag_tail full_lay (upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) (upd_meta m (m_set_maplen (Z.shiftr n3 12)) st2)) sc m (rid, 0) c3
                 (let ai := (4096 - UNIT) / (UNIT * size_class sc) - 1 in let ai := if c3 - 1 <? ai then c3 - 1 else ai in if ai <? 0 then 0 else ai) k)) Post).
      { intros c3 n3 E3. destruct (proj1 (AR c3 n3 Hsc Hreq Hfit) HB E3) as [GRP RED].
        exact (ag_mmap_ft T idle st st1 L L1 BL LS1 m sc req c3 n3 k bail Post INV1 NIm TF1 Hsc Hfit HA1 HA (lf_live _ _ LF) (GP_amf _ _ AF) GRP RED HK). }
      unfold ag_cn3 in GO. cbn zeta in GO.
      destruct (negb ns && (c2 <=? 7)).
      * destruct ((round_up_pg (req + IB + UNIT) <? UNIT * size_class sc + UNIT) || ((4 * PGSZ <=? round_up_pg (req + IB + UNIT)) && (u1 <? 2 * c2))).
        -- cbn beta iota. exact (GO _ _ eq_refl).
        -- cbn beta iota. exact (GO _ _ eq_refl).
      * cbn beta iota. exact (GO _ _ eq_refl).
    + (* [comment removed for export] *)
      pose proof (proj2 (AR 0 false 0 0 Hsc Hreq Hfit) HB) as NEST.
      exact (ag_nest_ft T rec idle st st1 L L1 BL LS1 m sc req c1 k bail Post REC INV1 NIm ND TF1 Hsc Hfit HA1 HA (lf_live _ _ LF) (GP_amf _ _ AF) NEST HK).
Qed.
End AG.
End MI_Wvdb.

Module MI_Wdy2.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require STree Malloc KInv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_List.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Inv MI_Kit MI_Arith MI_Geom MI_List MI_Ext MI_S421.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres4 MI_Ws22.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_WTry2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_WTry2 MI_Wp9i MI_Cnt.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.STree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malloc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_List.MI_Tree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Kit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Arith OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Geom OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_List OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ext OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_S421 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres2.MI_Pres1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres4.MI_Pres3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ws22 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WTry2.MI_WTry OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WTry2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Wp9i OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Cnt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_TF2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_Wm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_WSlot OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_Wvdb.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.  (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section SLOT.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
Variable T : Type.
Variable Post : mled -> T -> Prop.

Theorem alloc_slot_ft (f : nat) : forall sc idle st L BL LS req (k : mstate -> Z -> M T) bail,
  49 - sc <= Z.of_nat f ->
  INVL (X_as idle) st L BL LS -> TF0 st -> NoDup idle -> 0 <= sc < 48 -> 0 <= req -> req + IB <= UNIT * size_class sc ->
  (forall st1 idx L1 LS1, SLOT_POST idle sc req st L BL st1 idx L1 LS1 -> ftree L1 (k st1 idx) Post) ->
  ftree L (alloc_slot full_lay f st sc req k bail) Post.
Proof.
  induction f as [|f IH]; intros sc idle st L BL LS req k bail Hf INV TF ND Hsc Hreq Hfit HK.
  { exfalso. cbn in Hf. lia. }
  change (alloc_slot full_lay (S f) st sc req k bail) with
    (try_avail sc st (fun st1 first =>
       if negb (first =? 0) then k st1 (ctz32 first)
       else alloc_group T full_lay (alloc_slot full_lay f) st1 sc req (fun st2 go =>
              match go with
              | None => k st2 (-1)
              | Some g => let st3 := upd_meta g (fun r => m_set_avail (m_avail r - 1) r) st2 in
                          queue (LActive sc) g st3 (fun st4 => k st4 0) bail
              end) bail) bail).
  (first [ pose proof ((try_avail_ok T (X_as idle) L BL sc
              (fun st1 first =>
                 if negb (first =? 0) then k st1 (ctz32 first)
                 else alloc_group T full_lay (alloc_slot full_lay f) st1 sc req (fun st2 go =>
                        match go with
                        | None => k st2 (-1)
                        | Some g => let st3 := upd_meta g (fun r => m_set_avail (m_avail r - 1) r) st2 in
                                    queue (LActive sc) g st3 (fun st4 => k st4 0) bail
                        end) bail) bail eq_refl eq_refl Hsc st LS INV)) as dR_1; dex2 dR_1 as st1 first; dand4 dR_1 as LS1 E TAF RES | pose proof ((try_avail_ok T (X_as idle) L BL sc
              (fun st1 first =>
                 if negb (first =? 0) then k st1 (ctz32 first)
                 else alloc_group T full_lay (alloc_slot full_lay f) st1 sc req (fun st2 go =>
                        match go with
                        | None => k st2 (-1)
                        | Some g => let st3 := upd_meta g (fun r => m_set_avail (m_avail r - 1) r) st2 in
                                    queue (LActive sc) g st3 (fun st4 => k st4 0) bail
                        end) bail) bail eq_refl eq_refl Hsc st LS INV)) as dR_1; dand6 dR_1 as st1 first LS1 E TAF RES | destruct (try_avail_ok T (X_as idle) L BL sc
              (fun st1 first =>
                 if negb (first =? 0) then k st1 (ctz32 first)
                 else alloc_group T full_lay (alloc_slot full_lay f) st1 sc req (fun st2 go =>
                        match go with
                        | None => k st2 (-1)
                        | Some g => let st3 := upd_meta g (fun r => m_set_avail (m_avail r - 1) r) st2 in
                                    queue (LActive sc) g st3 (fun st4 => k st4 0) bail
                        end) bail) bail eq_refl eq_refl Hsc st LS INV) as (st1 & first & LS1 & E & TAF & RES) ]).
  rewrite E. cbn beta.
  assert (ACT1 : forall sc', sc' < sc -> active st1 sc' = active st sc').
  { intros sc' Hs. change (active st1 sc') with (get_head st1 (LActive sc')). rewrite (taf_heads _ _ _ TAF) by (intros EQ; inversion EQ; lia). reflexivity. }
  assert (TF1 : TF0 st1) by exact (TF0_ctrl st st1 (taf_shadow _ _ _ TAF) (taf_tick _ _ _ TAF) TF).
  destruct RES as [(-> & HA & INV1)|(g & bg & ai & idx & NZ & POS & Eidx & HA & Hg & Hidx & SC & STR & INV1)].
  - (* [comment removed for export] *)
    change (negb (0 =? 0)) with false. cbn iota.
    assert (REC : REC_OK T (alloc_slot full_lay f) sc Post).
    { intros j idle' st' L' BL' LS' req' k' bail' Hj INV' TF' ND' Hreq' Hfit' HK'.
      apply (IH j idle' st' L' BL' LS' req' k' bail'); try assumption; lia. }
    apply (alloc_group_ft T (alloc_slot full_lay f) sc Post REC idle st1 L BL LS1 req _ bail INV1 TF1 ND Hsc Hreq Hfit HA).
    (intros st2 go L2 LS2; (first [ intro dR_5; dand4 dR_5 as ACT2 LIVE2 GP2 RES2 | intros (ACT2 & LIVE2 & GP2 & RES2) ])). destruct go as [g|].
    + (first [ dex4 RES2 as b ai last ml; dand9 RES2 as Hb Em Hai Hl FIT STR UND INV2 TF2' | dand13 RES2 as b ai last ml Hb Em Hai Hl FIT STR UND INV2 TF2' | destruct RES2 as (b & ai & last & ml & Hb & Em & Hai & Hl & FIT & STR & UND & INV2 & TF2') ]).
      cbn zeta.
        (first [ pose proof ((slot_finish_ok T idle st2 L2 BL LS2 g b ai last sc ml (fun st4 => k st4 0) bail INV2 Hb Em Hai Hl Hsc
                    ltac:(rewrite ACT2 by lia; exact HA) UND TF2')) as dR_3; dand15 dR_3 as LS4 EQ INV4 TF4 HA4 ACT4 G4 TK4 SH4 L4 SC4 STR4 SS4 RG4 SE4 | destruct (slot_finish_ok T idle st2 L2 BL LS2 g b ai last sc ml (fun st4 => k st4 0) bail INV2 Hb Em Hai Hl Hsc
                    ltac:(rewrite ACT2 by lia; exact HA) UND TF2')
          as (LS4 & EQ & INV4 & TF4 & HA4 & ACT4 & G4 & TK4 & SH4 & L4 & SC4 & STR4 & SS4 & RG4 & SE4) ]).
        rewrite EQ. eapply HK. split; [intros sc' Hs; rewrite ACT4, ACT2 by lia; apply ACT1; exact Hs|]. split; [exact LIVE2|].
        split; [eapply GP_trans; [exact (GP_taf _ _ _ TAF)| eapply GP_trans; [exact GP2| apply GP_eq; [exact RG4| exact SE4]]]|].
        right. exists g, b, ai. rewrite L4, SC4, STR4, G4, SS4.
        split; [lia|]. split; [exact HA4|]. split; [exact Hb|]. split; [reflexivity|]. split; [exact FIT|]. split; [exact STR|].
        split; [exact INV4| exact TF4].
    + destruct RES2 as [INV2 TF2']. eapply HK. split; [intros sc' Hs; rewrite ACT2 by lia; apply ACT1; exact Hs|]. split; [exact LIVE2|].
      split; [eapply GP_trans; [exact (GP_taf _ _ _ TAF)| exact GP2]|].
      left. split; [reflexivity|]. split; [exact INV2| exact TF2'].
  - (* [comment removed for export] *)
    replace (negb (first =? 0)) with true by (symmetry; apply negb_true_iff; apply Z.eqb_neq; exact NZ).
    cbn iota. rewrite Eidx. eapply HK.
    split; [exact ACT1|]. split; [reflexivity|]. split; [exact (GP_taf _ _ _ TAF)|]. right.
    pose proof (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV1))))) _ _ _ Hg) as GO.
    (first [ pose proof ((g_stride _ _ _ _ _ _ GO ltac:(rewrite SC; lia))) as dR_4; dand3 dR_4 as GS _ _ | pose proof (g_stride _ _ _ _ _ _ GO ltac:(rewrite SC; lia)) as (GS & _ & _) ]). rewrite SC in GS.
    exists g, bg, ai. split; [exact Hidx|]. split; [exact HA|]. split; [exact Hg|]. split; [exact SC|].
    split; [lia|]. split; [intros Hs28; destruct GS; lia|]. split; [exact INV1|]. apply TF0_TF2. exact TF1.
Qed.
End SLOT.
End MI_Wdy2.

Module MI_Wj0q.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require STree Malloc KInv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_List.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Inv MI_Kit MI_Arith MI_Geom MI_List MI_Ext MI_S421.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_WFree.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Ws22 MI_Wp9i MI_Cnt.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.STree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malloc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_List.MI_Tree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Kit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Arith OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Geom OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_List OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ext OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_S421 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres2.MI_Pres1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WFree.MI_Read OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ws22 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Wp9i OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Cnt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_TF2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.  (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition fold_f (s : Z) : bool := forallb (fun off => negb (s <? off) || ((0 <=? fold_off off s) && (fold_off off s <=? s))) (zrange 0 256).
Lemma fold_all : forallb fold_f (zrange 0 256) = true. Proof. vm_compute. reflexivity. Qed.

Lemma fold_off_le off slack : 0 <= off < 256 -> 0 <= slack -> 0 <= fold_off off slack <= slack.
Proof.
  intros Ho Hs. destruct (Z.ltb_spec slack off) as [LT|GE].
  - pose proof (forallb_zrange fold_f 0 256 slack fold_all ltac:(lia) ltac:(lia)) as H. unfold fold_f in H.
    pose proof (forallb_zrange _ 0 256 off H ltac:(lia) ltac:(lia)) as H2. cbn beta in H2.
    replace (slack <? off) with true in H2 by (symmetry; apply Z.ltb_lt; exact LT). cbn in H2.
    apply andb_true_iff in H2 as [A B]. apply Z.leb_le in A. apply Z.leb_le in B. lia.
  - unfold fold_off. replace (slack <? off) with false by (symmetry; apply Z.ltb_ge; exact GE). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma s_shadow_havoc p n st : 0 < n ->
  s_shadow (havoc p n st) = <[fst p := get_shadow (havoc p n st) (fst p)]> (s_shadow st).
Proof.
  intros Hn. unfold havoc at 1. replace (n <=? 0) with false by (symmetry; apply Z.leb_gt; lia). unfold upd_shadow. cbn -[havoc get_shadow Z.add Z.mul Z.div Z.ltb].
  f_equal. unfold havoc. replace (n <=? 0) with false by (symmetry; apply Z.leb_gt; lia). rewrite get_shadow_upd_shadow, N.eqb_refl. reflexivity.
Qed.

Lemma TKS_havoc p n st : snd p mod 16 = 0 -> 0 < n -> TKS st (s_tick st) -> TKS (havoc p n st) (s_tick st).
Proof.
  intros Al Hn TK rid sh. rewrite s_shadow_havoc by exact Hn.
  destruct (N.eq_dec rid (fst p)) as [->|NE]; [| rewrite lookup_insert_ne by congruence; apply TK].
  rewrite lookup_insert_eq. intros E. inversion E. subst sh. clear E.
  pose proof (sh_ticks_of st (fst p) TK) as [T1 T2].
  destruct (havoc_ticks p n st Hn ltac:(intros u hl Hu ch Hch; exact (T1 u hl ch Hu Hch)) (fst p)
              ltac:(intros u hl Hu ch Hch; exact (T1 u hl ch Hu Hch)) T2) as [A B].
  split; [| split; [intros u hl ch Hu Hch; exact (A u hl Hu ch Hch)| exact B]].
  rewrite havoc_cells by exact Hn. unfold get_shadow. destruct (s_shadow st !! fst p) as [sh0|] eqn:E0; cbn.
  - exact (proj1 (TK _ _ E0)).
  - intros o w t Ho. rewrite lookup_empty in Ho. discriminate.
Qed.

Lemma DOMS_havoc st0 p n st : 0 < n -> DOMS st0 st -> (exists r, s_regions st0 !! fst p = Some r /\ r_kind r = RKGroup) -> DOMS st0 (havoc p n st).
Proof.
  intros Hn D Hp rid sh. rewrite s_shadow_havoc by exact Hn.
  destruct (N.eq_dec rid (fst p)) as [->|NE]; [intros _; exact Hp|]. rewrite lookup_insert_ne by congruence. apply D.
Qed.

Lemma havoc_ctrl p n st : ctrl_eq st (havoc p n st) /\ s_tick (havoc p n st) = s_tick st.
Proof. unfold havoc. destruct (n <=? 0); [split; [apply ctrl_eq_refl| reflexivity]|]. split; [constructor; reflexivity| reflexivity]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section EF.
Variables (st : mstate) (g : aptr) (idx n off : Z).
Let mr := get_meta_rec st g.
Let stride := get_stride mr.
Let gm := default (0%N, 0) (m_mem mr).
Let c : aptr := aadd gm (UNIT + stride * idx).
Let e : aptr := aadd c (stride - IB).
Let p0 : aptr := if off =? 0 then c else aadd c (UNIT * off).
Let res := snd e - snd p0 - n.
Let q := (snd p0 - (snd gm + UNIT)) / UNIT.

Definition ef_list : list (aptr * Z) :=
  (if negb (off =? 0) then [(aadd c (-2), off); (aadd (aadd c (-2)) 1, Z.shiftr off 8); (aadd c (-3), 224); (aadd p0 (-4), 0)] else [])
  ++ [(aadd p0 (-2), q); (aadd (aadd p0 (-2)) 1, Z.shiftr q 8); (aadd p0 (-3), idx)]
  ++ (if negb (res =? 0) then [(aadd e (- res), 0)] else [])
  ++ (if 5 <=? res then [(aadd e (-4), res); (aadd (aadd e (-4)) 1, Z.shiftr res 8); (aadd (aadd e (-4)) 2, Z.shiftr res 16); (aadd (aadd e (-4)) 3, Z.shiftr res 24); (aadd e (-5), 0)] else [])
  ++ [(aadd p0 (-3), Z.land idx 31 + Z.shiftl (if 5 <=? res then 5 else res) 5)].

Lemma enframe_at_eq : enframe_at st g idx n off = (wrs ef_list st, p0).
Proof.
  unfold enframe_at, set_size, ef_list. unfold q, res, p0, e, c, gm, stride, mr.
  (* [comment removed for export] *)
  destruct (off =? 0); cbn beta iota delta [wr16 wr32 wrs app negb];
    match goal with |- context [if negb (?x =? 0) then _ else _] => destruct (x =? 0) end;
    match goal with |- context [if 5 <=? ?x then _ else _] => destruct (5 <=? x) end; cbn beta iota delta [wrs app negb]; reflexivity.
Qed.

Lemma p0_eq : p0 = aadd c (UNIT * off).
Proof. unfold p0. destruct (Z.eqb_spec off 0) as [->|]; [| reflexivity]. unfold c, aadd. cbn. f_equal. lia. Qed.
End EF.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint lastw (l : list (aptr * Z)) (r : aptr) (acc : option Z) : option Z :=
  match l with
  | [] => acc
  | (a, v) :: l' => lastw l' r (if aptr_eqb a r then Some v else acc)
  end.

Lemma lastw_acc l r v : lastw l r (Some v) = match lastw l r None with Some w => Some w | None => Some v end.
Proof.
  revert v. induction l as [|[a w] l IH]; intros v; cbn; [reflexivity|].
  destruct (aptr_eqb a r); [| apply IH]. rewrite !(IH w). destruct (lastw l r None); reflexivity.
Qed.

Lemma wrs_lastw l : forall st r, TKS st (s_tick st) ->
  cell_read (get_shadow (wrs l st) (fst r)) (snd r) =
  match lastw l r None with Some w => Known (Z.land w 255) | None => cell_read (get_shadow st (fst r)) (snd r) end.
Proof.
  induction l as [|[a v] l IH]; intros st r TK; cbn [wrs lastw]; [reflexivity|].
  rewrite IH by (apply TKS_wr8; [cbn; lia| exact TK]).
  destruct (aptr_eqb_spec a r) as [<-|NE].
  - rewrite lastw_acc. destruct (lastw l a None); [reflexivity|]. apply cell_read_wr8_same. apply sh_ticks_of. exact TK.
  - destruct (lastw l r None); [reflexivity|]. apply cell_read_wr8_other. congruence.
Qed.

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma known_range X st L BL LS q v : INVL X st L BL LS -> cell_read (get_shadow st (fst q)) (snd q) = Known v -> 0 <= v < 256.
Proof.
  intros INV H. eapply known_byte; [| exact H]. intros sh o' v' t Hs Hc. exact (proj1 (proj1 (TKS_of _ _ _ _ _ INV _ _ Hs) o' v' t Hc)).
Qed.

End CEIL.

(* [comment removed for export] *)

Lemma land255_range a : 0 <= Z.land a 255 < 256.
Proof.
  split; [apply Z.land_nonneg; right; lia|].
  change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia.
Qed.
End MI_Wj0q.

Module MI_W9kq.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require STree Malloc KInv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_List.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Inv MI_Kit MI_Arith MI_Geom MI_List MI_Ext MI_S421.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_WFree.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Ws22 MI_Wp9i MI_Cnt.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.STree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malloc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_List.MI_Tree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Kit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Arith OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Geom OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_List OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ext OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_S421 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres2.MI_Pres1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WFree.MI_Read OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ws22 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Wp9i OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Cnt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_TF2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_Wj0q.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.  (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma havoc_le0 p n st : n <= 0 -> havoc p n st = st.
Proof. intros H. unfold havoc. destruct (Z.leb_spec n 0); [reflexivity| lia]. Qed.

Section ENFRAME.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
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

#[using="IM Hg INV LS BL L X Clg"] Lemma ef_gbase : gbase (MR st g) = bg. Proof. exact (hosts_gbase _ _ _ IM _ _ Hg). Qed.
#[using="IM slack stride Hg INV n LS BL L X Clg"] Lemma ef_c : aadd (default (0%N, 0) (m_mem (get_meta_rec st g))) (UNIT + get_stride (get_meta_rec st g) * idx) = c.
Proof. fold (MR st g). change (default (0%N, 0) (m_mem (MR st g))) with (gbase (MR st g)). rewrite ef_gbase. unfold c, sstart, aadd. rewrite ef_gbase. f_equal. lia. Qed.
#[using="IM Hg INV LS BL L X Clg"] Lemma ef_slot : slot_start' (MR st g) idx = c. Proof. exact (slot_start'_eq _ _ _ IM _ _ idx Hg). Qed.
#[using="IS IM Hidx Hg INV LS BL L X Clg"] Lemma ef_slots : s_slots st !! c = Some (g, idx). Proof. rewrite <- ef_slot. exact (is_total _ _ _ IS _ _ _ Hg Hidx). Qed.
#[using="IG Hg INV bg LS BL L X Clg"] Lemma ef_stride : 16 <= stride /\ stride mod 16 = 0.
Proof. pose proof (stride_ge _ _ _ IG _ _ Hg) as [A B]. unfold UNIT in *. split; assumption. Qed.
#[using="slack stride Hg INV n LS BL L X Clg"] Lemma ef_c16 : snd c mod 16 = 0.
Proof.
  pose proof (sstart_res X st L BL LS INV bg g idx Hg) as R. unfold c. cbn [snd]. unfold IB in R.
  pose proof (Z.div_mod (sstart (MR st g) idx - 4) 16 ltac:(lia)). pose proof (Z.div_mod (sstart (MR st g) idx) 16 ltac:(lia)).
  pose proof (Z.mod_pos_bound (sstart (MR st g) idx) 16 ltac:(lia)). lia.
Qed.
#[using="IS IM HP Hidx Hg INV LS BL L X Clg"] Lemma ef_NH : s_groups st !! c = None.
Proof.
  destruct Hg as [ai Hb]. pose proof (is_part _ _ _ IS _ _ _ idx Hb Hidx) as P5. cbn zeta in P5. rewrite ef_slot, HP in P5.
  destruct (s_groups st !! c) eqn:E; [| reflexivity]. exfalso. (first [ dand11 P5 as _ _ _ _ _ _ _ _ _ _ nDE | destruct P5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & nDE) ]). apply nDE. split; [congruence| reflexivity].
Qed.
(* [comment removed for export] *)
#[using="IG IM slack Hres Hfit Hn HP Hidx Hg INV LS BL L X Clg"] Lemma ef_q_range off : 0 <= off <= 255 -> UNIT * off + n <= stride - IB -> 0 <= (snd c + UNIT * off - (snd bg + UNIT)) / UNIT < 2 ^ 16.
Proof.
  intros Ho Hf. destruct Hg as [ai Hb]. pose proof (ig_ok _ _ _ IG _ _ _ Hb) as GO.
  pose proof (g_stride _ _ _ _ _ _ GO) as GS. pose proof (g_sc _ _ _ _ _ _ GO) as SC. pose proof (g_li _ _ _ _ _ _ GO) as LI.
  unfold c. cbn [snd]. unfold sstart. rewrite ef_gbase. fold stride. pose proof ef_stride as [S16 SM].
  replace (snd bg + UNIT + stride * idx + UNIT * off - (snd bg + UNIT)) with ((stride / 16 * idx + off) * 16)
    by (unfold UNIT; pose proof (Z.div_mod stride 16 ltac:(lia)) as DM; clear - DM SM; nia).   (* [comment removed for export] *)
  unfold UNIT. rewrite Z.div_mul by lia.
  assert (0 <= stride / 16 * idx) by (apply Z.mul_nonneg_nonneg; [apply Z.div_pos; lia| lia]).
  split; [lia|].
  destruct SC as [[SC1 _]|(SC63 & L0 & _)].
  - (first [ pose proof ((GS ltac:(lia))) as dR_3; dand3 dR_3 as _ _ LT | destruct (GS ltac:(lia)) as (_ & _ & LT) ]). unfold cnt_of in LT. fold stride in LT.
    assert (HM : stride * idx <= stride * (m_last_idx (MR st g))) by (apply Z.mul_le_mono_nonneg_l; lia).
    pose proof (Z.div_mod stride 16 ltac:(lia)) as DM. unfold IB, UNIT in Hf.
    clear - HM DM SM S16 Hf LT Ho Hidx LI; nia.   (* [comment removed for export] *)
  - rewrite L0 in Hidx. assert (idx = 0) by lia. subst idx. rewrite Z.mul_0_r. lia.
Qed.

(* [comment removed for export] *)
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

#[using="IM slack Hg INV LS BL L X Clg"] Lemma EL_eq off : ef_list st g idx n off = EL off.
Proof.
  unfold ef_list, EL. rewrite (p0_eq st g idx n off). rewrite ef_c. fold (MR st g). fold stride.
  change (default (0%N, 0) (m_mem (MR st g))) with (gbase (MR st g)). rewrite ef_gbase. reflexivity.
Qed.

#[using="IM slack Hg INV LS BL L X Clg"] Lemma enframe_at_EL off : enframe_at st g idx n off = (wrs (EL off) st, pp off).
Proof. rewrite (enframe_at_eq st g idx n off), EL_eq, (p0_eq st g idx n off), ef_c. reflexivity. Qed.

Definition stw (off : Z) : mstate := wrs (EL off) st.
Definition stf (off : Z) : mstate := havoc (pp off) n (stw off).

#[using="slack INV LS BL L X Clg"] Lemma stw_TKS off : TKS (stw off) (s_tick st).
Proof. apply wrs_TKS; [lia| exact (TKS_of _ _ _ _ _ INV)]. Qed.
Lemma stw_tick off : s_tick (stw off) = s_tick st. Proof. exact (proj2 (wrs_ctrl (EL off) st)). Qed.
Lemma stw_ctrl off : ctrl_eq st (stw off). Proof. exact (proj1 (wrs_ctrl (EL off) st)). Qed.
#[using="slack stride Hg INV n LS BL L X Clg"] Lemma pp16 off : snd (pp off) mod 16 = 0.
Proof. unfold pp, aadd. cbn [snd]. unfold UNIT. rewrite Z.add_mod, ef_c16, Z.mul_comm, Z_mod_mult by lia. reflexivity. Qed.
#[using="slack INV LS BL L X Clg"] Lemma stw_hav off u hl : r_hav (get_shadow (stw off) (fst (pp off))) !! u = Some hl -> hl_ticks hl (s_tick (stw off)).
Proof. intros Hu ch Hch. rewrite stw_tick. pose proof (stw_TKS off) as TK. rewrite <- (stw_tick off) in TK. rewrite <- (stw_tick off). exact (proj1 (sh_ticks_of _ _ TK) u hl ch Hu Hch). Qed.

Lemma stf_ctrl off : ctrl_eq st (stf off) /\ s_tick (stf off) = s_tick st.
Proof.
  destruct (havoc_ctrl (pp off) n (stw off)) as [C T]. split; [exact (ctrl_eq_trans _ _ _ (stw_ctrl off) C)| rewrite T; apply stw_tick].
Qed.

#[using="slack Hn Hg INV LS BL L X Clg"] Lemma stf_read_out off r : ~ (fst r = fst bg /\ snd (pp off) <= snd r < snd (pp off) + n) ->
  cell_read (get_shadow (stf off) (fst r)) (snd r) = cell_read (get_shadow (stw off) (fst r)) (snd r).
Proof.
  intros Hr. unfold stf. destruct (Z.eq_dec n 0) as [N0|NZ]; [rewrite havoc_le0 by lia; reflexivity|].
  apply (cell_read_havoc_out (pp off) n (stw off) (pp16 off) ltac:(lia) (stw_hav off)). exact Hr.
Qed.

(* [comment removed for export] *)
#[using="IG slack Hfit Hn Hg INV LS BL L X Clg"] Lemma EL_addrs off a : 0 <= off -> UNIT * off + n <= stride - IB -> In a (map fst (EL off)) ->
  fst a = fst bg /\ snd c - 3 <= snd a < snd c + stride - 4 /\ ~ (snd (pp off) <= snd a < snd (pp off) + n).
Proof.
  intros Ho Hf Hin. pose proof ef_stride as [S16 _].
  assert (R : 0 <= resv off) by (unfold resv, ee, pp, aadd; cbn [fst snd]; unfold IB, UNIT in *; lia).
  unfold EL in Hin.
  destruct (Z.eqb_spec off 0) as [O0|O0]; destruct (Z.eqb_spec (resv off) 0) as [R0|R0]; destruct (Z.leb_spec 5 (resv off)) as [R5|R5];
    cbn [negb app map fst In] in Hin; unfold resv, ee, pp, aadd in *; cbn [fst snd] in *; unfold IB, UNIT in *;
    repeat match type of Hin with _ \/ _ => destruct Hin as [<-|Hin] | False => destruct Hin end; unfold c; cbn [fst snd]; (split; [reflexivity| lia]).
Qed.

(* [comment removed for export] *)
#[using="slack Hn Hidx Hg INV LS BL L X Clg"] Lemma stf_known_w off x w : 0 <= off -> UNIT * off + n <= stride - IB ->
  ~ (snd (pp off) <= x < snd (pp off) + n) ->
  lastw (EL off) (fst bg, x) None = Some w -> known (stf off) (fst bg, x) (Z.land w 255).
Proof.
  intros Ho Hf Hx HL. unfold known, SHd. cbn [fst snd].
  rewrite (stf_read_out off (fst bg, x)) by (cbn [fst snd]; tauto).
  unfold stw. rewrite (wrs_lastw (EL off) st (fst bg, x) (TKS_of _ _ _ _ _ INV)). rewrite HL. reflexivity.
Qed.

#[using="slack Hn Hidx Hg INV LS BL L X Clg"] Lemma stf_known_old off x v : 0 <= off -> UNIT * off + n <= stride - IB ->
  ~ (snd (pp off) <= x < snd (pp off) + n) ->
  lastw (EL off) (fst bg, x) None = None -> known st (fst bg, x) v -> known (stf off) (fst bg, x) v.
Proof.
  intros Ho Hf Hx HL K. unfold known, SHd in *. cbn [fst snd] in *.
  rewrite (stf_read_out off (fst bg, x)) by (cbn [fst snd]; tauto).
  unfold stw. rewrite (wrs_lastw (EL off) st (fst bg, x) (TKS_of _ _ _ _ _ INV)). rewrite HL. exact K.
Qed.

#[using="IG slack Hfit Hn Hg INV LS BL L X Clg"] Lemma EL_not_in off a : 0 <= off -> UNIT * off + n <= stride - IB ->
  snd (pp off) <= a < snd (pp off) + n -> ~ In (fst bg, a) (map fst (EL off)).
Proof. intros Ho Hf Ha Hin. (first [ pose proof ((EL_addrs off _ Ho Hf Hin)) as dR_4; dand3 dR_4 as _ _ NR | destruct (EL_addrs off _ Ho Hf Hin) as (_ & _ & NR) ]). apply NR. exact Ha. Qed.

#[using="IS IG IM slack TF Hfit Hn HP Hidx Hg INV LS BL L X Clg"] Lemma stf_unknown off a : 0 <= off -> UNIT * off + n <= stride - IB ->
  snd (pp off) <= a < snd (pp off) + n -> unknown (stf off) (fst bg, a).
Proof.
  intros Ho Hf Ha. unfold unknown, SHd, stf. cbn [fst snd].
  destruct (cell_read_havoc_in (pp off) n (stw off) (pp16 off) ltac:(lia) (stw_hav off) (fst bg, a) eq_refl Ha) as [h Hh]; [| exists h; exact Hh].
  cbn [snd]. intros v tk Hc. unfold stw in Hc. rewrite wrs_cells_other in Hc by (apply EL_not_in; assumption).
  rewrite stw_tick. change (fst (pp off)) with (fst bg) in Hc.
  apply (TF2_interior_old X st L BL LS INV g bg idx Hg Hidx ef_NH TF a v tk Hc).
  unfold pp, aadd, c in Ha. cbn [fst snd] in Ha. rewrite sstart_succ. fold stride. unfold IB, UNIT in *. lia.
Qed.

(* [comment removed for export] *)
Ltac aeq :=
  match goal with
  | |- context [aptr_eqb ?a ?b] =>
      first [ rewrite (aptr_eqb_neq a b) by (unfold pp, ee, aadd, c; cbn [fst snd]; intros E; apply (f_equal snd) in E; cbn [snd] in E; unfold IB, UNIT in *; lia)
            | rewrite (proj2 (aptr_eqb_eq a b)) by (unfold pp, ee, aadd, c; cbn [fst snd]; unfold IB, UNIT in *; f_equal; lia) ]
  end.
Ltac lastw_eval :=
  unfold EL; cbn [lastw app negb]; repeat aeq; reflexivity.

#[using="slack"] Lemma res_eq off : resv off = stride - IB - UNIT * off - n.
Proof. unfold resv, ee, pp, aadd. cbn [snd]. lia. Qed.
(* [comment removed for export] *)

#[using="ISH IS IG IM slack Hres TF Hfit Hn HP Hidx Hg INV LS BL L X Clg"] Lemma blk_ok off : 0 <= off <= 255 -> UNIT * off + n <= stride - IB ->
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
  - (* [comment removed for export] *) destruct (Z.eqb_spec off 0) as [O0|O0].
    + apply (stf_known_old off); [lia| exact Hf| apply NP; lia| |].
      * unfold EL. rewrite O0 at 1. cbn [Z.eqb negb app lastw].
        destruct (negb (resv off =? 0)); destruct (5 <=? resv off); cbn [lastw app]; try (exfalso; lia); repeat aeq; reflexivity.
      * subst off. pose proof (ish_hdr0 _ _ ISH bg g idx (ex_intro _ ai Hb) ltac:(unfold cnt_of; lia)) as K.
        unfold c. cbn [snd]. replace (sstart (MR st g) idx + UNIT * 0 - 4) with (sstart (MR st g) idx - IB) by (unfold IB, UNIT; lia). exact K.
    + apply (stf_known_w off _ 0); [lia| exact Hf| apply NP; lia|].
      unfold EL. replace (off =? 0) with false by (symmetry; apply Z.eqb_neq; exact O0). cbn [negb app lastw].
      destruct (negb (resv off =? 0)); destruct (5 <=? resv off); cbn [lastw app]; try (exfalso; lia); repeat aeq; reflexivity.
  - (* [comment removed for export] *)
    replace (idx + 32 * Z.min (resv off) 5) with (Z.land (Z.land idx 31 + Z.shiftl (if 5 <=? resv off then 5 else resv off) 5) 255).
    2:{ replace (Z.land idx 31) with idx by (change 31 with (Z.ones 5); rewrite Z.land_ones by lia; rewrite Z.mod_small; lia). rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
        destruct (Z.leb_spec 5 (resv off)).
        - rewrite Z.min_r by lia. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. rewrite Z.mod_small; lia.
        - rewrite Z.min_l by lia. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. rewrite Z.mod_small; lia. }
    apply (stf_known_w off); [lia| exact Hf| apply NP; lia|].
    unfold EL. destruct (off =? 0); destruct (negb (resv off =? 0)); destruct (5 <=? resv off); cbn [negb lastw app]; try (exfalso; lia); repeat aeq; reflexivity.
  - (* [comment removed for export] *) unfold byte_of. rewrite Z.mul_0_r, Z.shiftr_0_r.
    apply (stf_known_w off); [lia| exact Hf| apply NP; lia|].
    unfold EL. destruct (off =? 0); destruct (Z.eqb_spec (resv off) 0); destruct (Z.leb_spec 5 (resv off)); cbn [negb lastw app]; try (exfalso; lia); repeat aeq; reflexivity.
  - (* [comment removed for export] *) unfold byte_of. rewrite Z.mul_1_r.
    apply (stf_known_w off); [lia| exact Hf| apply NP; lia|].
    unfold EL. destruct (off =? 0); destruct (Z.eqb_spec (resv off) 0); destruct (Z.leb_spec 5 (resv off)); cbn [negb lastw app]; try (exfalso; lia); repeat aeq; reflexivity.
  - (* [comment removed for export] *) intros R5. unfold byte_of. rewrite Z.mul_0_r, Z.shiftr_0_r, Z.mul_1_r.
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
  - (* [comment removed for export] *) intros RP.
    replace (snd c + stride - IB - resv off) with (snd (pp off) + n) by (rewrite RE, PP; lia).
    apply (stf_known_w off _ 0); [lia| exact Hf| apply NP; lia|].
    assert (EZ : (resv off =? 0) = false) by (apply Z.eqb_neq; lia).
    unfold EL; rewrite EZ. destruct (off =? 0); destruct (Z.leb_spec 5 (resv off)); cbn [negb lastw app];
      try (destruct (Z.eq_dec (resv off) 5)); try (exfalso; lia); repeat aeq; reflexivity.
  - (* [comment removed for export] *) intros a Ha. apply (stf_unknown off); [lia| exact Hf|]. rewrite PP. exact Ha.
Qed.


(* [comment removed for export] *)
#[using="ISH IS IG IM slack Hres TF Hfit Hn HP Hidx Hg INV"] Lemma ef_INVL off : 0 <= off <= 255 -> UNIT * off + n <= stride - IB ->
  INVL X' (stf off) L (((c, off), n) :: BL) LS.
Proof.
  intros Ho Hf. destruct (stf_ctrl off) as [CE TK]. pose proof ef_stride as [S16 _].
  destruct Hg as [ai Hb] eqn:EHg.
  apply (INVL_add_block X st (stf off) L BL LS c off n INV HP CE TK).
  - intros m i Hs q Hq. rewrite ef_slots in Hs. inversion Hs. subst m i.
    assert (NQ : ~ (fst q = fst bg /\ snd (pp off) <= snd q < snd (pp off) + n)).
    { intros [F R]. apply Hq. unfold inT, c. cbn [fst snd]. split; [exact F|]. unfold pp, aadd, c in R. cbn [snd] in R. rewrite sstart_succ. fold stride. unfold IB, UNIT in *. lia. }
    rewrite (stf_read_out off q NQ). unfold stw. apply wrs_read_other.
    intros Hin. (first [ pose proof ((EL_addrs off q ltac:(lia) Hf Hin)) as dR_5; dand3 dR_5 as F R _ | destruct (EL_addrs off q ltac:(lia) Hf Hin) as (F & R & _) ]). apply Hq. unfold inT, c. cbn [fst snd]. split; [exact F|].
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

#[using="ISH IS IG IM slack Hres TF Hfit Hn HP Hidx Hg INV"] Theorem enframe_ft ctr (Post : mled -> mstate * optr -> Prop) :
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
End MI_W9kq.

Module MI_Wkfj.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require STree Malloc KInv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_List.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Inv MI_Kit MI_Arith MI_Geom MI_List MI_Ext MI_S421.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres4 MI_Ws22.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_W2ig.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_W2ig MI_W3do.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_WTry2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_WTry2 MI_Wp9i MI_Cnt.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Bits.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.STree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malloc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_List.MI_Tree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Kit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Arith OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Geom OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_List OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ext OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_S421 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres2.MI_Pres1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres4.MI_Pres3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ws22 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_W2ig.MI_Lsjc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_W2ig OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_W3do OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WTry2.MI_WTry OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WTry2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Wp9i OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Cnt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_TF2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_Wm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_WSlot OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_Wvdb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_Wdy2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_Wj0q OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_W9kq OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Bits.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.  (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma INVL_set_tick X st L BL LS t : (s_tick st <= t)%N -> INVL X st L BL LS -> INVL X (set_tick t st) L BL LS.
Proof.
  (intros Ht; (first [ intro dR_10; dand7 dR_10 as IR IA IM IL IG IS ISH | intros (IR & IA & IM & IL & IG & IS & ISH) ])).
  assert (CE : ctrl_eq st (set_tick t st)) by (constructor; reflexivity).
  split; [apply (inv_R_ctrl X st _ L CE); exact IR|]. split; [apply (inv_A_ctrl st _ CE); exact IA|].
  split; [apply (inv_M_ctrl X st _ LS CE); exact IM|]. split; [apply (inv_L_ctrl st _ LS CE); exact IL|].
  split; [apply (inv_G_ctrl X st _ LS CE); exact IG|]. split; [apply (inv_S_ctrl X st _ BL CE); exact IS|].
  apply inv_SH_set_tick; [exact Ht| exact ISH].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition CORE_POST (st0 : mstate) (n : Z) (L : mled) (BL : list blk) (L1 : mled) (r : mstate * option (aptr * Z)) : Prop :=
  ld_live L1 = ld_live L /\ GP st0 (fst r) /\
  match snd r with
  | None => exists LS1, INVL x0 (fst r) L1 BL LS1
  | Some (g, idx) => exists LS1 bg, let st1 := fst r in
      hosts st1 bg g /\ 0 <= idx <= m_last_idx (MR st1 g)
      /\ INVL (xpend x0 (Some (fst bg, sstart (MR st1 g) idx))) st1 L1 BL LS1
      /\ n + IB <= get_stride (MR st1 g) /\ TF2 st1 /\ get_stride (MR st1 g) - IB - n < 2 ^ 32
  end.

Lemma small_stride X st L BL LS bg g : INVL X st L BL LS -> hosts st bg g -> m_sizeclass (MR st g) < 48 -> get_stride (MR st g) < 2 ^ 20.
Proof.
  intros INV [ai Hb] Hsc. pose proof (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) _ _ _ Hb) as GO.
  (first [ pose proof ((g_stride _ _ _ _ _ _ GO Hsc)) as dR_1; dand3 dR_1 as _ _ LT | destruct (g_stride _ _ _ _ _ _ GO Hsc) as (_ & _ & LT) ]). pose proof (g_li _ _ _ _ _ _ GO). unfold cnt_of in LT.
  pose proof (stride_ge _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) _ _ (ex_intro _ ai Hb)) as [S _]. unfold UNIT in S. nia.
Qed.

End CEIL.

Section CORE.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
Variables (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (n : Z).
Hypothesis INV : INVL x0 st L BL LS.
Hypothesis TF : TF0 st.
Hypothesis Hn : 0 <= n.

(* [comment removed for export] *)
Lemma malloc_small_ft : n < MMAP_THRESHOLD ->
  ftree L (malloc_small_ctrl full_lay st n (fun st1 r => ret (st1, r)) (ret (st, @None (aptr * Z)))) (CORE_POST st n L BL).
Proof.
  intros Hlt. pose proof (size_to_class_ok n ltac:(lia)) as [SC FIT].
  unfold malloc_small_ctrl.
  set (sc0 := size_to_class n) in *.
  set (sc := match active st sc0 with Some _ => sc0 | None => _ end).
  assert (SC' : 0 <= sc < 48 /\ n + IB <= UNIT * size_class sc).
  { subst sc. destruct (active st sc0); [auto|].
    destruct ((4 <=? sc0) && (sc0 <? 32) && negb (sc0 =? 6) && Z.even sc0 && (usage st sc0 =? 0)) eqn:E; [| auto].
    match goal with |- context [if ?c then Z.lor sc0 1 else sc0] => destruct c end; [| auto].
    apply andb_true_iff in E as [E _]. apply andb_true_iff in E as [E EV]. apply andb_true_iff in E as [E _]. apply andb_true_iff in E as [E1 E2].
    apply Z.leb_le in E1. apply Z.ltb_lt in E2.
    rewrite (lor1_even sc0 ltac:(lia) EV). split; [lia|].
    pose proof (size_class_lt sc0 (sc0 + 1) ltac:(lia) ltac:(lia) ltac:(lia)). unfold UNIT in *. lia. }
  clearbody sc. destruct SC' as [SC' FIT'].
  destruct (active st sc) as [gp|] eqn:HA.
  - (* [comment removed for export] *)
    destruct (Z.eqb_spec (m_avail (get_meta_rec st gp)) 0) as [AZ|ANZ].
    + rewrite AZ. change (lowbit 0) with 0. cbn [negb Z.eqb].
      (* [comment removed for export] *)
      apply (alloc_slot_ft (mstate * option (aptr * Z)) (CORE_POST st n L BL) FUEL sc [] st L BL LS n); try assumption.
      * unfold FUEL. cbn. lia.
      * apply NoDup_nil_2.
      * (intros st1 idx L1 LS1; (first [ intro dR_11; dand4 dR_11 as ACT LIVE GP1 RES | intros (ACT & LIVE & GP1 & RES) ])). destruct RES as [(-> & INV1 & TF1)|(g & bg & ai & Hidx & HA1 & Hg & SCg & FIT1 & STR1 & INV1 & TF1)].
        -- cbn [ftree ret]. unfold CORE_POST. cbn [fst snd]. split; [exact LIVE|]. split; [exact GP1|]. exists LS1. exact INV1.
        -- replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia). rewrite HA1. cbn [ftree ret]. unfold CORE_POST. cbn [fst snd]. split; [exact LIVE|]. split; [exact GP1|].
           exists LS1, bg. split; [exists ai; exact Hg|]. split; [exact Hidx|]. split; [exact INV1|]. split; [exact FIT1|]. split; [exact TF1|].
           pose proof (small_stride _ _ _ _ _ bg g INV1 (ex_intro _ ai Hg) ltac:(lia)). unfold IB. lia.
    + (* [comment removed for export] *)
      (first [ pose proof ((hd_facts x0 st L BL LS sc gp INV HA)) as dR_2; dand5 dR_2 as _ Esc bm ai Hbm | destruct (hd_facts x0 st L BL LS sc gp INV HA) as (_ & Esc & bm & ai & Hbm) ]).
      pose proof (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) _ _ _ Hbm) as GO.
      pose proof (proj1 (g_masks _ _ _ _ _ _ GO)) as A0. fold (MR st gp) in ANZ |- *.
      (first [ pose proof ((lowbit_idiom (m_avail (MR st gp)) ltac:(lia))) as dR_3; dex1 dR_3 as k; dand5 dR_3 as Hk LB CTZ TB _ | pose proof ((lowbit_idiom (m_avail (MR st gp)) ltac:(lia))) as dR_3; dand6 dR_3 as k Hk LB CTZ TB _ | destruct (lowbit_idiom (m_avail (MR st gp)) ltac:(lia)) as (k & Hk & LB & CTZ & TB & _) ]).
      assert (LNZ : (lowbit (m_avail (MR st gp)) =? 0) = false) by (apply Z.eqb_neq; rewrite LB; pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk); lia).
      rewrite LNZ. cbn [negb ftree ret]. unfold CORE_POST. cbn [fst snd]. split; [reflexivity|]. split; [apply GP_eq; reflexivity|].
      (first [ pose proof ((ta_fin_ok x0 st L BL LS gp bm ai INV eq_refl eq_refl Hbm ltac:(rewrite Esc; exact (hd_head x0 st L BL LS sc gp INV HA)) ANZ)) as dR_4; dand5 dR_4 as INV1 Hidx _ _ STR | pose proof (ta_fin_ok x0 st L BL LS gp bm ai INV eq_refl eq_refl Hbm ltac:(rewrite Esc; exact (hd_head x0 st L BL LS sc gp INV HA)) ANZ) as (INV1 & Hidx & _ & _ & STR) ]).
      set (st1 := upd_meta gp (m_set_avail (m_avail (MR st gp) - lowbit (m_avail (MR st gp)))) st) in *.
      assert (MR1 : forall x, x <> gp -> MR st1 x = MR st x) by (intros x NE; unfold st1, MR; apply get_meta_rec_upd_other; exact NE).
      assert (MRg : m_last_idx (MR st1 gp) = m_last_idx (MR st gp) /\ get_stride (MR st1 gp) = get_stride (MR st gp) /\ (forall i, sstart (MR st1 gp) i = sstart (MR st gp) i) /\ m_sizeclass (MR st1 gp) = m_sizeclass (MR st gp)).
      { unfold st1, MR. rewrite get_meta_rec_upd_same. destruct (get_meta_rec st gp); cbn; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity. }
      (first [ dand4 MRg as ML MS MSS MSC | destruct MRg as (ML & MS & MSS & MSC) ]).
      exists LS, bm. rewrite ML, MS, MSS. split; [exists ai; exact Hbm|]. split; [exact Hidx|]. split; [exact INV1|].
      rewrite Esc in STR. split; [lia|].
      split; [apply TF0_TF2; apply (TF0_ctrl st st1); [reflexivity| reflexivity| exact TF]|].
      pose proof (small_stride _ _ _ _ _ bm gp INV (ex_intro _ ai Hbm) ltac:(lia)). unfold IB. lia.
  - (* [comment removed for export] *)
    change (lowbit 0) with 0. cbn [negb Z.eqb].
    apply (alloc_slot_ft (mstate * option (aptr * Z)) (CORE_POST st n L BL) FUEL sc [] st L BL LS n); try assumption.
    + unfold FUEL. cbn. lia.
    + apply NoDup_nil_2.
    + (intros st1 idx L1 LS1; (first [ intro dR_12; dand4 dR_12 as ACT LIVE GP1 RES | intros (ACT & LIVE & GP1 & RES) ])). destruct RES as [(-> & INV1 & TF1)|(g & bg & ai & Hidx & HA1 & Hg & SCg & FIT1 & STR1 & INV1 & TF1)].
      * cbn [ftree ret]. unfold CORE_POST. cbn [fst snd]. split; [exact LIVE|]. split; [exact GP1|]. exists LS1. exact INV1.
      * replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia). rewrite HA1. cbn [ftree ret]. unfold CORE_POST. cbn [fst snd]. split; [exact LIVE|]. split; [exact GP1|].
        exists LS1, bg. split; [exists ai; exact Hg|]. split; [exact Hidx|]. split; [exact INV1|]. split; [exact FIT1|]. split; [exact TF1|].
        pose proof (small_stride _ _ _ _ _ bg g INV1 (ex_intro _ ai Hg) ltac:(lia)). unfold IB. lia.
Qed.

(* [comment removed for export] *)
Lemma malloc_big_ft : MMAP_THRESHOLD <= n -> size_overflows n = false ->
  ftree L
    (SVis (EMmap 0 (n + IB + UNIT) PROT_RW (MAP_PRIVATE + MAP_ANON)) (fun r =>
      if negb (mmap_answer_ok (live_ranges st) (n + IB + UNIT) r) then bad_answer (ret (st, @None (aptr * Z))) else
      if is_err r then ret (st, None) else
      let '(st1, rid) := new_region RKGroup r (n + IB + UNIT) st in
      let st2 := step_seq st1 in
      alloc_meta st2 (fun st3 go =>
        match go with
        | None => SVis (EMunmap r (n + IB + UNIT)) (fun ru => if munmap_answer_ok ru then ret (drop_region rid st3, @None (aptr * Z)) else bad_answer (ret (st, @None (aptr * Z))))
        | Some g =>
          let st4 := upd_meta g (fun mr => m_set_freed 0 (m_set_avail 0 (m_set_maplen ((n + IB + UNIT + 4095) / 4096)
                       (m_set_sizeclass 63 (m_set_freeable 1 (m_set_last_idx 0 (m_set_mem (Some (rid, 0)) mr))))))) st3 in
          let st5 := put_group (rid, 0) (Some g) (group_active_idx st4 (rid, 0)) (lh_hdr full_lay st4 (rid, 0)) in
          let st6 := add_slots g (rid, 0) (get_stride (get_meta_rec st5 g)) 1 st5 in
          let st7 := upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) st6 in
          ret (st7, Some (g, 0))
        end) (ret (st, @None (aptr * Z)))))
    (CORE_POST st n L BL).
Proof.
  intros Hbig Hov. unfold size_overflows in Hov. apply Z.leb_gt in Hov.
  set (needed := n + IB + UNIT).
  assert (HN : 131072 <= needed < 2 ^ 63 - 4000) by (unfold needed, IB, UNIT, MMAP_THRESHOLD in *; lia).
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  apply ftree_vis; [reflexivity| reflexivity| | |].
  - cbn. left. split; [exact (brk_quiet_of _ _ _ IR)|]. split; [reflexivity|]. split; [reflexivity|]. split; [right; reflexivity|].
    unfold LEN_MAX. clear -HN. lia.
  - intros a Ha. cbn [answer_ok] in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn iota in Ha.
    change (event_post L (EMmap 0 needed PROT_RW (MAP_PRIVATE + MAP_ANON)) a)
      with (if Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0 then if is_err a then L else if PROT_RW =? PROT_NONE then KInv.set_metas ((a, needed, 0) :: ld_metas L) L else KInv.set_groups ((a, needed) :: ld_groups L) L else set_brkph BPLive (set_brkreg (Some (0, 2 * PGSZ)) L)).
    change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true. change (PROT_RW =? PROT_NONE) with false. cbn iota.
    rewrite (mmap_answer_ok_eq _ _ _ IR) in Ha. rewrite Ha. cbn [negb].
    destruct (is_err a) eqn:ER.
    + cbn [ftree ret]. unfold CORE_POST. cbn [fst snd]. split; [reflexivity|]. split; [apply GP_refl|]. exists LS. exact INV.
    + destruct (new_region RKGroup a needed st) as [st1 rid] eqn:EN.
      assert (Erid : rid = s_next_rid st) by (unfold new_region in EN; inversion EN; reflexivity).
      assert (Est1 : st1 = fst (new_region RKGroup a needed st)) by (rewrite EN; reflexivity).
      pose proof (INVL_new_group_region x0 st L BL LS a needed INV eq_refl Ha ER ltac:(unfold LEN_MAX; clear -HN; lia)) as INV1.
      rewrite <- Est1, <- Erid in INV1.
      set (L1 := KInv.set_groups ((a, needed) :: ld_groups L) L) in *.
      assert (Hr1 : s_regions st1 !! rid = Some (mkRegion RKGroup a needed)) by (rewrite Est1, ng_lookup, Erid, N.eqb_refl; reflexivity).
      assert (NS1 : s_shadow st1 !! rid = None).
      { rewrite Est1, Erid. change (s_shadow (fst (new_region RKGroup a needed st))) with (s_shadow st). exact (shadow_next_rid_none _ _ _ _ _ INV). }
      assert (TF1 : TF0 (step_seq st1)).
      { (first [ pose proof ((step_seq_fields st1)) as dR_6; dand3 dR_6 as A B _ | destruct (step_seq_fields st1) as (A & B & _) ]). apply (TF0_ctrl st1); [exact A| exact B|]. apply (TF0_ctrl st); [rewrite Est1; reflexivity| rewrite Est1; reflexivity| exact TF]. }
      pose proof (INVL_step_seq _ _ _ _ _ INV1) as INV2.
      (first [ pose proof ((step_seq_fields st1)) as dR_7; dand6 dR_7 as SS1 SS2 SS3 SS4 SS5 _ | destruct (step_seq_fields st1) as (SS1 & SS2 & SS3 & SS4 & SS5 & _) ]).
      eapply (alloc_meta_ft (mstate * option (aptr * Z)) BL (CORE_POST st n L BL) _ _ (xorph x0 (Some rid)) (step_seq st1) L1);
        [ | | exact INV2| apply amf_refl| apply lf_refl].
      * (* [comment removed for export] *)
        intros st3 L3 LS3 INV3 AF LF. cbn beta iota.
        apply ftree_vis; [reflexivity| reflexivity| | |].
        -- cbn. split; [exact (brk_quiet_of _ _ _ (proj1 INV3))|]. exists needed. rewrite (lf_groups _ _ LF). split; [left; reflexivity| left; reflexivity].
        -- intros ru Hru. cbn [answer_ok] in Hru. rewrite Hru. cbn [ftree ret]. unfold CORE_POST. cbn [fst snd event_post].
           split; [cbn; rewrite (lf_live _ _ LF); reflexivity|].
           split.
           { split.
             - intros q rq Hq Kq. unfold drop_region. rewrite s_regions_set_shadow, s_regions_set_regions. rewrite lookup_delete_ne.
               + apply (amf_regions _ _ AF); [| exact Kq]. rewrite SS4, Est1. apply (ng_keep _ _ _ _ _ _ _ INV). exact Hq.
               + intros ->. pose proof (ir_ids _ _ _ (proj1 INV) _ _ Hq). rewrite Erid in H. lia.
             - transitivity (s_secret st3); [reflexivity|]. rewrite (amf_ssec _ _ AF). unfold step_seq. destruct (c_seq _ =? 255); rewrite Est1; reflexivity. }
           exists LS3.
           pose proof (INVL_drop_orph (xorph x0 (Some rid)) st3 L3 BL LS3 rid (mkRegion RKGroup a needed) INV3 eq_refl
                         (amf_regions _ _ AF rid _ ltac:(rewrite SS4; exact Hr1) eq_refl)) as INV4.
           cbn [r_base xorph x_idle x_zomb x_pend x_fresh x_orph] in INV4. exact INV4.
        -- intros ru Hru. cbn [answer_ok] in Hru. rewrite Hru. exact I.
      * (* [comment removed for export] *)
        intros st3 L3 LS3 g INV3 NIg AF LF. cbn beta iota zeta.
        change (lh_hdr full_lay) with (fun s b => hdr_havoc b s). cbn beta.
        assert (Hr3 : s_regions st3 !! rid = Some (mkRegion RKGroup a needed)) by (apply (amf_regions _ _ AF); [rewrite SS4; exact Hr1| reflexivity]).
        assert (NS3 : s_shadow st3 !! rid = None) by (rewrite (amf_shadow _ _ AF), SS1; exact NS1).
        assert (TF3 : TF0 st3) by (apply (TF0_ctrl (step_seq st1)); [exact (amf_shadow _ _ AF)| exact (amf_tick _ _ AF)| exact TF1]).
        cbn [xidle xorph x_idle x_zomb x_pend x_orph x_fresh x0] in INV3.
        (first [ pose proof ((create63_ok st3 L3 BL LS3 g rid (mkRegion RKGroup a needed) needed INV3 Hr3 eq_refl eq_refl NS3 ltac:(lia) TF3)) as dR_8; dand9 dR_8 as INV6 TF6 MR6 GR6 CTX6 TK6 RG6 STR6 RU6 | destruct (create63_ok st3 L3 BL LS3 g rid (mkRegion RKGroup a needed) needed INV3 Hr3 eq_refl eq_refl NS3 ltac:(lia) TF3)
          as (INV6 & TF6 & MR6 & GR6 & CTX6 & TK6 & RG6 & STR6 & RU6) ]).
        match goal with |- ftree _ (ret (upd_ctx ?f ?s6, _)) _ => set (st6 := s6) in * end.
        cbn [ftree ret]. unfold CORE_POST. cbn [fst snd]. split; [cbn; exact (lf_live _ _ LF)|].
        split.
        { split.
          - intros q rq Hq Kq. rewrite s_regions_upd_ctx, RG6. apply (amf_regions _ _ AF); [| exact Kq]. rewrite SS4, Est1. apply (ng_keep _ _ _ _ _ _ _ INV). exact Hq.
          - rewrite s_secret_upd_ctx. transitivity (s_secret st3); [reflexivity|]. rewrite (amf_ssec _ _ AF). unfold step_seq. destruct (c_seq _ =? 255); rewrite Est1; reflexivity. }
        pose proof (INVL_mmap_counter _ _ _ _ _ INV6) as INV7.
        set (st7 := upd_ctx _ st6) in *.
        assert (MR7 : MR st7 g = MR st6 g) by reflexivity.
        exists LS3, (rid, 0). rewrite MR7, MR6. cbn [m_last_idx].
        assert (SS0 : sstart (mkMeta None None (Some (rid, 0)) 0 0 0 1 63 ((needed + 4095) / 4096)) 0 = 16).
        { unfold sstart, gbase. cbn -[Z.mul Z.add get_stride]. unfold UNIT. lia. }
        rewrite SS0. change (fst (rid, 0)) with rid.
        split; [exists 0; exact GR6|]. split; [lia|]. split; [exact INV7|].
        rewrite STR6. pose proof (round_up_pg_spec needed) as [RU _]. unfold needed, IB, UNIT in *.
        split; [lia|]. split; [apply TF0_TF2; apply (TF0_ctrl st6); [reflexivity| reflexivity| exact TF6]| lia].
  - intros a Ha. cbn [answer_ok] in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn iota in Ha.
    rewrite (mmap_answer_ok_eq _ _ _ IR) in Ha. rewrite Ha. exact I.
Qed.

Theorem malloc_core_ft : ftree L (malloc_core full_lay st n) (CORE_POST st n L BL).
Proof.
  unfold malloc_core.
  destruct (size_overflows n) eqn:Hov.
  - cbn [ftree ret]. unfold CORE_POST. cbn [fst snd]. split; [reflexivity|]. split; [apply GP_refl|]. exists LS. exact INV.
  - destruct (Z.leb_spec MMAP_THRESHOLD n) as [Hbig|Hsmall].
    + exact (malloc_big_ft Hbig Hov).
    + exact (malloc_small_ft Hsmall).
Qed.
End CORE.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section CEIL2.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Theorem malloc_INVL st L BL LS n :
  INVL x0 st L BL LS -> 0 <= n ->
  ftree L (malloc st n) (fun L' r =>
    ld_live L' = ld_live L /\ GP st (fst r) /\
    match snd r with
    | None => exists LS', INVL x0 (fst r) L' BL LS'
    | Some p => exists c off LS', p = aadd c (UNIT * off) /\ 0 <= off <= 255
        /\ INVL x0 (fst r) L' (((c, off), n) :: BL) LS' /\ ~ In c (map bslot BL)
    end).
Proof.
  intros INV Hn. unfold malloc.
  set (st0 := set_tick (N.succ (s_tick st)) st).
  assert (INV0 : INVL x0 st0 L BL LS) by (apply INVL_set_tick; [cbn; lia| exact INV]).
  assert (TF0' : TF0 st0) by (apply TF0_tick_new; [exact (TKS_of _ _ _ _ _ INV)| cbn; lia]).
  eapply ftree_bind; [exact (malloc_core_ft st0 L BL LS n INV0 TF0' Hn)|].
  (intros L1 [st1 r]; (first [ intro dR_13; dand3 dR_13 as LIVE GP1 RES | intros (LIVE & GP1 & RES) ])). cbn [fst snd] in RES, GP1 |- *.
  assert (GP0 : GP st st1) by (eapply GP_trans; [apply GP_eq; reflexivity| exact GP1]).
  destruct r as [[g idx]|].
  - (first [ dand8 RES as LS1 bg Hg Hidx INV1 FIT TF1 RES32 | destruct RES as (LS1 & bg & Hg & Hidx & INV1 & FIT & TF1 & RES32) ]).
    apply (enframe_ft (xpend x0 (Some (fst bg, sstart (MR st1 g) idx))) st1 L1 BL LS1 g bg idx n INV1 Hg Hidx eq_refl Hn FIT TF1 RES32).
    intros off st' Ho Hf INV' CE TK. cbn [fst snd]. split; [exact LIVE|]. split; [eapply GP_trans; [exact GP0| apply GP_eq; [exact (ce_regions _ _ CE)| exact (ce_secret _ _ CE)]]|].
    exists (fst bg, sstart (MR st1 g) idx), off, LS1. split; [reflexivity|]. split; [exact Ho|]. split; [exact INV'|].
    pose proof (is_nodup _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV'))))))) as ND. cbn [map bslot fst] in ND.
    apply NoDup_cons in ND as [NI _]. intros Hin. apply NI. apply list_elem_of_In. exact Hin.
  - destruct RES as (LS1 & INV1). cbn [ftree ret fst snd]. split; [exact LIVE|]. split; [exact GP0|]. exists LS1. exact INV1.
Qed.

End CEIL2.
End MI_Wkfj.


Module MI_Sim.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require STree Malloc Mall7vg KInv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_List.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Inv MI_Kit MI_Arith MI_Geom MI_List MI_Ext MI_S421.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_WFree.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_WFree MI_Ws22 MI_WNtf2 MI_Wp9i MI_Cnt.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.STree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malloc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall7vg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_List.MI_Tree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Kit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Arith OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Geom OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_List OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ext OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_S421 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres2.MI_Pres1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WFree.MI_Read OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WFree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ws22 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WNtf2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Wp9i OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Cnt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_TF2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_WSlot OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_Wvdb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_Wdy2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_Wj0q OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_W9kq OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_Wkfj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.  (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Set Implicit Arguments.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint lafter {R} (L : mled) (t : M R) (ans : list Z) {struct t} : mled :=
  match t, ans with
  | SRet _, _ => L
  | SVis (EUndef _) _, _ => L
  | SVis e k, a :: ans' => lafter (event_post L e a) (k a) ans'
  | SVis _ _, [] => L
  end.

(* [comment removed for export] *)
Fixpoint followk {R} (t : M R) (ans : list Z) {struct t} : option (R * list Z) :=
  match t, ans with
  | SRet r, _ => Some (r, ans)
  | SVis (EUndef _) _, _ => None
  | SVis _ k, a :: ans' => followk (k a) ans'
  | SVis _ _, [] => None
  end.

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma ptree_follow_lafter {R} : forall (t : M R) L Post ans r,
  ptree L t Post -> follow t ans = Some r -> cpath L t (lafter L t ans) r /\ Post (lafter L t ans) r.
Proof.
  induction t as [r0|e k IH]; intros L Post ans r H Hf; cbn [ptree follow lafter] in *.
  - inversion Hf; subst. split; [constructor| exact H].
  - destruct e; try (destruct H; fail); try contradiction.
    all: destruct H as [He Hk]; destruct ans as [|a ans']; [discriminate|];
      specialize (Hk a); case_ans;
      [ destruct (IH a _ _ _ _ Hk Hf) as [Hp HP]; split; [econstructor; eauto| exact HP]
      | (first [ pose proof ((rejects_inv _ Hk)) as dR_1; dex2 dR_1 as w k'; rename dR_1 into E | pose proof ((rejects_inv _ Hk)) as dR_1; dand3 dR_1 as w k' E | destruct (rejects_inv _ Hk) as (w & k' & E) ]); rewrite E in Hf; cbn in Hf; discriminate ].
Qed.

Lemma followk_follow {R} : forall (t : M R) ans x rest, followk t ans = Some (x, rest) -> follow t ans = Some x.
Proof.
  induction t as [r0|e k IH]; intros ans x rest H; cbn [followk follow] in *.
  - inversion H. reflexivity.
  - destruct e; try discriminate; destruct ans as [|a ans']; try discriminate; eapply IH; exact H.
Qed.

Lemma follow_sbind {R S} : forall (t : M R) (k : R -> M S) ans,
  follow (sbind t k) ans = match followk t ans with Some (x, rest) => follow (k x) rest | None => None end.
Proof.
  induction t as [r0|e k0 IH]; intros k ans; cbn [sbind followk follow]; [reflexivity|].
  destruct e; destruct ans as [|a ans']; cbn [follow]; try reflexivity; apply IH.
Qed.

Lemma lafter_sbind {R S} : forall (t : M R) (k : R -> M S) L ans x rest,
  followk t ans = Some (x, rest) -> lafter L (sbind t k) ans = lafter (lafter L t ans) (k x) rest.
Proof.
  induction t as [r0|e k0 IH]; intros k L ans x rest H; cbn [sbind followk lafter] in *.
  - inversion H. reflexivity.
  - destruct e; try discriminate; destruct ans as [|a ans']; try discriminate; cbn [lafter]; apply IH; exact H.
Qed.

Lemma strel_followk {R1 R2} (RR : R1 -> R2 -> Prop) (t1 : M R1) (t2 : M R2) :
  strel RR t1 t2 -> forall ans x1 rest, followk t1 ans = Some (x1, rest) ->
  exists x2, followk t2 ans = Some (x2, rest) /\ RR x1 x2.
Proof.
  induction 1 as [r1 r2 Hr|e k1 k2 Hk IH]; intros ans x1 rest H; cbn [followk] in *.
  - inversion H. subst. eauto.
  - destruct e; try discriminate; destruct ans as [|a ans']; try discriminate; eapply IH; exact H.
Qed.

Lemma strel_lafter {R1 R2} (RR : R1 -> R2 -> Prop) (t1 : M R1) (t2 : M R2) :
  strel RR t1 t2 -> forall L ans, lafter L t1 ans = lafter L t2 ans.
Proof.
  induction 1 as [r1 r2 Hr|e k1 k2 Hk IH]; intros L ans; cbn [lafter]; [reflexivity|].
  destruct e; destruct ans; try reflexivity; apply IH.
Qed.

Lemma strel_follow_some {R1 R2} (RR : R1 -> R2 -> Prop) (t1 : M R1) (t2 : M R2) ans r1 :
  strel RR t1 t2 -> follow t1 ans = Some r1 -> exists r2, follow t2 ans = Some r2 /\ RR r1 r2.
Proof.
  intros H Hf. pose proof (strel_follow H ans) as F. rewrite Hf in F.
  destruct (follow t2 ans) as [r2|]; [exists r2; auto| destruct F].
Qed.

Lemma steq_follow {R} (t1 t2 : M R) ans : steq t1 t2 -> follow t1 ans = follow t2 ans.
Proof.
  intros H. apply strel_eq_steq in H. pose proof (strel_follow H ans) as F.
  destruct (follow t1 ans), (follow t2 ans); cbn in F; try reflexivity; [congruence| destruct F| destruct F].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma ptree_followk {R} (t : M R) L Post ans x rest :
  ptree L t Post -> followk t ans = Some (x, rest) -> Post (lafter L t ans) x.
Proof. intros HP Hf. exact (proj2 (ptree_follow_lafter t L Post ans HP (followk_follow _ _ Hf))). Qed.

(* [comment removed for export] *)
Lemma event_post_live L e z : ld_live (event_post L e z) = ld_live L.
Proof.
  destruct e as [rq|a len prot flags|a len|a len prot|p c h|w]; cbn; try reflexivity.
  - destruct (rq =? 0); [reflexivity|]. destruct (z =? rq); [| reflexivity]. destruct (ld_brk L); try reflexivity; destruct (ld_brkreg L) as [[b l]|]; reflexivity.
  - destruct (Z.land flags MAP_FIXED =? 0); [| reflexivity]. destruct (is_err z); [reflexivity|]. destruct (prot =? PROT_NONE); reflexivity.
  - destruct ((z =? 0) || (z =? TWO64 - ENOSYS)); reflexivity.
Qed.

Lemma cpath_live {R} L (t : M R) L' r : cpath L t L' r -> ld_live L' = ld_live L.
Proof. induction 1; [reflexivity|]. rewrite IHcpath. apply event_post_live. Qed.

End CEIL.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Unset Implicit Arguments.

Section SIM.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
Context {O : Type} (pans : O -> aptr -> Z -> Z -> Z) (pupd : O -> ev -> Z -> O).
Hypothesis Hpans : forall o p c h, 0 <= pans o p c h < 256.
Local Notation PRUN := (prun pans pupd).

Lemma prun_ret {R} o (x : R) : PRUN o (SRet x) = SRet (o, x).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma free_prefix st L BL LS c off n :
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
  (first [ pose proof ((block_facts x0 st L BL LS INV c off n Hk)) as dR_2; dex7 dR_2 as m bm i ai a ar ka; rename dR_2 into BF | pose proof ((block_facts x0 st L BL LS INV c off n Hk)) as dR_2; dand8 dR_2 as m bm i ai a ar ka BF | destruct (block_facts x0 st L BL LS INV c off n Hk) as (m & bm & i & ai & a & ar & ka & BF) ]).
  (first [ pose proof (INV) as dR_3; dand7 dR_3 as IR IA IM IL IG IS ISH | pose proof INV as (IR & IA & IM & IL & IG & IS & ISH) ]).
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
      assert (HP : P (fst bm)) by ((first [ pose proof ((ig_region _ _ _ IG _ _ Hm)) as dR_4; dex1 dR_4 as r; destruct dR_4 as [Hr Hkr] | pose proof ((ig_region _ _ _ IG _ _ Hm)) as dR_4; dand3 dR_4 as r Hr Hkr | destruct (ig_region _ _ _ IG _ _ Hm) as (r & Hr & Hkr) ]); exists r; auto).
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

(* [comment removed for export] *)
Theorem INVL_hdr_ok st L BL LS c off n :
  INVL x0 st L BL LS -> In ((c, off), n) BL -> hdr_ok pans pupd st (aadd c (UNIT * off)) c.
Proof.
  intros INV Hk. (first [ pose proof ((free_prefix st L BL LS c off n INV Hk)) as dR_5; dex3 dR_5 as m bm i; dand12 dR_5 as FH CE1 STR1 Hs INV1 Hm1 Hi Ec NA NF SC AGREE | pose proof ((free_prefix st L BL LS c off n INV Hk)) as dR_5; dand15 dR_5 as m bm i FH CE1 STR1 Hs INV1 Hm1 Hi Ec NA NF SC AGREE | destruct (free_prefix st L BL LS c off n INV Hk) as (m & bm & i & FH & CE1 & STR1 & Hs & INV1 & Hm1 & Hi & Ec & NA & NF & SC & AGREE) ]).
  cbn zeta in FH, AGREE, STR1.
  eexists _, m, i. split; [| split; [exact STR1| split; [exact Hs|]]].
  - intros o. rewrite FH. reflexivity.
  - intros o. rewrite AGREE, <- STR1. apply free_tail_slots_control.
Qed.

(* [comment removed for export] *)
Theorem free_leaf_facts st L BL LS c off n o ans o' st' :
  INVL x0 st L BL LS -> In ((c, off), n) BL ->
  follow (PRUN o (free st (Some (aadd c (UNIT * off))))) ans = Some (o', st') ->
  (forall rid r, s_regions st' !! rid = Some r -> s_regions st !! rid = Some r) /\ s_secret st' = s_secret st.
Proof.
  intros INV Hk Hf. (first [ pose proof ((free_prefix st L BL LS c off n INV Hk)) as dR_6; dex3 dR_6 as m bm i; dand12 dR_6 as FH CE1 STR1 Hs INV1 Hm1 Hi Ec NA NF SC AGREE | pose proof ((free_prefix st L BL LS c off n INV Hk)) as dR_6; dand15 dR_6 as m bm i FH CE1 STR1 Hs INV1 Hm1 Hi Ec NA NF SC AGREE | destruct (free_prefix st L BL LS c off n INV Hk) as (m & bm & i & FH & CE1 & STR1 & Hs & INV1 & Hm1 & Hi & Ec & NA & NF & SC & AGREE) ]).
  cbn zeta in *.
  set (st1 := wr16 (aadd (aadd c (UNIT * off)) (-2)) 0 (wr8 (aadd (aadd c (UNIT * off)) (-3)) 255 st)) in *.
  unfold free in Hf. rewrite FH in Hf. cbn [sbind] in Hf. unfold free_tail in Hf.
  rewrite (guard_true 60) in Hf by (unfold testbit; rewrite Z.lor_spec; fold (MR st1 m); unfold tbit in NA, NF; rewrite NA, NF; reflexivity).
  fold (MR st1 m) in Hf.
  pose proof (ce_regions _ _ CE1) as RG1. pose proof (ce_secret _ _ CE1) as SE1.
  destruct (negb ((m_freed (MR st1 m) =? 0) || (Z.lor (m_freed (MR st1 m)) (m_avail (MR st1 m)) + bit i =? mask_upto (m_last_idx (MR st1 m))))).
  - rewrite prun_ret in Hf. cbn [follow] in Hf. inversion Hf. subst st'. split; [intros rid r H; rewrite <- RG1; exact H| rewrite <- SE1; reflexivity].
  - (first [ pose proof ((ntf_spec2 mstate FUEL dec_hdr dec_hdr (dec_hdr_ok _) (dec_hdr_ok _) (xpend x0 (Some c)) st1 L (bl_remove c BL) LS m bm i
                (fun st2 mi => match mi with
                               | Some (base, len) => if negb (len =? 0)
                                   then SVis (EMunmap (conc st2 base) len) (fun ru => if munmap_answer_ok ru then ret (drop_region (fst base) st2) else bad_answer (ret st1))
                                   else ret st2
                               | None => ret st2 end) (ret st1) INV1 Hm1 Hi ltac:(cbn; rewrite Ec; reflexivity) eq_refl eq_refl ltac:(unfold FUEL; lia) ltac:(unfold FUEL; lia))) as dR_7; dex2 dR_7 as st2 mi; dand5 dR_7 as LS2 EQ _ [RG2 SE2] _ | pose proof ((ntf_spec2 mstate FUEL dec_hdr dec_hdr (dec_hdr_ok _) (dec_hdr_ok _) (xpend x0 (Some c)) st1 L (bl_remove c BL) LS m bm i
                (fun st2 mi => match mi with
                               | Some (base, len) => if negb (len =? 0)
                                   then SVis (EMunmap (conc st2 base) len) (fun ru => if munmap_answer_ok ru then ret (drop_region (fst base) st2) else bad_answer (ret st1))
                                   else ret st2
                               | None => ret st2 end) (ret st1) INV1 Hm1 Hi ltac:(cbn; rewrite Ec; reflexivity) eq_refl eq_refl ltac:(unfold FUEL; lia) ltac:(unfold FUEL; lia))) as dR_7; dand7 dR_7 as st2 mi LS2 EQ _ [RG2 SE2] _ | destruct (ntf_spec2 mstate FUEL dec_hdr dec_hdr (dec_hdr_ok _) (dec_hdr_ok _) (xpend x0 (Some c)) st1 L (bl_remove c BL) LS m bm i
                (fun st2 mi => match mi with
                               | Some (base, len) => if negb (len =? 0)
                                   then SVis (EMunmap (conc st2 base) len) (fun ru => if munmap_answer_ok ru then ret (drop_region (fst base) st2) else bad_answer (ret st1))
                                   else ret st2
                               | None => ret st2 end) (ret st1) INV1 Hm1 Hi ltac:(cbn; rewrite Ec; reflexivity) eq_refl eq_refl ltac:(unfold FUEL; lia) ltac:(unfold FUEL; lia))
      as (st2 & mi & LS2 & EQ & _ & [RG2 SE2] & _) ]).
    rewrite EQ in Hf.
    assert (K2 : (forall rid r, s_regions st2 !! rid = Some r -> s_regions st !! rid = Some r) /\ s_secret st2 = s_secret st).
    { split; [intros rid r H; rewrite <- RG1, <- RG2; exact H| rewrite <- SE1, <- SE2; reflexivity]. }
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

(* [comment removed for export] *)
Theorem free_sim st L BL LS c off n o ans o' st' :
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
  (first [ pose proof ((strel_follow_some ans REL Hf)) as dR_8; dex1 dR_8 as cs'; destruct dR_8 as [Hf2 FR] | pose proof ((strel_follow_some ans REL Hf)) as dR_8; dand3 dR_8 as cs' Hf2 FR | destruct (strel_follow_some ans REL Hf) as (cs' & Hf2 & FR) ]). unfold FREL in FR. cbn in FR. subst cs'.
  split; [exact Hf2|].
  pose proof (ptree_strel REL L _ (fun _ _ => True) ltac:(intros; exact I) PT) as PT2.
  destruct (ptree_follow_lafter _ L _ ans PT2 Hf2) as [CP _].
  split; [exact CP|]. split; [exact (cpath_live CP)|].
  destruct (ptree_follow_lafter _ L _ ans PT Hf) as [_ POST]. cbn in POST.
  rewrite <- (strel_lafter REL L ans). exact POST.
Qed.

(* [comment removed for export] *)
Theorem malloc_sim st L BL LS n o ans o' st' r :
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
  (* [comment removed for export] *)
  pose proof (ftree_prun pans pupd Hpans (malloc_core full_lay st0 n) L _ o (malloc_core_ft st0 L BL LS n INV0 TF0' Hn)) as PTC.
  pose proof (ptree_followk _ L _ ans PTC FK) as CP. cbn [snd fst] in CP.
  set (L1 := lafter L (PRUN o (malloc_core full_lay st0 n)) ans) in *.
  (first [ dand3 CP as LIVE1 GP1 CP | destruct CP as (LIVE1 & GP1 & CP) ]).
  (* [comment removed for export] *)
  pose proof (malloc_core_ctrl pans pupd n o st0 (strip st) ltac:(unfold st0; rewrite strip_set_tick; reflexivity)) as RELC.
  (first [ pose proof ((strel_followk RELC ans FK)) as dR_10; dand3 dR_10 as [cst1 rg'] FK2 [CR1 CR2] | destruct (strel_followk RELC ans FK) as ([cst1 rg'] & FK2 & [CR1 CR2]) ]). cbn in CR1, CR2. subst rg'.
  assert (FT : follow (cmalloc (strip st) n) ans
               = Some (strip cst1, match rg with Some (g, idx) => Some (slot_of cst1 g idx) | None => None end)).
  { unfold cmalloc. rewrite follow_sbind, FK2. reflexivity. }
  assert (LT : lafter L (cmalloc (strip st) n) ans = L1).
  { unfold cmalloc. rewrite (lafter_sbind _ _ L ans FK2). cbn [lafter]. unfold L1. symmetry. apply (strel_lafter RELC). }
  rewrite LT.
  (* [comment removed for export] *)
  assert (PT2 : ptree L (cmalloc (strip st) n) (fun _ _ => True)).
  { eapply (ptree_strel (malloc_control pans pupd Hpans st n o)); [intros; exact I|].
    eapply ptree_mono; [intros; exact I|]. exact (ftree_prun pans pupd Hpans (malloc st n) L _ o (malloc_INVL st L BL LS n INV Hn)). }
  assert (SS1 : strip cst1 = strip st1) by (rewrite <- CR1; apply strip_strip).
  assert (GP0 : GP st st1) by (eapply GP_trans; [apply GP_eq; reflexivity| exact GP1]).
  destruct rg as [[g idx]|].
  - (first [ dand8 CP as LS1 bg Hg Hidx INV1 FIT TF1 RES32 | destruct CP as (LS1 & bg & Hg & Hidx & INV1 & FIT & TF1 & RES32) ]).
    set (c0 := (fst bg, sstart (MR st1 g) idx)) in *.
    assert (Ec0 : slot_of cst1 g idx = c0).
    { rewrite <- CR1, slot_of_strip. unfold slot_of. exact (slot_start'_eq _ _ _ (proj1 (proj2 (proj2 INV1))) _ _ idx Hg). }
    rewrite Ec0 in FT.
    (* [comment removed for export] *)
    pose proof (enframe_ft (xpend x0 (Some c0)) st1 L1 BL LS1 g bg idx n INV1 Hg Hidx eq_refl Hn FIT TF1 RES32 (c_mmap_counter (ctx st1))
      (fun _ res => exists off, 0 <= off <= 255 /\ snd res = Some (aadd c0 (UNIT * off))
                      /\ INVL x0 (fst res) L1 (((c0, off), n) :: BL) LS1 /\ strip (fst res) = strip st1 /\ GP st1 (fst res))) as EF.
    cbn [fst snd] in EF.
    specialize (EF ltac:(intros off st2 Ho Hf2 INV2 CE TK; exists off; split; [exact Ho|]; split; [reflexivity|]; split; [exact INV2|];
                         split; [destruct CE as [C1 C2 C3 C4 C5 C6 C7 C8 C9]; unfold strip; rewrite C1, C2, C3, C4, C5, C6, C7, C8, C9; reflexivity| apply GP_eq; [exact (ce_regions _ _ CE)| exact (ce_secret _ _ CE)]])).
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
End SIM.
End MI_Sim.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.STree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malloc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall7vg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_List.MI_Tree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Kit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Geom OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_List OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ext OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ws22 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WNtf2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_TF2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_WSlot OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_Wkfj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_Sim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.  (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.

Module LB_Grant.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg KInv MI_Arith MI_Cnt.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Local Open Scope Z_scope.

Set Implicit Arguments.

Section LBCEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ACT (st st' : mstate) : Prop := forall c, active st' c = active st c.

Lemma ACT_refl st : ACT st st. Proof. intros c; reflexivity. Qed.
Lemma ACT_trans a b c : ACT a b -> ACT b c -> ACT a c.
Proof. intros H1 H2 x. rewrite H2. apply H1. Qed.

(* [comment removed for export] *)
Lemma s_ctx_upd_ctx f st : s_ctx (upd_ctx f st) = f (s_ctx st). Proof. reflexivity. Qed.
Lemma s_ctx_set_regions v st : s_ctx (set_regions v st) = s_ctx st. Proof. reflexivity. Qed.
Lemma s_ctx_set_shadow v st : s_ctx (set_shadow v st) = s_ctx st. Proof. reflexivity. Qed.
Lemma s_ctx_set_next_rid v st : s_ctx (set_next_rid v st) = s_ctx st. Proof. reflexivity. Qed.
Lemma s_ctx_set_metas v st : s_ctx (Malloc.set_metas v st) = s_ctx st. Proof. reflexivity. Qed.
Lemma s_ctx_set_areas v st : s_ctx (set_areas v st) = s_ctx st. Proof. reflexivity. Qed.
Lemma s_ctx_set_groups v st : s_ctx (Malloc.set_groups v st) = s_ctx st. Proof. reflexivity. Qed.
Lemma s_ctx_set_slots v st : s_ctx (set_slots v st) = s_ctx st. Proof. reflexivity. Qed.
Lemma s_ctx_set_tick v st : s_ctx (set_tick v st) = s_ctx st. Proof. reflexivity. Qed.
Lemma s_ctx_put_meta m r st : s_ctx (put_meta m r st) = s_ctx st. Proof. reflexivity. Qed.
Lemma s_ctx_upd_meta m f st : s_ctx (upd_meta m f st) = s_ctx st. Proof. reflexivity. Qed.
Lemma s_ctx_put_group g m ai st : s_ctx (put_group g m ai st) = s_ctx st. Proof. reflexivity. Qed.
Lemma s_ctx_set_group_active_idx g ai st : s_ctx (set_group_active_idx g ai st) = s_ctx st.
Proof. unfold set_group_active_idx. destruct (get_group st g); reflexivity. Qed.
Lemma s_ctx_upd_region rid f st : s_ctx (upd_region rid f st) = s_ctx st.
Proof. unfold upd_region. destruct (get_region st rid); reflexivity. Qed.
Lemma s_ctx_new_region k b l st : s_ctx (fst (new_region k b l st)) = s_ctx st. Proof. reflexivity. Qed.
Lemma s_ctx_drop_region rid st : s_ctx (drop_region rid st) = s_ctx st. Proof. reflexivity. Qed.
Lemma s_ctx_del_group g st : s_ctx (del_group g st) = s_ctx st. Proof. reflexivity. Qed.
Lemma s_ctx_add_slots m p s n st : s_ctx (add_slots m p s n st) = s_ctx st. Proof. reflexivity. Qed.
Lemma s_ctx_del_slots p s n st : s_ctx (del_slots p s n st) = s_ctx st. Proof. reflexivity. Qed.
Lemma s_ctx_strip st : s_ctx (strip st) = s_ctx st. Proof. reflexivity. Qed.

Lemma c_active_set_secret v c : c_active (set_secret v c) = c_active c. Proof. reflexivity. Qed.
Lemma c_active_set_init_done v c : c_active (set_init_done v c) = c_active c. Proof. reflexivity. Qed.
Lemma c_active_set_mmap_counter v c : c_active (set_mmap_counter v c) = c_active c. Proof. reflexivity. Qed.
Lemma c_active_set_free_meta_head v c : c_active (set_free_meta_head v c) = c_active c. Proof. reflexivity. Qed.
Lemma c_active_set_avail_meta v c : c_active (set_avail_meta v c) = c_active c. Proof. reflexivity. Qed.
Lemma c_active_set_avail_meta_count v c : c_active (set_avail_meta_count v c) = c_active c. Proof. reflexivity. Qed.
Lemma c_active_set_avail_meta_area_count v c : c_active (set_avail_meta_area_count v c) = c_active c. Proof. reflexivity. Qed.
Lemma c_active_set_meta_alloc_shift v c : c_active (set_meta_alloc_shift v c) = c_active c. Proof. reflexivity. Qed.
Lemma c_active_set_meta_area_head v c : c_active (set_meta_area_head v c) = c_active c. Proof. reflexivity. Qed.
Lemma c_active_set_meta_area_tail v c : c_active (set_meta_area_tail v c) = c_active c. Proof. reflexivity. Qed.
Lemma c_active_set_avail_meta_areas v c : c_active (set_avail_meta_areas v c) = c_active c. Proof. reflexivity. Qed.
Lemma c_active_set_usage_map v c : c_active (set_usage_map v c) = c_active c. Proof. reflexivity. Qed.
Lemma c_active_set_unmap_seq_map v c : c_active (set_unmap_seq_map v c) = c_active c. Proof. reflexivity. Qed.
Lemma c_active_set_bounces_map v c : c_active (set_bounces_map v c) = c_active c. Proof. reflexivity. Qed.
Lemma c_active_set_seq v c : c_active (set_seq v c) = c_active c. Proof. reflexivity. Qed.
Lemma c_active_set_brk v c : c_active (set_brk v c) = c_active c. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma c_active_step_seq st : c_active (s_ctx (step_seq st)) = c_active (s_ctx st).
Proof. unfold step_seq. destruct (c_seq (ctx st) =? 255); reflexivity. Qed.
Lemma c_active_record_seq sc st : c_active (s_ctx (record_seq sc st)) = c_active (s_ctx st).
Proof. unfold record_seq. destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma c_active_account_bounce sc st : c_active (s_ctx (account_bounce sc st)) = c_active (s_ctx st).
Proof.
  unfold account_bounce. destruct (sc_in_seq_range sc); [|reflexivity].
  destruct (negb _ && _); [|reflexivity]. destruct (_ <? 100); reflexivity.
Qed.
Lemma c_active_decay_bounces sc st : c_active (s_ctx (decay_bounces sc st)) = c_active (s_ctx st).
Proof. unfold decay_bounces. destruct (_ && _); reflexivity. Qed.
Lemma c_active_set_usage sc v st : c_active (s_ctx (set_usage sc v st)) = c_active (s_ctx st). Proof. reflexivity. Qed.
Lemma c_active_set_bounce i v st : c_active (s_ctx (set_bounce i v st)) = c_active (s_ctx st). Proof. reflexivity. Qed.
Lemma c_active_set_head_free v st : c_active (s_ctx (set_head LFree v st)) = c_active (s_ctx st). Proof. reflexivity. Qed.
Lemma c_active_dequeue_free m st : c_active (s_ctx (dequeue LFree m st)) = c_active (s_ctx st).
Proof.
  unfold dequeue. cbn zeta.
  destruct (negb (optr_eqb (m_next (get_meta_rec st m)) (Some m))).
  - destruct (m_prev (get_meta_rec st m)) as [pv|]; destruct (m_next (get_meta_rec st m)) as [nx|];
    destruct (optr_eqb _ (Some m)); reflexivity.
  - reflexivity.
Qed.

Hint Rewrite s_ctx_upd_ctx s_ctx_set_regions s_ctx_set_shadow s_ctx_set_next_rid s_ctx_set_metas s_ctx_set_areas
  s_ctx_set_groups s_ctx_set_slots s_ctx_set_tick s_ctx_put_meta s_ctx_upd_meta s_ctx_put_group s_ctx_set_group_active_idx
  s_ctx_upd_region s_ctx_new_region s_ctx_drop_region s_ctx_del_group s_ctx_add_slots s_ctx_del_slots s_ctx_strip
  c_active_set_secret c_active_set_init_done c_active_set_mmap_counter c_active_set_free_meta_head c_active_set_avail_meta
  c_active_set_avail_meta_count c_active_set_avail_meta_area_count c_active_set_meta_alloc_shift c_active_set_meta_area_head
  c_active_set_meta_area_tail c_active_set_avail_meta_areas c_active_set_usage_map c_active_set_unmap_seq_map
  c_active_set_bounces_map c_active_set_seq c_active_set_brk
  c_active_step_seq c_active_record_seq c_active_account_bounce c_active_decay_bounces c_active_set_usage c_active_set_bounce
  c_active_set_head_free c_active_dequeue_free : sctx.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac act_hit := first [
  match goal with |- context [c_active (s_ctx ?x)] => lazymatch x with
     | step_seq ?st => rewrite (c_active_step_seq st)
     | record_seq ?sc ?st => rewrite (c_active_record_seq sc st)
     | account_bounce ?sc ?st => rewrite (c_active_account_bounce sc st)
     | decay_bounces ?sc ?st => rewrite (c_active_decay_bounces sc st)
     | set_usage ?sc ?v ?st => rewrite (c_active_set_usage sc v st)
     | set_bounce ?i ?v ?st => rewrite (c_active_set_bounce i v st)
     | set_head LFree ?v ?st => rewrite (c_active_set_head_free v st)
     | dequeue LFree ?m ?st => rewrite (c_active_dequeue_free m st)
     end end
| match goal with |- context [s_ctx ?x] => lazymatch x with
     | upd_ctx ?f ?st => rewrite (s_ctx_upd_ctx f st)
     | set_regions ?v ?st => rewrite (s_ctx_set_regions v st)
     | set_shadow ?v ?st => rewrite (s_ctx_set_shadow v st)
     | set_next_rid ?v ?st => rewrite (s_ctx_set_next_rid v st)
     | Malloc.set_metas ?v ?st => rewrite (s_ctx_set_metas v st)
     | set_areas ?v ?st => rewrite (s_ctx_set_areas v st)
     | Malloc.set_groups ?v ?st => rewrite (s_ctx_set_groups v st)
     | set_slots ?v ?st => rewrite (s_ctx_set_slots v st)
     | set_tick ?v ?st => rewrite (s_ctx_set_tick v st)
     | put_meta ?m ?r ?st => rewrite (s_ctx_put_meta m r st)
     | upd_meta ?m ?f ?st => rewrite (s_ctx_upd_meta m f st)
     | put_group ?g ?m ?ai ?st => rewrite (s_ctx_put_group g m ai st)
     | set_group_active_idx ?g ?ai ?st => rewrite (s_ctx_set_group_active_idx g ai st)
     | upd_region ?rid ?f ?st => rewrite (s_ctx_upd_region rid f st)
     | fst (new_region ?k ?b ?l ?st) => rewrite (s_ctx_new_region k b l st)
     | drop_region ?rid ?st => rewrite (s_ctx_drop_region rid st)
     | del_group ?g ?st => rewrite (s_ctx_del_group g st)
     | add_slots ?m ?p ?s ?n ?st => rewrite (s_ctx_add_slots m p s n st)
     | del_slots ?p ?s ?n ?st => rewrite (s_ctx_del_slots p s n st)
     | strip ?st => rewrite (s_ctx_strip st)
     end end
| match goal with |- context [c_active ?x] => lazymatch x with
     | set_secret ?v ?c => rewrite (c_active_set_secret v c)
     | set_init_done ?v ?c => rewrite (c_active_set_init_done v c)
     | set_mmap_counter ?v ?c => rewrite (c_active_set_mmap_counter v c)
     | set_free_meta_head ?v ?c => rewrite (c_active_set_free_meta_head v c)
     | set_avail_meta ?v ?c => rewrite (c_active_set_avail_meta v c)
     | set_avail_meta_count ?v ?c => rewrite (c_active_set_avail_meta_count v c)
     | set_avail_meta_area_count ?v ?c => rewrite (c_active_set_avail_meta_area_count v c)
     | set_meta_alloc_shift ?v ?c => rewrite (c_active_set_meta_alloc_shift v c)
     | set_meta_area_head ?v ?c => rewrite (c_active_set_meta_area_head v c)
     | set_meta_area_tail ?v ?c => rewrite (c_active_set_meta_area_tail v c)
     | set_avail_meta_areas ?v ?c => rewrite (c_active_set_avail_meta_areas v c)
     | set_usage_map ?v ?c => rewrite (c_active_set_usage_map v c)
     | set_unmap_seq_map ?v ?c => rewrite (c_active_set_unmap_seq_map v c)
     | set_bounces_map ?v ?c => rewrite (c_active_set_bounces_map v c)
     | set_seq ?v ?c => rewrite (c_active_set_seq v c)
     | set_brk ?v ?c => rewrite (c_active_set_brk v c)
     end end ].
Ltac act := intros ?; unfold active, ctx; repeat (repeat act_hit; cbn beta); reflexivity.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section SPATH.
Variable C : ev -> Z -> Prop.

Inductive spath {R} : M R -> R -> Prop :=
| sp_ret r : spath (SRet r) r
| sp_vis e k z r : C e z -> spath (k z) r -> spath (SVis e k) r.

Hypothesis C_undef : forall w z, ~ C (EUndef w) z.

Lemma spath_ret_inv {R} (r r' : R) : spath (SRet r) r' -> r' = r.
Proof. intros H. inversion H; subst; reflexivity. Qed.

Lemma spath_vis_inv {R} e (k : Z -> M R) r : spath (SVis e k) r -> exists z, C e z /\ spath (k z) r.
Proof. intros H. inversion H; subst. eauto. Qed.

Lemma spath_undef {R} w (k : Z -> M R) r : spath (SVis (EUndef w) k) r -> False.
Proof. intros H. apply spath_vis_inv in H as (z & Hz & _). exact (C_undef Hz). Qed.

Lemma spath_bad {R} (bail : M R) r : spath (bad_answer bail) r -> False.
Proof. unfold bad_answer. apply spath_undef. Qed.

Lemma spath_guard {R} tag c (k bail : M R) r : spath (guard tag c k bail) r -> c = true /\ spath k r.
Proof. unfold guard. destruct c; [auto|]. intros H. destruct (spath_undef H). Qed.

Lemma spath_sbind {R S} (t : M R) (f : R -> M S) y :
  spath (sbind t f) y -> exists x, spath t x /\ spath (f x) y.
Proof.
  revert y. induction t as [r|e k IH]; intros y H; cbn in H.
  - exists r. split; [constructor| exact H].
  - apply spath_vis_inv in H as (z & Hz & Hp). destruct (IH z y Hp) as (x & H1 & H2).
    exists x. split; [econstructor; eauto| exact H2].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma spath_if_bad {R} (b : bool) (bail k : M R) r :
  spath (if b then bad_answer bail else k) r -> b = false /\ spath k r.
Proof. destruct b; [intros H; destruct (spath_bad H)| auto]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma spath_queue {R} h m st (k : mstate -> M R) bail r :
  spath (queue h m st k bail) r ->
  exists st', spath (k st') r /\ (h = LFree -> ACT st st').
Proof.
  unfold queue. intros H. apply spath_guard in H as [_ H]. apply spath_guard in H as [_ H].
  destruct (get_head st h) as [hd|].
  - destruct (m_prev (get_meta_rec st hd)) as [pv|]; eexists; (split; [exact H|]); intros ->; act.
  - eexists. split; [exact H|]. intros ->. act.
Qed.

(* [comment removed for export] *)

Lemma spath_activate_group {R} m st (k : mstate -> Z -> M R) bail r :
  spath (activate_group m st k bail) r -> exists st' mask, spath (k st' mask) r /\ ACT st st'.
Proof.
  unfold activate_group. intros H. apply spath_guard in H as [_ H]. do 2 eexists. split; [exact H|]. act.
Qed.

Lemma spath_am_take {R} st (k : mstate -> optr -> M R) bail r :
  spath (am_take st k bail) r -> exists st' m, spath (k st' (Some m)) r /\ ACT st st'.
Proof.
  unfold am_take. destruct (c_avail_meta (ctx st)) as [m|]; [| intros H; destruct (spath_undef H)].
  intros H. do 2 eexists. split; [exact H|]. act.
Qed.

Lemma spath_am_carve {R} st p (k : mstate -> optr -> M R) bail r :
  spath (am_carve st p k bail) r -> exists st' m, spath (k st' (Some m)) r /\ ACT st st'.
Proof.
  unfold am_carve. intros H. apply spath_am_take in H as (st' & m & H & HA). do 2 eexists. split; [exact H|].
  eapply ACT_trans; [| exact HA]. destruct (c_meta_area_tail _) as [tl|]; act.
Qed.

(* [comment removed for export] *)
Definition admits_fail : Prop :=
  (exists a l p fl z, C (EMmap a l p fl) z /\ Z.land fl MAP_FIXED = 0 /\ is_err z = true)
  \/ (exists a l p z, C (EMprotect a l p) z /\ (z =? 0) || (z =? TWO64 - ENOSYS) = false).

Definition AMres {R} (st : mstate) (k : mstate -> optr -> M R) (r : R) : Prop :=
  (exists st' m, ACT st st' /\ spath (k st' (Some m)) r)
  \/ (exists st', ACT st st' /\ spath (k st' None) r /\ admits_fail).

Lemma AMres_act {R} st0 st (k : mstate -> optr -> M R) r : ACT st0 st -> AMres st k r -> AMres st0 k r.
Proof.
  intros HA [(st' & m & HA' & H)|(st' & HA' & H & Hf)].
  - left. exists st', m. split; [eapply ACT_trans; eauto| exact H].
  - right. exists st'. split; [eapply ACT_trans; eauto| auto].
Qed.

Lemma spath_am_finish {R} st nu (k : mstate -> optr -> M R) bail r :
  spath (am_finish st nu k bail) r -> AMres st k r.
Proof.
  unfold am_finish. destruct (c_avail_meta_areas (ctx st)) as [p|]; [| intros H; destruct (spath_undef H)].
  cbn zeta. destruct (if negb (snd p mod PGSZ =? 0) then false else nu).
  - intros H. apply spath_vis_inv in H as (z & Hz & H). apply spath_if_bad in H as [Hok H].
    destruct ((z =? 0) || (z =? TWO64 - ENOSYS)) eqn:E.
    + apply spath_am_carve in H as (st' & m & H & HA). left. exists st', m. auto.
    + right. exists st. split; [apply ACT_refl|]. split; [exact H|]. right. do 4 eexists. eauto.
  - intros H. apply spath_am_carve in H as (st' & m & H & HA). left. exists st', m. auto.
Qed.

Lemma spath_am_after_brk {R} st nu (k : mstate -> optr -> M R) bail r :
  spath (am_after_brk st nu k bail) r -> AMres st k r.
Proof.
  unfold am_after_brk. destruct (c_avail_meta_area_count (ctx st) =? 0).
  - intros H. apply spath_vis_inv in H as (z & Hz & H). apply spath_if_bad in H as [Hok H].
    destruct (is_err z) eqn:E.
    + right. exists st. split; [apply ACT_refl|]. split; [exact H|]. left. do 5 eexists. split; [exact Hz|]. split; [reflexivity| exact E].
    + lazy beta iota zeta delta [new_region] in H. apply spath_am_finish in H. eapply AMres_act; [| exact H]. act.
  - apply spath_am_finish.
Qed.

Lemma spath_alloc_meta {R} st (k : mstate -> optr -> M R) bail r :
  spath (alloc_meta st k bail) r -> AMres st k r.
Proof.
  unfold alloc_meta.
  set (sti := if c_init_done (ctx st) =? 0 then upd_ctx (fun c => set_init_done 1 (set_secret (s_secret st) c)) st else st).
  assert (HAi : ACT st sti) by (subst sti; destruct (_ =? 0); act).
  destruct (c_free_meta_head (ctx sti)) as [m|].
  { intros H. left. exists (dequeue LFree m sti), m. split; [| exact H]. eapply ACT_trans; [exact HAi|]. act. }
  destruct (negb (c_avail_meta_count (ctx sti) =? 0)).
  { intros H. apply spath_am_take in H as (st' & m & H & HA). left. exists st', m. split; [eapply ACT_trans; eauto| exact H]. }
  cbn zeta. destruct (_ && _).
  - destruct (c_brk (ctx sti)) as [| |rid off].
    + intros H. apply spath_vis_inv in H as (cur & _ & H). apply spath_if_bad in H as [_ H].
      apply spath_vis_inv in H as (z & _ & H). apply spath_if_bad in H as [_ H].
      destruct (negb (z =? round_up_pg cur + 2 * PGSZ)).
      * apply spath_am_after_brk in H. eapply AMres_act; [| exact H]. eapply ACT_trans; [exact HAi|]. act.
      * apply spath_if_bad in H as [_ H]. apply spath_vis_inv in H as (zg & _ & H). apply spath_if_bad in H as [_ H].
        lazy beta iota zeta delta [new_region] in H. apply spath_am_after_brk in H. eapply AMres_act; [| exact H]. eapply ACT_trans; [exact HAi|]. act.
    + intros H. apply spath_am_after_brk in H. eapply AMres_act; [| exact H]. exact HAi.
    + intros H. apply spath_vis_inv in H as (z & _ & H). apply spath_if_bad in H as [_ H].
      destruct (negb (z =? conc sti (rid, off) + PGSZ)).
      * apply spath_am_after_brk in H. eapply AMres_act; [| exact H]. eapply ACT_trans; [exact HAi|]. act.
      * apply spath_if_bad in H as [_ H]. apply spath_am_after_brk in H. eapply AMres_act; [| exact H]. eapply ACT_trans; [exact HAi|]. act.
  - intros H. apply spath_am_after_brk in H. eapply AMres_act; [| exact H]. exact HAi.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition SELF0 (st : mstate) (sc : Z) : Prop :=
  exists m, active st sc = Some m /\ m_avail (get_meta_rec st m) = 0 /\ m_freed (get_meta_rec st m) = 0
            /\ m_next (get_meta_rec st m) = Some m.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma spath_try_avail {R} sc st (k : mstate -> Z -> M R) bail r :
  spath (try_avail sc st k bail) r -> exists st' first, spath (k st' first) r.
Proof.
  unfold try_avail. destruct (active st sc) as [m|]; [| intros H; eauto].
  destruct (negb (m_avail _ =? 0)); [intros H; unfold ta_fin in H; eauto|]. cbn zeta.
  lazymatch goal with |- spath ?t _ -> _ => lazymatch t with context [match ?x with _ => _ end] => destruct x as [[st1 m1]|] end end.
  2:{ destruct (m_freed _ =? 0); intros H; [eauto| destruct (spath_undef H)]. }
  lazymatch goal with |- spath ?t _ -> _ => lazymatch t with context [match ?x with _ => _ end] => destruct x as [[st2 m2] mask] end end.
  cbn zeta.
  lazymatch goal with |- spath ?t _ -> _ => lazymatch t with context [match ?x with _ => _ end] => destruct x as [st3 m3] end end.
  intros H. apply spath_activate_group in H as (st4 & mask4 & H & _). apply spath_guard in H as [_ H]. unfold ta_fin in H. eauto.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition stc24_f (k : Z) : bool := (0 <=? stc_k k) && (stc_k k <=? 24).
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma ctz32_nonneg m : 0 <= ctz32 m.
Proof. unfold ctz32. apply Z.log2_nonneg. Qed.

Lemma land_MAPF_FIXED : Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED = 0.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma alloc_slot_S {R} lay f st sc req (k : mstate -> Z -> M R) bail :
  alloc_slot lay (S f) st sc req k bail =
  try_avail sc st (fun st1 first =>
    if negb (first =? 0) then k st1 (ctz32 first) else
    alloc_group R lay (alloc_slot lay f) st1 sc req (fun st2 go =>
      match go with
      | None => k st2 (-1)
      | Some g =>
        let st3 := upd_meta g (fun r => m_set_avail (m_avail r - 1) r) st2 in
        queue (LActive sc) g st3 (fun st4 => k st4 0) bail
      end) bail) bail.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Tactic Notation "dmatch" hyp(H) "as" simple_intropattern(pat) :=
  lazymatch type of H with spath ?t _ =>
    lazymatch t with context [match ?x with _ => _ end] => destruct x as pat end end.

Section GRANT.
Hypothesis C_mmap_ok : forall a l p fl z, C (EMmap a l p fl) z -> Z.land fl MAP_FIXED = 0 -> is_err z = false.
Hypothesis C_mprot_ok : forall a l p z, C (EMprotect a l p) z -> (z =? 0) || (z =? TWO64 - ENOSYS) = true.

Lemma not_admits_fail : ~ admits_fail.
Proof.
  intros [(a & l & p & fl & z & Hc & Hf & He)|(a & l & p & z & Hc & He)].
  - rewrite (C_mmap_ok Hc Hf) in He. discriminate.
  - rewrite (C_mprot_ok Hc) in He. discriminate.
Qed.


Lemma ag_grant {R} lay rec st sc req (k : mstate -> optr -> M R) bail r :
  (forall st j rq (k' : mstate -> Z -> M R) r', spath (rec st j rq k' bail) r' -> exists st' idx, 0 <= idx /\ spath (k' st' idx) r') ->
  spath (alloc_group R lay rec st sc req k bail) r -> exists st' m, spath (k st' (Some m)) r.
Proof.
  intros Hrec H. unfold alloc_group in H. apply spath_alloc_meta in H.
  destruct H as [(st' & m & _ & H)|(st' & _ & _ & Hf)]; [| destruct (not_admits_fail Hf)].
  cbn beta iota in H. lazy zeta in H.
  match type of H with spath (if ?b then _ else _) _ => destruct b end.
  - (* [comment removed for export] *)
    dmatch H as [cnt1 needed1].
    apply spath_vis_inv in H as (z & Hz & H). apply spath_if_bad in H as [_ H].
    rewrite (C_mmap_ok Hz land_MAPF_FIXED) in H.
    dmatch H as [st2 rid]. lazy zeta in H. unfold ag_tail in H. lazy zeta in H. eauto.
  - (* [comment removed for export] *)
    apply Hrec in H as (st1 & idx & Hidx & H). rewrite (proj2 (Z.ltb_ge idx 0)) in H by lia.
    dmatch H as [g|]; [| destruct (spath_undef H)].
    lazy zeta in H. unfold ag_tail in H. lazy zeta in H. eauto.
Qed.

Lemma as_grant {R} lay f : forall st sc req (k : mstate -> Z -> M R) bail r,
  spath (alloc_slot lay f st sc req k bail) r -> exists st' idx, 0 <= idx /\ spath (k st' idx) r.
Proof.
  induction f as [|f IH]; intros st sc req k bail r H.
  - cbn in H. destruct (spath_undef H).
  - rewrite alloc_slot_S in H. apply spath_try_avail in H as (st1 & first & H).
    destruct (negb (first =? 0)).
    + exists st1, (ctz32 first). split; [apply ctz32_nonneg| exact H].
    + apply ag_grant in H as (st2 & g & H); [| intros; eapply IH; eauto].
      cbn beta iota zeta in H. apply spath_queue in H as (st4 & H & _). exists st4, 0. split; [lia| exact H].
Qed.

Lemma msc_grant {R} lay st n (k : mstate -> option (aptr * Z) -> M R) bail r :
  spath (malloc_small_ctrl lay st n k bail) r -> exists st' g idx, spath (k st' (Some (g, idx))) r.
Proof.
  intros H. unfold malloc_small_ctrl in H. lazy zeta in H.
  dmatch H as [gp|].
  - dmatch H as [|]; [eauto|].
    apply as_grant in H as (st1 & idx & Hidx & H). rewrite (proj2 (Z.ltb_ge idx 0)) in H by lia.
    dmatch H as [gp'|]; [eauto| destruct (spath_undef H)].
  - apply as_grant in H as (st1 & idx & Hidx & H). rewrite (proj2 (Z.ltb_ge idx 0)) in H by lia.
    dmatch H as [gp'|]; [eauto| destruct (spath_undef H)].
Qed.

Lemma mcore_grant lay st n st' r :
  size_overflows n = false -> spath (malloc_core lay st n) (st', r) -> exists g idx, r = Some (g, idx).
Proof.
  intros Hov H. unfold malloc_core in H. rewrite Hov in H. destruct (MMAP_THRESHOLD <=? n).
  - apply spath_vis_inv in H as (z & Hz & H). apply spath_if_bad in H as [_ H].
    rewrite (C_mmap_ok Hz land_MAPF_FIXED) in H. dmatch H as [st1 rid]. lazy zeta in H.
    apply spath_alloc_meta in H. destruct H as [(st3 & g & _ & H)|(st3 & _ & _ & Hf)]; [| destruct (not_admits_fail Hf)].
    cbn beta iota in H. lazy zeta delta [ret] in H. apply spath_ret_inv in H. inversion H. eauto.
  - apply msc_grant in H as (st1 & g & idx & H). unfold ret in H. apply spath_ret_inv in H. inversion H. eauto.
Qed.

Theorem cmalloc_grant_some cs n cs' r :
  size_overflows n = false -> spath (cmalloc cs n) (cs', r) -> exists c, r = Some c.
Proof.
  intros Hov H. unfold cmalloc in H. apply spath_sbind in H as ([st1 r1] & H1 & H2).
  apply mcore_grant in H1 as (g & idx & ->); [| exact Hov]. unfold ret in H2. apply spath_ret_inv in H2. inversion H2. eauto.
Qed.
End GRANT.
End SPATH.
End LBCEIL.

Arguments spath {C R} _ _.

(* [comment removed for export] *)
Definition gcls (e : ev) (z : Z) : Prop :=
  match e with
  | EMmap a l p fl => Z.land fl MAP_FIXED = 0 -> is_err z = false
  | EMprotect _ _ _ => (z =? 0) || (z =? TWO64 - ENOSYS) = true
  | EUndef _ | EPeek _ _ _ => False
  | _ => True
  end.

Lemma gcls_undef : forall w z, ~ gcls (EUndef w) z. Proof. intros w z H. exact H. Qed.
Lemma gcls_mmap_ok : forall a l p fl z, gcls (EMmap a l p fl) z -> Z.land fl MAP_FIXED = 0 -> is_err z = false.
Proof. intros a l p fl z H. exact H. Qed.
Lemma gcls_mprot_ok : forall a l p z, gcls (EMprotect a l p) z -> (z =? 0) || (z =? TWO64 - ENOSYS) = true.
Proof. intros a l p z H. exact H. Qed.
End LB_Grant.

   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma INVL_init secret resv : 0 <= secret < 2 ^ 64 ->
  INVL x0 (minit secret resv) (led_init resv) [] (fun _ => []).
Proof.
  intros Hs.
  assert (NOH : forall b m, ~ hosts (minit secret resv) b m) by (intros b m [ai H]; cbn in H; rewrite lookup_empty in H; discriminate).
  assert (MR0 : forall m, MR (minit secret resv) m = meta0) by (intros m; unfold MR, get_meta_rec; cbn; rewrite lookup_empty; reflexivity).
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - constructor; cbn; try (intros; rewrite lookup_empty in *; discriminate).
    + reflexivity.
    + rewrite map_to_list_empty. cbn. apply Permutation_refl.
    + rewrite map_to_list_empty. cbn. apply Permutation_refl.
    + split; [lia| left; reflexivity].
    + intros b l. split; [discriminate|]. ((first [ intro dR_28; dex2 dR_28 as rid r; destruct dR_28 as [H _] | intro dR_28; dand4 dR_28 as rid r H _ | intros (rid & r & H & _) ])). rewrite lookup_empty in H. discriminate.
    + split; [reflexivity|]. intros rid r H. rewrite lookup_empty in H. discriminate.
    + split; [lia|]. split; [lia|]. intros rid off H. discriminate.
  - constructor; cbn; try (intros; rewrite lookup_empty in *; discriminate).
    + split; [lia|]. split; [lia|]. split; intros i v H; rewrite lookup_empty in H; discriminate.
    + split; [exact Hs|]. left. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity.
    + intros _. split; reflexivity.
    + split; [unfold NSLOTS; lia|]. intros H. lia.
    + intros sc Hsc. unfold usage, gcnt. cbn. rewrite lookup_empty, map_to_list_empty. reflexivity.
  - constructor; cbn.
    + intros m _. rewrite MR0. reflexivity.
    + intros m b H. rewrite MR0 in H. discriminate.
    + intros b h H. rewrite lookup_empty in H. discriminate.
    + intros m [].
    + intros z [].
  - constructor; cbn.
    + intros h. destruct h; cbn; [unfold active; cbn; rewrite lookup_empty|]; reflexivity.
    + intros h. exact I.
    + intros h. constructor.
    + intros h1 h2 m [].
    + intros m. rewrite MR0. cbn. split; [| reflexivity]. split; [intros [h []]| congruence].
    + intros m [].
    + intros sc m [].
    + intros h H. exfalso. apply H. reflexivity.
  - constructor; cbn.
    + intros m b ai H. rewrite lookup_empty in H. discriminate.
    + intros b ai H. rewrite lookup_empty in H. discriminate.
    + intros m1 m2 b1 b2 ai1 ai2 H. rewrite lookup_empty in H. discriminate.
    + intros rid r H. rewrite lookup_empty in H. discriminate.
    + intros b h H. rewrite lookup_empty in H. discriminate.
  - constructor; cbn.
    + intros s m i H. rewrite lookup_empty in H. discriminate.
    + intros b m i H. exfalso. exact (NOH _ _ H).
    + intros b m ai i H. rewrite lookup_empty in H. discriminate.
    + intros s H. discriminate.
    + constructor.
    + intros k [].
  - constructor; cbn.
    + intros rid sh H. rewrite lookup_empty in H. discriminate.
    + intros rid sh H. rewrite lookup_empty in H. discriminate.
    + intros b m i H. exfalso. exact (NOH _ _ H).
    + intros b m o H. exfalso. exact (NOH _ _ H).
    + intros b m p i H. exfalso. exact (NOH _ _ H).
    + intros k m i [].
Qed.

Lemma INVL_set_live X st L BL LS v : INVL X st L BL LS -> INVL X st (set_live v L) BL LS.
Proof.
  ((first [ intro dR_29; dand7 dR_29 as IR IA IM IL IG IS ISH | intros (IR & IA & IM & IL & IG & IS & ISH) ])). split; [| split; [exact IA| split; [exact IM| split; [exact IL| split; [exact IG| split; [exact IS| exact ISH]]]]]].
  destruct IR; constructor; cbn; auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma cpath_follow {R} L (t : M R) L' r : cpath L t L' r -> exists ans, follow t ans = Some r /\ lafter L t ans = L'.
Proof.
  induction 1 as [L0 r0|L0 e k z L1 r0 Hz Hp IH].
  - exists []. split; reflexivity.
  - (first [ dex1 IH as ans; destruct IH as [Hf Hl] | dand3 IH as ans Hf Hl | destruct IH as (ans & Hf & Hl) ]). exists (z :: ans).
    destruct e; cbn [follow lafter]; try (split; [exact Hf| exact Hl]). cbn in Hz. discriminate.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bl_remove_map c BL : map bslot (bl_remove c BL) = ap_remove c (map bslot BL).
Proof.
  induction BL as [|k BL IH]; cbn; [reflexivity|]. destruct (aptr_eqb_spec (bslot k) c) as [E|NE]; [reflexivity|]. cbn. rewrite IH. reflexivity.
Qed.

Lemma In_bslot c BL : In c (map bslot BL) -> exists off n, In ((c, off), n) BL.
Proof.
  intros H. apply in_map_iff in H as ([[c' off] n] & E & Hin). cbn in E. subst c'. exists off, n. exact Hin.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition pans0 (_ : unit) (_ : aptr) (_ _ : Z) : Z := 0.
Definition pupd0 (o : unit) (_ : ev) (_ : Z) : unit := o.
Lemma pans0_range : forall o p c h, 0 <= pans0 o p c h < 256.
Proof. intros. unfold pans0. lia. Qed.

Definition SIMREL (cs : mstate) (L : mled) : Prop :=
  exists st BL LS, strip st = cs /\ INVL x0 st L BL LS /\ ld_live L = map bslot BL.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem cfree_contract_sim : forall cs L c,
  SIMREL cs L -> In c (ld_live L) -> ctree_ok L (cfree cs (Some c)) (fun _ _ => True).
Proof.
  intros cs L c SR Hc. (first [ dex1 SR as st; dand5 SR as BL LS <- INV LIVE | dand6 SR as st BL LS <- INV LIVE | destruct SR as (st & BL & LS & <- & INV & LIVE) ]).
  rewrite LIVE in Hc. (first [ pose proof ((In_bslot _ _ Hc)) as dR_27; dex2 dR_27 as off n; rename dR_27 into Hk | pose proof ((In_bslot _ _ Hc)) as dR_27; dand3 dR_27 as off n Hk | destruct (In_bslot _ _ Hc) as (off & n & Hk) ]).
  apply ptree_ctree_ok.
  eapply (ptree_strel (free_control pans0 pupd0 st (aadd c (UNIT * off)) c tt (INVL_hdr_ok pans0 pupd0 st L BL LS c off n INV Hk))); [intros; exact I|].
  eapply ptree_mono; [intros; exact I|]. exact (ftree_prun pans0 pupd0 pans0_range _ L _ tt (free_INVL_closed st L BL LS c off n INV Hk)).
Qed.

End CEIL.
