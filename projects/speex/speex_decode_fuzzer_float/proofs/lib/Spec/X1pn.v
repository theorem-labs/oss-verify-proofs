(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1ra X1qu X1og X1po X1pv X1px.
Import ListNotations.
Local Open Scope Z_scope.

Definition geo_of (r : meta) : (optr * Z * Z * Z)%type := (m_mem r, m_last_idx r, m_maplen r, m_sizeclass r).
Lemma geo_of_data r r' : data_of r' = data_of r -> geo_of r' = geo_of r.
Proof. unfold data_of, geo_of. destruct r, r'; cbn. intros H. injection H. intros; subst; reflexivity. Qed.
Lemma geo_upd_meta st m f : (forall r, geo_of (f r) = geo_of r) -> forall x, geo_of (MR (upd_meta m f st) x) = geo_of (MR st x).
Proof.
intros Hf x. unfold MR. destruct (aptr_eq_dec x m) as [->|NE].
- rewrite get_meta_rec_upd_same. apply Hf.
- rewrite get_meta_rec_upd_other by exact NE. reflexivity.
Qed.

Definition HB (st : mstate) (c : aptr) (q : Z) : Prop :=
(exists v3, cell_read (get_shadow st (fst c)) (snd c - 3) = Known v3 /\ v3 <> 0 /\ 0 <= v3 < 256)
/\ cell_read (get_shadow st (fst c)) (snd c - 2) = Known (byte_of q 0)
/\ cell_read (get_shadow st (fst c)) (snd c - 1) = Known (byte_of q 1)
/\ 0 <= q < 2 ^ 16.

Record HK (st st' : mstate) : Prop := mkHK {
hk_groups : forall (b : aptr) mo ai, s_groups st !! b = Some (mkGhdr mo ai) -> exists ai', s_groups st' !! b = Some (mkGhdr mo ai');
hk_slots : forall (c : aptr) gi, s_slots st !! c = Some gi -> s_slots st' !! c = Some gi;
hk_geo : forall (b g : aptr) ai, s_groups st !! b = Some (mkGhdr (Some g) ai) -> geo_of (MR st' g) = geo_of (MR st g);

hk_cells : forall (c : aptr) k, snd c mod 16 = 0 -> 1 <= k <= 3 -> (s_groups st !! c <> None \/ s_groups st' !! c = None) ->
cell_read (get_shadow st' (fst c)) (snd c - k) = cell_read (get_shadow st (fst c)) (snd c - k);
hk_newcont : forall (c g : aptr) ai, s_groups st !! c = None -> s_groups st' !! c = Some (mkGhdr (Some g) ai) -> snd c <> 0 ->
exists (p : aptr) i (bp : aptr) aip, s_slots st' !! c = Some (p, i) /\ s_groups st' !! bp = Some (mkGhdr (Some p) aip) /\ fst bp = fst c
/\ snd c mod 16 = 0 /\ HB st' c ((snd c - snd bp - UNIT) / UNIT)
}.

Lemma HK_refl st : HK st st.
Proof.
constructor.
- intros b mo ai H. exists ai. exact H.
- intros c gi H. exact H.
- intros; reflexivity.
- intros; reflexivity.
- intros c g ai H1 H2. rewrite H1 in H2. discriminate H2.
Qed.

Lemma HB_cells st st' c q :
(forall k, 1 <= k <= 3 -> cell_read (get_shadow st' (fst c)) (snd c - k) = cell_read (get_shadow st (fst c)) (snd c - k)) ->
HB st c q -> HB st' c q.
Proof.
intros E ((v3 & A1 & A2 & A3) & B & C & D). unfold HB.
rewrite (E 3) by lia. rewrite (E 2) by lia. rewrite (E 1) by lia. split; [exists v3; auto| auto].
Qed.

Lemma HK_trans a b c : HK a b -> HK b c -> HK a c.
Proof.
intros [G1 S1 E1 C1 N1] [G2 S2 E2 C2 N2]. constructor.
- intros bb mo ai H. destruct (G1 bb mo ai H) as [ai1 H1]. exact (G2 bb mo ai1 H1).
- intros cc gi H. exact (S2 cc gi (S1 cc gi H)).
- intros bb g ai H. destruct (G1 bb (Some g) ai H) as [ai1 H1]. rewrite (E2 bb g ai1 H1). exact (E1 bb g ai H).
- intros cc k Hal Hk Hg.
assert (Hgb : s_groups a !! cc <> None \/ s_groups b !! cc = None).
{ destruct Hg as [Hg|Hg]; [left; exact Hg| right].
destruct (s_groups b !! cc) as [[mo ai]|] eqn:E; [| reflexivity]. destruct (G2 cc mo ai E) as [ai' H']. exfalso. pose proof (eq_trans (eq_sym Hg) H') as XX. discriminate XX. }
assert (Hgc : s_groups b !! cc <> None \/ s_groups c !! cc = None).
{ destruct Hg as [Hg|Hg]; [left| right; exact Hg].
destruct (s_groups a !! cc) as [[mo ai]|] eqn:E; [| congruence]. destruct (G1 cc mo ai E) as [ai' H']. intros XH. pose proof (eq_trans (eq_sym XH) H') as XX. discriminate XX. }
rewrite (C2 cc k Hal Hk Hgc). exact (C1 cc k Hal Hk Hgb).
- intros cc g ai Ha Hc Hnz. destruct (s_groups b !! cc) as [[mo aib]|] eqn:Eb.
+ destruct (G2 cc mo aib Eb) as [ai2 H2]. rewrite Hc in H2. inversion H2. subst mo.
destruct (N1 cc g aib Ha Eb Hnz) as (p & i & bp & aip & Hs & Hbp & Hf & Hal & HBb).
destruct (G2 bp (Some p) aip Hbp) as [aip' Hbp'].
exists p, i, bp, aip'. split; [exact (S2 _ _ Hs)|]. split; [exact Hbp'|]. split; [exact Hf|]. split; [exact Hal|].
eapply HB_cells; [| exact HBb]. intros k Hk. apply (C2 cc k Hal Hk). left. rewrite Eb. discriminate.
+ exact (N2 cc g ai Eb Hc Hnz).
Qed.

Lemma HK_of_eq st st' :
(forall (b : aptr) mo ai, s_groups st !! b = Some (mkGhdr mo ai) -> exists ai', s_groups st' !! b = Some (mkGhdr mo ai')) ->
(forall b : aptr, s_groups st !! b = None -> s_groups st' !! b = None) ->
s_slots st' = s_slots st -> s_shadow st' = s_shadow st ->
(forall x, geo_of (MR st' x) = geo_of (MR st x)) -> HK st st'.
Proof.
intros G GN S SH GE. constructor.
- exact G.
- intros c gi H. rewrite S. exact H.
- intros b g ai _. apply GE.
- intros c k _ _ _. unfold get_shadow. rewrite SH. reflexivity.
- intros c g ai H1 H2. rewrite (GN c H1) in H2. discriminate H2.
Qed.
Lemma HK_eq st st' : s_groups st' = s_groups st -> s_slots st' = s_slots st -> s_shadow st' = s_shadow st ->
(forall x, geo_of (MR st' x) = geo_of (MR st x)) -> HK st st'.
Proof.
intros G S SH GE. apply HK_of_eq; [| intros b H; rewrite G; exact H| exact S| exact SH| exact GE].
intros b mo ai H. exists ai. rewrite G. exact H.
Qed.
