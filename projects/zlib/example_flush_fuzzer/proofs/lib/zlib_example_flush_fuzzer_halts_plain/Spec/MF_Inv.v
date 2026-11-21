(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.Spec Require Import STree Malloc MallocCtrl KInv MI_Tree MI_Inv MI_Kit MI_Arith MI_Geom MI_List MI_Ext
  MI_WTry2 MI_WSlot MI_Cnt LB_Sum FreshIface MF_Defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


Definition inrange (c n : Z) : Prop :=
  (c = 31 /\ 5437 <= n <= 8172) \/ (c = 40 /\ 32749 <= n <= 37436) \/ (c = 44 /\ 65517 <= n <= 74876).

Definition FG (X : list blk) (st : mstate) : Prop :=
  forall b m ai, s_groups st !! b = Some (mkGhdr (Some m) ai) ->
    m_sizeclass (MR st m) <> 30 /\
    (KCLS (m_sizeclass (MR st m)) ->
       m_last_idx (MR st m) = 0 /\ exists xb, In xb X /\ bslot xb = slot_start' (MR st m) 0 /\ inrange (m_sizeclass (MR st m)) (bsize xb)).

Definition FB (k : Z) (st : mstate) : Prop := bounces st 24 <= k /\ bounces st 24 <= 99.

Definition FF (X : list blk) (k : Z) (st : mstate) : Prop := FG X st /\ FB k st.


Lemma FF_strip X k st : FF X k (strip st) = FF X k st.
Proof. reflexivity. Qed.

Lemma FF_perm X Y k st : Permutation X Y -> FF X k st -> FF Y k st.
Proof.
  intros HP [G B]. split; [| exact B]. intros b m ai Hb. destruct (G _ _ _ Hb) as [N30 K]. split; [exact N30|].
  intros HK. destruct (K HK) as [L (xb & Hin & E & R)]. split; [exact L|]. exists xb. split; [| auto]. eapply Permutation_in; [exact HP| exact Hin].
Qed.

Lemma FF_incl X Y k st : incl X Y -> FF X k st -> FF Y k st.
Proof.
  intros HI [G B]. split; [| exact B]. intros b m ai Hb. destruct (G _ _ _ Hb) as [N30 K]. split; [exact N30|].
  intros HK. destruct (K HK) as [L (xb & Hin & E & R)]. split; [exact L|]. exists xb. split; [apply HI; exact Hin| auto].
Qed.

Lemma FF_kle X k k' st : k <= k' -> FF X k st -> FF X k' st.
Proof. intros Hk [G [B1 B2]]. split; [exact G|]. split; lia. Qed.

Lemma FF_init resv atop : FF [] 0 (minit 0 resv atop).
Proof.
  split.
  - intros b m ai Hb. cbn in Hb. rewrite lookup_empty in Hb. discriminate.
  - unfold FB, bounces, ctx. cbn. rewrite lookup_empty. cbn. lia.
Qed.

Lemma FF_ctrl X k st st1 : ctrl_eq st st1 -> FF X k st -> FF X k st1.
Proof.
  intros CE [G B]. pose proof (ce_groups _ _ CE) as EG. pose proof (MR_ext st st1 (ce_metas _ _ CE)) as EM.
  split.
  - intros b m ai Hb. rewrite EG in Hb. rewrite !EM. exact (G _ _ _ Hb).
  - unfold FB, bounces, ctx in *. rewrite (ce_ctx _ _ CE). exact B.
Qed.

Lemma same_geo_slot0 r1 r0 : same_geo r1 r0 -> slot_start' r1 0 = slot_start' r0 0.
Proof. intros G. destruct (same_geo_stride _ _ G) as (S & _ & _). destruct G as (M & _). unfold slot_start'. rewrite M, S. reflexivity. Qed.

Lemma FG_old X st st2 b m ai : FG X st -> s_groups st2 !! b = Some (mkGhdr (Some m) ai) -> OLD st st2 b m ->
  m_sizeclass (MR st2 m) <> 30 /\
  (KCLS (m_sizeclass (MR st2 m)) -> m_last_idx (MR st2 m) = 0 /\ exists xb, In xb X /\ bslot xb = slot_start' (MR st2 m) 0 /\ inrange (m_sizeclass (MR st2 m)) (bsize xb)).
Proof.
  intros G Hb [[ai0 H0] SG]. destruct (G _ _ _ H0) as [N30 K]. pose proof SG as (_ & EL & _ & EC). rewrite EC, EL, (same_geo_slot0 _ _ SG).
  split; [exact N30| exact K].
Qed.

Lemma FF_frame X X' k k' sc st st2 : FF X k st -> MFR sc st st2 -> ~ KCLS sc -> sc <> 30 -> incl X X' -> k <= k' -> FF X' k' st2.
Proof.
  intros F M NK N30 HI Hk. apply (FF_incl X X' k' st2 HI). apply (FF_kle X k k' st2 Hk). destruct F as [G [B1 B2]]. split.
  - intros b m ai Hb. destruct (mfr_old _ _ _ M _ _ _ Hb) as [O|N]; [exact (FG_old X st st2 b m ai G Hb O)|].
    destruct N as [E|H]; [rewrite E; split; [exact N30| intros K; exfalso; exact (NK K)]|].
    split; [lia| intros K; exfalso; destruct K; lia].
  - assert (NE : (sc =? 31) = false) by (apply Z.eqb_neq; intros ->; apply NK; left; reflexivity).
    pose proof (mfr_bnc _ _ _ M ltac:(intros ->; exfalso; apply NK; left; reflexivity)) as B. rewrite NE in B. unfold FB. lia.
Qed.

Lemma FF_knew X k sc st st2 g bg ai (xb : blk) : FF X k st -> k <= 98 -> MFR sc st st2 -> KCLS sc ->
  KNEW st st2 g bg -> s_groups st2 !! bg = Some (mkGhdr (Some g) ai) -> m_sizeclass (MR st2 g) = sc ->
  bslot xb = slot_start' (MR st2 g) 0 -> inrange sc (bsize xb) ->
  FF (xb :: X) (k + 1) st2.
Proof.
  intros [G [B1 B2]] K98 M HK (L0 & _ & _ & _ & OTH) Hg SC Hs Hr. split.
  - intros b m ai' Hb. destruct (decide (b = bg)) as [->|NE].
    + rewrite Hg in Hb. inversion Hb. subst m. rewrite SC. split; [intros E; rewrite E in HK; unfold KCLS in HK; lia|].
      intros _. split; [exact L0|]. exists xb. split; [left; reflexivity|]. split; [exact Hs| first [exact Hr| rewrite <- SC in Hr; exact Hr| rewrite SC; exact Hr]].
    + destruct (FG_old X st st2 b m ai' G Hb (OTH _ _ _ Hb NE)) as [N30 KK]. split; [exact N30|].
      intros HK2. destruct (KK HK2) as [L (xb' & Hin & E & R)]. split; [exact L|]. exists xb'. split; [right; exact Hin| auto].
  - pose proof (mfr_bnc _ _ _ M ltac:(intros; lia)) as B. unfold FB. destruct (sc =? 31); lia.
Qed.

Lemma FF_free X k st st2 (xb : blk) : FF (xb :: X) k st ->
  (forall b m ai, s_groups st2 !! b = Some (mkGhdr (Some m) ai) ->
     OLD st st2 b m /\ (KCLS (m_sizeclass (MR st2 m)) -> slot_start' (MR st m) 0 <> bslot xb)) ->
  bounces st2 24 <= bounces st 24 -> FF X k st2.
Proof.
  intros [G [B1 B2]] OTH HB. split; [| unfold FB; lia].
  intros b m ai Hb. destruct (OTH _ _ _ Hb) as [O NS]. destruct (FG_old _ st st2 b m ai G Hb O) as [N30 K]. split; [exact N30|].
  intros HK. destruct (K HK) as [L (xb' & Hin & E & R)]. split; [exact L|]. exists xb'. split; [| auto].
  destruct Hin as [<-|Hin]; [| exact Hin]. exfalso. apply (NS HK). rewrite E. symmetry. apply same_geo_slot0. exact (proj2 O).
Qed.

Lemma FF_fields X k st st2 : s_groups st2 = s_groups st -> s_metas st2 = s_metas st -> s_ctx st2 = s_ctx st -> FF X k st -> FF X k st2.
Proof.
  intros EG EM EC [G B]. pose proof (MR_ext st st2 EM) as MRE. split.
  - intros b m ai Hb. rewrite EG in Hb. rewrite !MRE. exact (G _ _ _ Hb).
  - unfold FB, bounces, ctx in *. rewrite EC. exact B.
Qed.
Lemma FF_drop_region X k st rid : FF X k st -> FF X k (drop_region rid st).
Proof. apply FF_fields; reflexivity. Qed.


Lemma mask_le0_zero x : 0 <= x -> (forall i, 0 <= i -> Z.testbit x i = true -> i <= 0) -> Z.testbit x 0 = false -> x = 0.
Proof.
  intros Hx Hb H0. apply Z.bits_inj_0. intros j.
  destruct (Z_lt_dec j 0) as [Hn|Hn]; [apply Z.testbit_neg_r; lia|].
  destruct (Z.testbit x j) eqn:E; [| reflexivity]. exfalso.
  pose proof (Hb j ltac:(lia) E). assert (j = 0) by lia. subst j. rewrite H0 in E. discriminate.
Qed.

Section CONSEQ.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (XB : list blk).
Hypothesis INV : INVL X st L BL LS.
Hypothesis HG : FG XB st.
Hypothesis HX : forall xb, In xb XB -> In (bslot xb) (map bslot BL) \/ x_pend X = Some (bslot xb).

Let IA := proj1 (proj2 INV).
Let IM := proj1 (proj2 (proj2 INV)).
Let IL := proj1 (proj2 (proj2 (proj2 INV))).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))).
Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

Lemma FG_full b m ai : s_groups st !! b = Some (mkGhdr (Some m) ai) -> KCLS (m_sizeclass (MR st m)) ->
  m_avail (MR st m) = 0 /\ m_freed (MR st m) = 0 /\ m_maplen (MR st m) <> 0 /\ m_last_idx (MR st m) = 0.
Proof.
  intros Hb HK. destruct (HG _ _ _ Hb) as [_ K]. destruct (K HK) as [L0 (xb & Hin & Es & _)].
  pose proof (ig_ok _ _ _ IG _ _ _ Hb) as GO. pose proof (g_masks _ _ _ _ _ _ GO) as (M1 & M2 & M3 & M4 & M5 & M6). pose proof (g_ai _ _ _ _ _ _ GO) as AI.
  pose proof (is_part _ _ _ IS _ _ _ 0 Hb ltac:(lia)) as P. cbn zeta in P. rewrite <- Es in P.
  destruct P as (_ & _ & nAC & _ & nAE & nBC & _ & nBE & _).
  assert (A0 : tbit (m_avail (MR st m)) 0 = false).
  { destruct (tbit (m_avail (MR st m)) 0) eqn:E; [| reflexivity]. exfalso. destruct (HX xb Hin) as [C|E5]; [exact (nAC (conj eq_refl C))| exact (nAE (conj eq_refl E5))]. }
  assert (B0 : tbit (m_freed (MR st m)) 0 = false).
  { destruct (tbit (m_freed (MR st m)) 0) eqn:E; [| reflexivity]. exfalso. destruct (HX xb Hin) as [C|E5]; [exact (nBC (conj eq_refl C))| exact (nBE (conj eq_refl E5))]. }
  unfold tbit in *.
  split; [apply mask_le0_zero; [exact M1| intros i Hi Ht; pose proof (M3 i Hi Ht); lia| exact A0]|].
  split; [apply mask_le0_zero; [exact M2| intros i Hi Ht; pose proof (M4 i Hi Ht); lia| exact B0]|].
  split; [| exact L0]. pose proof (KCLS_range _ HK). exact (proj1 (proj1 (proj2 (g_stride _ _ _ _ _ _ GO ltac:(lia))) L0)).
Qed.

Lemma FG_head_full c m : KCLS c -> active st c = Some m -> m_avail (MR st m) = 0 /\ m_freed (MR st m) = 0.
Proof.
  intros HK HA. destruct (hd_facts X st L BL LS c m INV HA) as (_ & Esc & b & ai & Hb).
  destruct (FG_full b m ai Hb ltac:(rewrite Esc; exact HK)) as (A & B & _). auto.
Qed.

Lemma FG_no30 : active st 30 = None /\ usage st 30 = 0.
Proof.
  split.
  - destruct (active st 30) as [m|] eqn:HA; [| reflexivity]. exfalso.
    destruct (hd_facts X st L BL LS 30 m INV HA) as (_ & Esc & b & ai & Hb). exact (proj1 (HG _ _ _ Hb) Esc).
  - rewrite (ia_usage _ IA 30 ltac:(lia)). unfold gcnt.
    assert (Z0 : forall l, (forall bh, In bh l -> exists b h, bh = (b, h) /\ s_groups st !! b = Some h) ->
      zsum (map (fun bh : aptr * ghdr => match g_meta (snd bh) with Some m => if m_sizeclass (MR st m) =? 30 then cnt_of (MR st m) else 0 | None => 0 end) l) = 0).
    { induction l as [|bh l IH]; intros Hl; [reflexivity|]. cbn [map]. rewrite zsum_cons. rewrite IH by (intros bh' H'; apply Hl; right; exact H').
      destruct (Hl bh ltac:(left; reflexivity)) as (b & h & -> & Hb). cbn [snd]. destruct h as [[m|] ai]; cbn [g_meta]; [| lia].
      destruct (Z.eqb_spec (m_sizeclass (MR st m)) 30) as [E|NE]; [exfalso; exact (proj1 (HG _ _ _ Hb) E)| lia]. }
    apply Z0. intros [b h] Hin. exists b, h. split; [reflexivity|]. apply mtl_in. exact Hin.
Qed.

Definition crange (c : Z) : Z * Z := if c =? 31 then (5437, 8172) else if c =? 40 then (32749, 37436) else (65517, 74876).

Hypothesis HND : List.NoDup (map bslot XB).

Lemma inrange_crange c n : KCLS c -> inrange c n -> fst (crange c) <= n <= snd (crange c).
Proof. intros HK [[-> R]|[[-> R]|[-> R]]]; cbn; lia. Qed.

Lemma FG_usage c : KCLS c -> usage st c <= cntr (fst (crange c)) (snd (crange c)) XB.
Proof.
  intros HK. pose proof (KCLS_range _ HK) as (R48 & _).
  rewrite (ia_usage _ IA c ltac:(lia)). unfold gcnt, cntr.
  set (G := map_to_list (s_groups st)).
  set (w := fun bh : aptr * ghdr => match g_meta (snd bh) with
                                     | Some m => if m_sizeclass (MR st m) =? c then find (fun xb => aptr_eqb (bslot xb) (slot_start' (MR st m) 0)) XB else None
                                     | None => None end).
  set (f := fun bh : aptr * ghdr => match g_meta (snd bh) with Some m => if m_sizeclass (MR st m) =? c then cnt_of (MR st m) else 0 | None => 0 end).
  set (W := flat_map (fun bh => match w bh with Some xb => [xb] | None => [] end) G).
  assert (HGin : forall b h, In (b, h) G -> s_groups st !! b = Some h) by (intros b h Hin; apply mtl_in; exact Hin).
  assert (WF : forall b m ai, s_groups st !! b = Some (mkGhdr (Some m) ai) -> m_sizeclass (MR st m) = c ->
            exists xb, find (fun xb => aptr_eqb (bslot xb) (slot_start' (MR st m) 0)) XB = Some xb /\ In xb XB /\ bslot xb = slot_start' (MR st m) 0 /\ inrange c (bsize xb)).
  { intros b m ai Hb Ec. destruct (HG _ _ _ Hb) as [_ K]. rewrite Ec in K. destruct (K HK) as [_ (xb & Hin & Es & Hr)].
    destruct (find (fun xb0 => aptr_eqb (bslot xb0) (slot_start' (MR st m) 0)) XB) as [xb'|] eqn:F.
    - apply find_some in F as [Hin' E']. destruct (aptr_eqb_spec (bslot xb') (slot_start' (MR st m) 0)) as [E2|]; [| discriminate].
      assert (xb' = xb).
      { clear - HND Hin Hin' Es E2. induction XB as [|y l IH]; [destruct Hin|]. cbn [map] in HND. apply List.NoDup_cons_iff in HND as [NI ND].
        destruct Hin as [->|Hin]; destruct Hin' as [->|Hin']; [reflexivity| | | exact (IH ND Hin Hin')].
        - exfalso. apply NI. rewrite Es, <- E2. apply in_map. exact Hin'.
        - exfalso. apply NI. rewrite E2, <- Es. apply in_map. exact Hin. }
      subst xb'. exists xb. auto.
    - exfalso. pose proof (find_none _ _ F xb Hin) as NF. cbn in NF. rewrite Es, aptr_eqb_refl in NF. discriminate. }
  assert (SUM : zsum (map f G) = Z.of_nat (length W)).
  { assert (GEN : forall l, (forall bh, In bh l -> In bh G) -> zsum (map f l) = Z.of_nat (length (flat_map (fun bh => match w bh with Some xb => [xb] | None => [] end) l))).
    { induction l as [|bh l IH]; intros Hl; [reflexivity|]. cbn [map flat_map]. rewrite zsum_cons, length_app, (IH ltac:(intros bh' H'; apply Hl; right; exact H')).
      destruct bh as [b [[m|] ai]]; unfold f, w; cbn [snd g_meta]; [| cbn; lia].
      destruct (Z.eqb_spec (m_sizeclass (MR st m)) c) as [Ec|NE]; [| cbn; lia].
      pose proof (HGin b _ (Hl _ ltac:(left; reflexivity))) as Hb.
      destruct (WF b m ai Hb Ec) as (xb & F & _). rewrite F. cbn [length].
      destruct (HG _ _ _ Hb) as [_ K]. rewrite Ec in K. destruct (K HK) as [L0 _]. unfold cnt_of. rewrite L0. lia. }
    apply GEN. intros bh H; exact H. }
  rewrite SUM. apply inj_le. apply NoDup_incl_length.
  -
    assert (GEN : forall l, List.NoDup (map fst l) -> (forall bh, In bh l -> In bh G) -> List.NoDup (flat_map (fun bh => match w bh with Some xb => [xb] | None => [] end) l)).
    { induction l as [|bh l IH]; intros ND Hl; [apply List.NoDup_nil|]. cbn [map] in ND. apply List.NoDup_cons_iff in ND as [NI ND].
      cbn [flat_map]. specialize (IH ND ltac:(intros bh' H'; apply Hl; right; exact H')).
      destruct bh as [b [[m|] ai]]; unfold w at 1; cbn [snd g_meta app]; [| exact IH].
      destruct (Z.eqb_spec (m_sizeclass (MR st m)) c) as [Ec|NE]; cbn [app]; [| exact IH].
      pose proof (HGin b _ (Hl _ ltac:(left; reflexivity))) as Hb.
      destruct (WF b m ai Hb Ec) as (xb & F & Hin & Es & _). rewrite F. cbn [app]. apply List.NoDup_cons; [| exact IH].
      intros HinW. apply in_flat_map in HinW as ([b' [[m'|] ai']] & Hin' & Hw); unfold w in Hw; cbn [snd g_meta] in Hw; [| destruct Hw].
      destruct (Z.eqb_spec (m_sizeclass (MR st m')) c) as [Ec'|]; [| destruct Hw].
      pose proof (HGin b' _ (Hl _ ltac:(right; exact Hin'))) as Hb'.
      destruct (WF b' m' ai' Hb' Ec') as (xb' & F' & _ & Es' & _). rewrite F' in Hw. destruct Hw as [<-|[]].
      assert (Em : m' = m).
      { pose proof (is_total _ _ _ IS b m 0 (ex_intro _ ai Hb) ltac:(pose proof (g_li _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Hb)); lia)) as T1.
        pose proof (is_total _ _ _ IS b' m' 0 (ex_intro _ ai' Hb') ltac:(pose proof (g_li _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Hb')); lia)) as T2.
        rewrite <- Es', Es, T1 in T2. inversion T2. reflexivity. }
      subst m'. pose proof (hosts_inj _ _ _ IM _ _ _ (ex_intro _ ai' Hb') (ex_intro _ ai Hb)) as ->.
      apply NI. apply in_map_iff. exists (b, mkGhdr (Some m) ai'). split; [reflexivity| exact Hin'].
    }
    apply GEN; [apply mtl_nodup_keys| intros bh H; exact H].
  -
    intros xb HinW. apply in_flat_map in HinW as ([b [[m|] ai]] & Hin & Hw); unfold w in Hw; cbn [snd g_meta] in Hw; [| destruct Hw].
    destruct (Z.eqb_spec (m_sizeclass (MR st m)) c) as [Ec|]; [| destruct Hw].
    destruct (WF b m ai (HGin _ _ Hin) Ec) as (xb' & F & Hin' & _ & Hr). rewrite F in Hw. destruct Hw as [<-|[]].
    apply filter_In. split; [exact Hin'|]. pose proof (inrange_crange c _ HK Hr) as [R1 R2].
    apply andb_true_iff. split; apply Z.leb_le; [exact R1| exact R2].
Qed.
End CONSEQ.
