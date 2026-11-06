(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Fuel__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Cnt__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_List__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WKill. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Pres2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Quant. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Geom OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.MI_Cnt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_Pres1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WKill OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_WFree2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.KArith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.KLink OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.LB_Tables OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.LB_Sum OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Quant.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCeil.
Context {CE : CEIL}.
#[using="Type"] Lemma zsum_indicator (a : Z) (v : Z) (cs : list Z) : List.NoDup cs -> In a cs ->
  zsum (map (fun c => if a =? c then v else 0) cs) = v.
Proof.
  induction cs as [|c cs IH]; intros ND Hin; [destruct Hin|]. cbn [map]. rewrite zsum_cons.
  apply List.NoDup_cons_iff in ND as [NI ND].
  destruct (Z.eqb_spec a c) as [E|NE].
  - subst c. assert (Z0 : zsum (map (fun c => if a =? c then v else 0) cs) = 0).
    { transitivity (zsum (map (fun _ : Z => 0) cs)); [| rewrite zsum_map_const; lia].
      apply zsum_map_ext. intros c' Hc'. destruct (Z.eqb_spec a c'); [subst; contradiction| reflexivity]. }
    lia.
  - destruct Hin as [->|Hin]; [contradiction|]. rewrite IH; auto.
Qed.

#[using="Type"] Lemma classes_nodup : List.NoDup classes.
Proof. unfold classes. apply Finite.Injective_map_NoDup; [intros a b; lia| apply seq_NoDup]. Qed.

#[using="Type"] Lemma zsum_by_class {A} (cf : A -> Z) (F : A -> Z) (l : list A) :
  (forall x, In x l -> 0 <= cf x < 48) ->
  zsum (map F l) = zsum (map (fun c => zsum (map (fun x => if cf x =? c then F x else 0) l)) classes).
Proof.
  induction l as [|x l IH]; intros Hc.
  - cbn [map]. rewrite zsum_nil. symmetry. rewrite zsum_map_const. lia.
  - cbn [map]. rewrite zsum_cons. rewrite IH by (intros y Hy; apply Hc; right; exact Hy).
    transitivity (zsum (map (fun c => (if cf x =? c then F x else 0) + zsum (map (fun x0 => if cf x0 =? c then F x0 else 0) l)) classes)).
    2:{ apply zsum_map_ext. intros c _. rewrite zsum_cons. reflexivity. }
    rewrite zsum_map_add. f_equal. symmetry. apply zsum_indicator; [apply classes_nodup| apply In_classes; apply Hc; left; reflexivity].
Qed.

#[using="Type"] Lemma zsum_pow2_range s : 0 <= s -> zsum (map (fun j => 2 ^ j) (zrange 1 s)) = 2 ^ (s + 1) - 2.
Proof.
  intros Hs. unfold zrange. rewrite <- (Z2Nat.id s) at 2 by lia. generalize (Z.to_nat s). clear s Hs. intros n.
  induction n as [|n IH]; [reflexivity|].
  rewrite seq_S, map_app, map_app, zsum_app, IH. cbn [map]. rewrite zsum_cons, zsum_nil.
  rewrite Nat2Z.inj_succ. replace (1 + Z.of_nat n) with (Z.succ (Z.of_nat n)) by lia. rewrite !Z.pow_succ_r by lia. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma zsum_distinct_pow2 (l : list Z) s : 0 <= s -> List.NoDup l -> (forall j, In j l -> 1 <= j <= s) ->
  zsum (map (fun j => 2 ^ j) l) <= 2 ^ (s + 1) - 2.
Proof.
  intros Hs ND Hr. rewrite <- (zsum_pow2_range s Hs).
  apply (zsum_inj_le Z.eq_dec (fun j => 2 ^ j) (fun j => 2 ^ j) (fun j => j)); [exact ND| | auto|].
  - intros x Hx. split; [apply in_zrange; [lia|]; pose proof (Hr x Hx); lia| lia].
  - intros y Hy. apply in_zrange in Hy; [| lia]. apply Z.pow_nonneg. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma find_some_iff {A} (p : A -> bool) l x : find p l = Some x -> In x l /\ p x = true.
Proof. intros H. split; [eapply find_some; exact H| apply find_some in H; tauto]. Qed.

Section QMB.
Variables (X : extras) (st : mstate) (L : mled).
Hypothesis IR : inv_R X st L.
Hypothesis QBRK : forall rid r, s_regions st !! rid = Some r -> r_kind r = RKBrk -> 101 * (r_len r / PGSZ - 2) <= ncarved st.
Hypothesis QLEN : forall rid r, s_regions st !! rid = Some r -> r_kind r = RKMeta ->
      exists j, 1 <= j <= c_meta_alloc_shift (s_ctx st) /\ r_len r = 2 ^ j * PGSZ.
Hypothesis QDIST : forall rid1 rid2 r1 r2, s_regions st !! rid1 = Some r1 -> s_regions st !! rid2 = Some r2 ->
      r_kind r1 = RKMeta -> r_kind r2 = RKMeta -> rid1 <> rid2 -> r_len r1 <> r_len r2.
Hypothesis QSHIFT : 1 <= c_meta_alloc_shift (s_ctx st) -> 101 * (2 ^ c_meta_alloc_shift (s_ctx st) - 1) <= 2 * ncarved st + 101.


Definition isMb (kr : N * region) : bool := match r_kind (snd kr) with RKMeta => true | _ => false end.
Definition isBb (kr : N * region) : bool := match r_kind (snd kr) with RKBrk => true | _ => false end.
Definition j_of (kr : N * region) : Z := Z.log2 (r_len (snd kr) / PGSZ).

#[using="QLEN"] Lemma meta_region_jQ rid r : s_regions st !! rid = Some r -> r_kind r = RKMeta ->
  1 <= j_of (rid, r) <= c_meta_alloc_shift (s_ctx st) /\ r_len r = 2 ^ j_of (rid, r) * PGSZ.
Proof.
  intros Hr K. destruct (QLEN rid r Hr K) as (j & Hj & E). unfold j_of. cbn.
  rewrite E. unfold PGSZ. rewrite Z.div_mul by lia. rewrite Z.log2_pow2 by lia. split; [exact Hj| reflexivity].
Qed.

#[using="QLEN QDIST"] Lemma meta_bytes_pow :
  meta_bytes st <= PGSZ * (if c_meta_alloc_shift (s_ctx st) <? 1 then 0 else 2 ^ (c_meta_alloc_shift (s_ctx st) + 1) - 2).
Proof.
  unfold meta_bytes, msum, regions_l.
  transitivity (zsum (map (fun kr => PGSZ * 2 ^ j_of kr) (List.filter isMb (map_to_list (s_regions st))))).
  { rewrite zsum_map_filter. apply zsum_map_le. intros [rid r] Hin. apply mtl_in in Hin. unfold isMb. cbn.
    destruct (r_kind r) eqn:K; try lia. destruct (meta_region_jQ rid r Hin K) as [_ E]. cbn in E |- *. lia. }
  rewrite zsum_map_mul. apply Z.mul_le_mono_nonneg_l; [unfold PGSZ; lia|].
  rewrite <- (map_map j_of (fun j => 2 ^ j)).
  destruct (Z.ltb_spec (c_meta_alloc_shift (s_ctx st)) 1) as [S0|S1].
  - (* [comment removed for export] *)
    replace (List.filter isMb (map_to_list (s_regions st))) with (@nil (N * region)); [cbn; lia|].
    symmetry. destruct (List.filter isMb (map_to_list (s_regions st))) as [|[rid r] l] eqn:E; [reflexivity|]. exfalso.
    assert (Hin : In (rid, r) (List.filter isMb (map_to_list (s_regions st)))) by (rewrite E; left; reflexivity).
    apply filter_In in Hin as [Hin K]. apply mtl_in in Hin. unfold isMb in K. cbn in K.
    destruct (meta_region_jQ rid r Hin ltac:(destruct (r_kind r); try discriminate; reflexivity)) as [J _]. lia.
  - apply zsum_distinct_pow2; [lia| |].
    + (* [comment removed for export] *)
      assert (ND : List.NoDup (List.filter isMb (map_to_list (s_regions st)))) by (apply List.NoDup_filter; apply mtl_nodup).
      assert (INJ : forall a b, In a (List.filter isMb (map_to_list (s_regions st))) -> In b (List.filter isMb (map_to_list (s_regions st))) -> j_of a = j_of b -> a = b).
      { intros [q1 r1] [q2 r2] H1 H2 E. apply filter_In in H1 as [H1 K1]. apply filter_In in H2 as [H2 K2]. apply mtl_in in H1. apply mtl_in in H2.
        unfold isMb in K1, K2. cbn in K1, K2.
        assert (M1 : r_kind r1 = RKMeta) by (destruct (r_kind r1); try discriminate; reflexivity).
        assert (M2 : r_kind r2 = RKMeta) by (destruct (r_kind r2); try discriminate; reflexivity).
        destruct (meta_region_jQ q1 r1 H1 M1) as [_ E1]. destruct (meta_region_jQ q2 r2 H2 M2) as [_ E2].
        destruct (N.eq_dec q1 q2) as [->|NE]; [rewrite H1 in H2; inversion H2; reflexivity|].
        exfalso. apply (QDIST q1 q2 r1 r2 H1 H2 M1 M2 NE). rewrite E1, E2, E. reflexivity. }
      revert ND INJ. generalize (List.filter isMb (map_to_list (s_regions st))). clear. intros l ND INJ.
      induction l as [|a l IH]; cbn; [constructor|]. inversion ND; subst. constructor.
      * intros Hin. apply in_map_iff in Hin as (b & E & Hb). rewrite (INJ a b ltac:(left; reflexivity) ltac:(right; exact Hb) (eq_sym E)) in H1. exact (H1 Hb).
      * apply IH; [assumption|]. intros x y Hx Hy. apply INJ; right; assumption.
    + intros j Hj. apply in_map_iff in Hj as ([rid r] & <- & Hin). apply filter_In in Hin as [Hin K]. apply mtl_in in Hin. unfold isMb in K. cbn in K.
      exact (proj1 (meta_region_jQ rid r Hin ltac:(destruct (r_kind r); try discriminate; reflexivity))).
Qed.

#[using="QLEN QDIST QSHIFT"] Lemma meta_bytes_boundQ : meta_bytes st <= PGSZ * (2 * ((2 * ncarved st + 101) / 101)).
Proof.
  pose proof meta_bytes_pow as MP.
  assert (NC : 0 <= ncarved st) by (unfold ncarved; apply zlen_nonneg).
  destruct (Z.ltb_spec (c_meta_alloc_shift (s_ctx st)) 1) as [S0|S1].
  - assert (0 <= (2 * ncarved st + 101) / 101) by (apply Z.div_pos; lia). unfold PGSZ in *. lia.
  - pose proof (QSHIFT S1) as QS. rewrite Z.pow_add_r in MP by lia. change (2 ^ 1) with 2 in MP.
    assert (2 ^ c_meta_alloc_shift (s_ctx st) - 1 <= (2 * ncarved st + 101) / 101) by (apply Zdiv_le_lower_bound; lia). unfold PGSZ in *. lia.
Qed.

(* [comment removed for export] *)
#[using="QLEN QDIST QSHIFT"] Lemma meta_bytes_bound4 : meta_bytes st <= PGSZ * (4 * (ncarved st / 101) + 4).
Proof.
  pose proof meta_bytes_boundQ as MB. assert (NC : 0 <= ncarved st) by (unfold ncarved; apply zlen_nonneg).
  set (n := ncarved st) in *. set (q := n / 101) in *.
  pose proof (Z.div_mod n 101 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound n 101 ltac:(lia)) as MB2. fold q in DM.
  assert (A : (2 * n + 101) / 101 < 2 * q + 3) by (apply Z.div_lt_upper_bound; lia). unfold PGSZ in *. lia.
Qed.

#[using="CE X L IR QBRK"] Lemma brk_pages_boundQ : PGSZ * brk_pages st <= PGSZ * (ncarved st / 101 + 2).
Proof.
  apply Z.mul_le_mono_nonneg_l; [unfold PGSZ; lia|].
  assert (NC : 0 <= ncarved st) by (unfold ncarved; apply zlen_nonneg).
  unfold brk_pages, regions_l.
  set (F := fun kr : N * region => match r_kind (snd kr) with RKBrk => r_len (snd kr) / PGSZ | _ => 0 end).
  destruct (find isBb (map_to_list (s_regions st))) as [[rid r]|] eqn:FD.
  - apply find_some_iff in FD as [Hin K]. apply mtl_in in Hin. unfold isBb in K. cbn in K.
    assert (KB : r_kind r = RKBrk) by (destruct (r_kind r); try discriminate; reflexivity).
    change (zsum (map F (map_to_list (s_regions st)))) with (msum F (s_regions st)).
    rewrite (msum_delete F (s_regions st) rid r Hin).
    assert (Z0 : msum F (delete rid (s_regions st)) = 0).
    { unfold msum. transitivity (zsum (map (fun _ : N * region => 0) (map_to_list (delete rid (s_regions st))))); [| rewrite zsum_map_const; lia].
      apply zsum_map_ext. intros [q rq] Hq. apply mtl_in in Hq. rewrite lookup_delete_Some in Hq. destruct Hq as [NE Hq].
      unfold F. cbn. destruct (r_kind rq) eqn:Kq; try reflexivity. exfalso. apply NE. apply (ir_brk1 _ _ _ IR _ _ _ _ Hin Hq KB Kq). }
    rewrite Z0, Z.add_0_r. unfold F. cbn. rewrite KB.
    pose proof (QBRK rid r Hin KB) as QB.
    assert (r_len r / PGSZ - 2 <= ncarved st / 101) by (apply Zdiv_le_lower_bound; lia). lia.
  - transitivity 0; [| apply Z.add_nonneg_nonneg; [apply Z.div_pos; lia| lia]].
    apply Z.eq_le_incl. transitivity (zsum (map (fun _ : N * region => 0) (map_to_list (s_regions st)))); [| rewrite zsum_map_const; lia].
    apply zsum_map_ext. intros [q rq] Hq. pose proof (find_none _ _ FD _ Hq) as N0. unfold isBb in N0. unfold F. cbn in N0 |- *. destruct (r_kind rq); try reflexivity. discriminate.
Qed.

#[using="CE X L IR QBRK QLEN QDIST QSHIFT"] Lemma meta_brk_boundQ : meta_bytes st + PGSZ * brk_pages st <= PGSZ * (5 * ncarved st / 101 + 6).
Proof.
  pose proof meta_bytes_boundQ as MB. pose proof brk_pages_boundQ as BB0.
  assert (NC : 0 <= ncarved st) by (unfold ncarved; apply zlen_nonneg).
  set (n := ncarved st) in *. set (q := n / 101) in *.
  pose proof (Z.div_mod n 101 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound n 101 ltac:(lia)) as MB2. fold q in DM.
  assert (A : (2 * n + 101) / 101 < 2 * q + 3) by (apply Z.div_lt_upper_bound; lia).
  assert (B : 5 * q <= 5 * n / 101) by (apply Zdiv_le_lower_bound; lia).
  unfold PGSZ in *. lia.
Qed.

End QMB.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section BOUND.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (P : Z -> Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis SI : SINV X st BL.
Hypothesis HAQ : AQ st BL P.
Let IR := proj1 INV.
Let IG : inv_G X st LS := proj1 (proj2 (proj2 (proj2 (proj2 INV)))).
Let IS : inv_S X st BL := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

#[using="Type"] Lemma gmetas_in m b : In (m, b) (gmetas st) <-> exists ai, s_groups st !! b = Some (mkGhdr (Some m) ai).
Proof.
  unfold gmetas, groups_l. rewrite in_flat_map. split.
  - intros ([b' [gm ai]] & Hin & Hm). cbn in Hm. destruct gm as [m'|]; [| destruct Hm]. destruct Hm as [E|[]]. inversion E; subst.
    exists ai. apply mtl_in. exact Hin.
  - intros [ai H]. exists (b, mkGhdr (Some m) ai). split; [apply mtl_in; exact H| cbn; auto].
Qed.

#[using="CE L BL INV IG"] Lemma gmetas_ok m b : In (m, b) (gmetas st) -> exists ai, s_groups st !! b = Some (mkGhdr (Some m) ai) /\ group_ok X st LS m b ai.
Proof. intros H. apply gmetas_in in H as [ai H]. exists ai. split; [exact H| exact (ig_ok _ _ _ IG _ _ _ H)]. Qed.

#[using="Type"] Lemma gmetas_nodup : List.NoDup (gmetas st).
Proof.
  unfold gmetas. pose proof (mtl_nodup_keys (s_groups st)) as ND. unfold groups_l. revert ND.
  induction (map_to_list (s_groups st)) as [|[b h] l IH]; intros ND; cbn; [constructor|].
  cbn in ND. inversion ND; subst. destruct (g_meta h) as [m|]; cbn; [| apply IH; assumption].
  constructor; [| apply IH; assumption]. rewrite in_flat_map. intros ([b' h'] & Hin & Hm). cbn in Hm.
  destruct (g_meta h'); [| destruct Hm]. destruct Hm as [E|[]]. inversion E; subst. apply H1. apply in_map_iff. exists (b, h'). auto.
Qed.

(* [comment removed for export] *)
#[using="CE X L BL LS INV IG"] Lemma gmetas_meta_inj m b1 b2 : In (m, b1) (gmetas st) -> In (m, b2) (gmetas st) -> b1 = b2.
Proof.
  intros H1 H2. apply gmetas_ok in H1 as (ai1 & Hg1 & G1). apply gmetas_ok in H2 as (ai2 & Hg2 & G2).
  pose proof (im_hdr _ _ _ (proj1 (proj2 (proj2 INV))) _ _ Hg1) as (m1 & E1 & M1 & _). cbn in E1. inversion E1; subst m1.
  pose proof (im_hdr _ _ _ (proj1 (proj2 (proj2 INV))) _ _ Hg2) as (m2 & E2 & M2 & _). cbn in E2. inversion E2; subst m2.
  rewrite M1 in M2. inversion M2. reflexivity.
Qed.

#[using="Type"] Lemma gcnt_gmetas c : gcnt st c = zsum (map (fun mb => if m_sizeclass (MR st (fst mb)) =? c then cnt_of (MR st (fst mb)) else 0) (gmetas st)).
Proof.
  unfold gcnt, gmetas, groups_l. rewrite zsum_flat_map. f_equal. apply map_ext_in. intros [b h] _. cbn.
  destruct (g_meta h) as [m|]; cbn; [| reflexivity]. lia.
Qed.

(* [comment removed for export] *)
#[using="CE X L BL LS INV IG"] Lemma gfacts m b : In (m, b) (gmetas st) ->
  1 <= cnt_of (MR st m) <= 32 /\ 0 <= m_maplen (MR st m)
  /\ ((0 <= m_sizeclass (MR st m) < 48) \/ (m_sizeclass (MR st m) = 63 /\ m_last_idx (MR st m) = 0 /\ m_maplen (MR st m) <> 0)).
Proof.
  intros H. apply gmetas_ok in H as (ai & Hg & G). pose proof (g_li _ _ _ _ _ _ G). pose proof (g_maplen _ _ _ _ _ _ G).
  unfold cnt_of. split; [lia|]. split; [lia|]. destruct (g_sc _ _ _ _ _ _ G) as [[? ?]|(? & ? & ? & _)]; [left; lia| right; auto].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition isGb (kr : N * region) : bool := match r_kind (snd kr) with RKGroup => true | _ => false end.
(* [comment removed for export] *)
Definition topof (kr : N * region) : aptr * aptr :=
  (match s_groups st !! (fst kr, 0) with Some h => default (0%N, 0) (g_meta h) | None => (0%N, 0) end, (fst kr, 0)).
Definition ORPH : Z :=
  match x_orph X with Some rid => match s_regions st !! rid with Some r => round_up_pg (r_len r) | None => 0 end | None => 0 end.

#[using="Type"] Lemma dec_pair : forall x y : aptr * aptr, {x = y} + {x <> y}.
Proof. intros x y. apply (decide (x = y)). Qed.

#[using="Type"] Lemma round_up_pg_nonneg x : 0 <= x -> 0 <= round_up_pg x.
Proof. intros. pose proof (round_up_pg_spec x). lia. Qed.

#[using="CE L BL LS INV IR IG"] Lemma group_bytes_le_groups :
  group_bytes st <= zsum (map (fun mb => m_maplen (MR st (fst mb)) * 4096) (gmetas st)) + ORPH.
Proof.
  unfold group_bytes, regions_l.
  (* [comment removed for export] *)
  set (F := fun kr : N * region => match r_kind (snd kr) with RKGroup => round_up_pg (r_len (snd kr)) | _ => 0 end).
  assert (STEP : forall regs : list (N * region), List.NoDup (map fst regs) ->
            (forall kr, In kr regs -> s_regions st !! fst kr = Some (snd kr)) ->
            (forall kr, In kr regs -> r_kind (snd kr) = RKGroup -> x_orph X <> Some (fst kr)) ->
            zsum (map F regs) <= zsum (map (fun mb => m_maplen (MR st (fst mb)) * 4096) (gmetas st))).
  { intros regs ND Hregs NO.
    rewrite <- (zsum_map_filter isGb (fun kr => round_up_pg (r_len (snd kr))) regs) || idtac.
    transitivity (zsum (map (fun kr => round_up_pg (r_len (snd kr))) (List.filter isGb regs))).
    { rewrite zsum_map_filter. apply Z.eq_le_incl. apply zsum_map_ext. intros [rid r] _. unfold F, isGb. cbn. destruct (r_kind r); reflexivity. }
    apply (zsum_inj_le dec_pair _ _ topof).
    - apply List.NoDup_filter. revert ND. clear. induction regs as [|kr regs IH]; cbn; intros ND; [constructor|]. inversion ND; subst. constructor; [| apply IH; assumption].
      intros Hin. apply H1. apply in_map_iff. exists kr. auto.
    - intros [rid r] Hin. apply filter_In in Hin as [Hin K]. unfold isGb in K. cbn in K. specialize (Hregs _ Hin). cbn in Hregs.
      assert (Kg : r_kind r = RKGroup) by (destruct (r_kind r); try discriminate; reflexivity).
      destruct (ig_top _ _ _ IG rid r Hregs Kg (NO _ Hin Kg)) as (m & [ai Hm] & Hml).
      pose proof (ig_ok _ _ _ IG _ _ _ Hm) as G. destruct (g_top _ _ _ _ _ _ G Hml) as (_ & r' & Hr' & _ & E & _). cbn in Hr'. rewrite Hregs in Hr'. inversion Hr'; subst r'.
      unfold topof. cbn [fst snd]. rewrite Hm. cbn. split; [apply gmetas_in; exists ai; exact Hm| lia].
    - intros [rid1 r1] [rid2 r2] H1 H2 E. unfold topof in E. cbn in E. apply filter_In in H1 as [H1 _]. apply filter_In in H2 as [H2 _].
      assert (rid1 = rid2) by (inversion E; reflexivity). subst rid2. pose proof (Hregs _ H1) as A1. pose proof (Hregs _ H2) as A2. cbn in A1, A2. rewrite A1 in A2. inversion A2. reflexivity.
    - intros [m b] Hin. destruct (gfacts m b Hin) as (_ & ML & _). cbn. lia. }
  destruct (x_orph X) as [orid|] eqn:HO.
  - unfold ORPH. rewrite HO. destruct (s_regions st !! orid) as [ro|] eqn:Hro.
    + unfold msum. rewrite (zsum_map_perm F _ _ (mtl_delete (s_regions st) orid ro Hro)). cbn [map]. rewrite zsum_cons.
      assert (F (orid, ro) <= round_up_pg (r_len ro)).
      { unfold F. cbn. pose proof (ir_shape _ _ _ IR _ _ Hro) as (_ & _ & L0 & _). pose proof (round_up_pg_nonneg (r_len ro) ltac:(lia)). destruct (r_kind ro); lia. }
      assert (zsum (map F (map_to_list (delete orid (s_regions st)))) <= zsum (map (fun mb => m_maplen (MR st (fst mb)) * 4096) (gmetas st))); [| lia].
      apply STEP.
      * apply mtl_nodup_keys.
      * intros [q rq] Hin. cbn. apply mtl_in in Hin. rewrite lookup_delete_Some in Hin. tauto.
      * intros [q rq] Hin _ E. cbn in E. inversion E; subst. apply mtl_in in Hin. rewrite lookup_delete_eq in Hin. discriminate.
    + transitivity (zsum (map (fun mb => m_maplen (MR st (fst mb)) * 4096) (gmetas st))); [| lia]. apply STEP.
      * apply mtl_nodup_keys.
      * intros [q rq] Hin. apply mtl_in. exact Hin.
      * intros [q rq] Hin _ E. cbn in E. inversion E; subst. apply mtl_in in Hin. cbn in Hin. rewrite Hro in Hin. discriminate.
  - unfold ORPH. rewrite HO, Z.add_0_r. apply STEP.
    + apply mtl_nodup_keys.
    + intros [q rq] Hin. apply mtl_in. exact Hin.
    + intros kr _ _. discriminate.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition T63 (mb : aptr * aptr) : Z := if m_sizeclass (MR st (fst mb)) =? 63 then m_maplen (MR st (fst mb)) * 4096 else 0.
Definition TST (mb : aptr * aptr) : Z := if (m_sizeclass (MR st (fst mb)) <? 48) && stdg st (fst mb) then m_maplen (MR st (fst mb)) * 4096 else 0.
Definition TNS (mb : aptr * aptr) : Z := if (m_sizeclass (MR st (fst mb)) <? 48) && negb (stdg st (fst mb)) then m_maplen (MR st (fst mb)) * 4096 else 0.

#[using="CE X L BL LS INV IG"] Lemma split3 : zsum (map (fun mb => m_maplen (MR st (fst mb)) * 4096) (gmetas st))
  = zsum (map T63 (gmetas st)) + zsum (map TST (gmetas st)) + zsum (map TNS (gmetas st)).
Proof.
  rewrite <- !zsum_map_add. apply zsum_map_ext. intros [m b] Hin. destruct (gfacts m b Hin) as (_ & _ & CL). unfold T63, TST, TNS. cbn [fst].
  destruct CL as [Hc|(Hc & _)].
  - replace (m_sizeclass (MR st m) =? 63) with false by (symmetry; apply Z.eqb_neq; lia). replace (m_sizeclass (MR st m) <? 48) with true by (symmetry; apply Z.ltb_lt; lia).
    cbn [andb]. destruct (stdg st m); cbn; lia.
  - rewrite Hc. cbn. lia.
Qed.

(* [comment removed for export] *)
Definition blk_of (mb : aptr * aptr) : blk :=
  match find (fun k => aptr_eqb (bslot k) (slot_start' (MR st (fst mb)) 0)) BL with Some k => k | None => ((0%N, 0), 0, 0) end.


#[using="Type"] Lemma aptr_eqb_refl a : aptr_eqb a a = true. Proof. apply aptr_eqb_eq. reflexivity. Qed.

#[using="CE L LS INV SI IG IS"] Lemma blk63 m b : x_pend X = None -> In (m, b) (gmetas st) -> m_sizeclass (MR st m) = 63 ->
  In (blk_of (m, b)) BL /\ bslot (blk_of (m, b)) = slot_start' (MR st m) 0 /\ isbig (blk_of (m, b)) = true
  /\ m_maplen (MR st m) * 4096 <= round_up_pg (bsize (blk_of (m, b)) + IB + UNIT) + PGSZ.
Proof.
  intros HP Hin Hc. destruct (gmetas_ok m b Hin) as (ai & Hg & G). pose proof (g_li _ _ _ _ _ _ G) as LI0.
  pose proof (qg_63 _ _ _ SI b m ai Hg Hc) as HB.
  apply in_map_iff in HB as (k & Ek & Hk).
  unfold blk_of. cbn [fst].
  destruct (find (fun k0 => aptr_eqb (bslot k0) (slot_start' (MR st m) 0)) BL) as [k'|] eqn:F.
  2:{ exfalso. pose proof (find_none _ _ F k Hk) as N. cbn in N. rewrite Ek, aptr_eqb_refl in N. discriminate. }
  apply find_some_iff in F as [Hk' E']. apply aptr_eqb_eq in E'.
  destruct (qb_cls _ _ _ SI k' Hk') as (m' & i' & Hs' & _ & B63).
  rewrite E', (is_total _ _ _ IS b m 0 (ex_intro _ ai Hg) ltac:(lia)) in Hs'. inversion Hs'; subst m' i'.
  destruct (B63 Hc) as [BIG EQ]. unfold isbig. split; [exact Hk'|]. split; [exact E'|]. split; [apply Z.leb_le; exact BIG| lia].
Qed.

#[using="CE L LS INV SI IG IS"] Lemma T63_bound : x_pend X = None -> zsum (map T63 (gmetas st)) <= R63 BL.
Proof.
  intros HP. unfold R63.
  rewrite <- (zsum_map_filter (fun mb => m_sizeclass (MR st (fst mb)) =? 63) (fun mb => m_maplen (MR st (fst mb)) * 4096)).
  apply (zsum_inj_le (fun x y : blk => decide (x = y)) _ _ blk_of).
  - apply List.NoDup_filter. apply gmetas_nodup.
  - intros [m b] Hin. apply filter_In in Hin as [Hin Hc]. cbn in Hc. apply Z.eqb_eq in Hc.
    destruct (blk63 m b HP Hin Hc) as (Hk & _ & BIG & EQ). split; [exact Hk|]. rewrite BIG. cbn [fst]. lia.
  - intros [m1 b1] [m2 b2] H1 H2 E. apply filter_In in H1 as [H1 C1]. apply filter_In in H2 as [H2 C2]. cbn in C1, C2. apply Z.eqb_eq in C1. apply Z.eqb_eq in C2.
    destruct (blk63 m1 b1 HP H1 C1) as (_ & S1 & _). destruct (blk63 m2 b2 HP H2 C2) as (_ & S2 & _). rewrite E in S1. rewrite S1 in S2.
    destruct (gmetas_ok m1 b1 H1) as (ai1 & Hg1 & G1). destruct (gmetas_ok m2 b2 H2) as (ai2 & Hg2 & G2).
    destruct (slot_key_inj _ _ _ IS b1 m1 b2 m2 0 0 (ex_intro _ ai1 Hg1) (ex_intro _ ai2 Hg2) ltac:(pose proof (g_li _ _ _ _ _ _ G1); lia) ltac:(pose proof (g_li _ _ _ _ _ _ G2); lia) S2) as [<- _].
    rewrite (gmetas_meta_inj m1 b1 b2 H1 H2). reflexivity.
  - intros k _. unfold isbig. destruct (Z.leb_spec MMAP_THRESHOLD (bsize k)); [| lia].
    pose proof (round_up_pg_nonneg (bsize k + IB + UNIT) ltac:(unfold IB, UNIT, MMAP_THRESHOLD in *; lia)). unfold PGSZ. lia.
Qed.

Definition cf (mb : aptr * aptr) : Z := if m_sizeclass (MR st (fst mb)) <? 48 then m_sizeclass (MR st (fst mb)) else 0.
#[using="CE X L BL LS INV IG"] Lemma cf_range mb : In mb (gmetas st) -> 0 <= cf mb < 48.
Proof. intros Hin. destruct mb as [m b]. destruct (gfacts m b Hin) as (_ & _ & CL). unfold cf. cbn. destruct (Z.ltb_spec (m_sizeclass (MR st m)) 48); lia. Qed.

#[using="CE X L BL LS INV IG"] Lemma std_lt48 m b : In (m, b) (gmetas st) -> stdg st m = true -> 0 <= m_sizeclass (MR st m) < 48.
Proof.
  intros Hin SG. destruct (gfacts m b Hin) as (CNT & _ & [Hc|(Hc & L0 & _)]); [exact Hc|]. exfalso.
  unfold stdg, cls in SG. rewrite Hc in SG. apply andb_prop in SG as [SG _]. apply Z.eqb_eq in SG. unfold cnt_of in SG. rewrite L0 in SG.
  vm_compute in SG. discriminate.
Qed.

#[using="CE X L BL LS INV SI HAQ IG"] Lemma TST_bound : zsum (map TST (gmetas st)) <= zsum (map (fun c => if std_nested c then 0 else std_len c * ((CAP P c + 32) / cmax c)) classes).
Proof.
  rewrite (zsum_by_class cf TST (gmetas st) cf_range). apply zsum_map_le. intros c Hc. apply In_classes in Hc.
  pose proof (tab_basic_ok c Hc) as (TB1 & TB2 & TB3 & TB4 & TB5).
  assert (PT : forall m b, In (m, b) (gmetas st) -> cf (m, b) = c -> stdg st m = true ->
            (m_maplen (MR st m) = 0 <-> std_nested c = true) /\ (m_maplen (MR st m) <> 0 -> m_maplen (MR st m) * 4096 = std_len c) /\ m_sizeclass (MR st m) = c /\ cnt_of (MR st m) = cmax c).
  { intros m b Hin Ecf SG. destruct (gmetas_ok m b Hin) as (ai & Hg & G).
    pose proof (std_lt48 m b Hin SG) as L48. assert (Ec : m_sizeclass (MR st m) = c) by (unfold cf in Ecf; cbn in Ecf; destruct (Z.ltb_spec (m_sizeclass (MR st m)) 48); [exact Ecf| lia]).
    destruct (qg_std _ _ _ SI b m ai Hg SG) as (Q1 & Q2 & Q3). rewrite Ec in Q1, Q3.
    unfold stdg in SG. apply andb_prop in SG as [SG _]. apply Z.eqb_eq in SG. unfold cls in SG. rewrite Ec in SG. auto. }
  destruct (std_nested c) eqn:NS.
  - apply Z.eq_le_incl. transitivity (zsum (map (fun _ : aptr * aptr => 0) (gmetas st))); [| rewrite zsum_map_const; lia].
    apply zsum_map_ext. intros [m b] Hin. destruct (Z.eqb_spec (cf (m, b)) c) as [E|NE]; [| reflexivity].
    unfold TST. cbn [fst]. destruct (stdg st m) eqn:SG; [| rewrite andb_false_r; reflexivity].
    destruct (PT m b Hin E SG) as (Q1 & _ & Ec & _). rewrite (proj2 Q1 eq_refl). destruct (_ <? 48); reflexivity.
  - set (CNT := zcount (fun mb : aptr * aptr => (m_sizeclass (MR st (fst mb)) =? c) && stdg st (fst mb)) (gmetas st)).
    transitivity (std_len c * CNT).
    + unfold CNT. rewrite zcount_eq_zsum, <- zsum_map_mul. apply zsum_map_le. intros [m b] Hin. unfold TST. cbn [fst].
      destruct (Z.eqb_spec (cf (m, b)) c) as [E|NE].
      * destruct (stdg st m) eqn:SG.
        -- destruct (PT m b Hin E SG) as (Q1 & Q2 & Ec & _). rewrite Ec, Z.eqb_refl. replace (c <? 48) with true by (symmetry; apply Z.ltb_lt; lia). cbn.
           assert (NZ : m_maplen (MR st m) <> 0) by (intros Z0; apply Q1 in Z0; discriminate). rewrite (Q2 NZ). lia.
        -- rewrite !andb_false_r. lia.
      * assert (SL : 0 <= std_len c) by (unfold std_span, UNIT in TB3; nia). destruct ((m_sizeclass (MR st m) =? c) && stdg st m); nia.
    + apply Z.mul_le_mono_nonneg_l; [unfold std_span, UNIT in TB3; nia|]. apply Zdiv_le_lower_bound; [lia|].
      transitivity (gcnt st c); [| exact (aq_slots _ _ _ HAQ c Hc)].
      rewrite gcnt_gmetas. unfold CNT. rewrite zcount_eq_zsum, Z.mul_comm, <- zsum_map_mul. apply zsum_map_le. intros [m b] Hin. cbn [fst].
      destruct (Z.eqb_spec (m_sizeclass (MR st m)) c) as [Ec|NE]; cbn [andb]; [| lia].
      destruct (stdg st m) eqn:SG; [| destruct (gfacts m b Hin) as ([? ?] & _); lia].
      destruct (PT m b Hin ltac:(unfold cf; cbn; rewrite Ec; replace (c <? 48) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity) SG) as (_ & _ & _ & Ecnt). rewrite Ecnt. lia.
Qed.

#[using="CE X L BL LS INV SI IG"] Lemma TNS_bound : zsum (map TNS (gmetas st)) <= zsum (map (fun c => 160 * (S_ c + 4111)) classes).
Proof.
  rewrite (zsum_by_class cf TNS (gmetas st) cf_range). apply zsum_map_le. intros c Hc. apply In_classes in Hc.
  pose proof (tab_basic_ok c Hc) as (TB1 & _). pose proof (qg_small _ _ _ SI c Hc) as SM.
  assert (NSN : 0 <= nsc st c).
  { unfold nsc. apply zsum_map_nonneg. intros [m b] Hin. destruct (_ && _); [| lia]. destruct (gfacts m b Hin) as ([? ?] & _). cbn. lia. }
  transitivity ((S_ c + 4111) * nsc st c); [| nia].
  unfold nsc. rewrite <- zsum_map_mul. apply zsum_map_le. intros [m b] Hin. unfold TNS, cls. cbn [fst].
  destruct (gfacts m b Hin) as (CNT & ML & _).
  unfold cf. cbn [fst]. destruct (Z.ltb_spec (m_sizeclass (MR st m)) 48) as [LT|GE]; cbn [andb].
  - destruct (Z.eqb_spec (m_sizeclass (MR st m)) c) as [E|NE]; cbn [andb].
    + destruct (stdg st m); cbn [negb]; [lia|].
      destruct (Z.eq_dec (m_maplen (MR st m)) 0) as [Z0|NZ]; [rewrite Z0; nia|].
      destruct (gmetas_ok m b Hin) as (ai & Hg & G). pose proof (qg_map _ _ _ SI b m ai Hg ltac:(lia) NZ) as QM. rewrite E in QM. nia.
    + replace (0 =? c) with (0 =? c) by reflexivity. destruct (Z.eqb_spec 0 c); [subst c; lia| lia].
  - destruct (0 =? c); destruct ((m_sizeclass (MR st m) =? c) && negb (stdg st m)); nia.
Qed.

(* [comment removed for export] *)
#[using="X BL SI"] Lemma meta_region_j rid r : s_regions st !! rid = Some r -> r_kind r = RKMeta ->
  1 <= j_of (rid, r) <= c_meta_alloc_shift (s_ctx st) /\ r_len r = 2 ^ j_of (rid, r) * PGSZ.
Proof. apply (meta_region_jQ st); exact (qm_len _ _ _ SI). Qed.
#[using="CE X L BL LS INV SI IR"] Lemma meta_brk_bound : meta_bytes st + PGSZ * brk_pages st <= PGSZ * (5 * ncarved st / 101 + 8).
Proof.
  pose proof (meta_brk_boundQ X st L IR (qm_brk _ _ _ SI) (qm_len _ _ _ SI) (qm_dist _ _ _ SI) (qm_shift _ _ _ SI)). unfold PGSZ in *. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="CE L LS INV SI HAQ IR IG IS"] Theorem regions_bound : x_pend X = None ->
  group_bytes st + meta_bytes st + PGSZ * brk_pages st + 3 * PGSZ <= PHI P + R63 BL + ORPH.
Proof.
  intros HP. unfold PHI.
  pose proof group_bytes_le_groups as G1. rewrite split3 in G1.
  pose proof (T63_bound HP) as G2. pose proof TST_bound as G3. pose proof TNS_bound as G4. pose proof meta_brk_bound as G5.
  assert (NC : 0 <= ncarved st) by (unfold ncarved; apply zlen_nonneg).
  assert (G6 : 5 * ncarved st / 101 <= 5 * NCAP P / 101) by (apply Z.div_le_mono; [lia|]; pose proof (aq_carved _ _ _ HAQ); lia).
  unfold PGSZ in *. lia.
Qed.

(* [comment removed for export] *)
#[using="CE L LS INV SI HAQ IR IG IS"] Theorem group_bytes_bound : x_pend X = None ->
  group_bytes st + PGSZ * (5 * NCAP P / 101 + 8) + 3 * PGSZ <= PHI P + R63 BL + ORPH.
Proof.
  intros HP. unfold PHI.
  pose proof group_bytes_le_groups as G1. rewrite split3 in G1.
  pose proof (T63_bound HP) as G2. pose proof TST_bound as G3. pose proof TNS_bound as G4.
  unfold PGSZ in *. lia.
Qed.

#[using="CE X L BL LS INV IR"] Lemma brk_pages_nonneg : 0 <= brk_pages st.
Proof.
  unfold brk_pages, regions_l. apply zsum_map_nonneg. intros [rid r] Hin. cbn. apply mtl_in in Hin.
  pose proof (ir_shape _ _ _ IR _ _ Hin) as (_ & _ & L0 & _). destruct (r_kind r); try lia. apply Z.div_pos; unfold PGSZ; lia.
Qed.

#[using="CE X BL LS INV IR"] Theorem ledger_bound : gm L + BB L <= group_bytes st + meta_bytes st + PGSZ * brk_pages st.
Proof.
  assert (E1 : zsum (map (fun g : Z * Z => mmap_len (snd g)) (ld_groups L)) = group_bytes st).
  { rewrite (zsum_map_perm _ _ _ (ir_groups _ _ _ IR)). rewrite map_map. unfold group_bytes, msum, regions_l. rewrite zsum_map_filter.
    apply zsum_map_ext. intros [rid r] _. cbn. destruct (r_kind r); try reflexivity. unfold mmap_len. rewrite round_up_pg_eq. reflexivity. }
  assert (E2 : zsum (map (fun m : Z * Z * Z => mmap_len (snd (fst m))) (ld_metas L)) = meta_bytes st).
  { rewrite (zsum_map_perm _ _ _ (ir_metas _ _ _ IR)). rewrite map_map. unfold meta_bytes, msum, regions_l. rewrite zsum_map_filter.
    apply zsum_map_ext. intros [rid r] Hin. apply mtl_in in Hin. cbn. destruct (r_kind r) eqn:K; try reflexivity.
    pose proof (ir_shape _ _ _ IR _ _ Hin) as (_ & _ & L0 & _ & _ & MK). destruct (MK ltac:(right; exact K)) as [AL _].
    apply mmap_len_of_aligned; [lia| unfold PGSZ in AL; exact AL]. }
  unfold gm. change (fold_right Z.add 0 (map (fun g : Z * Z => mmap_len g.2) (ld_groups L))) with (zsum (map (fun g : Z * Z => mmap_len (snd g)) (ld_groups L))).
  change (fold_right Z.add 0 (map (fun m : Z * Z * Z => mmap_len m.1.2) (ld_metas L))) with (zsum (map (fun m : Z * Z * Z => mmap_len (snd (fst m))) (ld_metas L))).
  rewrite E1, E2.
  assert (B0 : BB L <= PGSZ * brk_pages st); [| lia].
  pose proof brk_pages_nonneg as BP.
  assert (REG : forall b l, ld_brkreg L = Some (b, l) -> l <= PGSZ * brk_pages st).
  { intros b l H. apply (ir_brkreg _ _ _ IR) in H as (rid & r & Hr & K & _ & El).
    unfold brk_pages, regions_l. change (zsum (map ?f (map_to_list (s_regions st)))) with (msum f (s_regions st)).
    rewrite (msum_delete _ (s_regions st) rid r Hr). cbn. rewrite K, El.
    assert (NN : 0 <= msum (fun kr : N * region => match r_kind kr.2 with RKBrk => r_len kr.2 / PGSZ | _ => 0 end) (delete rid (s_regions st))).
    { apply msum_nonneg. intros q rq Hq. cbn. rewrite lookup_delete_Some in Hq. destruct Hq as [_ Hq].
      pose proof (ir_shape _ _ _ IR _ _ Hq) as (_ & _ & L0 & _). destruct (r_kind rq); try lia. apply Z.div_pos; unfold PGSZ; lia. }
    pose proof (ir_shape _ _ _ IR _ _ Hr) as (_ & _ & L0 & _ & _ & MK). destruct (MK ltac:(left; exact K)) as [AL _].
    pose proof (Z.div_mod l PGSZ ltac:(unfold PGSZ; lia)). rewrite <- El in *. unfold PGSZ in *. nia. }
  unfold BB. pose proof (ir_brk _ _ _ IR) as B. destruct (c_brk (s_ctx st)) as [| |rid off].
  - destruct B as [-> NB]. destruct (ld_brkreg L) as [[b l]|] eqn:E; [| unfold PGSZ; lia]. apply (REG b l eq_refl).
  - rewrite B. destruct (ld_brkreg L) as [[b l]|] eqn:E; [| unfold PGSZ; lia]. apply (REG b l eq_refl).
  - destruct B as [-> _]. destruct (ld_brkreg L) as [[b l]|] eqn:E; [| unfold PGSZ; lia]. apply (REG b l eq_refl).
Qed.

(* [comment removed for export] *)
#[using="CE X st BL LS INV IR"] Theorem gm_BB_nonneg : 0 <= gm L /\ 0 <= BB L.
Proof.
  split.
  - unfold gm.
    assert (G1 : forall g, In g (ld_groups L) -> 0 <= mmap_len (snd g)).
    { intros g Hg. apply (Permutation_in _ (ir_groups _ _ _ IR)) in Hg. apply in_map_iff in Hg as ([q rq] & <- & Hin). cbn.
      apply filter_In in Hin as [Hin _]. apply mtl_in in Hin. pose proof (ir_shape _ _ _ IR _ _ Hin) as (_ & _ & L0 & _). pose proof (mmap_len_ge (r_len rq) L0). lia. }
    assert (G2 : forall m, In m (ld_metas L) -> 0 <= mmap_len (snd (fst m))).
    { intros m Hm. apply (Permutation_in _ (ir_metas _ _ _ IR)) in Hm. apply in_map_iff in Hm as ([q rq] & <- & Hin). cbn.
      apply filter_In in Hin as [Hin _]. apply mtl_in in Hin. pose proof (ir_shape _ _ _ IR _ _ Hin) as (_ & _ & L0 & _). pose proof (mmap_len_ge (r_len rq) L0). lia. }
    assert (S1 : forall (l : list (Z * Z)), (forall g, In g l -> 0 <= mmap_len (snd g)) -> 0 <= fold_right Z.add 0 (map (fun g : Z * Z => mmap_len (snd g)) l)).
    { induction l as [|g l IH]; intros Hl; cbn; [lia|]. pose proof (Hl g (or_introl eq_refl)). specialize (IH ltac:(intros; apply Hl; right; assumption)). lia. }
    assert (S2 : forall (l : list (Z * Z * Z)), (forall m, In m l -> 0 <= mmap_len (snd (fst m))) -> 0 <= fold_right Z.add 0 (map (fun m : Z * Z * Z => mmap_len (snd (fst m))) l)).
    { induction l as [|m l IH]; intros Hl; cbn; [lia|]. pose proof (Hl m (or_introl eq_refl)). specialize (IH ltac:(intros; apply Hl; right; assumption)). lia. }
    pose proof (S1 _ G1). pose proof (S2 _ G2). lia.
  - unfold BB. destruct (ld_brk L); try (unfold PGSZ; lia).
    all: destruct (ld_brkreg L) as [[b l]|] eqn:E; [| lia]; apply (ir_brkreg _ _ _ IR) in E as (rid & r & Hr & _ & _ & <-);
         pose proof (ir_shape _ _ _ IR _ _ Hr) as (_ & _ & L0 & _); lia.
Qed.

(* [comment removed for export] *)
#[using="LS INV SI HAQ IR IG IS"] Theorem live_bound pbrk mo : x_pend X = None -> KL L pbrk mo -> LI L mo ->
  vm_live_bytes (m_vmmaps mo) + 3 * PGSZ <= PHI P + R63 BL + ORPH + PINB.
Proof.
  intros HP HK HL. apply LI_elim in HL. pose proof (regions_bound HP). pose proof ledger_bound. lia.
Qed.
End BOUND.


End WithCeil.
