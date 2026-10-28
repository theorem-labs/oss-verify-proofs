(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzArrD. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCSortM BzCQsortM1.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition entry : Type := (Z * Z * Z)%type.
Definition esz (e : entry) : Z := let '(lo, hi, _) := e in hi - lo + 1.
Definition elo (e : entry) : Z := let '(lo, _, _) := e in lo.
Definition ehi (e : entry) : Z := let '(_, hi, _) := e in hi.
Definition ed (e : entry) : Z := let '(_, _, d) := e in d.
Definition e0 : entry := (0, 0, 0).

Definition ent (q : mqs) (i : Z) : entry := (zget (mq_slo q) i, zget (mq_shi q) i, zget (mq_sd q) i).

(* [comment removed for export] *)
Definition mst (q : mqs) (F : list entry) : Prop :=
  mq_sp q = Z.of_nat (length F) /\
  forall k, (k < length F)%nat -> ent q (Z.of_nat (length F) - 1 - Z.of_nat k) = nth k F e0.

Lemma mst_top : forall q e F, mst q (e :: F) -> ent q (mq_sp q - 1) = e.
Proof.
  intros q e F [SP M]. rewrite SP. specialize (M 0%nat ltac:(cbn; lia)). cbn [nth] in M.
  replace (Z.of_nat (length (e :: F)) - 1 - Z.of_nat 0) with (Z.of_nat (length (e :: F)) - 1) in M by lia. exact M.
Qed.

(* [comment removed for export] *)
Lemma mst_pop : forall q e F a1 nlo nhi nd b x,
  mst q (e :: F) ->
  mst (MQS a1 (mq_sp q - 1) (mq_slo q) (mq_shi q) (mq_sd q) nlo nhi nd b x) F.
Proof.
  intros q e F a1 nlo nhi nd b x [SP M]. split; cbn [mq_sp mq_slo mq_shi mq_sd].
  - rewrite SP. cbn [length]. lia.
  - intros k Hk. specialize (M (S k) ltac:(cbn; lia)). cbn [nth] in M. unfold ent in *. cbn [mq_slo mq_shi mq_sd].
    replace (Z.of_nat (length F) - 1 - Z.of_nat k) with (Z.of_nat (length (e :: F)) - 1 - Z.of_nat (S k)) by (cbn [length]; lia).
    exact M.
Qed.

Lemma mst_push : forall q F lo hi d, mst q F -> mst (mpush q lo hi d) ((lo, hi, d) :: F).
Proof.
  intros q F lo hi d [SP M]. split; unfold mpush; cbn [mq_sp mq_slo mq_shi mq_sd length].
  - lia.
  - intros k Hk. unfold ent; cbn [mq_slo mq_shi mq_sd].
    destruct k as [|k].
    + cbn [nth]. replace (Z.of_nat (S (length F)) - 1 - Z.of_nat 0) with (mq_sp q) by lia. rewrite !zget_zset_same. reflexivity.
    + cbn [nth]. rewrite !zget_zset_other by lia.
      specialize (M k ltac:(lia)). unfold ent in M.
      replace (Z.of_nat (S (length F)) - 1 - Z.of_nat (S k)) with (Z.of_nat (length F) - 1 - Z.of_nat k) by lia. exact M.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ntrip (q : mqs) (i : Z) : entry := (zget (mq_nlo q) i, zget (mq_nhi q) i, zget (mq_nd q) i).
Definition nsz (e : entry) : Z := let '(lo, hi, _) := e in hi - lo.   (* [comment removed for export] *)

Lemma mnextsize_ntrip : forall q i, mnextsize q i = nsz (ntrip q i).
Proof. intros. unfold mnextsize, ntrip, nsz. reflexivity. Qed.

Lemma ntrip_swap : forall q a b i, 0 <= a -> 0 <= b -> a <> b ->
  ntrip (mnextswap q a b) i = if i =? a then ntrip q b else if i =? b then ntrip q a else ntrip q i.
Proof.
  intros q a b i Ha Hb Hab. unfold mnextswap, ntrip; cbn [mq_nlo mq_nhi mq_nd].
  rewrite !zget_zset. destruct (Z.eqb_spec i b) as [->|NB]; destruct (Z.eqb_spec b a) as [E|NE]; try lia.
  - replace (b =? b) with true by (symmetry; apply Z.eqb_refl). reflexivity.
  - destruct (Z.eqb_spec i a); reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition net (q : mqs) : mqs :=
  let q := if mnextsize q 0 <? mnextsize q 1 then mnextswap q 0 1 else q in
  let q := if mnextsize q 1 <? mnextsize q 2 then mnextswap q 1 2 else q in
  if mnextsize q 0 <? mnextsize q 1 then mnextswap q 0 1 else q.

Definition perm3 (x y z a b c : entry) : Prop :=
  (x = a /\ y = b /\ z = c) \/ (x = a /\ y = c /\ z = b) \/ (x = b /\ y = a /\ z = c) \/
  (x = b /\ y = c /\ z = a) \/ (x = c /\ y = a /\ z = b) \/ (x = c /\ y = b /\ z = a).

Ltac p3 := first [ solve [repeat split; reflexivity] | solve [left; repeat split; reflexivity] | right; p3 ].
Lemma net_spec : forall q,
  perm3 (ntrip (net q) 0) (ntrip (net q) 1) (ntrip (net q) 2) (ntrip q 0) (ntrip q 1) (ntrip q 2) /\
  nsz (ntrip (net q) 2) <= nsz (ntrip (net q) 1) <= nsz (ntrip (net q) 0) /\
  mq_sp (net q) = mq_sp q /\ mq_slo (net q) = mq_slo q /\ mq_shi (net q) = mq_shi q /\ mq_sd (net q) = mq_sd q /\
  mq_a1 (net q) = mq_a1 q /\ mq_budget (net q) = mq_budget q /\ mq_exit (net q) = mq_exit q.
Proof.
  intros q. unfold net.
  destruct (Z.ltb_spec (mnextsize q 0) (mnextsize q 1)) as [C1|C1];
  match goal with |- context [if mnextsize ?qa 1 <? mnextsize ?qa 2 then _ else _] => set (q1 := qa) in * end;
  destruct (Z.ltb_spec (mnextsize q1 1) (mnextsize q1 2)) as [C2|C2];
  match goal with |- context [if mnextsize ?qb 0 <? mnextsize ?qb 1 then _ else _] => set (q2 := qb) in * end;
  destruct (Z.ltb_spec (mnextsize q2 0) (mnextsize q2 1)) as [C3|C3];
  subst q1 q2; rewrite !mnextsize_ntrip in *; rewrite ?ntrip_swap in * by lia; rewrite ?ntrip_swap by lia; cbn [Z.eqb Pos.eqb] in *;
  (split; [unfold perm3; p3 | split; [lia | unfold mnextswap; cbn; repeat split; reflexivity]]).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Ghost.
  Variables (l0 r0 d0 : Z).
  Let N0 := r0 - l0 + 1.

  Definition sane (e : entry) : Prop := l0 <= elo e /\ elo e <= ehi e + 1 /\ ehi e <= r0 /\ d0 <= ed e <= 15.

  Fixpoint asc (es : list entry) : Prop :=
    match es with
    | e1 :: ((e2 :: _) as r) => esz e1 <= esz e2 /\ asc r
    | _ => True
    end.
  Fixpoint pairsum (p : Z) (es : list entry) : Prop :=
    match es with
    | [] => True
    | e :: r => (forall e', In e' r -> esz e + esz e' <= p) /\ pairsum p r
    end.
  Definition grp_ok (g : Z * list entry) : Prop :=
    let '(p, es) := g in
    es <> [] /\ (length es <= 3)%nat /\ asc es /\ pairsum p es /\
    (forall e, In e es -> 0 <= esz e <= p /\ sane e) /\ p <= N0.
  Fixpoint chain (G : list (Z * list entry)) : Prop :=
    match G with
    | (p1, _) :: (((p2, _) :: _) as r) => 2 * p1 <= p2 /\ 21 <= p1 /\ chain r
    | _ => True
    end.
  Definition flat (G : list (Z * list entry)) : list entry := concat (map snd G).

  Definition GI (G : list (Z * list entry)) (q : mqs) : Prop :=
    mst q (flat G) /\ Forall grp_ok G /\ chain G.

  (* [comment removed for export] *)
  Lemma chain_tl : forall g G, chain (g :: G) -> chain G.
  Proof. intros g [|g' G] H; [exact I|]. destruct g as [p1 es1], g' as [p2 es2]. cbn in H. cps_destruct H as (_ & _ & H). exact H. Qed.

  Lemma chain_bound : forall G p es, chain ((p, es) :: G) -> Forall grp_ok ((p, es) :: G) ->
    p * 2 ^ (Z.of_nat (length G)) <= N0 * 1 /\ (G <> [] -> 21 <= p).
  Proof.
    induction G as [|[p2 es2] G IH]; intros p es CH FA.
    - cbn [length Z.of_nat Z.pow]. inversion FA as [|x l G1 _]. cps_destruct G1 as (_ & _ & _ & _ & _ & PN). split; [lia|congruence].
    - cbn [chain] in CH. fold (chain ((p2, es2) :: G)) in CH. cps_destruct CH as (C1 & C2 & CH).
      inversion FA as [|x l _ FA']. subst.
      destruct (IH p2 es2 CH FA') as [B _].
      replace (Z.of_nat (length ((p2, es2) :: G))) with (Z.succ (Z.of_nat (length G))) by (cbn [length]; lia).
      rewrite Z.pow_succ_r by lia. split; [|intros; lia].
      assert (0 < 2 ^ Z.of_nat (length G)) by (apply Z.pow_pos_nonneg; lia). nia.
  Qed.

  Lemma flat_length : forall G, Forall grp_ok G -> (length (flat G) <= 3 * length G)%nat.
  Proof.
    unfold flat. induction G as [|[p es] G IH]; intros FA; cbn; [lia|].
    inversion FA as [|x l G1 FA']; subst. rewrite length_app. cps_destruct G1 as (_ & L & _). specialize (IH FA'). cbn in IH. lia.
  Qed.

  Lemma GI_depth : forall G q, GI G q -> N0 < 21 * 2 ^ 16 -> mq_sp q <= 51.
  Proof.
    (intros G q; cps_intros (M & FA & CH); intros HN). destruct M as [SP _]. rewrite SP.
    pose proof (flat_length G FA).
    destruct G as [|[p es] G]; [cbn; lia|].
    destruct (chain_bound G p es CH FA) as [B P21].
    assert (length G <= 16)%nat.
    { destruct G as [|g G']; [cbn; lia|]. specialize (P21 ltac:(discriminate)).
      destruct (Nat.le_gt_cases (length (g :: G')) 16) as [|GT]; [assumption|exfalso].
      assert (2 ^ 16 <= 2 ^ Z.of_nat (length (g :: G'))) by (apply Z.pow_le_mono_r; lia). nia. }
    cbn [length] in H. lia.
  Qed.

  (* [comment removed for export] *)
  Definition ephi (e : entry) : Z := (16 - ed e) * 3 * esz e + 1.
  Fixpoint lphi (F : list entry) : Z := match F with [] => 0 | e :: r => ephi e + lphi r end.
  Lemma lphi_app : forall F1 F2, lphi (F1 ++ F2) = lphi F1 + lphi F2.
  Proof. induction F1; intros; cbn; [lia|]. rewrite IHF1. lia. Qed.
  (* [comment removed for export] *)

  Lemma mmed3_in : forall a b c, mmed3 a b c = a \/ mmed3 a b c = b \/ mmed3 a b c = c.
  Proof.
    intros a b c. unfold mmed3. destruct (b <? a); destruct (c <? _); try destruct (c <? _); tauto.
  Qed.

  Lemma chain_cons_iff : forall p es G, chain ((p, es) :: G) <-> match G with [] => True | (p2, _) :: _ => 2 * p <= p2 /\ 21 <= p /\ chain G end.
  Proof. intros p es [|[p2 es2] G]; cbn; tauto. Qed.

  (* [comment removed for export] *)
  Lemma GI_pop : forall G q e F, GI G q -> flat G = e :: F ->
    exists G1 p, flat G1 = F /\ Forall grp_ok G1 /\ chain G1 /\ 0 <= esz e <= p /\ sane e /\ p <= N0 /\
      (* [comment removed for export] *)
      match G1 with [] => True | (p1, _) :: _ => 2 * esz e <= p1 end.
  Proof.
    (intros G q e F; cps_intros (M & FA & CH); intros HF).
    destruct G as [|[p es] G']; [cbn in HF; discriminate|].
    inversion FA as [|x l GOK FA']; subst.
    cps_destruct GOK as (NE & LEN & ASC & PS & EL & PN).
    destruct es as [|e' es']; [congruence|]. unfold flat in HF; cbn in HF. injection HF as HF1 HF2. subst e'.
    destruct es' as [|e2 es2].
    - (* [comment removed for export] *)
      exists G', p. cbn in HF2. split; [exact HF2|]. split; [exact FA'|]. split; [exact (chain_tl _ _ CH)|].
      destruct (EL e ltac:(left; reflexivity)) as [SZ SN]. split; [exact SZ|]. split; [exact SN|]. split; [exact PN|].
      destruct G' as [|[p1 es1] G'']; [exact I|]. cps_pose (proj1 (chain_cons_iff p [e] ((p1, es1) :: G'')) CH) as (C1 & C2 & _). lia.
    - exists ((p, e2 :: es2) :: G'), p. split; [unfold flat; cbn; cbn in HF2; exact HF2|]. split.
      + constructor; [|exact FA']. split; [discriminate|]. split; [cbn in LEN |- *; lia|]. split; [exact (proj2 ASC)|].
        split; [exact (proj2 PS)|]. split; [intros x Hx; apply EL; right; exact Hx| exact PN].
      + split; [apply (proj2 (chain_cons_iff p (e2 :: es2) G')); apply (proj1 (chain_cons_iff p (e :: e2 :: es2) G')); exact CH|].
        destruct (EL e ltac:(left; reflexivity)) as [SZ SN]. split; [exact SZ|]. split; [exact SN|]. split; [exact PN|].
        destruct ASC as [A1 _]. destruct PS as [P1 _]. specialize (P1 e2 ltac:(left; reflexivity)). lia.
  Qed.
End Ghost.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition TOPlo (q : mqs) : Z := zget (mq_slo q) (mq_sp q - 1).
Definition TOPhi (q : mqs) : Z := zget (mq_shi q) (mq_sp q - 1).
Definition TOPd (q : mqs) : Z := zget (mq_sd q) (mq_sp q - 1).
Definition MED (a2 : zarr) (q : mqs) : Z :=
  let a1 := mq_a1 q in let lo := TOPlo q in let hi := TOPhi q in let d := TOPd q in
  mmed3 (rd8 a2 (rd32 a1 lo + d)) (rd8 a2 (rd32 a1 hi + d)) (rd8 a2 (rd32 a1 (Z.shiftr (lo + hi) 1) + d)).
Definition PART (a2 : zarr) (q : mqs) : mpart :=
  let lo := TOPlo q in let hi := TOPhi q in let sz := Z.to_nat (hi - lo + 1) in
  mpart_loop (S sz) sz a2 (TOPd q) (MED a2 q) (MP (mq_a1 q) lo hi lo hi).
Definition LEAF (a2 : zarr) (qoff nblock : Z) (q : mqs) : mqs :=
  let '(a1, budget) := mainSimpleSort (mq_a1 q) a2 qoff nblock (TOPlo q) (TOPhi q) (TOPd q) (mq_budget q) in
  MQS a1 (mq_sp q - 1) (mq_slo q) (mq_shi q) (mq_sd q) (mq_nlo q) (mq_nhi q) (mq_nd q) budget (budget <? 0).
Definition Q1 (q : mqs) (p : mpart) : mqs :=
  MQS (mp_a1 p) (mq_sp q - 1) (mq_slo q) (mq_shi q) (mq_sd q) (mq_nlo q) (mq_nhi q) (mq_nd q) (mq_budget q) false.
Definition A1V (q : mqs) (p : mpart) : zarr :=
  let lo := TOPlo q in let hi := TOPhi q in
  let n := mmin (mp_ltLo p - lo) (mp_unLo p - mp_ltLo p) in
  let a1 := mvswap (S (Z.to_nat n)) (mp_a1 p) lo (mp_unLo p - n) n in
  let m := mmin (hi - mp_gtHi p) (mp_gtHi p - mp_unHi p) in
  mvswap (S (Z.to_nat m)) a1 (mp_unLo p) (hi - m + 1) m.
Definition KN (q : mqs) (p : mpart) : Z := TOPlo q + mp_unLo p - mp_ltLo p - 1.
Definition KM (q : mqs) (p : mpart) : Z := TOPhi q - (mp_gtHi p - mp_unHi p) + 1.
Definition Q2 (q : mqs) (p : mpart) : mqs :=
  let lo := TOPlo q in let hi := TOPhi q in let d := TOPd q in let n := KN q p in let m := KM q p in
  MQS (A1V q p) (mq_sp q - 1) (mq_slo q) (mq_shi q) (mq_sd q)
      (zset (zset (zset (mq_nlo q) 0 lo) 1 m) 2 (n + 1))
      (zset (zset (zset (mq_nhi q) 0 n) 1 hi) 2 (m - 1))
      (zset (zset (zset (mq_nd q) 0 d) 1 d) 2 (d + 1)) (mq_budget q) false.
Definition PUSH3 (q : mqs) : mqs :=
  let q3 := mpush q (zget (mq_nlo q) 0) (zget (mq_nhi q) 0) (zget (mq_nd q) 0) in
  let q3 := mpush q3 (zget (mq_nlo q3) 1) (zget (mq_nhi q3) 1) (zget (mq_nd q3) 1) in
  mpush q3 (zget (mq_nlo q3) 2) (zget (mq_nhi q3) 2) (zget (mq_nd q3) 2).
Definition ITER (a2 : zarr) (qoff nblock : Z) (q : mqs) : mqs :=
  if (TOPhi q - TOPlo q <? 20) || (14 <? TOPd q) then LEAF a2 qoff nblock q
  else let p := PART a2 q in
       if mp_gtHi p <? mp_ltLo p then mpush (Q1 q p) (TOPlo q) (TOPhi q) (TOPd q + 1)
       else PUSH3 (net (Q2 q p)).

Lemma mqs_iter_ITER : forall a2 qoff nblock q, mqs_iter a2 qoff nblock q = ITER a2 qoff nblock q.
Proof.
  (* [comment removed for export] *)
  intros. exact_no_check (@eq_refl mqs (mqs_iter a2 qoff nblock q)).
Qed.

(* [comment removed for export] *)

Lemma mst_push3 : forall q F, mst q F ->
  let q3 := mpush q (zget (mq_nlo q) 0) (zget (mq_nhi q) 0) (zget (mq_nd q) 0) in
  let q4 := mpush q3 (zget (mq_nlo q3) 1) (zget (mq_nhi q3) 1) (zget (mq_nd q3) 1) in
  let q5 := mpush q4 (zget (mq_nlo q4) 2) (zget (mq_nhi q4) 2) (zget (mq_nd q4) 2) in
  mst q5 (ntrip q 2 :: ntrip q 1 :: ntrip q 0 :: F).
Proof.
  intros q F M. cbn zeta. exact (mst_push _ _ _ _ _ (mst_push _ _ _ _ _ (mst_push _ _ _ _ _ M))).
Qed.

Section Step.
  Variables (l0 r0 d0 : Z) (a2 : zarr) (qoff nblock : Z).
  Hypothesis HD0 : 0 <= d0 <= 14.
  Let N0 := r0 - l0 + 1.

  Lemma mqs_iter_GI : forall G q, GI l0 r0 d0 G q -> 0 < mq_sp q ->
    exists G', GI l0 r0 d0 G' (mqs_iter a2 qoff nblock q) /\ lphi (flat G') <= lphi (flat G) - 1.
  Proof.
    intros G q GIq Hsp.
    destruct (flat G) as [|e F] eqn:HF.
    { destruct GIq as ([SP _] & _). rewrite HF in SP. cbn in SP. lia. }
    cps_pose GIq as (M & FA & CH). rewrite HF in M.
    pose proof (mst_top q e F M) as TOP.
    cps_destruct (GI_pop l0 r0 d0 G q e F GIq HF) as (G1 & p & F1 & FA1 & CH1 & SZ & SN & PN & NXT).
    destruct e as [[lo hi] d]. unfold ent in TOP. injection TOP as Td Thi Tlo.
    unfold sane, elo, ehi, ed in SN. unfold esz in SZ, NXT.
    rewrite mqs_iter_ITER. unfold ITER. unfold TOPlo, TOPhi, TOPd. rewrite Tlo, Thi, Td.
    assert (PHE : 1 <= ephi (lo, hi, d)). { unfold ephi, ed, esz. nia. }
    destruct (Sumbool.sumbool_of_bool ((hi - lo <? 20) || (14 <? d))) as [LF|NODE]; rewrite ?LF, ?NODE.
    { (* [comment removed for export] *)
      unfold LEAF. unfold TOPlo, TOPhi, TOPd. rewrite Tlo, Thi, Td.
      destruct (mainSimpleSort (mq_a1 q) a2 qoff nblock lo hi d (mq_budget q)) as [a1' budget'].
      exists G1. split; [|rewrite F1; cbn [lphi]; lia]. split; [|split; [exact FA1|exact CH1]].
      rewrite F1. eapply mst_pop. exact M. }
    apply Bool.orb_false_iff in NODE. destruct NODE as [N1 N2]. apply Z.ltb_ge in N1. apply Z.ltb_ge in N2.
    set (med := MED a2 q).
    assert (HX : exists x, lo <= x <= hi /\ med = rd8 a2 (rd32 (mq_a1 q) x + d)).
    { subst med. unfold MED, TOPlo, TOPhi, TOPd. rewrite Tlo, Thi, Td.
      pose proof (mmed3_in (rd8 a2 (rd32 (mq_a1 q) lo + d)) (rd8 a2 (rd32 (mq_a1 q) hi + d)) (rd8 a2 (rd32 (mq_a1 q) (Z.shiftr (lo + hi) 1) + d))) as MM.
      assert (MID : lo <= Z.shiftr (lo + hi) 1 <= hi).
      { rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2. split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia]. }
      destruct MM as [MM|[MM|MM]]; [exists lo | exists hi | exists (Z.shiftr (lo + hi) 1)]; split; try exact MM; lia. }
    cps_destruct HX as (x & Hx & Hmed).
    pose proof (mq_part a2 d med lo hi (mq_a1 q) x Hx ltac:(unfold key; exact Hmed)) as PP. cbn zeta in PP.
    assert (PPdef : PART a2 q = mpart_loop (S (Z.to_nat (hi - lo + 1))) (Z.to_nat (hi - lo + 1)) a2 d med (MP (mq_a1 q) lo hi lo hi)).
    { unfold PART. fold med. unfold TOPlo, TOPhi, TOPd. rewrite Tlo, Thi, Td. reflexivity. }
    rewrite <- PPdef in PP. set (pp := PART a2 q) in *.
    cps_destruct PP as (A & B & C & D & E & Fq).
    destruct (Z.ltb_spec (mp_gtHi pp) (mp_ltLo pp)) as [ALLEQ|SPLIT].
    { (* [comment removed for export] *)
      exists ((hi - lo + 1, [(lo, hi, d + 1)]) :: G1). split.
      - split; [|split].
        + unfold flat; cbn [map concat app snd]. fold (flat G1). rewrite F1. apply mst_push. unfold Q1. eapply mst_pop. exact M.
        + constructor; [|exact FA1]. split; [discriminate|]. split; [cbn; lia|]. split; [exact I|]. split; [cbn; split; [intros; tauto|exact I]|].
          split; [|unfold esz in *; lia]. intros e' [<-|[]]. unfold esz, sane, elo, ehi, ed; cbn. lia.
        + apply (proj2 (chain_cons_iff (hi - lo + 1) [(lo, hi, d + 1)] G1)).
          destruct G1 as [|[p1 es1] G1']; [exact I|]. split; [lia|]. split; [lia| exact CH1].
      - unfold flat; cbn [map concat app lphi snd]. fold (flat G1). rewrite F1. cbn [lphi app]. unfold ephi, ed, esz. nia. }
    (* [comment removed for export] *)
    set (a := mp_unLo pp - mp_ltLo pp) in *. set (c := mp_gtHi pp - mp_unHi pp) in *.
    set (nn := lo + mp_unLo pp - mp_ltLo pp - 1). set (mm := hi - c + 1).
    set (q2 := Q2 q pp).
    cps_pose (net_spec q2) as (PERM & SORT & Fsp & Fslo & Fshi & Fsd & _).
    set (q2' := net q2) in *.
    assert (Q2f : mq_sp q2 = mq_sp q - 1 /\ mq_slo q2 = mq_slo q /\ mq_shi q2 = mq_shi q /\ mq_sd q2 = mq_sd q) by (subst q2; unfold Q2; cbn; repeat split; reflexivity).
    assert (T0 : ntrip q2 0 = (lo, nn, d)). { unfold ntrip; subst q2; unfold Q2, KN, KM, TOPlo, TOPhi, TOPd; cbn [mq_nlo mq_nhi mq_nd]. rewrite ?Tlo, ?Thi, ?Td. rewrite !zget_zset. cbn. rewrite ?Tlo, ?Thi, ?Td. subst nn. reflexivity. }
    assert (T1 : ntrip q2 1 = (mm, hi, d)). { unfold ntrip; subst q2; unfold Q2, KN, KM, TOPlo, TOPhi, TOPd; cbn [mq_nlo mq_nhi mq_nd]. rewrite ?Tlo, ?Thi, ?Td. rewrite !zget_zset. cbn. rewrite ?Tlo, ?Thi, ?Td. subst mm c. reflexivity. }
    assert (T2 : ntrip q2 2 = (nn + 1, mm - 1, d + 1)). { unfold ntrip; subst q2; unfold Q2, KN, KM, TOPlo, TOPhi, TOPd; cbn [mq_nlo mq_nhi mq_nd]. rewrite ?Tlo, ?Thi, ?Td. rewrite !zget_zset. cbn. rewrite ?Tlo, ?Thi, ?Td. subst nn mm c. reflexivity. }
    rewrite T0, T1, T2 in PERM.
    set (t0 := ntrip q2' 0) in *. set (t1 := ntrip q2' 1) in *. set (t2 := ntrip q2' 2) in *.
    (* [comment removed for export] *)
    assert (AC : 0 <= a /\ 0 <= c /\ a + c <= hi - lo) by (subst a c; lia).
    assert (P3 : forall P : entry -> Prop, P (lo, nn, d) -> P (mm, hi, d) -> P (nn + 1, mm - 1, d + 1) -> P t0 /\ P t1 /\ P t2).
    { intros P X Y W. destruct PERM as [K|[K|[K|[K|[K|K]]]]]; cps_destruct K as (-> & -> & ->); tauto. }
    assert (SUM : esz t0 + esz t1 + esz t2 = hi - lo + 1).
    { destruct PERM as [K|[K|[K|[K|[K|K]]]]]; cps_destruct K as (-> & -> & ->); unfold esz; subst nn mm; lia. }
    cps_destruct (P3 (fun e => 0 <= esz e /\ sane l0 r0 d0 e)) as (S0 & S1 & S2).
    { unfold esz, sane, elo, ehi, ed. subst nn. lia. }
    { unfold esz, sane, elo, ehi, ed. subst mm. lia. }
    { unfold esz, sane, elo, ehi, ed. subst nn mm. lia. }
    assert (NSZ : forall e, nsz e = esz e - 1) by (intros [[u v] w]; unfold nsz, esz; lia).
    rewrite !NSZ in SORT.
    exists ((hi - lo + 1, [t2; t1; t0]) :: G1). split.
    - split; [|split].
      + unfold flat; cbn [map concat app snd]. fold (flat G1). rewrite F1.
        cps_destruct Q2f as (Qsp & Qslo & Qshi & Qsd).
        assert (M2' : mst q2' F).
        { split; [rewrite Fsp, Qsp; destruct M as [SP _]; rewrite SP; cbn [length]; lia|].
          intros k Hk. unfold ent. rewrite Fslo, Fshi, Fsd, Qslo, Qshi, Qsd.
          pose proof (mst_pop q (lo, hi, d) F (mq_a1 q) (mq_nlo q) (mq_nhi q) (mq_nd q) (mq_budget q) false M) as [_ MP'].
          specialize (MP' k Hk). unfold ent in MP'. cbn [mq_slo mq_shi mq_sd] in MP'. exact MP'. }
        unfold PUSH3. exact (mst_push3 q2' F M2').
      + constructor; [|exact FA1]. split; [discriminate|]. split; [cbn; lia|]. split; [cbn [asc]; lia|].
        pose proof (proj1 S0) as Z0. pose proof (proj1 S1) as Z1. pose proof (proj1 S2) as Z2.
        split. { cbn [pairsum]. repeat split; intros e' Hin; cbn [In] in Hin; repeat (destruct Hin as [Hin|Hin]); subst; lia. }
        split; [| lia].
        assert (EACH : forall e', e' = t2 \/ e' = t1 \/ e' = t0 -> 0 <= esz e' <= hi - lo + 1 /\ sane l0 r0 d0 e').
        { intros e' [->|[->| ->]]; (split; [lia|]); [exact (proj2 S2)|exact (proj2 S1)|exact (proj2 S0)]. }
        intros e' Hin. apply EACH. cbn [In] in Hin. intuition.
      + apply (proj2 (chain_cons_iff (hi - lo + 1) [t2; t1; t0] G1)).
        destruct G1 as [|[p1 es1] G1']; [exact I|]. split; [lia|]. split; [lia| exact CH1].
    - unfold flat; cbn [map concat app lphi snd]. fold (flat G1). rewrite F1. cbn [lphi app].
      destruct S0 as [Z0 [_ [_ [_ D0']]]]. destruct S1 as [Z1 [_ [_ [_ D1']]]]. destruct S2 as [Z2 [_ [_ [_ D2']]]].
      (* [comment removed for export] *)
      destruct PERM as [K|[K|[K|[K|[K|K]]]]]; cps_destruct K as (K0 & K1 & K2); subst t0 t1 t2; rewrite K0, K1, K2 in *;
        unfold ephi, ed, esz in *; subst nn mm; nia.
  Qed.
End Step.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mqs_loop_S : forall f a2 qoff nb q, mqs_loop (S f) a2 qoff nb q =
  (if (0 <? mq_sp q) && negb (mq_exit q) then mqs_loop f a2 qoff nb (mqs_iter a2 qoff nb q) else q).
Proof. reflexivity. Qed.

Section Main.
  Variables (l0 r0 d0 : Z) (a2 : zarr) (qoff nblock : Z).
  Hypothesis HD0 : 0 <= d0 <= 14.
  Hypothesis HLR : l0 <= r0.
  Hypothesis HN : r0 - l0 + 1 < 21 * 2 ^ 16.

  Lemma mqs_loop_GI : forall v G q, GI l0 r0 d0 G q -> exists G', GI l0 r0 d0 G' (mqs_loop v a2 qoff nblock q).
  Proof.
    induction v as [|v IH]; intros G q GIq; [exists G; exact GIq|].
    rewrite mqs_loop_S. destruct (Z.ltb_spec 0 (mq_sp q)) as [P|NP]; cbn [andb]; [|exists G; exact GIq].
    destruct (mq_exit q); cbn [negb]; [exists G; exact GIq|].
    cps_destruct (mqs_iter_GI l0 r0 d0 a2 qoff nblock HD0 G q GIq P) as (G' & GI' & _). apply (IH G'). exact GI'.
  Qed.

  Lemma lphi_len : forall G, Forall (grp_ok l0 r0 d0) G -> Z.of_nat (length (flat G)) <= lphi (flat G).
  Proof.
    unfold flat. induction G as [|[p es] G IH]; intros FA; cbn; [lia|].
    inversion FA as [|x l G1 FA']; subst. rewrite lphi_app, length_app. specialize (IH FA'). cbn in IH.
    cps_destruct G1 as (_ & _ & _ & _ & EL & _).
    assert (Z.of_nat (length es) <= lphi es); [|lia].
    clear -EL. induction es as [|e es IH2]; cbn [length lphi]; [lia|].
    assert (1 <= ephi e). { destruct (EL e ltac:(left; reflexivity)) as [SZ [_ [_ [_ D]]]]. unfold ephi. nia. }
    assert (Z.of_nat (length es) <= lphi es) by (apply IH2; intros; apply EL; right; assumption). lia.
    Unshelve. all: exact 0.
  Qed.

  Lemma mqs_loop_term : forall f G q, GI l0 r0 d0 G q -> lphi (flat G) <= Z.of_nat f ->
    mq_sp (mqs_loop f a2 qoff nblock q) = 0 \/ mq_exit (mqs_loop f a2 qoff nblock q) = true.
  Proof.
    induction f as [|f IH]; intros G q GIq PH.
    - cbn [mqs_loop]. left. cps_destruct GIq as ([SP _] & FA & _). pose proof (lphi_len G FA). rewrite SP. lia.
    - rewrite mqs_loop_S. destruct (Z.ltb_spec 0 (mq_sp q)) as [P|NP]; cbn [andb].
      + destruct (mq_exit q) eqn:EX; cbn [negb]; [right; exact EX|].
        cps_destruct (mqs_iter_GI l0 r0 d0 a2 qoff nblock HD0 G q GIq P) as (G' & GI' & PH'). apply (IH G'); [exact GI'| lia].
      + left. cps_destruct GIq as ([SP _] & _ & _). lia.
  Qed.

  Theorem mqs_ok : forall a1 slo shi sd nlo nhi nd budget,
    let q0 := mpush (MQS a1 0 slo shi sd nlo nhi nd budget false) l0 r0 d0 in
    (forall v, let q := mqs_loop v a2 qoff nblock q0 in
       mq_sp q <= 51 /\
       (0 < mq_sp q -> let '(lo, hi, d) := ent q (mq_sp q - 1) in l0 <= lo /\ lo <= hi + 1 /\ hi <= r0 /\ d0 <= d <= 15)) /\
    (let q := mqs_loop (mqs_fuel l0 r0) a2 qoff nblock q0 in mq_sp q = 0 \/ mq_exit q = true).
  Proof.
    intros a1 slo shi sd nlo nhi nd budget. cbn zeta.
    set (q0 := mpush _ l0 r0 d0).
    assert (GI0 : GI l0 r0 d0 [(r0 - l0 + 1, [(l0, r0, d0)])] q0).
    { split; [|split].
      - unfold flat; cbn [map concat app snd]. subst q0. apply mst_push. split; [reflexivity| intros k Hk; cbn in Hk; lia].
      - constructor; [|constructor]. split; [discriminate|]. split; [cbn; lia|]. split; [exact I|]. split; [cbn; split; [intros; tauto| exact I]|].
        split; [|lia]. intros e [<-|[]]. unfold esz, sane, elo, ehi, ed. lia.
      - exact I. }
    split.
    - intros v. destruct (mqs_loop_GI v _ q0 GI0) as (G & GIq).
      split; [apply (GI_depth l0 r0 d0 G); [exact GIq| exact HN]|].
      intros P. cps_pose GIq as (M & FA & CH).
      destruct (flat G) as [|e F] eqn:HF. { destruct M as [SP _]. cbn in SP. lia. }
      pose proof (mst_top _ e F M) as TOP. rewrite TOP.
      cps_destruct (GI_pop l0 r0 d0 G _ e F GIq HF) as (G1 & p & _ & _ & _ & SZ & SN & _).
      destruct e as [[lo hi] d]. unfold sane, elo, ehi, ed in SN. lia.
    - apply (mqs_loop_term (mqs_fuel l0 r0) _ q0 GI0). unfold flat; cbn [map concat app snd lphi]. unfold ephi, ed, esz, mqs_fuel. nia.
  Qed.
End Main.
