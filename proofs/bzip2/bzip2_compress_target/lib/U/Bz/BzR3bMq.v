(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCMem BzArrD BzCSortF. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSortM. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCLemmasFs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCLemmasMs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCPermF BzCPermF2.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSewA.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSewA BzCQsortM1 BzCQsortM2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR2Theory. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzR3gtu. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR3aQs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzR3bMs.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCSortF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSortM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasFs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCLemmasMs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCPermF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCPermF2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewA.BzCBudget OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewA OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCQsortM1 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCQsortM2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR2Theory OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzR3gtu OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR3aQs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzR3bMs.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

Lemma mmin_fmin : forall a b, mmin a b = fmin a b.
Proof. reflexivity. Qed.

Lemma mvswap_fvswap : forall f a p1 p2 n, mvswap f a p1 p2 n = fvswap f a p1 p2 n.
Proof.
  induction f as [|f IH]; intros; [reflexivity|]. rewrite mvswap_S, fvswap_S, mswap_fswap, IH. reflexivity.
Qed.

Section S2.
  Variables (a2 : zarr) (qoff n : Z).
  Hypothesis Hn : 34 <= n.
  Hypothesis Hn9 : n <= 900000.
  Hypothesis OVB : forall i, 0 <= i < 34 -> rd8 a2 (n + i) = rd8 a2 i.
  Hypothesis OVQ : forall i, 0 <= i < 34 -> qrd a2 qoff (n + i) = qrd a2 qoff i.
  Hypothesis QIw : forall p p', 0 <= p < n -> 0 <= p' < n -> rd8 a2 p = rd8 a2 p' ->
    qrd a2 qoff p < qrd a2 qoff p' -> lexle (rot (blk a2 n) (Z.to_nat p)) (rot (blk a2 n) (Z.to_nat p')).

  Local Notation ROT := (rotz a2 n).
  Local Notation EQ := (EQB a2 n).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition bkey (d v : Z) : Z := rd8 a2 (v + d).

  Lemma bkey_bt : forall d v, 0 <= d <= 15 -> 0 <= v < n -> bkey d v = bt a2 n (v + d).
  Proof. intros d v Hd Hv. unfold bkey. apply (rd8_cyc a2 n Hn OVB). lia. Qed.

  Lemma byte_lt_rot : forall d x y, 0 <= d <= 15 -> 0 <= x < n -> 0 <= y < n -> EQ x y d ->
    bkey d x < bkey d y -> lexle (ROT x) (ROT y).
  Proof.
    intros d x y Hd Hx Hy E L. rewrite !bkey_bt in L by lia.
    pose proof (sound_byte a2 n Hn x y d ltac:(lia) E ltac:(lia)) as [_ SF]. apply SF.
    apply Z.ltb_ge. lia.
  Qed.

  Lemma byte_eq_EQB : forall d x y, 0 <= d <= 15 -> 0 <= x < n -> 0 <= y < n -> EQ x y d ->
    bkey d x = bkey d y -> EQ x y (d + 1).
  Proof.
    intros d x y Hd Hx Hy E K j Hj. destruct (Z.eq_dec j d) as [->|N]; [|apply E; lia].
    rewrite !bkey_bt in K by lia. exact K.
  Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section MPK.
    Variables (d med lo hi : Z).
    Hypothesis Hlo : 0 <= lo.
    Hypothesis Hhi : hi < n.

    Let K (a1 : zarr) (x : Z) : Z := bkey d (rd32 a1 x).

    Definition MPK (p : mpart) : Prop :=
      lo <= mp_ltLo p /\ mp_ltLo p <= mp_unLo p /\ mp_unLo p <= mp_unHi p + 1 /\ mp_unHi p <= mp_gtHi p /\ mp_gtHi p <= hi /\
      fm_perm (mp_a1 p) n /\
      (forall x, lo <= x < mp_ltLo p -> K (mp_a1 p) x = med) /\
      (forall x, mp_ltLo p <= x < mp_unLo p -> K (mp_a1 p) x < med) /\
      (forall x, mp_unHi p < x <= mp_gtHi p -> med < K (mp_a1 p) x) /\
      (forall x, mp_gtHi p < x <= hi -> K (mp_a1 p) x = med).

    Lemma K_swap_a : forall a1 a b, fm_perm a1 n -> 0 <= a < n -> 0 <= b < n -> K (mswap a1 a b) a = K a1 b.
    Proof. intros a1 a b PM Ha Hb. unfold K. rewrite mswap_fswap, rd32_fswap_a; [reflexivity| |]; [pose proof (proj1 PM a Ha)|pose proof (proj1 PM b Hb)]; lia. Qed.
    Lemma K_swap_b : forall a1 a b, fm_perm a1 n -> 0 <= a < n -> K (mswap a1 a b) b = K a1 a.
    Proof. intros a1 a b PM Ha. unfold K. rewrite mswap_fswap, rd32_fswap_b; [reflexivity|]. pose proof (proj1 PM a Ha). lia. Qed.
    Lemma K_swap_o : forall a1 a b x, x <> a -> x <> b -> K (mswap a1 a b) x = K a1 x.
    Proof. intros. unfold K. rewrite mswap_fswap, rd32_fswap_other by assumption. reflexivity. Qed.
    Lemma perm_mswap : forall a1 a b, fm_perm a1 n -> 0 <= a < n -> 0 <= b < n -> fm_perm (mswap a1 a b) n.
    Proof. intros. rewrite mswap_fswap. apply fm_perm_fswap; try assumption. lia. Qed.

    Lemma mpk_lo : forall f p,
      MPK p -> (Z.to_nat (mp_unHi p - mp_unLo p + 1) < f)%nat ->
      let p' := mpart_lo f a2 d med p in
      MPK p' /\ mp_unHi p' = mp_unHi p /\ mp_gtHi p' = mp_gtHi p /\ mp_unLo p <= mp_unLo p' /\
      (mp_unHi p' < mp_unLo p' \/ med < K (mp_a1 p') (mp_unLo p')).
    Proof.
      induction f as [|f IH]; intros p HP Hf; [lia|]. cbn zeta.
      rewrite mpart_lo_S. cbn zeta.
      destruct (Z.ltb_spec (mp_unHi p) (mp_unLo p)) as [LT|GE].
      { split; [exact HP|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. left; exact LT. }
      cps_destruct HP as (A & B & C & D & E & PM & K1 & K2 & K3 & K4).
      change (rd8 a2 (rd32 (mp_a1 p) (mp_unLo p) + d)) with (K (mp_a1 p) (mp_unLo p)).
      destruct (Z.eqb_spec (K (mp_a1 p) (mp_unLo p) - med) 0) as [EQ0|NE].
      - match goal with |- MPK (mpart_lo f a2 d med ?q) /\ _ => specialize (IH q) end.
        cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi] in IH.
        cps_destruct IH as (P1 & P2 & P3 & P5 & P4); [| lia |].
        { unfold MPK; cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
          split; [apply perm_mswap; try assumption; lia|].
          split. { intros x Hx. destruct (Z.eq_dec x (mp_ltLo p)) as [->|NX].
                   - rewrite K_swap_b by (try assumption; lia). lia.
                   - rewrite K_swap_o by lia. apply K1. lia. }
          split. { intros x Hx. destruct (Z.eq_dec x (mp_unLo p)) as [->|NX].
                   - destruct (Z.eq_dec (mp_ltLo p) (mp_unLo p)) as [E0|N0]; [lia|].
                     rewrite K_swap_a by (try assumption; lia). apply K2. lia.
                   - rewrite K_swap_o by lia. apply K2. lia. }
          split. { intros x Hx. rewrite K_swap_o by lia. apply K3. lia. }
          intros x Hx. rewrite K_swap_o by lia. apply K4. lia. }
        cbn [mp_unLo] in P5. split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [lia|exact P4].
      - destruct (Z.ltb_spec 0 (K (mp_a1 p) (mp_unLo p) - med)) as [GT|LE].
        + split. { unfold MPK. repeat (split; [first [lia|assumption]|]). assumption. }
          split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. right. lia.
        + match goal with |- MPK (mpart_lo f a2 d med ?q) /\ _ => specialize (IH q) end.
          cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi] in IH.
          cps_destruct IH as (P1 & P2 & P3 & P5 & P4); [| lia |].
          { unfold MPK; cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
            split; [exact PM|]. split; [exact K1|].
            split. { intros x Hx. destruct (Z.eq_dec x (mp_unLo p)) as [->|NX]; [lia|]. apply K2. lia. }
            split; [exact K3|exact K4]. }
          cbn [mp_unLo] in P5. split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [lia|exact P4].
    Qed.

    Lemma mpk_hi : forall f p,
      MPK p -> (Z.to_nat (mp_unHi p - mp_unLo p + 1) < f)%nat ->
      (mp_unHi p < mp_unLo p \/ med < K (mp_a1 p) (mp_unLo p)) ->
      let p' := mpart_hi f a2 d med p in
      MPK p' /\ mp_unLo p' = mp_unLo p /\ mp_ltLo p' = mp_ltLo p /\ mp_unHi p' <= mp_unHi p /\
      (mp_unHi p' < mp_unLo p' \/ (K (mp_a1 p') (mp_unHi p') < med /\ med < K (mp_a1 p') (mp_unLo p'))).
    Proof.
      induction f as [|f IH]; intros p HP Hf HK; [lia|]. cbn zeta.
      rewrite mpart_hi_S. cbn zeta.
      destruct (Z.ltb_spec (mp_unHi p) (mp_unLo p)) as [LT|GE].
      { split; [exact HP|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. left; exact LT. }
      destruct HK as [HK|HK]; [lia|].
      cps_destruct HP as (A & B & C & D & E & PM & K1 & K2 & K3 & K4).
      change (rd8 a2 (rd32 (mp_a1 p) (mp_unHi p) + d)) with (K (mp_a1 p) (mp_unHi p)).
      destruct (Z.eqb_spec (K (mp_a1 p) (mp_unHi p) - med) 0) as [EQ0|NE].
      - assert (NEQ : mp_unLo p <> mp_unHi p) by (intros X; rewrite X in HK; lia).
        match goal with |- MPK (mpart_hi f a2 d med ?q) /\ _ => specialize (IH q) end.
        cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi] in IH.
        cps_destruct IH as (P1 & P2 & P3 & P5 & P4); [| lia | |].
        { unfold MPK; cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
          split; [apply perm_mswap; try assumption; lia|].
          split. { intros x Hx. rewrite K_swap_o by lia. apply K1. lia. }
          split. { intros x Hx. rewrite K_swap_o by lia. apply K2. lia. }
          split. { intros x Hx. destruct (Z.eq_dec x (mp_unHi p)) as [->|NX].
                   - destruct (Z.eq_dec (mp_gtHi p) (mp_unHi p)) as [E0|N0]; [lia|].
                     rewrite K_swap_a by (try assumption; lia). apply K3. lia.
                   - rewrite K_swap_o by lia. apply K3. lia. }
          intros x Hx. destruct (Z.eq_dec x (mp_gtHi p)) as [->|NX].
          - rewrite K_swap_b by (try assumption; lia). lia.
          - rewrite K_swap_o by lia. apply K4. lia. }
        { right. rewrite K_swap_o by lia. exact HK. }
        cbn [mp_unHi] in P5. split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [lia|exact P4].
      - destruct (Z.ltb_spec (K (mp_a1 p) (mp_unHi p) - med) 0) as [LTm|GEm].
        + split. { unfold MPK. repeat (split; [first [lia|assumption]|]). assumption. }
          split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. right. lia.
        + match goal with |- MPK (mpart_hi f a2 d med ?q) /\ _ => specialize (IH q) end.
          cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi] in IH.
          cps_destruct IH as (P1 & P2 & P3 & P5 & P4); [| lia | |].
          { unfold MPK; cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
            split; [exact PM|]. split; [exact K1|]. split; [exact K2|].
            split. { intros x Hx. destruct (Z.eq_dec x (mp_unHi p)) as [->|NX]; [lia|]. apply K3. lia. }
            exact K4. }
          { right. exact HK. }
          cbn [mp_unHi] in P5. split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [lia|exact P4].
    Qed.

    Lemma mpk_loop : forall f sz p,
      MPK p -> (Z.to_nat (mp_unHi p - mp_unLo p + 1) <= sz)%nat -> (Z.to_nat (mp_unHi p - mp_unLo p + 1) < 2 * f)%nat ->
      let p' := mpart_loop f sz a2 d med p in
      MPK p' /\ mp_unLo p' = mp_unHi p' + 1.
    Proof.
      induction f as [|f IH]; intros sz p HP Hsz Hf; [lia|]. cbn zeta.
      rewrite mpart_loop_S. cbn zeta.
      pose proof (mpk_lo (S sz) p HP ltac:(lia)) as LL. cbn zeta in LL. cps_destruct LL as (L1 & L2 & L3 & L5 & L4).
      set (p1 := mpart_lo (S sz) a2 d med p) in *.
      assert (S1 : (Z.to_nat (mp_unHi p1 - mp_unLo p1 + 1) < S sz)%nat) by (rewrite L2; lia).
      pose proof (mpk_hi (S sz) p1 L1 S1 L4) as MM. cbn zeta in MM. cps_destruct MM as (M1 & M2 & M3 & M5 & M4).
      set (p2 := mpart_hi (S sz) a2 d med p1) in *.
      destruct (Z.ltb_spec (mp_unHi p2) (mp_unLo p2)) as [LT|GE].
      { split; [exact M1|]. cps_destruct M1 as (_ & _ & C2 & _). lia. }
      destruct M4 as [M4|[KH KL]]; [lia|].
      assert (NE : mp_unLo p2 < mp_unHi p2).
      { destruct (Z.eq_dec (mp_unLo p2) (mp_unHi p2)) as [X|X]; [|lia]. rewrite X in KL. lia. }
      cps_destruct M1 as (A & B & C & D & E & PM & K1 & K2 & K3 & K4).
      match goal with |- MPK (mpart_loop f sz a2 d med ?q) /\ _ => specialize (IH sz q) end.
      cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi] in IH.
      destruct IH as (P1 & P2); [| lia | lia | split; [exact P1|exact P2]].
      unfold MPK; cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [apply perm_mswap; try assumption; lia|].
      split. { intros x Hx. rewrite K_swap_o by lia. apply K1. lia. }
      split. { intros x Hx. destruct (Z.eq_dec x (mp_unLo p2)) as [->|NX].
               - rewrite K_swap_a by (try assumption; lia). exact KH.
               - rewrite K_swap_o by lia. apply K2. lia. }
      split. { intros x Hx. destruct (Z.eq_dec x (mp_unHi p2)) as [->|NX].
               - rewrite K_swap_b by (try assumption; lia). exact KL.
               - rewrite K_swap_o by lia. apply K3. lia. }
      intros x Hx. rewrite K_swap_o by lia. apply K4. lia.
    Qed.

    Lemma mqk_part : forall a1,
      fm_perm a1 n -> lo <= hi + 1 ->
      let sz := Z.to_nat (hi - lo + 1) in
      let p := mpart_loop (S sz) sz a2 d med (MP a1 lo hi lo hi) in
      MPK p /\ mp_unLo p = mp_unHi p + 1.
    Proof.
      intros a1 PM LH. cbn zeta. apply mpk_loop; cbn [mp_unLo mp_unHi]; [|lia|lia].
      unfold MPK; cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi]. repeat (split; [first [lia | exact PM | intros; lia]|]). intros; lia.
    Qed.

    (* [comment removed for export] *)
    Definition marranged (g : zarr) (a c : Z) : Prop :=
      (forall x, lo <= x < lo + a -> K g x < med) /\
      (forall x, lo + a <= x <= hi - c -> K g x = med) /\
      (forall x, hi - c < x <= hi -> med < K g x).

    Lemma mqk_arrange : forall (p : mpart),
      MPK p -> mp_unLo p = mp_unHi p + 1 ->
      let nn := mmin (mp_ltLo p - lo) (mp_unLo p - mp_ltLo p) in
      let g1 := mvswap (S (Z.to_nat nn)) (mp_a1 p) lo (mp_unLo p - nn) nn in
      let m := mmin (hi - mp_gtHi p) (mp_gtHi p - mp_unHi p) in
      let g2 := mvswap (S (Z.to_nat m)) g1 (mp_unLo p) (hi - m + 1) m in
      fm_perm g2 n /\ frame_out (mp_a1 p) g2 lo hi /\ marranged g2 (mp_unLo p - mp_ltLo p) (mp_gtHi p - mp_unHi p).
    Proof.
      (intros p; cps_intros (A & B & C & D & E & PM & K1 & K2 & K3 & K4); intros UU). cbn zeta.
      rewrite !(mvswap_fvswap _ (mp_a1 p)). rewrite !mvswap_fvswap. rewrite !(mmin_fmin (mp_ltLo p - lo)). rewrite !(mmin_fmin (hi - mp_gtHi p)).
      set (a := mp_unLo p - mp_ltLo p) in *. set (c := mp_gtHi p - mp_unHi p) in *.
      set (e1 := mp_ltLo p - lo) in *. set (e2 := hi - mp_gtHi p) in *.
      set (nn := fmin e1 a) in *.
      assert (Hn' : 0 <= nn /\ nn <= e1 /\ nn <= a /\ (nn = e1 \/ nn = a)) by (subst nn; unfold fmin; destruct (Z.ltb_spec e1 a); lia).
      destruct (fvswap_perm_frame (S (Z.to_nat nn)) (mp_a1 p) n lo (mp_unLo p - nn) nn lo hi PM ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [PM1 FR1].
      destruct (fvswap_blocks (S (Z.to_nat nn)) (mp_a1 p) n lo (mp_unLo p - nn) nn PM ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [X1 Y1].
      set (g1 := fvswap (S (Z.to_nat nn)) (mp_a1 p) lo (mp_unLo p - nn) nn) in *.
      assert (A1 : forall x, lo <= x < lo + a -> K g1 x < med).
      { intros x Hx. unfold K. destruct (Z.lt_ge_cases x (lo + nn)) as [L|G].
        - destruct (X1 (x - lo) ltac:(lia)) as [X _]. replace (lo + (x - lo)) with x in X by lia. rewrite X. apply K2. lia.
        - rewrite Y1 by lia. apply K2. lia. }
      assert (B1 : forall x, lo + a <= x < mp_unLo p -> K g1 x = med).
      { intros x Hx. unfold K. destruct (Z.lt_ge_cases x (mp_unLo p - nn)) as [L|G].
        - rewrite Y1 by lia. apply K1. lia.
        - destruct (X1 (x - (mp_unLo p - nn)) ltac:(lia)) as [_ X]. replace (mp_unLo p - nn + (x - (mp_unLo p - nn))) with x in X by lia.
          rewrite X. apply K1. lia. }
      assert (C1 : forall x, mp_unLo p <= x -> rd32 g1 x = rd32 (mp_a1 p) x) by (intros x Hx; apply Y1; lia).
      set (m := fmin e2 c) in *.
      assert (Hm : 0 <= m /\ m <= e2 /\ m <= c /\ (m = e2 \/ m = c)) by (subst m; unfold fmin; destruct (Z.ltb_spec e2 c); lia).
      destruct (fvswap_perm_frame (S (Z.to_nat m)) g1 n (mp_unLo p) (hi - m + 1) m lo hi PM1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [PM2 FR2].
      destruct (fvswap_blocks (S (Z.to_nat m)) g1 n (mp_unLo p) (hi - m + 1) m PM1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [X2 Y2].
      set (g2 := fvswap (S (Z.to_nat m)) g1 (mp_unLo p) (hi - m + 1) m) in *.
      split; [exact PM2|]. split; [eapply frame_out_trans; eassumption|].
      split; [|split].
      - intros x Hx. unfold K. rewrite Y2 by lia. apply A1. lia.
      - intros x Hx. destruct (Z.lt_ge_cases x (mp_unLo p)) as [L|G].
        + unfold K. rewrite Y2 by lia. apply B1. lia.
        + destruct (Z.lt_ge_cases x (mp_unLo p + m)) as [L2|G2].
          * destruct (X2 (x - mp_unLo p) ltac:(lia)) as [X _]. replace (mp_unLo p + (x - mp_unLo p)) with x in X by lia.
            unfold K. rewrite X. rewrite C1 by lia. apply K4. lia.
          * unfold K. rewrite Y2 by lia. rewrite C1 by lia. apply K4. lia.
      - intros x Hx. destruct (Z.lt_ge_cases x (hi - m + 1)) as [L|G].
        + unfold K. rewrite Y2 by lia. rewrite C1 by lia. apply K3. lia.
        + destruct (X2 (x - (hi - m + 1)) ltac:(lia)) as [_ X]. replace (hi - m + 1 + (x - (hi - m + 1))) with x in X by lia.
          unfold K. rewrite X. rewrite C1 by lia. apply K3. lia.
    Qed.
  End MPK.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Stack.
    Variables (lo0 hi0 d0 : Z).
    Hypothesis Hlo0 : 0 <= lo0.
    Hypothesis Hhi0 : hi0 < n.
    Hypothesis Hlh0 : lo0 <= hi0.
    Hypothesis HD0 : 0 <= d0 <= 14.

    Definition inr (e : entry) (x : Z) : Prop := elo e <= x <= ehi e.
    Definition esane (e : entry) : Prop := lo0 <= elo e /\ elo e <= ehi e + 1 /\ ehi e <= hi0 /\ d0 <= ed e <= 15.
    (* [comment removed for export] *)
    Fixpoint seps (F : list entry) : Prop :=
      match F with
      | [] => True
      | e :: F' => (forall f x, In f F' -> inr e x -> inr f x -> False) /\ seps F'
      end.

    Definition MQ (q : mqs) (F : list entry) : Prop :=
      mst q F /\ (forall e, In e F -> esane e) /\ fm_perm (mq_a1 q) n /\ seps F /\
      (forall e x y, In e F -> inr e x -> inr e y -> EQ (rd32 (mq_a1 q) x) (rd32 (mq_a1 q) y) (ed e)) /\
      (forall i j, lo0 <= i -> i < j -> j <= hi0 -> (forall e, In e F -> ~ (inr e i /\ inr e j)) ->
         lexle (ROT (rd32 (mq_a1 q) i)) (ROT (rd32 (mq_a1 q) j))) /\
      mq_exit q = false.

    Lemma seps_app : forall N F, seps N -> seps F -> (forall e f x, In e N -> In f F -> inr e x -> inr f x -> False) -> seps (N ++ F).
    Proof.
      induction N as [|e N IH]; intros F SN SF X; cbn; [exact SF|].
      destruct SN as [S1 S2]. split.
      - intros f x Hf. apply in_app_or in Hf. destruct Hf as [Hf|Hf]; [apply S1; exact Hf | apply X; [left; reflexivity|exact Hf]].
      - apply IH; [exact S2|exact SF|]. intros e' f x He' Hf. apply X; [right; exact He'|exact Hf].
    Qed.

    (* [comment removed for export] *)
    Lemma mq_step : forall q q' lo hi d F N,
      MQ q ((lo, hi, d) :: F) ->
      mst q' (N ++ F) -> fm_perm (mq_a1 q') n -> frame_out (mq_a1 q) (mq_a1 q') lo hi -> mq_exit q' = false ->
      (forall e, In e N -> esane e /\ lo <= elo e /\ ehi e <= hi) -> seps N ->
      (forall e x y, In e N -> inr e x -> inr e y -> EQ (rd32 (mq_a1 q') x) (rd32 (mq_a1 q') y) (ed e)) ->
      (forall i j, lo <= i -> i < j -> j <= hi -> (forall e, In e N -> ~ (inr e i /\ inr e j)) ->
         lexle (ROT (rd32 (mq_a1 q') i)) (ROT (rd32 (mq_a1 q') j))) ->
      MQ q' (N ++ F).
    Proof.
      (intros q q' lo hi d F N; cps_intros (M & SANE & PM & SEP & EQF & SRT & EX); intros M' PM' FR EX' NS NSEP NEQ NSRT).
      cps_destruct (SANE (lo, hi, d) ltac:(left; reflexivity)) as (E1 & E2 & E3 & E4). unfold elo, ehi, ed in E1, E2, E3, E4.
      cbn [seps] in SEP. destruct SEP as [DIS0 SEP].
      assert (DIS : forall f x, In f F -> lo <= x <= hi -> inr f x -> False) by (intros f x Hf Hx; apply (DIS0 f x Hf); unfold inr, elo, ehi; cbn; lia).
      assert (SRC : forall x, lo <= x <= hi -> exists x', lo <= x' <= hi /\ rd32 (mq_a1 q') x = rd32 (mq_a1 q) x').
      { intros x Hx. apply (perm_frame_src (mq_a1 q) (mq_a1 q') n lo hi); try assumption; lia. }
      split; [exact M'|]. split.
      { intros e He. apply in_app_or in He. destruct He as [He|He]; [apply NS; exact He | apply SANE; right; exact He]. }
      split; [exact PM'|]. split.
      { apply seps_app; [exact NSEP|exact SEP|]. intros e f x He Hf Ie If. cps_destruct (NS e He) as (_ & L1 & L2).
        apply (DIS f x Hf); [unfold inr in Ie; lia | exact If]. }
      split.
      { intros e x y He Hx Hy. apply in_app_or in He. destruct He as [He|He]; [apply NEQ; assumption|].
        cps_destruct (SANE e ltac:(right; exact He)) as (S1 & S2 & S3 & S4).
        assert (Ox : ~ (lo <= x <= hi)). { intros X. apply (DIS e x He); [lia|exact Hx]. }
        assert (Oy : ~ (lo <= y <= hi)). { intros X. apply (DIS e y He); [lia|exact Hy]. }
        rewrite !FR by lia. apply (EQF e x y); [right; exact He|exact Hx|exact Hy]. }
      split; [|exact EX'].
      intros i j Hi Hij Hj NF.
      assert (OLD : forall i0 j0, lo0 <= i0 -> i0 < j0 -> j0 <= hi0 -> ~ (lo <= i0 <= hi /\ lo <= j0 <= hi) ->
                (~ (lo <= i0 <= hi) -> ~ (lo <= j0 <= hi) -> forall e, In e F -> ~ (inr e i0 /\ inr e j0)) ->
                lexle (ROT (rd32 (mq_a1 q) i0)) (ROT (rd32 (mq_a1 q) j0))).
      { intros i0 j0 A0 B0 C0 NB0 NF0. apply SRT; try lia. intros e [He|He].
        - subst e. unfold inr, elo, ehi. cbn. lia.
        - intros [X Y].
          destruct (Z.le_gt_cases lo i0) as [U|U]; [destruct (Z.le_gt_cases i0 hi) as [V|V]; [exfalso; apply (DIS e i0 He); [lia|exact X]|]|];
          (destruct (Z.le_gt_cases lo j0) as [U'|U']; [destruct (Z.le_gt_cases j0 hi) as [V'|V']; [exfalso; apply (DIS e j0 He); [lia|exact Y]|]|]);
          (apply (NF0 ltac:(lia) ltac:(lia) e He); split; assumption). }
      destruct (Z.le_gt_cases lo i) as [LI|LI]; destruct (Z.le_gt_cases j hi) as [HJ|HJ].
      - apply NSRT; try lia. intros e He. apply NF. apply in_or_app. left; exact He.
      - destruct (Z.le_gt_cases i hi) as [IH2|IH2].
        + cps_destruct (SRC i ltac:(lia)) as (i' & Hi' & ->). rewrite (FR j) by lia. apply (OLD i' j); lia.
        + rewrite (FR i), (FR j) by lia. apply (OLD i j); try lia. intros _ _ e He. apply NF. apply in_or_app; right; exact He.
      - destruct (Z.le_gt_cases lo j) as [JL|JL].
        + cps_destruct (SRC j ltac:(lia)) as (j' & Hj' & ->). rewrite (FR i) by lia. apply (OLD i j'); lia.
        + rewrite (FR i), (FR j) by lia. apply (OLD i j); try lia. intros _ _ e He. apply NF. apply in_or_app; right; exact He.
      - rewrite (FR i), (FR j) by lia. apply (OLD i j); try lia. intros _ _ e He. apply NF. apply in_or_app; right; exact He.
    Qed.

    Lemma mq_iter : forall q F, MQ q F -> 0 < mq_sp q ->
      let q' := mqs_iter a2 qoff n q in
      mq_budget q' <= mq_budget q /\ (mq_exit q' = true -> mq_budget q' < 0) /\ (mq_exit q' = false -> exists F', MQ q' F').
    Proof.
      intros q F MQF Hsp. cps_pose MQF as (M & SANE & PM & SEP & EQF & SRT & EX).
      destruct F as [|e F']. { destruct M as [SP _]. cbn in SP. lia. }
      pose proof (mst_top q e F' M) as TOP. destruct e as [[lo hi] d]. unfold ent in TOP. injection TOP as Td Thi Tlo.
      cps_destruct (SANE (lo, hi, d) ltac:(left; reflexivity)) as (E1 & E2 & E3 & E4). unfold elo, ehi, ed in E1, E2, E3, E4.
      assert (RG : forall x, lo0 <= x <= hi0 -> 0 <= rd32 (mq_a1 q) x < n) by (intros x Hx; apply (proj1 PM); lia).
      assert (EQlo : forall x y, lo <= x <= hi -> lo <= y <= hi -> EQ (rd32 (mq_a1 q) x) (rd32 (mq_a1 q) y) d).
      { intros x y Hx Hy. apply (EQF (lo, hi, d) x y); [left; reflexivity|unfold inr, elo, ehi; cbn; lia|unfold inr, elo, ehi; cbn; lia]. }
      cbv zeta. rewrite mqs_iter_ITER. unfold ITER. unfold TOPlo, TOPhi, TOPd. rewrite Tlo, Thi, Td.
      destruct (Sumbool.sumbool_of_bool ((hi - lo <? 20) || (14 <? d))) as [LF|NODE]; rewrite ?LF, ?NODE.
      { (* [comment removed for export] *)
        unfold LEAF. unfold TOPlo, TOPhi, TOPd. rewrite Tlo, Thi, Td.
        assert (VS : vals a2 n d (rd32 (mq_a1 q) lo) (mq_a1 q) lo hi).
        { intros x Hx. split; [apply RG; lia|]. apply EQlo; lia. }
        pose proof (mainSimpleSort_sorted a2 qoff n Hn Hn9 OVB OVQ QIw d (rd32 (mq_a1 q) lo) ltac:(lia) (mq_a1 q) lo hi (mq_budget q) ltac:(lia) VS) as S1.
        pose proof (mss_perm_frame n ltac:(lia) a2 qoff n d (mq_a1 q) lo hi (mq_budget q) ltac:(lia) ltac:(lia) ltac:(lia) PM) as PF.
        cbv zeta in S1, PF. destruct (mainSimpleSort (mq_a1 q) a2 qoff n lo hi d (mq_budget q)) as [a1' b']. cbn [fst snd] in S1, PF.
        cps_destruct S1 as (_ & FRo & BLE & SORTED). destruct PF as [PM' FR'].
        cbn [mq_budget mq_exit mq_a1]. split; [exact BLE|]. split; [intros X; apply Z.ltb_lt in X; exact X|].
        intros X. apply Z.ltb_ge in X. specialize (SORTED X). exists F'.
        apply (mq_step q _ lo hi d F' []); cbn [app mq_a1 mq_exit]; try assumption.
        - eapply mst_pop. exact M.
        - apply Z.ltb_ge. exact X.
        - intros e [].
        - exact I.
        - intros e x y [].
        - intros i j Hi Hij Hj _. apply SORTED; lia. }
      apply Bool.orb_false_iff in NODE. destruct NODE as [N1 N2]. apply Z.ltb_ge in N1. apply Z.ltb_ge in N2.
      set (med := MED a2 q).
      pose proof (mqk_part d med lo hi ltac:(lia) ltac:(lia) (mq_a1 q) PM ltac:(lia)) as KP. cbv zeta in KP.
      pose proof (mpf_loop n ltac:(lia) a2 d med (S (Z.to_nat (hi - lo + 1))) (Z.to_nat (hi - lo + 1)) (mq_a1 q) lo hi (MP (mq_a1 q) lo hi lo hi) ltac:(lia) ltac:(lia)) as PFL.
      assert (PPdef : PART a2 q = mpart_loop (S (Z.to_nat (hi - lo + 1))) (Z.to_nat (hi - lo + 1)) a2 d med (MP (mq_a1 q) lo hi lo hi)).
      { unfold PART. fold med. unfold TOPlo, TOPhi, TOPd. rewrite Tlo, Thi, Td. reflexivity. }
      rewrite <- PPdef in KP, PFL. set (pp := PART a2 q) in *.
      cps_destruct PFL as (_ & PMp & FRp). { split; [unfold MPB; cbn; lia|]. cbn [mp_a1]. split; [exact PM | apply frame_out_refl]. }
      destruct KP as [KPK KU]. cps_pose KPK as (A & B & C & D & E & _ & K1 & K2 & K3 & K4).
      (* [comment removed for export] *)
      assert (SRCp : forall x, lo <= x <= hi -> exists x', lo <= x' <= hi /\ rd32 (mp_a1 pp) x = rd32 (mq_a1 q) x').
      { intros x Hx. apply (perm_frame_src (mq_a1 q) (mp_a1 pp) n lo hi); try assumption; lia. }
      destruct (Z.ltb_spec (mp_gtHi pp) (mp_ltLo pp)) as [ALLEQ|SPLIT].
      { (* [comment removed for export] *)
        cbn [mq_budget mq_exit mpush Q1]. split; [lia|]. split; [intros; discriminate|]. intros _.
        assert (ALL : forall x, lo <= x <= hi -> bkey d (rd32 (mp_a1 pp) x) = med).
        { intros x Hx. destruct (Z.lt_ge_cases x (mp_ltLo pp)); [apply K1; lia | apply K4; lia]. }
        exists ((lo, hi, d + 1) :: F').
        apply (mq_step q _ lo hi d F' [(lo, hi, d + 1)]); cbn [app mq_a1 mq_exit mpush Q1]; try assumption.
        - apply mst_push. unfold Q1. eapply mst_pop. exact M.
        - reflexivity.
        - intros e [<-|[]]. unfold esane, elo, ehi, ed. cbn. lia.
        - cbn. split; [intros f x []|exact I].
        - intros e x y [<-|[]] Hx Hy. unfold inr, elo, ehi in Hx, Hy. cbn in Hx, Hy. cbv beta iota delta [ed].
          cps_destruct (SRCp x ltac:(lia)) as (x' & Hx' & Ex). cps_destruct (SRCp y ltac:(lia)) as (y' & Hy' & Ey).
          apply byte_eq_EQB; [lia| rewrite Ex; apply RG; lia | rewrite Ey; apply RG; lia | rewrite Ex, Ey; apply EQlo; lia |].
          rewrite !ALL by lia. reflexivity.
        - intros i j Hi Hij Hj NF. exfalso. apply (NF (lo, hi, d + 1)); [left; reflexivity|]. unfold inr, elo, ehi; cbn. lia. }
      (* [comment removed for export] *)
      pose proof (mqk_arrange d med lo hi ltac:(lia) ltac:(lia) pp KPK KU) as AR. cbv zeta in AR.
      cps_destruct AR as (PM2 & FR2 & AR1 & AR2 & AR3).
      set (a := mp_unLo pp - mp_ltLo pp) in *. set (c := mp_gtHi pp - mp_unHi pp) in *.
      assert (AC : 0 <= a /\ 0 <= c /\ a + c <= hi - lo + 1) by (subst a c; lia).
      set (nn := lo + mp_unLo pp - mp_ltLo pp - 1). set (mm := hi - c + 1).
      assert (Hnn : nn = lo + a - 1) by (subst nn a; lia).
      set (q2 := Q2 q pp).
      cps_pose (net_spec q2) as (PERM & _ & Fsp & Fslo & Fshi & Fsd & Fa1 & Fb & Fx).
      set (q2' := net q2) in *.
      assert (Q2f : mq_sp q2 = mq_sp q - 1 /\ mq_slo q2 = mq_slo q /\ mq_shi q2 = mq_shi q /\ mq_sd q2 = mq_sd q /\
                    mq_budget q2 = mq_budget q /\ mq_exit q2 = false) by (subst q2; unfold Q2; cbn; repeat split; reflexivity).
      assert (A1Vdef : mq_a1 q2 = A1V q pp) by (subst q2; unfold Q2; reflexivity).
      assert (T0 : ntrip q2 0 = (lo, nn, d)). { unfold ntrip; subst q2; unfold Q2, KN, KM, TOPlo, TOPhi, TOPd; cbn [mq_nlo mq_nhi mq_nd]. rewrite ?Tlo, ?Thi, ?Td. rewrite !zget_zset. cbn. rewrite ?Tlo, ?Thi, ?Td. subst nn. reflexivity. }
      assert (T1 : ntrip q2 1 = (mm, hi, d)). { unfold ntrip; subst q2; unfold Q2, KN, KM, TOPlo, TOPhi, TOPd; cbn [mq_nlo mq_nhi mq_nd]. rewrite ?Tlo, ?Thi, ?Td. rewrite !zget_zset. cbn. rewrite ?Tlo, ?Thi, ?Td. subst mm c. reflexivity. }
      assert (T2 : ntrip q2 2 = (nn + 1, mm - 1, d + 1)). { unfold ntrip; subst q2; unfold Q2, KN, KM, TOPlo, TOPhi, TOPd; cbn [mq_nlo mq_nhi mq_nd]. rewrite ?Tlo, ?Thi, ?Td. rewrite !zget_zset. cbn. rewrite ?Tlo, ?Thi, ?Td. subst nn mm c. reflexivity. }
      rewrite T0, T1, T2 in PERM.
      set (t0 := ntrip q2' 0) in *. set (t1 := ntrip q2' 1) in *. set (t2 := ntrip q2' 2) in *.
      (* [comment removed for export] *)
      assert (R5 : mq_a1 (PUSH3 q2') = A1V q pp /\ mq_budget (PUSH3 q2') = mq_budget q /\ mq_exit (PUSH3 q2') = false).
      { unfold PUSH3, mpush. cbn [mq_a1 mq_budget mq_exit]. rewrite Fa1, Fb, Fx, A1Vdef. cps_destruct Q2f as (_ & _ & _ & _ & -> & ->). repeat split; reflexivity. }
      cps_destruct R5 as (Ra1 & Rb & Rx). rewrite Rb, Rx. split; [lia|]. split; [intros; discriminate|]. intros _.
      assert (M2' : mst q2' F').
      { cps_destruct Q2f as (Qsp & Qslo & Qshi & Qsd & _ & _).
        split; [rewrite Fsp, Qsp; destruct M as [SP _]; rewrite SP; cbn [length]; lia|].
        intros k Hk. unfold ent. rewrite Fslo, Fshi, Fsd, Qslo, Qshi, Qsd.
        pose proof (mst_pop q (lo, hi, d) F' (mq_a1 q) (mq_nlo q) (mq_nhi q) (mq_nd q) (mq_budget q) false M) as [_ MP'].
        specialize (MP' k Hk). unfold ent in MP'. cbn [mq_slo mq_shi mq_sd] in MP'. exact MP'. }
      pose proof (mst_push3 q2' F' M2') as M5. cbn zeta in M5. fold t0 t1 t2 in M5. change (mst (PUSH3 q2') (t2 :: t1 :: t0 :: F')) in M5.
      assert (P3 : forall P : entry -> Prop, P (lo, nn, d) -> P (mm, hi, d) -> P (nn + 1, mm - 1, d + 1) -> forall e, In e [t2; t1; t0] -> P e).
      { intros P X Y W e He. cbn [In] in He.
        destruct PERM as [Kp|[Kp|[Kp|[Kp|[Kp|Kp]]]]]; cps_destruct Kp as (K0 & K5 & K6); subst t0 t1 t2; rewrite K0, K5, K6 in He;
          (destruct He as [<-|[<-|[<-|[]]]]; assumption). }
      (* [comment removed for export] *)
      set (g2 := mvswap _ (mvswap _ (mp_a1 pp) _ _ _) _ _ _) in *.
      assert (A1Vq : A1V q pp = g2). { subst g2. unfold A1V, TOPlo, TOPhi. rewrite ?Tlo, ?Thi, ?Td. reflexivity. }
      rewrite A1Vq in Ra1.
      assert (SRC2 : forall x, lo <= x <= hi -> exists x', lo <= x' <= hi /\ rd32 g2 x = rd32 (mq_a1 q) x').
      { intros x Hx. cps_destruct (perm_frame_src (mp_a1 pp) g2 n lo hi PMp PM2 FR2 ltac:(lia) ltac:(lia) x Hx) as (x1 & Hx1 & ->).
        apply SRCp. exact Hx1. }
      assert (RG2 : forall x, lo <= x <= hi -> 0 <= rd32 g2 x < n).
      { intros x Hx. cps_destruct (SRC2 x Hx) as (x' & Hx' & ->). apply RG. lia. }
      assert (EQ2 : forall x y, lo <= x <= hi -> lo <= y <= hi -> EQ (rd32 g2 x) (rd32 g2 y) d).
      { intros x y Hx Hy. cps_destruct (SRC2 x Hx) as (x' & Hx' & ->). cps_destruct (SRC2 y Hy) as (y' & Hy' & ->). apply EQlo; lia. }
      exists (t2 :: t1 :: t0 :: F').
      apply (mq_step q (PUSH3 q2') lo hi d F' [t2; t1; t0]); rewrite ?Ra1, ?Rx; try assumption.
      - eapply frame_out_trans; [exact FRp|exact FR2].
      - reflexivity.
      - apply (P3 (fun e => esane e /\ lo <= elo e /\ ehi e <= hi)); unfold esane, elo, ehi, ed; cbn; subst nn mm; lia.
      - (* [comment removed for export] *)
        destruct PERM as [Kp|[Kp|[Kp|[Kp|[Kp|Kp]]]]]; cps_destruct Kp as (K0 & K5 & K6); subst t0 t1 t2; rewrite K0, K5, K6;
          (cbn [seps]; repeat split; try exact I; intros f x Hf Ie If; cbn [In] in Hf; unfold inr, elo, ehi in Ie, If;
           repeat (destruct Hf as [Hf'|Hf]; [subst f; cbn beta iota in Ie, If; subst nn mm; lia|]); destruct Hf).
      - (* [comment removed for export] *)
        intros e x y He. revert x y.
        apply (P3 (fun e => forall x y, inr e x -> inr e y -> EQ (rd32 g2 x) (rd32 g2 y) (ed e))); [| | |exact He];
          cbv beta iota delta [inr elo ehi ed]; intros x y Hx Hy.
        + apply EQ2; subst nn; lia.
        + apply EQ2; subst mm; lia.
        + apply byte_eq_EQB; [lia | apply RG2; subst nn mm; lia | apply RG2; subst nn mm; lia | apply EQ2; subst nn mm; lia |].
          rewrite !AR2 by (subst nn mm; lia). reflexivity.
      - (* [comment removed for export] *)
        intros i j Hi Hij Hj NF.
        assert (NLT : ~ (i < lo + a /\ j < lo + a)).
        { intros [X Y]. apply (NF (lo, nn, d)); [|unfold inr, elo, ehi; cbn; subst nn; lia].
          destruct PERM as [Kp|[Kp|[Kp|[Kp|[Kp|Kp]]]]]; cps_destruct Kp as (K0 & K5 & K6); subst t0 t1 t2; rewrite K0, K5, K6; cbn; tauto. }
        assert (NEQ2 : ~ (lo + a <= i <= hi - c /\ lo + a <= j <= hi - c)).
        { intros [X Y]. apply (NF (nn + 1, mm - 1, d + 1)); [|unfold inr, elo, ehi; cbn; subst nn mm; lia].
          destruct PERM as [Kp|[Kp|[Kp|[Kp|[Kp|Kp]]]]]; cps_destruct Kp as (K0 & K5 & K6); subst t0 t1 t2; rewrite K0, K5, K6; cbn; tauto. }
        assert (NGT : ~ (hi - c < i /\ hi - c < j)).
        { intros [X Y]. apply (NF (mm, hi, d)); [|unfold inr, elo, ehi; cbn; subst mm; lia].
          destruct PERM as [Kp|[Kp|[Kp|[Kp|[Kp|Kp]]]]]; cps_destruct Kp as (K0 & K5 & K6); subst t0 t1 t2; rewrite K0, K5, K6; cbn; tauto. }
        apply (byte_lt_rot d); [lia | apply RG2; lia | apply RG2; lia | apply EQ2; lia |].
        destruct (Z.lt_ge_cases i (lo + a)) as [IA|IA].
        + pose proof (AR1 i ltac:(lia)). destruct (Z.le_gt_cases j (hi - c)) as [JB|JB]; [rewrite (AR2 j) by lia; lia | pose proof (AR3 j ltac:(lia)); lia].
        + destruct (Z.le_gt_cases i (hi - c)) as [IB|IB].
          * rewrite (AR2 i) by lia. destruct (Z.le_gt_cases j (hi - c)) as [JB|JB]; [exfalso; apply NEQ2; lia | pose proof (AR3 j ltac:(lia)); lia].
          * exfalso. apply NGT. lia.
    Qed.

    Lemma mqs_loop_exit : forall v q, mq_exit q = true -> mqs_loop v a2 qoff n q = q.
    Proof. intros [|v] q E; [reflexivity|]. rewrite mqs_loop_S, E. destruct (0 <? mq_sp q); reflexivity. Qed.

    Lemma mq_loop : forall v q F, MQ q F ->
      let r := mqs_loop v a2 qoff n q in
      mq_budget r <= mq_budget q /\ (mq_exit r = true -> mq_budget r < 0) /\ (mq_exit r = false -> exists F', MQ r F').
    Proof.
      induction v as [|v IH]; intros q F MQF; cbv zeta.
      - cbn [mqs_loop]. split; [lia|]. split; [intros E; cps_pose MQF as (_ & _ & _ & _ & _ & _ & EX); congruence | intros _; exists F; exact MQF].
      - rewrite mqs_loop_S. cps_pose MQF as (_ & _ & _ & _ & _ & _ & EX). rewrite EX. cbn [negb andb].
        destruct (Z.ltb_spec 0 (mq_sp q)) as [P|NP]; cbn [andb].
        + pose proof (mq_iter q F MQF P) as IT. cbv zeta in IT. cps_destruct IT as (B1 & E1 & M1).
          destruct (mq_exit (mqs_iter a2 qoff n q)) eqn:EX1.
          * rewrite mqs_loop_exit by exact EX1. split; [exact B1|]. split; [intros _; apply E1; reflexivity | intros X; exfalso; rewrite EX1 in X; discriminate].
          * destruct (M1 eq_refl) as [F' M']. specialize (IH _ F' M'). cbv zeta in IH. cps_destruct IH as (B2 & E2 & M2).
            split; [lia|]. split; [exact E2|exact M2].
        + split; [lia|]. split; [intros E'; exfalso; rewrite EX in E'; discriminate | intros _; exists F; exact MQF].
    Qed.

    Theorem mainQSort3_sorted : forall a1 budget l,
      fm_perm a1 n -> hi0 - lo0 + 1 < 21 * 2 ^ 16 ->
      (forall x y, lo0 <= x <= hi0 -> lo0 <= y <= hi0 -> EQ (rd32 a1 x) (rd32 a1 y) d0) ->
      let r := mainQSort3 a1 a2 qoff n lo0 hi0 d0 budget l in
      snd (fst r) <= budget /\ fm_perm (fst (fst r)) n /\ frame_out a1 (fst (fst r)) lo0 hi0 /\
      (0 <= snd (fst r) -> forall i j, lo0 <= i -> i <= j -> j <= hi0 -> lexle (ROT (rd32 (fst (fst r)) i)) (ROT (rd32 (fst (fst r)) j))).
    Proof.
      intros a1 budget l PM HN EQ0. cbv zeta.
      pose proof (mqs3_perm_frame n ltac:(lia) lo0 hi0 d0 a2 qoff n HD0 Hlo0 Hhi0 HN a1 budget l PM Hlh0) as PF. cbv zeta in PF.
      pose proof (mqs_ok lo0 hi0 d0 a2 qoff n HD0 Hlh0 HN a1 (ml_slo l) (ml_shi l) (ml_sd l) (ml_nlo l) (ml_nhi l) (ml_nd l) budget) as OK.
      cbv zeta in OK. destruct OK as [_ TERM].
      unfold mainQSort3 in *. set (q0 := mpush _ lo0 hi0 d0) in *.
      assert (MQ0 : MQ q0 [(lo0, hi0, d0)]).
      { split; [|split; [|split; [|split; [|split; [|split]]]]].
        - subst q0. apply mst_push. split; [reflexivity|intros k Hk; cbn in Hk; lia].
        - intros e [<-|[]]. unfold esane, elo, ehi, ed; cbn. lia.
        - subst q0. cbn. exact PM.
        - cbn. split; [intros f x []|exact I].
        - intros e x y [<-|[]] Hx Hy. unfold inr, elo, ehi in Hx, Hy; cbn in Hx, Hy. cbv beta iota delta [ed]. subst q0; cbn [mq_a1 mpush]. apply EQ0; lia.
        - intros i j Hi Hij Hj NF. exfalso. apply (NF (lo0, hi0, d0)); [left; reflexivity|]. unfold inr, elo, ehi; cbn. lia.
        - subst q0. reflexivity. }
      pose proof (mq_loop (mqs_fuel lo0 hi0) q0 _ MQ0) as LP. cbv zeta in LP.
      set (r := mqs_loop (mqs_fuel lo0 hi0) a2 qoff n q0) in *. cbn [fst snd] in *.
      cps_destruct LP as (B & E & M). destruct PF as [P F].
      split; [subst q0; cbn in B; exact B|]. split; [exact P|]. split; [exact F|].
      intros GE i j Hi Hij Hj. destruct (Z.eq_dec i j) as [->|NE]; [right; reflexivity|].
      destruct (mq_exit r) eqn:EX. { specialize (E eq_refl). lia. }
      destruct (M eq_refl) as [F' MQ']. destruct TERM as [SP|EXT]; [|congruence].
      cps_pose MQ' as ([SPL _] & _ & _ & _ & _ & SRT & _). rewrite SP in SPL.
      destruct F' as [|e F'']; [|cbn in SPL; lia].
      apply SRT; try lia. intros e [].
    Qed.
  End Stack.
End S2.
