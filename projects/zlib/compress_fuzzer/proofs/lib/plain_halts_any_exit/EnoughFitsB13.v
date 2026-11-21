(** * EnoughFitsB13 — session 8 (S2, part 3): the count memo is live at
    the walk's seed cell.

    The actual code IS the reachability witness: its per-level counts
    sit inside every count-DP window (the B8 feasibility kit), its
    juncture chain (rem_syms l, kleft l, l) is the DP's child at
    use = cnt l (the recurrences ARE the child laws), and it completes
    at max (syms = left there).  So countF returns >= 1 along the walk,
    stores >= 1 at every walk cell it computes, and once any walk
    ancestor is memoized the target cell at rt+1 is memoized-good and
    persists (the memo only adds, and an add never collides thanks to
    key3 injectivity on the traversal domain). *)

From Stdlib Require Import ZArith List Lia Bool FMapPositive.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Inftrees ItGTblSortWin ItGSubCover.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import EnoughDP.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import EnoughFitsDesign EnoughFitsA12 EnoughFitsB1
  EnoughFitsB2 EnoughFitsB4 EnoughFitsB8 EnoughFitsB10 EnoughFitsB11.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   1.  key3 injectivity on the traversal domain.
   ========================================================================== *)

Definition dom3 (syms left len : Z) : Prop :=
  0 <= syms < W /\ 0 <= left < W /\ 0 <= len < W.

Lemma key3_inj : forall s1 l1 L1 s2 l2 L2,
  dom3 s1 l1 L1 -> dom3 s2 l2 L2 ->
  key3 s1 l1 L1 = key3 s2 l2 L2 ->
  s1 = s2 /\ l1 = l2 /\ L1 = L2.
Proof.
  intros s1 l1 L1 s2 l2 L2 (Hs1 & Hl1 & HL1) (Hs2 & Hl2 & HL2) He.
  assert (HW : 0 < W) by (unfold W; vm_compute; reflexivity).
  unfold key3 in He.
  assert (HP1 : 0 < 1 + L1 + W * (l1 + W * s1)).
  { assert (0 <= W * (l1 + W * s1))
      by (apply Z.mul_nonneg_nonneg;
          [clear -HW; lia|
           assert (0 <= W * s1)
             by (apply Z.mul_nonneg_nonneg; clear -HW Hs1; lia);
           clear -Hl1 H; lia]).
    clear -HL1 H; lia. }
  assert (HP2 : 0 < 1 + L2 + W * (l2 + W * s2)).
  { assert (0 <= W * (l2 + W * s2))
      by (apply Z.mul_nonneg_nonneg;
          [clear -HW; lia|
           assert (0 <= W * s2)
             by (apply Z.mul_nonneg_nonneg; clear -HW Hs2; lia);
           clear -Hl2 H; lia]).
    clear -HL2 H; lia. }
  apply Z2Pos.inj in He; [| exact HP1 | exact HP2].
  assert (He1 : L1 + W * (l1 + W * s1) = L2 + W * (l2 + W * s2))
    by (clear -He; lia).
  pose proof (mixed_radix_split L1 L2 (l1 + W * s1) (l2 + W * s2)
                ltac:(clear -HL1; lia) ltac:(clear -HL2; lia) He1)
    as [HLe He2].
  pose proof (mixed_radix_split l1 l2 s1 s2
                ltac:(clear -Hl1; lia) ltac:(clear -Hl2; lia) He2)
    as [Hle Hse].
  auto.
Qed.

(* ==========================================================================
   2.  The count loop, reified.
   ========================================================================== *)

Fixpoint cloopF (f : nat) (mx syms left len : Z)
                (n : nat) (use acc : Z) (m : PM.t Z) : Z * PM.t Z :=
  match n with
  | O => (acc, m)
  | S n' =>
      let '(got, m1) :=
        countF f mx (syms - use) (2 * (left - use)) (len + 1) m
      in cloopF f mx syms left len n' (use + 1) (acc + got) m1
  end.

Lemma countF_fresh_eq :
  forall f mx syms left len m,
  (syms =? left) = false ->
  PM.find (key3 syms left len) m = None ->
  countF (S f) mx syms left len m
  = (let '(sum, memo1) :=
       cloopF f mx syms left len
         (Z.to_nat ((left * 2 ^ (mx - len) - syms)
                    / (2 ^ (mx - len) - 1)
                    - Z.max 0 (2 * left - syms) + 1))
         (Z.max 0 (2 * left - syms)) 0 m in
     (sum, PM.add (key3 syms left len) sum memo1)).
Proof.
  intros f mx syms left len m Hne HF.
  cbn [countF].
  rewrite Hne, HF.
  generalize (Z.to_nat ((left * 2 ^ (mx - len) - syms)
                        / (2 ^ (mx - len) - 1)
                        - Z.max 0 (2 * left - syms) + 1)) as n.
  generalize (Z.max 0 (2 * left - syms)) as u0.
  intros u0 n.
  assert (HL : forall n0 u acc m0,
             (fix loop (n1 : nat) (use acc0 : Z) (mm : PM.t Z)
                : Z * PM.t Z :=
                match n1 with
                | O => (acc0, mm)
                | S n' =>
                    let '(got, m1) :=
                      countF f mx (syms - use) (2 * (left - use))
                             (len + 1) mm
                    in loop n' (use + 1) (acc0 + got) m1
                end) n0 u acc m0
             = cloopF f mx syms left len n0 u acc m0).
  { induction n0 as [|n0 IHn]; intros u acc m0.
    - reflexivity.
    - cbn [cloopF].
      destruct (countF f mx (syms - u) (2 * (left - u)) (len + 1) m0)
        as [got m1].
      apply IHn. }
  rewrite HL.
  destruct (cloopF f mx syms left len n u0 0 m) as [sum memo1].
  reflexivity.
Qed.

(* ==========================================================================
   3.  The walk, its cells, and the reach theorem.
   ========================================================================== *)

Section CountReach.
  Variable cnt : zarr.
  Variable mxw rt : Z.
  Hypothesis Hnn : forall c0, 0 <= cnt c0.
  Hypothesis Hmx : 1 <= mxw <= 15.
  Hypothesis Hmxz : forall l, mxw < l <= 15 -> cnt l = 0.
  Hypothesis Hmxpos : 1 <= cnt mxw.
  Hypothesis Hcomp : wmass 15%nat 1 cnt = 2 ^ 15.
  Hypothesis Hrt : 1 <= rt.
  Hypothesis Hrtmx : rt + 2 <= mxw.
  Hypothesis Hwcap : rem_syms cnt 1 mxw <= 2 ^ 20.

  Definition wsyms (l : Z) : Z := rem_syms cnt l mxw.
  Definition wleft (l : Z) : Z := kleft cnt l.
  Definition tkey : positive :=
    key3 (wsyms (rt + 1)) (wleft (rt + 1)) (rt + 1).

  (** Suffix sums shrink along the walk. *)
  Lemma wsyms_rec : forall l, l < mxw ->
    wsyms l = cnt l + wsyms (l + 1).
  Proof.
    intros l Hl.
    unfold wsyms, rem_syms.
    replace (Z.to_nat (mxw - l + 1))
      with (S (Z.to_nat (mxw - (l + 1) + 1)))%nat by (clear -Hl; lia).
    cbn [rem_syms_aux].
    reflexivity.
  Qed.

  Lemma wsyms_mono : forall l, 1 <= l <= mxw ->
    wsyms l <= wsyms 1.
  Proof.
    intros l Hl.
    unfold wsyms, rem_syms.
    replace (Z.to_nat (mxw - 1 + 1))
      with (Z.to_nat (l - 1) + Z.to_nat (mxw - l + 1))%nat
      by (clear -Hl; lia).
    rewrite aux_split.
    rewrite Z2Nat.id by (clear -Hl; lia).
    replace (1 + (l - 1)) with l by (clear; lia).
    pose proof (rem_syms_aux_nonneg (Z.to_nat (l - 1)) cnt 1 Hnn) as H.
    clear -H; lia.
  Qed.

  Lemma wcell_caps : forall l, 1 <= l <= mxw ->
    0 <= wsyms l <= 2 ^ 21 /\ 0 <= wleft l <= wsyms l.
  Proof.
    intros l Hl.
    assert (Hs0 : 0 <= wsyms l)
      by (unfold wsyms, rem_syms; apply rem_syms_aux_nonneg; exact Hnn).
    assert (Hsc : wsyms l <= 2 ^ 21).
    { pose proof (wsyms_mono l Hl) as H.
      assert ((2:Z) ^ 20 <= 2 ^ 21)
        by (apply Z.pow_le_mono_r; clear; lia).
      unfold wsyms in *. clear -H Hwcap H0; lia. }
    assert (Hlp : 1 <= wleft l)
      by (unfold wleft;
          apply (kleft_pos cnt mxw Hnn Hmx Hmxz Hmxpos Hcomp l Hl)).
    assert (Hls : wleft l <= wsyms l)
      by (unfold wleft, wsyms;
          apply (syms_ge_left cnt mxw Hnn Hmx Hmxz Hcomp l Hl)).
    split; [split; [exact Hs0 | exact Hsc]|].
    split; [clear -Hlp; lia | exact Hls].
  Qed.

  Lemma wcell_dom3 : forall l, 1 <= l <= mxw ->
    dom3 (wsyms l) (wleft l) l.
  Proof.
    intros l Hl.
    destruct (wcell_caps l Hl) as [Hs Hlf].
    unfold dom3, W.
    assert (H40 : (2:Z) ^ 40 = 1099511627776) by (vm_compute; reflexivity).
    assert (H21 : (2:Z) ^ 21 = 2097152) by (vm_compute; reflexivity).
    repeat split; try (clear -Hs Hlf Hl Hmx H40 H21; lia).
  Qed.

  Definition iswcell (syms left len : Z) : Prop :=
    1 <= len <= mxw /\ syms = wsyms len /\ left = wleft len.

  Lemma iswcell_dec : forall syms left len,
    {iswcell syms left len} + {~ iswcell syms left len}.
  Proof.
    intros syms left len.
    destruct (Z_le_dec 1 len); [| right; intros (H & _); lia].
    destruct (Z_le_dec len mxw); [| right; intros (H & _); lia].
    destruct (Z.eq_dec syms (wsyms len));
      [| right; intros (_ & H & _); auto].
    destruct (Z.eq_dec left (wleft len));
      [| right; intros (_ & _ & H); auto].
    left. repeat split; assumption.
  Qed.

  Definition CDOM (syms left len : Z) : Prop :=
    0 <= syms <= 2 ^ 21 /\ 0 <= left <= syms
    /\ 1 <= len <= mxw /\ (len <= mxw - 1 \/ syms = left).

  Lemma cdom_dom3 : forall syms left len,
    CDOM syms left len -> dom3 syms left len.
  Proof.
    intros syms left len (Hs & Hl & HL & _).
    unfold dom3, W.
    assert (H40 : (2:Z) ^ 40 = 1099511627776) by (vm_compute; reflexivity).
    assert (H21 : (2:Z) ^ 21 = 2097152) by (vm_compute; reflexivity).
    repeat split; try (clear -Hs Hl HL Hmx H40 H21; lia).
  Qed.

  Definition CINV (m : PM.t Z) : Prop :=
    forall k v, PM.find k m = Some v -> 0 <= v.

  Definition WINV (m : PM.t Z) : Prop :=
    (forall L v, 1 <= L <= mxw ->
       PM.find (key3 (wsyms L) (wleft L) L) m = Some v -> 1 <= v)
    /\ (forall L, 1 <= L <= rt ->
          (exists v0, PM.find (key3 (wsyms L) (wleft L) L) m = Some v0) ->
          exists v, PM.find tkey m = Some v /\ 1 <= v).

  (** THE COUNT SOUNDNESS. *)
  Lemma count_sound : forall (f : nat) (syms left len : Z) (m : PM.t Z),
    Z.of_nat f = mxw + 2 - len ->
    CDOM syms left len ->
    CINV m -> WINV m ->
    0 <= fst (countF f mxw syms left len m)
    /\ CINV (snd (countF f mxw syms left len m))
    /\ WINV (snd (countF f mxw syms left len m))
    /\ (forall k v, PM.find k m = Some v ->
          PM.find k (snd (countF f mxw syms left len m)) = Some v)
    /\ (iswcell syms left len ->
          1 <= fst (countF f mxw syms left len m)
          /\ (len <= rt + 1 ->
              exists v, PM.find tkey (snd (countF f mxw syms left len m))
                        = Some v /\ 1 <= v)).
  Proof.
    induction f as [|f IH]; intros syms left len m Hlink Hdom HC HW.
    - exfalso.
      destruct Hdom as (_ & _ & HL & _).
      clear -Hlink HL Hmx; cbn in Hlink; lia.
    - destruct Hdom as (Hs & Hl & HL & Hor).
      destruct (Z.eqb_spec syms left) as [Heq | Hne].
      + (* complete: count 1, memo untouched *)
        assert (HEeq : countF (S f) mxw syms left len m = (1, m)).
        { cbn [countF].
          destruct (Z.eqb_spec syms left) as [_|Habs];
            [reflexivity | exfalso; exact (Habs Heq)]. }
        rewrite HEeq.
        cbn [fst snd].
        split; [clear; lia|].
        split; [exact HC|].
        split; [exact HW|].
        split; [intros; assumption|].
        intros Hwc.
        split; [clear; lia|].
        intros Hle.
        exfalso.
        destruct Hwc as (HL2 & Hse & Hle2).
        assert (Hstrict : wleft len < wsyms len)
          by (unfold wleft, wsyms;
              apply (syms_gt_left cnt mxw Hnn Hmx Hmxz Hmxpos Hcomp len
                       ltac:(clear -HL2 Hle Hrtmx; lia))).
        clear -Hstrict Hse Hle2 Heq; lia.
      + assert (Hlen1 : len <= mxw - 1)
          by (destruct Hor as [Ho|Ho]; [exact Ho | exfalso; exact (Hne Ho)]).
        assert (Hneb : (syms =? left) = false)
          by (apply Z.eqb_neq; exact Hne).
        destruct (PM.find (key3 syms left len) m) as [v|] eqn:HF.
        * (* memo hit *)
          assert (HEeq : countF (S f) mxw syms left len m
                         = (if v =? 0 then (0, m) else (v, m))).
          { cbn [countF]. rewrite Hneb, HF. reflexivity. }
          rewrite HEeq.
          pose proof (HC _ _ HF) as Hv0.
          destruct (Z.eqb_spec v 0) as [-> | Hvne]; cbn [fst snd].
          -- split; [clear; lia|].
             split; [exact HC|].
             split; [exact HW|].
             split; [intros; assumption|].
             intros (HL2 & -> & ->).
             exfalso.
             destruct HW as [HW1 _].
             pose proof (HW1 len 0 HL2 HF) as Habs.
             clear -Habs; lia.
          -- split; [clear -Hv0; lia|].
             split; [exact HC|].
             split; [exact HW|].
             split; [intros; assumption|].
             intros (HL2 & -> & ->).
             destruct HW as [HW1 HW2].
             split; [exact (HW1 len v HL2 HF)|].
             intros Hle.
             destruct (Z.eq_dec len (rt + 1)) as [-> | Hne2].
             ++ exists v. split; [exact HF | exact (HW1 _ v HL2 HF)].
             ++ apply (HW2 len ltac:(clear -Hle Hne2 HL2; lia)).
                exists v. exact HF.
        * (* fresh: run the window *)
          rewrite (countF_fresh_eq f mxw syms left len m Hneb HF).
          (* the loop lemma, inline *)
          assert (HLOOP : forall (n : nat) (use acc : Z) (m0 : PM.t Z),
              Z.max 0 (2 * left - syms) <= use ->
              Z.of_nat n
                <= Z.max 0 ((left * 2 ^ (mxw - len) - syms)
                            / (2 ^ (mxw - len) - 1) - use + 1) ->
              0 <= acc ->
              CINV m0 -> WINV m0 ->
              (forall k v, PM.find k m = Some v ->
                 PM.find k m0 = Some v) ->
              acc <= fst (cloopF f mxw syms left len n use acc m0)
              /\ 0 <= fst (cloopF f mxw syms left len n use acc m0)
              /\ CINV (snd (cloopF f mxw syms left len n use acc m0))
              /\ WINV (snd (cloopF f mxw syms left len n use acc m0))
              /\ (forall k v, PM.find k m0 = Some v ->
                    PM.find k (snd (cloopF f mxw syms left len n use acc m0))
                    = Some v)
              /\ (iswcell syms left len ->
                  use <= cnt len ->
                  cnt len < use + Z.of_nat n ->
                  1 <= fst (cloopF f mxw syms left len n use acc m0)
                  /\ (len + 1 <= rt + 1 ->
                      exists v,
                        PM.find tkey
                          (snd (cloopF f mxw syms left len n use acc m0))
                        = Some v /\ 1 <= v))).
          { induction n as [|n IHn]; intros use acc m0 Huse Hwin Hacc
              HC0 HW0 Hmono0.
            - cbn [cloopF fst snd].
              split; [clear; lia|].
              split; [exact Hacc|].
              split; [exact HC0|].
              split; [exact HW0|].
              split; [intros; assumption|].
              intros _ Hu1 Hu2. exfalso. clear -Hu1 Hu2; cbn in Hu2; lia.
            - cbn [cloopF].
              assert (Husemost : use <= (left * 2 ^ (mxw - len) - syms)
                                        / (2 ^ (mxw - len) - 1))
                by (clear -Hwin; lia).
              assert (Hmostl : (left * 2 ^ (mxw - len) - syms)
                               / (2 ^ (mxw - len) - 1) <= left)
                by (apply most_le_left;
                    [clear -Hl; lia | clear -Hlen1; lia]).
              assert (Hchild : CDOM (syms - use) (2 * (left - use))
                                 (len + 1)).
              { unfold CDOM.
                split; [clear -Hs Hl Huse Husemost Hmostl; lia|].
                split; [pose proof (least_child syms left use Huse);
                        clear -H Huse Husemost Hmostl Hl; lia|].
                split; [clear -HL Hlen1; lia|].
                destruct (Z.le_gt_cases (len + 1) (mxw - 1)) as [Hle|Hgt];
                  [left; exact Hle | right].
                assert (Hleq : len = mxw - 1) by (clear -Hgt Hlen1 HL; lia).
                pose proof (window_forcing mxw syms left Hl) as HWF.
                cbv zeta in HWF.
                rewrite <- Hleq in HWF.
                destruct HWF as [(Hneg & HN0) | (Hpos & Hlm & Hcm)].
                - exfalso.
                  rewrite Z.max_l in Huse by (clear -Hneg; lia).
                  rewrite Z.max_l in HN0 by (clear -Hneg; lia).
                  clear -Hwin Hneg Huse Husemost HN0; lia.
                - rewrite Z.max_r in Huse by (clear -Hpos; lia).
                  assert (Hue : use = 2 * left - syms)
                    by (clear -Huse Husemost Hlm Hpos; lia).
                  rewrite Z.max_r in Hcm, Hlm by (clear -Hpos; lia).
                  clear -Hue Hcm; lia. }
              assert (Hlink' : Z.of_nat f = mxw + 2 - (len + 1))
                by (clear -Hlink; lia).
              pose proof (IH (syms - use) (2 * (left - use)) (len + 1) m0
                            Hlink' Hchild HC0 HW0)
                as (Hg0 & HCc & HWc & Hmc & Hwarm).
              destruct (countF f mxw (syms - use) (2 * (left - use))
                          (len + 1) m0) as [got m1] eqn:HCF.
              cbn [fst snd] in Hg0, HCc, HWc, Hmc, Hwarm.
              pose proof (IHn (use + 1) (acc + got) m1
                            ltac:(clear -Huse; lia)
                            ltac:(clear -Hwin; lia)
                            ltac:(clear -Hacc Hg0; lia)
                            HCc HWc
                            ltac:(intros k v Hk;
                                  apply Hmc; apply Hmono0; exact Hk))
                as (Hacc2 & Hpos2 & HC2 & HW2 & Hm2 & Hwarm2).
              split; [clear -Hacc2 Hg0; lia|].
              split; [exact Hpos2|].
              split; [exact HC2|].
              split; [exact HW2|].
              split; [intros k v Hk; apply Hm2; apply Hmc; exact Hk|].
              intros Hwc Hu1 Hu2.
              destruct (Z.eq_dec (cnt len) use) as [Hueq | Hune].
              ++ (* THE WALK CHILD *)
                 assert (Hwchild : iswcell (syms - use) (2 * (left - use))
                                     (len + 1)).
                 { destruct Hwc as (HL2 & -> & ->).
                   assert (HLlt : len < mxw)
                     by (clear -Hlen1 HL2; lia).
                   split; [clear -HL2 HLlt; lia|].
                   split.
                   - unfold wsyms at 2.
                     rewrite <- Hueq.
                     pose proof (wsyms_rec len HLlt) as Hr2.
                     unfold wsyms in Hr2. unfold wsyms.
                     clear -Hr2; lia.
                   - unfold wleft at 2.
                     rewrite <- Hueq.
                     unfold wleft.
                     rewrite kleft_step by (clear -HL2; lia).
                     reflexivity. }
                 pose proof (Hwarm Hwchild) as [Hgot1 Htgt].
                 split.
                 { eapply Z.le_trans; [| exact Hacc2].
                   clear -Hgot1 Hacc; lia. }
                 intros Hle.
                 destruct (Htgt ltac:(clear -Hle; lia)) as (v & Hv & Hv1).
                 exists v.
                 split; [apply Hm2; exact Hv | exact Hv1].
              ++ (* not this iteration *)
                 apply Hwarm2; [exact Hwc | clear -Hu1 Hune; lia
                                | clear -Hu2; lia]. }
          (* apply the loop lemma at the full window *)
          pose proof (HLOOP (Z.to_nat ((left * 2 ^ (mxw - len) - syms)
                                       / (2 ^ (mxw - len) - 1)
                                       - Z.max 0 (2 * left - syms) + 1))
                        (Z.max 0 (2 * left - syms)) 0 m
                        ltac:(clear; lia) ltac:(clear; lia)
                        ltac:(clear; lia) HC HW
                        ltac:(intros; assumption))
            as (Hacc & Hpos & HC1 & HW1 & Hm1 & Hwarm).
          destruct (cloopF f mxw syms left len
                      (Z.to_nat ((left * 2 ^ (mxw - len) - syms)
                                 / (2 ^ (mxw - len) - 1)
                                 - Z.max 0 (2 * left - syms) + 1))
                      (Z.max 0 (2 * left - syms)) 0 m)
            as [sum memo1] eqn:HCL.
          cbn [fst snd] in Hacc, Hpos, HC1, HW1, Hm1, Hwarm.
          cbn [fst snd].
          assert (Hd3 : dom3 syms left len)
            by (apply cdom_dom3; exact (conj Hs (conj Hl (conj HL Hor)))).
          (* the add never clobbers an existing entry *)
          assert (Hmono2 : forall k v, PM.find k m = Some v ->
                    PM.find k (PM.add (key3 syms left len) sum memo1)
                    = Some v).
          { intros k v Hk.
            destruct (PM.E.eq_dec k (key3 syms left len)) as [-> | Hkne].
            - exfalso. rewrite HF in Hk. discriminate Hk.
            - rewrite PM.gso by exact Hkne.
              apply Hm1. exact Hk. }
          destruct (iswcell_dec syms left len) as [Hwc | Hnwc].
          -- (* a walk cell: the window contains the walk use *)
             assert (Hfl : Z.max 0 (2 * left - syms) <= cnt len).
             { destruct Hwc as (HL2 & Hse & Hle2).
               rewrite Hse, Hle2.
               unfold wsyms, wleft.
               pose proof (feas_least cnt mxw Hnn Hmx Hmxz Hcomp len
                             ltac:(clear -HL2 Hlen1; lia)) as H.
               unfold dpm_least in H. exact H. }
             assert (Hfm : cnt len <= (left * 2 ^ (mxw - len) - syms)
                                      / (2 ^ (mxw - len) - 1)).
             { destruct Hwc as (HL2 & Hse & Hle2).
               rewrite Hse, Hle2.
               unfold wsyms, wleft.
               pose proof (feas_most cnt mxw Hnn Hmx Hmxz Hcomp len
                             ltac:(clear -HL2 Hlen1; lia)) as H.
               unfold dpm_most in H. exact H. }
             pose proof (Hwarm Hwc Hfl
                           ltac:(rewrite Z2Nat.id by (clear -Hfl Hfm; lia);
                                 clear -Hfm; lia)) as [Hsum1 Htgt].
             (* is this node itself the target? *)
             assert (Htk : len = rt + 1 ->
                       key3 syms left len = tkey).
             { intros ->.
               destruct Hwc as (_ & -> & ->).
               reflexivity. }
             assert (Htkne : len <> rt + 1 ->
                       key3 syms left len <> tkey).
             { intros Hne2 He.
               unfold tkey in He.
               pose proof (key3_inj _ _ _ _ _ _ Hd3
                             (wcell_dom3 (rt + 1)
                                ltac:(clear -Hrt Hrtmx; lia)) He)
                 as (_ & _ & HLe).
               exact (Hne2 HLe). }
             assert (Htgt2 : len <= rt + 1 ->
                       exists v,
                         PM.find tkey
                           (PM.add (key3 syms left len) sum memo1)
                         = Some v /\ 1 <= v).
             { intros Hle.
               destruct (Z.eq_dec len (rt + 1)) as [He | Hne2].
               - exists sum.
                 rewrite <- (Htk He), PM.gss.
                 split; [reflexivity | exact Hsum1].
               - destruct (Htgt ltac:(clear -Hle Hne2; lia))
                   as (v & Hv & Hv1).
                 exists v.
                 split; [| exact Hv1].
                 rewrite PM.gso
                   by (intro He2x; exact (Htkne Hne2 (eq_sym He2x))).
                 exact Hv. }
             split; [cbn [fst]; clear -Hpos; lia|].
             split.
             { cbn [snd].
               intros k v Hk.
               destruct (PM.E.eq_dec k (key3 syms left len)) as [-> | Hkne].
               - rewrite PM.gss in Hk. injection Hk as <-.
                 clear -Hpos; lia.
               - rewrite PM.gso in Hk by exact Hkne.
                 exact (HC1 k v Hk). }
             split.
             { cbn [snd].
               split.
               - intros L v HL2 Hk.
                 destruct (PM.E.eq_dec (key3 (wsyms L) (wleft L) L)
                             (key3 syms left len)) as [He | Hkne].
                 + rewrite He, PM.gss in Hk.
                   injection Hk as <-.
                   exact Hsum1.
                 + rewrite PM.gso in Hk by exact Hkne.
                   exact (proj1 HW1 L v HL2 Hk).
               - intros L HL2 (v0 & Hv0).
                 destruct (Z.le_gt_cases len (rt + 1)) as [Hle3 | Hgt3].
                 + exact (Htgt2 Hle3).
                 + assert (Hkne2 : key3 syms left len <> tkey).
                   { intro He2. unfold tkey in He2.
                     pose proof (key3_inj _ _ _ _ _ _ Hd3
                                   (wcell_dom3 (rt + 1)
                                      ltac:(clear -Hrt Hrtmx; lia)) He2)
                       as (_ & _ & HLe2).
                     clear -HLe2 Hgt3; lia. }
                   destruct (PM.E.eq_dec (key3 (wsyms L) (wleft L) L)
                               (key3 syms left len)) as [He | Hkne].
                   * exfalso.
                     pose proof (key3_inj _ _ _ _ _ _
                                   (wcell_dom3 L
                                      ltac:(clear -HL2 Hrt Hrtmx Hmx; lia))
                                   Hd3 He) as (_ & _ & HLe).
                     clear -HLe HL2 Hgt3 Hrt; lia.
                   * rewrite PM.gso in Hv0 by exact Hkne.
                     destruct (proj2 HW1 L HL2
                                 ltac:(exists v0; exact Hv0))
                       as (v & Hv & Hv1).
                     exists v.
                     split; [| exact Hv1].
                     rewrite PM.gso
                       by (intro He2x; exact (Hkne2 (eq_sym He2x))).
                     exact Hv. }
             split; [cbn [snd]; exact Hmono2|].
             intros _.
             split; [cbn [fst]; exact Hsum1|].
             intros Hle. cbn [snd].
             exact (Htgt2 Hle).
          -- (* not a walk cell *)
             split; [cbn [fst]; exact Hpos|].
             split.
             { cbn [snd].
               intros k v Hk.
               destruct (PM.E.eq_dec k (key3 syms left len)) as [-> | Hkne].
               - rewrite PM.gss in Hk. injection Hk as <-.
                 exact Hpos.
               - rewrite PM.gso in Hk by exact Hkne.
                 exact (HC1 k v Hk). }
             split.
             { cbn [snd].
               split.
               - intros L v HL2 Hk.
                 destruct (PM.E.eq_dec (key3 (wsyms L) (wleft L) L)
                             (key3 syms left len)) as [He | Hkne].
                 + exfalso.
                   pose proof (key3_inj _ _ _ _ _ _
                                 (wcell_dom3 L HL2) Hd3 He)
                     as (Hse & Hle2 & HLe).
                   apply Hnwc.
                   split; [rewrite <- HLe; exact HL2|].
                   split; [rewrite <- Hse, HLe; reflexivity
                           | rewrite <- Hle2, HLe; reflexivity].
                 + rewrite PM.gso in Hk by exact Hkne.
                   exact (proj1 HW1 L v HL2 Hk).
               - intros L HL2 (v0 & Hv0).
                 assert (Hkne2 : key3 syms left len <> tkey).
                 { intro He.
                   unfold tkey in He.
                   pose proof (key3_inj _ _ _ _ _ _ Hd3
                                 (wcell_dom3 (rt + 1)
                                    ltac:(clear -Hrt Hrtmx; lia)) He)
                     as (Hse & Hle2 & HLe).
                   apply Hnwc.
                   split; [clear -HLe Hrt Hrtmx; lia|].
                   split; [rewrite HLe; exact Hse
                           | rewrite HLe; exact Hle2]. }
                 destruct (PM.E.eq_dec (key3 (wsyms L) (wleft L) L)
                             (key3 syms left len)) as [He | Hkne].
                 + exfalso.
                   pose proof (key3_inj _ _ _ _ _ _
                                 (wcell_dom3 L
                                    ltac:(clear -HL2 Hrt Hrtmx Hmx; lia))
                                 Hd3 He) as (Hse & Hle2 & HLe).
                   apply Hnwc.
                   split; [clear -HLe HL2 Hrt Hrtmx Hmx; lia|].
                   split; [rewrite <- Hse, HLe; reflexivity
                           | rewrite <- Hle2, HLe; reflexivity].
                 + rewrite PM.gso in Hv0 by exact Hkne.
                   destruct (proj2 HW1 L HL2 ltac:(exists v0; exact Hv0))
                     as (v & Hv & Hv1).
                   exists v.
                   split; [| exact Hv1].
                   rewrite PM.gso
                     by (intro He2x; exact (Hkne2 (eq_sym He2x))).
                   exact Hv. }
             split; [cbn [snd]; exact Hmono2|].
             intros Hwc. exfalso. exact (Hnwc Hwc).
  Qed.

  (** The top fold makes the walk's own top call, and the target
      persists to the end. *)
  Lemma cnt_fold_reach : forall (i : nat) (n0 : Z) (m : PM.t Z)
                                (sum0 : Z),
    2 <= n0 ->
    Z.of_nat i <= 2 ^ 20 ->
    n0 <= wsyms 1 -> wsyms 1 < n0 + Z.of_nat i ->
    CINV m -> WINV m ->
    exists v,
      PM.find tkey
        (snd ((fix cnt (i0 : nat) (n sum : Z) (memo : PM.t Z)
                 {struct i0} : Z * PM.t Z :=
                 match i0 with
                 | O => (sum, memo)
                 | S i' =>
                     let '(got, memo') :=
                       countF (Z.to_nat mxw + 1)%nat mxw n 2 1 memo in
                     cnt i' (n + 1) (sum + got) memo'
                 end) i n0 sum0 m))
      = Some v /\ 1 <= v.
  Proof.
    induction i as [|i IH]; intros n0 m sum0 Hn0 Hicap Hlo Hhi HC HW.
    - exfalso. clear -Hlo Hhi; cbn in Hhi; lia.
    - assert (Hdom : CDOM n0 2 1).
      { unfold CDOM.
        assert ((2:Z) ^ 20 <= 2 ^ 21)
          by (apply Z.pow_le_mono_r; clear; lia).
        pose proof (wsyms_mono 1 ltac:(clear -Hmx; lia)) as _.
        split; [unfold wsyms in Hlo;
                pose proof Hwcap; clear -Hn0 Hlo H H0; lia|].
        split; [clear -Hn0; lia|].
        split; [clear -Hmx Hrtmx Hrt; lia|].
        left; clear -Hrtmx Hrt; lia. }
      assert (Hlink : Z.of_nat (Z.to_nat mxw + 1)%nat = mxw + 2 - 1).
      { rewrite Nat2Z.inj_add, Z2Nat.id by (clear -Hmx; lia).
        clear; lia. }
      pose proof (count_sound (Z.to_nat mxw + 1)%nat n0 2 1 m
                    Hlink Hdom HC HW) as (Hg & HCc & HWc & Hmc & Hwarm).
      destruct (countF (Z.to_nat mxw + 1)%nat mxw n0 2 1 m)
        as [got memo'] eqn:HCF.
      cbn [fst snd] in Hg, HCc, HWc, Hmc, Hwarm.
      destruct (Z.eq_dec n0 (wsyms 1)) as [-> | Hne].
      + (* the walk's top call *)
        assert (Hwc : iswcell (wsyms 1) 2 1).
        { split; [clear -Hmx; lia|].
          split; [reflexivity|].
          unfold wleft, kleft.
          change (Z.to_nat (1 - 1)) with 0%nat.
          cbn [kleft_aux].
          reflexivity. }
        destruct (Hwarm Hwc) as [_ Htgt].
        destruct (Htgt ltac:(clear -Hrt; lia)) as (v & Hv & Hv1).
        (* persist through the remaining iterations *)
        assert (Hpers : forall (i0 : nat) (n1 sum1 : Z) (m1 : PM.t Z),
                   CINV m1 -> WINV m1 ->
                   PM.find tkey m1 = Some v ->
                   2 <= n1 -> n1 + Z.of_nat i0 <= 2 ^ 21 + 1 ->
                   PM.find tkey
                     (snd ((fix cnt (i1 : nat) (n sum : Z)
                              (memo : PM.t Z) {struct i1} : Z * PM.t Z :=
                              match i1 with
                              | O => (sum, memo)
                              | S i' =>
                                  let '(got0, memo'0) :=
                                    countF (Z.to_nat mxw + 1)%nat mxw n 2 1
                                      memo
                                  in cnt i' (n + 1) (sum + got0) memo'0
                              end) i0 n1 sum1 m1))
                   = Some v).
        { induction i0 as [|i0 IHp]; intros n1 sum1 m1 HC2 HW2 Hf2
            Hn1 Hcap2.
          - cbn [snd]. exact Hf2.
          - assert (Hdom2 : CDOM n1 2 1).
            { unfold CDOM.
              split; [clear -Hn1 Hcap2; lia|].
              split; [clear -Hn1; lia|].
              split; [clear -Hmx Hrtmx Hrt; lia|].
              left; clear -Hrtmx Hrt; lia. }
            pose proof (count_sound (Z.to_nat mxw + 1)%nat n1 2 1 m1
                          Hlink Hdom2 HC2 HW2)
              as (_ & HC3 & HW3 & Hm3 & _).
            destruct (countF (Z.to_nat mxw + 1)%nat mxw n1 2 1 m1)
              as [got1 memo1] eqn:HCF2.
            cbn [snd] in HC3, HW3, Hm3.
            apply (IHp (n1 + 1) (sum1 + got1) memo1 HC3 HW3
                     (Hm3 tkey v Hf2)
                     ltac:(clear -Hn1; lia)
                     ltac:(clear -Hcap2; lia)). }
        exists v.
        split; [| exact Hv1].
        apply (Hpers i (wsyms 1 + 1) (sum0 + got) memo' HCc HWc Hv
                 ltac:(clear -Hn0; lia)).
        pose proof Hwcap as Hc2.
        unfold wsyms.
        assert (H21 : (2:Z) ^ 21 = 2097152) by (vm_compute; reflexivity).
        assert (H20 : (2:Z) ^ 20 = 1048576) by (vm_compute; reflexivity).
        clear -Hc2 Hicap H20 H21; lia.
      + (* not yet: recurse *)
        apply (IH (n0 + 1) memo' (sum0 + got) ltac:(clear -Hn0; lia)
                 ltac:(clear -Hicap; lia)
                 ltac:(clear -Hlo Hne; lia)
                 ltac:(clear -Hhi; lia) HCc HWc).
  Qed.

End CountReach.
