(** * EnoughFitsB8 — session 6: the dp-side (o1-o6 + open_future).

    THE DESIGN MOVE, named (two instances make it a pattern): carry
    the position-side quantity AS the accounting quantity.
    Instance 1 (B5, AJP): the intra-unit room [aj_left] IS the
    accounting rem, so preservation is local chain algebra and the
    global mass-sum bridge was never built.  Instance 2 (here,
    descend_mem): the it_subsz fold IS the chain rem along the opened
    unit's descent, so o4's telescoping and o5's openness are ONE
    induction.

    o1: dp_max's least-drain is chain_codes in batched form — the
    composite (drain, then the use-loop's j codes) is the plain replay
    chain_codes (least + j), aligning dp_max_child_le's position with
    the invariant's accounting.
    o2: dp_max dominates its own mem parameter at COMPLETE nodes (the
    general floor is FALSE at a loop node with an empty use range).
    o3: the kraft feasibility kit under the completeness premise.
    o6: the juncture walk, iterated to the complete node at mx.
    open_future: at the depth-clamped fuel S (to_nat (mx - len)) —
    fixed fuel would force the seed bound at overshot fuel, where
    dp_max's value is not known bounded. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Inftrees ItGTblRev ItGTblGeom ItGTblSortWin ItGTblCover ItGSubCover.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import Gap7Strict.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import EnoughDP.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import EnoughFitsDesign EnoughFitsA12 EnoughFitsB1
  EnoughFitsB2 EnoughFitsB3 EnoughFitsB4 EnoughFitsB5 EnoughFitsB6
  EnoughFitsB7.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   1.  chain_codes plumbing.
   ========================================================================== *)

Lemma chain_codes_compose : forall a b s m r,
  chain_codes (a + b) s m r
  = chain_codes b s (fst (chain_codes a s m r)) (snd (chain_codes a s m r)).
Proof.
  induction a as [|a IH]; intros b s m r.
  - cbn [Nat.add chain_codes fst snd]. reflexivity.
  - cbn [Nat.add chain_codes].
    destruct (chain_code s m r) as [m' r'].
    apply IH.
Qed.

(** Burning exactly the open slots: no charge. *)
Lemma chain_codes_burn : forall k s m,
  chain_codes k s m (Z.of_nat k) = (m, 0).
Proof.
  induction k as [|k IH]; intros s m.
  - cbn [chain_codes]. reflexivity.
  - cbn [chain_codes].
    unfold chain_code.
    destruct (Z.eqb_spec (Z.of_nat (S k)) 0) as [Habs|_];
      [exfalso; clear -Habs; lia|].
    replace (Z.of_nat (S k) - 1) with (Z.of_nat k) by (clear; lia).
    apply IH.
Qed.

(** Consuming within the open table: pure decrement. *)
Lemma chain_codes_dec : forall k s m r,
  Z.of_nat k <= r ->
  chain_codes k s m r = (m, r - Z.of_nat k).
Proof.
  induction k as [|k IH]; intros s m r Hk.
  - cbn [chain_codes]. f_equal. clear; lia.
  - cbn [chain_codes].
    unfold chain_code.
    destruct (Z.eqb_spec r 0) as [He|_];
      [exfalso; clear -He Hk; lia|].
    rewrite (IH s m (r - 1)) by (clear -Hk; lia).
    f_equal. clear; lia.
Qed.

(* ==========================================================================
   2.  o1 — the drain/chain correspondence.
   ========================================================================== *)

Lemma drain_chain_pos : forall fuel s x mem rem,
  0 < s -> 1 <= rem -> 0 <= x -> (Z.to_nat x + 1 <= fuel)%nat ->
  chain_codes (Z.to_nat x) s mem rem
  = (snd (fst (drain fuel s x mem rem)),
     snd (drain fuel s x mem rem) - fst (fst (drain fuel s x mem rem))).
Proof.
  induction fuel as [|f IH]; intros s x mem rem Hs Hr Hx Hfuel;
    [exfalso; clear -Hfuel; lia|].
  cbn [drain].
  destruct (Z.ltb_spec rem x) as [Hlt|Hge].
  - (* close the table, open the next: burn rem slots then compose *)
    replace (Z.to_nat x)
      with (Z.to_nat rem + (S (Z.to_nat (x - rem - 1))))%nat
      by (clear -Hlt Hr; lia).
    rewrite chain_codes_compose.
    rewrite (chain_codes_dec (Z.to_nat rem) s mem rem)
      by (rewrite Z2Nat.id by (clear -Hr; lia); clear; lia).
    cbn [fst snd].
    rewrite Z2Nat.id by (clear -Hr; lia).
    rewrite Z.sub_diag.
    cbn [chain_codes].
    unfold chain_code.
    change (0 =? 0) with true. cbv iota.
    rewrite <- (IH s (x - rem) (mem + s) s Hs
                  ltac:(clear -Hs; lia) ltac:(clear -Hlt Hr; lia)
                  ltac:(clear -Hfuel Hlt Hr Hx; lia)).
    replace (Z.to_nat (x - rem)) with (S (Z.to_nat (x - rem - 1)))
      by (clear -Hlt Hr; lia).
    cbn [chain_codes].
    unfold chain_code.
    destruct (Z.eqb_spec s 0) as [Habs|_]; [exfalso; clear -Habs Hs; lia|].
    reflexivity.
  - (* everything fits in the open table *)
    rewrite (chain_codes_dec (Z.to_nat x) s mem rem)
      by (rewrite Z2Nat.id by (clear -Hx; lia); clear -Hge; lia).
    cbn [fst snd].
    rewrite Z2Nat.id by (clear -Hx; lia).
    reflexivity.
Qed.

Lemma drain_chain : forall s x mem rem,
  0 < s -> 0 <= rem -> 0 <= x ->
  chain_codes (Z.to_nat x) s mem rem
  = (snd (fst (drain (Z.to_nat x + 2) s x mem rem)),
     snd (drain (Z.to_nat x + 2) s x mem rem)
       - fst (fst (drain (Z.to_nat x + 2) s x mem rem))).
Proof.
  intros s x mem rem Hs Hr Hx.
  destruct (Z.eq_dec rem 0) as [-> | Hne].
  - destruct (Z.eq_dec x 0) as [-> | Hxne].
    + change (Z.to_nat 0 + 2)%nat with 2%nat.
      change (Z.to_nat 0) with 0%nat.
      cbn [drain chain_codes].
      destruct (Z.ltb_spec 0 0) as [Habs|_]; [exfalso; clear -Habs; lia|].
      cbn [fst snd]. reflexivity.
    + (* first step burns no x but opens the table *)
      replace (Z.to_nat x + 2)%nat with (S (Z.to_nat x + 1))%nat
        by (clear; lia).
      cbn [drain].
      destruct (Z.ltb_spec 0 x) as [_|Habs];
        [| exfalso; clear -Habs Hx Hxne; lia].
      rewrite Z.sub_0_r.
      assert (Hb : chain_codes (Z.to_nat x) s mem 0
                   = chain_codes (Z.to_nat x) s (mem + s) s).
      { replace (Z.to_nat x) with (S (Z.to_nat (x - 1)))
          by (clear -Hx Hxne; lia).
        cbn [chain_codes].
        unfold chain_code.
        change (0 =? 0) with true. cbv iota.
        destruct (Z.eqb_spec s 0) as [Habs2|_];
          [exfalso; clear -Habs2 Hs; lia|].
        reflexivity. }
      rewrite Hb.
      apply drain_chain_pos;
        [exact Hs | clear -Hs; lia | exact Hx | clear; lia].
  - apply drain_chain_pos;
      [exact Hs | clear -Hr Hne; lia | exact Hx | clear; lia].
Qed.

(* ==========================================================================
   3.  o2 — dp_max dominates its own mem.
   ========================================================================== *)

Lemma drain_mem_mono : forall fuel s x mem rem,
  0 <= s ->
  mem <= snd (fst (drain fuel s x mem rem)).
Proof.
  induction fuel as [|f IH]; intros s x mem rem Hs.
  - cbn [drain fst snd]. clear; lia.
  - cbn [drain].
    destruct (rem <? x).
    + eapply Z.le_trans; [| apply (IH s (x - rem) (mem + s) s Hs)].
      clear -Hs; lia.
    + cbn [fst snd]. clear; lia.
Qed.

(** At a COMPLETE node dp_max is the drained mem, which dominates the
    node's own mem.  (At a loop node with an empty use range the
    accumulator 0 escapes, so the floor is stated where the walk uses
    it: the complete node the walk always reaches at mx.) *)
Lemma dp_max_complete_ge : forall f mx rt syms left len mem rem,
  syms = left ->
  mem <= dp_max (S f) mx rt syms left len mem rem.
Proof.
  intros f mx rt syms left len mem rem He.
  cbn [dp_max].
  destruct (Z.eqb_spec syms left) as [_|Habs]; [| exfalso; exact (Habs He)].
  destruct (drain (Z.to_nat left + 2) (2 ^ (len - rt)) left mem rem)
    as [[u1 m1] r1] eqn:Hd.
  pose proof (drain_mem_mono (Z.to_nat left + 2) (2 ^ (len - rt))
                left mem rem
                ltac:(apply Z.pow_nonneg; clear; lia)) as HM.
  rewrite Hd in HM. cbn [fst snd] in HM. exact HM.
Qed.

(* ==========================================================================
   4.  o3 — the feasibility kit: kleft's mass identity and the
       symbols-vs-patterns bounds at a juncture.
   ========================================================================== *)

Lemma mul_cancel_le : forall a b p, 0 < p -> a * p <= b * p -> a <= b.
Proof.
  intros a b p Hp H.
  destruct (Z.le_gt_cases a b) as [Hle|Hgt]; [exact Hle | exfalso].
  assert (Hm : b * p <= (a - 1) * p)
    by (apply Z.mul_le_mono_nonneg_r; clear -Hp Hgt; lia).
  rewrite Z.mul_sub_distr_r, Z.mul_1_l in Hm.
  clear -H Hm Hp; lia.
Qed.

Lemma wmass_split : forall a b l cnt,
  wmass (a + b) l cnt = wmass a l cnt + wmass b (l + Z.of_nat a) cnt.
Proof.
  induction a as [|a IH]; intros b l cnt.
  - cbn [Nat.add wmass].
    replace (l + Z.of_nat 0) with l by (clear; cbn; lia).
    clear; lia.
  - cbn [Nat.add wmass].
    rewrite IH.
    replace (l + 1 + Z.of_nat a) with (l + Z.of_nat (S a))
      by (clear; lia).
    clear; lia.
Qed.

Lemma aux_split : forall a b cnt l,
  rem_syms_aux (a + b) cnt l
  = rem_syms_aux a cnt l + rem_syms_aux b cnt (l + Z.of_nat a).
Proof.
  induction a as [|a IH]; intros b cnt l.
  - cbn [Nat.add rem_syms_aux].
    replace (l + Z.of_nat 0) with l by (clear; cbn; lia).
    clear; lia.
  - cbn [Nat.add rem_syms_aux].
    rewrite IH.
    replace (l + 1 + Z.of_nat a) with (l + Z.of_nat (S a))
      by (clear; lia).
    clear; lia.
Qed.

(** kleft's own left-child law. *)
Lemma kleft_aux_last : forall n cnt l acc,
  kleft_aux (S n) cnt l acc
  = 2 * kleft_aux n cnt l acc - cnt (l + Z.of_nat n).
Proof.
  induction n as [|n IH]; intros cnt l acc.
  - cbn [kleft_aux].
    replace (l + Z.of_nat 0) with l by (clear; cbn; lia).
    clear; lia.
  - change (kleft_aux (S (S n)) cnt l acc)
      with (kleft_aux (S n) cnt (l + 1) (2 * acc - cnt l)).
    rewrite IH.
    change (kleft_aux (S n) cnt l acc)
      with (kleft_aux n cnt (l + 1) (2 * acc - cnt l)).
    replace (l + 1 + Z.of_nat n) with (l + Z.of_nat (S n))
      by (clear; lia).
    reflexivity.
Qed.

Lemma kleft_step : forall cnt l,
  1 <= l ->
  kleft cnt (l + 1) = 2 * (kleft cnt l - cnt l).
Proof.
  intros cnt l Hl.
  unfold kleft.
  replace (l + 1 - 1) with l by (clear; lia).
  replace (Z.to_nat l) with (S (Z.to_nat (l - 1))) by (clear -Hl; lia).
  rewrite kleft_aux_last.
  rewrite Z2Nat.id by (clear -Hl; lia).
  replace (1 + (l - 1)) with l by (clear; lia).
  clear; lia.
Qed.

(** The suffix mass identity, from completeness. *)
Lemma kleft_suffix : forall cnt k,
  wmass 15%nat 1 cnt = 2 ^ 15 ->
  (Z.of_nat k <= 14)%Z ->
  kleft cnt (1 + Z.of_nat k) * 2 ^ (15 - (1 + Z.of_nat k))
  = wmass (15 - k)%nat (1 + Z.of_nat k) cnt.
Proof.
  intros cnt k Hcomp Hk.
  induction k as [|k IH].
  - cbn [Z.of_nat].
    replace (1 + 0) with 1 by (clear; lia).
    change (15 - 0)%nat with 15%nat.
    rewrite Hcomp.
    unfold kleft.
    change (Z.to_nat (1 - 1)) with 0%nat.
    cbn [kleft_aux].
    clear; lia.
  - assert (Hk' : Z.of_nat k <= 14) by (clear -Hk; lia).
    specialize (IH Hk').
    replace (1 + Z.of_nat (S k)) with ((1 + Z.of_nat k) + 1)
      by (clear; lia).
    rewrite kleft_step by (clear; lia).
    replace (15 - k)%nat with (S (15 - S k))%nat in IH
      by (clear -Hk; lia).
    cbn [wmass] in IH.
    replace (15 - (1 + Z.of_nat k + 1)) with (15 - (1 + Z.of_nat k) - 1)
      by (clear; lia).
    assert (Hp : 2 * 2 ^ (15 - (1 + Z.of_nat k) - 1)
                 = 2 ^ (15 - (1 + Z.of_nat k))).
    { rewrite <- Z.pow_succ_r by (clear -Hk; lia).
      f_equal. clear; lia. }
    replace (2 * (kleft cnt (1 + Z.of_nat k) - cnt (1 + Z.of_nat k))
               * 2 ^ (15 - (1 + Z.of_nat k) - 1))
      with ((kleft cnt (1 + Z.of_nat k) - cnt (1 + Z.of_nat k))
              * (2 * 2 ^ (15 - (1 + Z.of_nat k) - 1)))
      by ring.
    rewrite Hp.
    rewrite Z.mul_sub_distr_r.
    replace ((1 + Z.of_nat k) + 1) with (1 + Z.of_nat k + 1)
      by (clear; lia).
    clear -IH; lia.
Qed.

(** Symbols dominate their own mass at the window scale, and are
    dominated by it at the max scale. *)
Lemma aux_ge_mass : forall n cnt l,
  (forall c0, 0 <= cnt c0) ->
  1 <= l -> l + Z.of_nat n <= 16 ->
  wmass n l cnt <= rem_syms_aux n cnt l * 2 ^ (15 - l).
Proof.
  induction n as [|n IH]; intros cnt l Hnn Hl Hrange.
  - cbn [wmass rem_syms_aux]. clear; lia.
  - cbn [wmass rem_syms_aux].
    rewrite Z.mul_add_distr_r.
    pose proof (IH cnt (l + 1) Hnn ltac:(clear -Hl; lia)
                  ltac:(clear -Hrange; lia)) as H1.
    pose proof (rem_syms_aux_nonneg n cnt (l + 1) Hnn) as H2.
    assert (Hpm : 2 ^ (15 - (l + 1)) <= 2 ^ (15 - l))
      by (apply Z.pow_le_mono_r; clear; lia).
    assert (H3 : rem_syms_aux n cnt (l + 1) * 2 ^ (15 - (l + 1))
                 <= rem_syms_aux n cnt (l + 1) * 2 ^ (15 - l))
      by (apply Z.mul_le_mono_nonneg_l; first [exact Hpm | exact H2]).
    clear -H1 H3; lia.
Qed.

Lemma aux_le_mass : forall n cnt l mx,
  (forall c0, 0 <= cnt c0) ->
  1 <= l -> l + Z.of_nat n <= mx + 1 -> mx <= 15 ->
  rem_syms_aux n cnt l * 2 ^ (15 - mx) <= wmass n l cnt.
Proof.
  induction n as [|n IH]; intros cnt l mx Hnn Hl Hrange Hmx.
  - cbn [wmass rem_syms_aux]. clear; lia.
  - cbn [wmass rem_syms_aux].
    rewrite Z.mul_add_distr_r.
    pose proof (IH cnt (l + 1) mx Hnn ltac:(clear -Hl; lia)
                  ltac:(clear -Hrange; lia) Hmx) as H1.
    assert (H2 : cnt l * 2 ^ (15 - mx) <= cnt l * 2 ^ (15 - l))
      by (apply Z.mul_le_mono_nonneg_l;
          first [apply Hnn
                | apply Z.pow_le_mono_r; clear -Hrange; lia]).
    clear -H1 H2; lia.
Qed.

(** The three juncture facts (l < mx), under completeness. *)
Section Feasibility.
  Variable cnt : zarr.
  Variable mx : Z.
  Hypothesis Hnn : forall c0, 0 <= cnt c0.
  Hypothesis Hmx : 1 <= mx <= 15.
  Hypothesis Hmxz : forall l, mx < l <= 15 -> cnt l = 0.
  Hypothesis Hmxpos : 1 <= cnt mx.
  Hypothesis Hcomp : wmass 15%nat 1 cnt = 2 ^ 15.

  (** The suffix identity in juncture form: mass over [l, mx]. *)
  Lemma suffix_mass : forall l,
    1 <= l <= mx ->
    wmass (Z.to_nat (mx - l + 1)) l cnt = kleft cnt l * 2 ^ (15 - l).
  Proof.
    intros l Hl.
    pose proof (kleft_suffix cnt (Z.to_nat (l - 1)) Hcomp
                  ltac:(clear -Hl Hmx; lia)) as HS.
    rewrite Z2Nat.id in HS by (clear -Hl; lia).
    replace (1 + (l - 1)) with l in HS by (clear; lia).
    rewrite HS.
    replace (15 - Z.to_nat (l - 1))%nat
      with (Z.to_nat (mx - l + 1) + Z.to_nat (15 - mx))%nat
      by (clear -Hl Hmx; lia).
    rewrite wmass_split.
    rewrite (wmass_zero_on (Z.to_nat (15 - mx))).
    2:{ intros i Hi.
        apply Hmxz.
        rewrite Z2Nat.id in Hi by (clear -Hl Hmx; lia).
        clear -Hi Hl Hmx; lia. }
    clear; lia.
  Qed.

  Lemma syms_ge_left : forall l,
    1 <= l <= mx ->
    kleft cnt l <= rem_syms cnt l mx.
  Proof.
    intros l Hl.
    apply (mul_cancel_le _ _ (2 ^ (15 - l)))
      ;[apply Z.pow_pos_nonneg; clear -Hl Hmx; lia|].
    unfold rem_syms.
    eapply Z.le_trans;
      [rewrite <- (suffix_mass l Hl) | apply aux_ge_mass];
      [apply Z.le_refl | exact Hnn | clear -Hl; lia
       | rewrite Z2Nat.id by (clear -Hl Hmx; lia); clear -Hmx; lia].
  Qed.

  Lemma syms_le_cap : forall l,
    1 <= l <= mx ->
    rem_syms cnt l mx <= kleft cnt l * 2 ^ (mx - l).
  Proof.
    intros l Hl.
    apply (mul_cancel_le _ _ (2 ^ (15 - mx)))
      ;[apply Z.pow_pos_nonneg; clear -Hmx; lia|].
    unfold rem_syms.
    eapply Z.le_trans;
      [apply (aux_le_mass (Z.to_nat (mx - l + 1)) cnt l mx Hnn
                ltac:(clear -Hl; lia)
                ltac:(rewrite Z2Nat.id by (clear -Hl; lia); clear; lia)
                ltac:(clear -Hmx; lia)) |].
    rewrite (suffix_mass l Hl).
    rewrite <- Z.mul_assoc.
    rewrite <- Z.pow_add_r by (clear -Hl Hmx; lia).
    replace (mx - l + (15 - mx)) with (15 - l) by (clear; lia).
    apply Z.le_refl.
  Qed.

  Lemma syms_gt_left : forall l,
    1 <= l < mx ->
    kleft cnt l < rem_syms cnt l mx.
  Proof.
    intros l Hl.
    assert (Hq : 0 < 2 ^ (15 - l))
      by (apply Z.pow_pos_nonneg; clear -Hl Hmx; lia).
    assert (Hqm : 0 < 2 ^ (15 - mx))
      by (apply Z.pow_pos_nonneg; clear -Hmx; lia).
    (* split the mx term off both sides *)
    assert (Hsplit : rem_syms cnt l mx
                     = rem_syms_aux (Z.to_nat (mx - l)) cnt l + cnt mx).
    { unfold rem_syms.
      replace (Z.to_nat (mx - l + 1))
        with (Z.to_nat (mx - l) + 1)%nat by (clear -Hl; lia).
      rewrite aux_split.
      cbn [rem_syms_aux].
      rewrite Z2Nat.id by (clear -Hl; lia).
      replace (l + (mx - l)) with mx by (clear; lia).
      clear; lia. }
    assert (Hmass : wmass (Z.to_nat (mx - l)) l cnt + cnt mx * 2 ^ (15 - mx)
                    = kleft cnt l * 2 ^ (15 - l)).
    { rewrite <- (suffix_mass l ltac:(clear -Hl; lia)).
      replace (Z.to_nat (mx - l + 1))
        with (Z.to_nat (mx - l) + 1)%nat by (clear -Hl; lia).
      rewrite wmass_split.
      cbn [wmass].
      rewrite Z2Nat.id by (clear -Hl; lia).
      replace (l + (mx - l)) with mx by (clear; lia).
      clear; lia. }
    (* symbols beat mass strictly through the mx term *)
    assert (Hge : wmass (Z.to_nat (mx - l)) l cnt
                  <= rem_syms_aux (Z.to_nat (mx - l)) cnt l * 2 ^ (15 - l))
      by (apply aux_ge_mass;
          [exact Hnn | clear -Hl; lia
           | rewrite Z2Nat.id by (clear -Hl; lia); clear -Hmx Hl; lia]).
    assert (Hterm : cnt mx * 2 ^ (15 - mx) < cnt mx * 2 ^ (15 - l)).
    { apply Z.mul_lt_mono_pos_l; [clear -Hmxpos; lia|].
      apply Z.pow_lt_mono_r; clear -Hl Hmx; lia. }
    apply (Z.mul_lt_mono_pos_r (2 ^ (15 - l))); [exact Hq|].
    rewrite Hsplit.
    rewrite Z.mul_add_distr_r.
    clear -Hmass Hge Hterm; lia.
  Qed.

  Lemma feas_least : forall l,
    1 <= l < mx ->
    dpm_least (rem_syms cnt l mx) (kleft cnt l) <= cnt l.
  Proof.
    intros l Hl.
    unfold dpm_least.
    apply Z.max_lub; [apply Hnn|].
    (* 2 kleft l - syms l <= cnt l  <->  kleft (l+1) <= syms (l+1) *)
    pose proof (syms_ge_left (l + 1) ltac:(clear -Hl; lia)) as HS.
    rewrite kleft_step in HS by (clear -Hl; lia).
    assert (Hrec : rem_syms cnt l mx = cnt l + rem_syms cnt (l + 1) mx).
    { unfold rem_syms.
      replace (Z.to_nat (mx - l + 1))
        with (S (Z.to_nat (mx - (l + 1) + 1)))%nat by (clear -Hl; lia).
      cbn [rem_syms_aux].
      reflexivity. }
    rewrite Hrec.
    clear -HS; lia.
  Qed.

  Lemma feas_most : forall l,
    1 <= l < mx ->
    cnt l <= dpm_most mx (rem_syms cnt l mx) (kleft cnt l) l.
  Proof.
    intros l Hl.
    unfold dpm_most.
    apply Z.div_le_lower_bound;
      [assert (2 ^ 1 <= 2 ^ (mx - l))
        by (apply Z.pow_le_mono_r; clear -Hl; lia);
       clear -H; lia|].
    (* (2^(mx-l) - 1) cnt l <= kleft l 2^(mx-l) - syms l
       <->  syms (l+1) <= kleft (l+1) * 2^(mx-l-1) *)
    pose proof (syms_le_cap (l + 1) ltac:(clear -Hl; lia)) as HS.
    rewrite kleft_step in HS by (clear -Hl; lia).
    assert (Hrec : rem_syms cnt l mx = cnt l + rem_syms cnt (l + 1) mx).
    { unfold rem_syms.
      replace (Z.to_nat (mx - l + 1))
        with (S (Z.to_nat (mx - (l + 1) + 1)))%nat by (clear -Hl; lia).
      cbn [rem_syms_aux].
      reflexivity. }
    rewrite Hrec.
    replace (mx - (l + 1)) with (mx - l - 1) in HS by (clear; lia).
    assert (Hp : 2 * 2 ^ (mx - l - 1) = 2 ^ (mx - l)).
    { rewrite <- Z.pow_succ_r by (clear -Hl; lia).
      f_equal. clear; lia. }
    replace (2 * (kleft cnt l - cnt l) * 2 ^ (mx - l - 1))
      with ((kleft cnt l - cnt l) * (2 * 2 ^ (mx - l - 1))) in HS by ring.
    rewrite Hp in HS.
    rewrite Z.mul_sub_distr_r in HS.
    (* target: 2^(mx-l) * cnt l <= kleft l * 2^(mx-l) - (cnt l + syms(l+1)) *)
    assert (Hc : cnt l * 2 ^ (mx - l) = 2 ^ (mx - l) * cnt l) by ring.
    clear -HS Hc; lia.
  Qed.

End Feasibility.

(* ==========================================================================
   5.  The juncture walk: dp_max dominates the actual code's own
       boundary-to-boundary step (o6's engine, shared with i2').
   ========================================================================== *)

Section Walk.
  Variable cnt : zarr.
  Variable mx R0 : Z.
  Hypothesis Hnn : forall c0, 0 <= cnt c0.
  Hypothesis Hmx : 1 <= mx <= 15.
  Hypothesis Hmxz : forall l, mx < l <= 15 -> cnt l = 0.
  Hypothesis Hmxpos : 1 <= cnt mx.
  Hypothesis Hcomp : wmass 15%nat 1 cnt = 2 ^ 15.
  Hypothesis HR0 : 1 <= R0.

  Lemma dpm_walk_step : forall f l,
    R0 + 1 <= l -> l < mx ->
    dp_max f mx R0 (rem_syms cnt (l + 1) mx) (kleft cnt (l + 1)) (l + 1)
      (fst (chain_at cnt R0 (l + 1))) (snd (chain_at cnt R0 (l + 1)))
    <= dp_max (S f) mx R0 (rem_syms cnt l mx) (kleft cnt l) l
         (fst (chain_at cnt R0 l)) (snd (chain_at cnt R0 l)).
  Proof.
    intros f l Hl Hlmx.
    (* the node is a live loop node *)
    assert (Hne : (rem_syms cnt l mx =? kleft cnt l) = false).
    { apply Z.eqb_neq.
      pose proof (syms_gt_left cnt mx Hnn Hmx Hmxz Hmxpos Hcomp l
                    ltac:(clear -Hl Hlmx HR0; lia)) as H.
      clear -H; lia. }
    set (SB := 2 ^ (l - R0)).
    assert (HSB : 0 < SB)
      by (unfold SB; apply Z.pow_pos_nonneg; clear -Hl HR0; lia).
    assert (Hr0 : 0 <= snd (chain_at cnt R0 l))
      by (apply chain_at_rem_nonneg; clear -Hl; lia).
    assert (Hle0 : 0 <= dpm_least (rem_syms cnt l mx) (kleft cnt l))
      by (unfold dpm_least; apply Z.le_max_l).
    (* the drain equation *)
    destruct (drain (Z.to_nat (dpm_least (rem_syms cnt l mx) (kleft cnt l))
                       + 2) SB
                (dpm_least (rem_syms cnt l mx) (kleft cnt l))
                (fst (chain_at cnt R0 l)) (snd (chain_at cnt R0 l)))
      as [[u1 m1] r1] eqn:Hd.
    pose proof (drain_chain SB
                  (dpm_least (rem_syms cnt l mx) (kleft cnt l))
                  (fst (chain_at cnt R0 l)) (snd (chain_at cnt R0 l))
                  HSB Hr0 Hle0) as HDC.
    rewrite Hd in HDC. cbn [fst snd] in HDC.
    (* the feasibility window *)
    pose proof (feas_least cnt mx Hnn Hmx Hmxz Hcomp l
                  ltac:(clear -Hl Hlmx HR0; lia)) as HFl.
    pose proof (feas_most cnt mx Hnn Hmx Hmxz Hcomp l
                  ltac:(clear -Hl Hlmx HR0; lia)) as HFm.
    set (j := Z.to_nat (cnt l - dpm_least (rem_syms cnt l mx)
                          (kleft cnt l))).
    assert (Hjlt : (j < Z.to_nat
                          (dpm_most mx (rem_syms cnt l mx) (kleft cnt l) l
                           - dpm_least (rem_syms cnt l mx) (kleft cnt l)
                           + 1))%nat)
      by (unfold j; clear -HFl HFm; lia).
    pose proof (dp_max_child_le f mx R0 (rem_syms cnt l mx) (kleft cnt l)
                  l (fst (chain_at cnt R0 l)) (snd (chain_at cnt R0 l))
                  u1 m1 r1 j Hne ltac:(fold SB; exact Hd) Hjlt) as HC.
    fold SB in HC.
    (* the child's position is the full-level replay *)
    assert (Hcomp1 : chain_codes j SB m1 (r1 - u1)
                     = chain_codes (Z.to_nat (cnt l)) SB
                         (fst (chain_at cnt R0 l))
                         (snd (chain_at cnt R0 l))).
    { replace (Z.to_nat (cnt l))
        with (Z.to_nat (dpm_least (rem_syms cnt l mx) (kleft cnt l)) + j)%nat
        by (unfold j; clear -HFl Hle0; lia).
      rewrite chain_codes_compose.
      rewrite HDC.
      cbn [fst snd].
      reflexivity. }
    rewrite Hcomp1 in HC.
    (* the child's parameters are the next juncture's *)
    assert (Huse : dpm_least (rem_syms cnt l mx) (kleft cnt l) + Z.of_nat j
                   = cnt l)
      by (unfold j; clear -HFl Hle0; lia).
    rewrite Huse in HC.
    assert (Hsyms : rem_syms cnt l mx - cnt l = rem_syms cnt (l + 1) mx).
    { unfold rem_syms.
      replace (Z.to_nat (mx - l + 1))
        with (S (Z.to_nat (mx - (l + 1) + 1)))%nat
        by (clear -Hlmx; lia).
      cbn [rem_syms_aux].
      clear; lia. }
    rewrite Hsyms in HC.
    assert (Hkl : 2 * (kleft cnt l - cnt l) = kleft cnt (l + 1))
      by (rewrite kleft_step by (clear -Hl HR0; lia); reflexivity).
    rewrite Hkl in HC.
    (* the child's accounting is the next boundary *)
    pose proof (chain_at_step cnt R0 l ltac:(clear -Hl; lia)) as HB.
    cbv zeta in HB.
    fold SB in HB.
    destruct (chain_codes (Z.to_nat (cnt l)) SB
                (fst (chain_at cnt R0 l)) (snd (chain_at cnt R0 l)))
      as [cm cr] eqn:HK.
    cbn [fst snd] in HC.
    unfold chain_descend in HB.
    rewrite HB.
    cbn [fst snd].
    exact HC.
  Qed.

  Lemma dpm_walk_iter : forall (k f : nat) l,
    R0 + 1 <= l -> l + Z.of_nat k <= mx -> (k <= f)%nat ->
    dp_max (S (f - k)) mx R0 (rem_syms cnt (l + Z.of_nat k) mx)
      (kleft cnt (l + Z.of_nat k)) (l + Z.of_nat k)
      (fst (chain_at cnt R0 (l + Z.of_nat k)))
      (snd (chain_at cnt R0 (l + Z.of_nat k)))
    <= dp_max (S f) mx R0 (rem_syms cnt l mx) (kleft cnt l) l
         (fst (chain_at cnt R0 l)) (snd (chain_at cnt R0 l)).
  Proof.
    induction k as [|k IH]; intros f l Hl Hrange Hkf.
    - replace (l + Z.of_nat 0) with l by (clear; cbn; lia).
      rewrite Nat.sub_0_r.
      apply Z.le_refl.
    - eapply Z.le_trans;
        [| apply (IH f l Hl ltac:(clear -Hrange; lia)
                    ltac:(clear -Hkf; lia))].
      replace (S (f - k)) with (S (S (f - S k))) by (clear -Hkf; lia).
      replace (l + Z.of_nat (S k)) with ((l + Z.of_nat k) + 1)
        by (clear; lia).
      apply dpm_walk_step;
        [clear -Hl; lia | clear -Hrange; lia].
  Qed.

  (** The walk's terminal: at mx the node is complete. *)
  Lemma syms_eq_left_mx : rem_syms cnt mx mx = kleft cnt mx.
  Proof.
    pose proof (suffix_mass cnt mx Hmx Hmxz Hcomp mx
                  ltac:(clear -Hmx; lia)) as HS.
    replace (Z.to_nat (mx - mx + 1)) with 1%nat in HS by (clear; lia).
    cbn [wmass] in HS.
    rewrite Z.add_0_r in HS.
    unfold rem_syms.
    replace (Z.to_nat (mx - mx + 1)) with 1%nat by (clear; lia).
    cbn [rem_syms_aux].
    assert (Hq : 0 < 2 ^ (15 - mx))
      by (apply Z.pow_pos_nonneg; clear -Hmx; lia).
    assert (Hle1 : cnt mx <= kleft cnt mx)
      by (apply (mul_cancel_le _ _ (2 ^ (15 - mx)) Hq); clear -HS; lia).
    assert (Hle2 : kleft cnt mx <= cnt mx)
      by (apply (mul_cancel_le _ _ (2 ^ (15 - mx)) Hq); clear -HS; lia).
    clear -Hle1 Hle2; lia.
  Qed.

End Walk.

(* ==========================================================================
   6.  The descent: the opened unit's charges telescope to the full
       lookahead (o4 + o5 in one induction, the fold AS the rem).
   ========================================================================== *)

(** The first code from a fresh boundary pays the opener. *)
Lemma first_charge : forall n s m,
  (1 <= n)%nat -> 0 <= s ->
  m + s <= fst (chain_codes n s m 0).
Proof.
  intros n s m Hn Hs.
  destruct n as [|n]; [exfalso; clear -Hn; lia|].
  cbn [chain_codes].
  unfold chain_code.
  change (0 =? 0) with true. cbv iota.
  apply chain_codes_mem_mono. exact Hs.
Qed.

Lemma descend_mem : forall cnt R0 SL' c0 m0 (j : nat),
  1 <= R0 -> R0 + 1 <= SL' ->
  (forall c, 0 <= cnt c) ->
  1 <= c0 ->
  chain_codes (Z.to_nat (cnt SL')) (2 ^ (SL' - R0))
      (fst (chain_at cnt R0 SL')) (snd (chain_at cnt R0 SL'))
    = chain_codes (Z.to_nat c0) (2 ^ (SL' - R0)) m0 0 ->
  (1 <= j)%nat ->
  (forall i, (1 <= i <= j)%nat ->
     0 < szfold (zset cnt SL' c0) R0 (SL' - R0) (2 ^ (SL' - R0)) i) ->
  chain_at cnt R0 (SL' + Z.of_nat j)
  = (m0 + 2 ^ (SL' + Z.of_nat j - R0),
     szfold (zset cnt SL' c0) R0 (SL' - R0) (2 ^ (SL' - R0)) j).
Proof.
  intros cnt R0 SL' c0 m0 j HR0 HSL Hnn Hc0 Hbase Hj Hpos.
  induction j as [|j IH]; [exfalso; clear -Hj; lia|].
  assert (HSB : 0 < 2 ^ (SL' - R0))
    by (apply Z.pow_pos_nonneg; clear -HSL HR0; lia).
  destruct j as [|j'].
  - (* the first boundary: opener + decrements + one doubling *)
    clear IH.
    pose proof (Hpos 1%nat ltac:(clear; lia)) as HP1.
    cbn [szfold] in HP1 |- *.
    rewrite Z.add_0_r in HP1 |- *.
    replace (SL' - R0 + R0) with SL' in HP1 |- * by (clear; lia).
    rewrite zset_same in HP1 |- *.
    assert (Hc0lt : c0 < 2 ^ (SL' - R0)) by (clear -HP1; lia).
    replace (SL' + Z.of_nat 1) with (SL' + 1) by (clear; cbn; lia).
    rewrite (chain_at_step cnt R0 SL' ltac:(clear -HSL; lia)).
    cbv zeta.
    rewrite Hbase.
    replace (Z.to_nat c0) with (S (Z.to_nat (c0 - 1)))
      by (clear -Hc0; lia).
    cbn [chain_codes].
    unfold chain_code at 1.
    change (0 =? 0) with true. cbv iota.
    rewrite (chain_codes_dec (Z.to_nat (c0 - 1)) _ _ (2 ^ (SL' - R0) - 1))
      by (rewrite Z2Nat.id by (clear -Hc0; lia); clear -Hc0lt; lia).
    rewrite Z2Nat.id by (clear -Hc0; lia).
    unfold chain_descend.
    destruct (Z.eqb_spec (2 ^ (SL' - R0) - 1 - (c0 - 1)) 0) as [Habs|_];
      [exfalso; clear -Habs Hc0lt; lia|].
    apply (f_equal2 (@pair Z Z)).
    + assert (Hpw : 2 ^ (SL' + 1 - R0) = 2 * 2 ^ (SL' - R0)).
      { rewrite <- Z.pow_succ_r by (clear -HSL HR0; lia).
        f_equal. clear; lia. }
      rewrite Hpw. clear; lia.
    + clear; lia.
  - (* the inductive boundary: pure decrements, still open *)
    specialize (IH ltac:(clear; lia)
                  ltac:(intros i Hi; apply Hpos; clear -Hi; lia)).
    set (jj := S j') in *.
    pose proof (Hpos (S jj) ltac:(unfold jj; clear; lia)) as HPS.
    pose proof (Hpos jj ltac:(unfold jj; clear; lia)) as HPj.
    cbn [szfold] in HPS.
    fold jj in HPS.
    set (F := szfold (zset cnt SL' c0) R0 (SL' - R0) (2 ^ (SL' - R0)) jj)
      in *.
    assert (Hcj : zset cnt SL' c0 (SL' - R0 + Z.of_nat jj + R0)
                  = cnt (SL' + Z.of_nat jj)).
    { rewrite zset_other by (unfold jj; clear; lia).
      f_equal. clear; lia. }
    rewrite Hcj in HPS.
    replace (SL' + Z.of_nat (S jj)) with ((SL' + Z.of_nat jj) + 1)
      by (clear; lia).
    rewrite (chain_at_step cnt R0 (SL' + Z.of_nat jj)
               ltac:(unfold jj; clear -HSL; lia)).
    cbv zeta.
    rewrite IH.
    rewrite (chain_codes_dec (Z.to_nat (cnt (SL' + Z.of_nat jj)))
               _ _ F)
      by (rewrite Z2Nat.id by (apply Hnn); clear -HPS; lia).
    rewrite Z2Nat.id by (apply Hnn).
    cbv iota.
    unfold chain_descend.
    destruct (Z.eqb_spec (F - cnt (SL' + Z.of_nat jj)) 0) as [Habs|_];
      [exfalso; clear -Habs HPS; lia|].
    cbv iota.
    apply (f_equal2 (@pair Z Z)).
    + assert (Hpw : 2 ^ (SL' + Z.of_nat jj + 1 - R0)
                    = 2 * 2 ^ (SL' + Z.of_nat jj - R0)).
      { rewrite <- Z.pow_succ_r by (unfold jj; clear -HSL HR0; lia).
        f_equal. clear; lia. }
      assert (Hpw2 : 2 ^ (SL' + Z.of_nat jj - R0)
                     = 2 ^ (SL' + Z.of_nat (S j') - R0)).
      { f_equal. }
      rewrite Hpw. cbn [fst]. clear; lia.
    + cbn [szfold snd].
      fold jj.
      rewrite Hcj.
      fold F.
      clear; lia.
Qed.

(* ==========================================================================
   7.  open_future — the crossing's future is inside dp_max.
   ========================================================================== *)

(** The core: from the fresh boundary the walk reaches mx's complete
    node, whose drained value dominates the descent's telescoped mem. *)
Lemma open_future_core : forall cnt0 R0 mx len SL' c0 m0 oc,
  (forall j, 0 <= cnt0 j) ->
  1 <= mx <= 15 ->
  (forall l, mx < l <= 15 -> cnt0 l = 0) ->
  1 <= cnt0 mx ->
  wmass 15%nat 1 cnt0 = 2 ^ 15 ->
  1 <= R0 ->
  R0 + 1 <= len -> len <= SL' <= mx ->
  1 <= c0 ->
  SL' - R0 <= oc <= mx - R0 ->
  chain_codes (Z.to_nat (cnt0 SL')) (2 ^ (SL' - R0))
      (fst (chain_at cnt0 R0 SL')) (snd (chain_at cnt0 R0 SL'))
    = chain_codes (Z.to_nat c0) (2 ^ (SL' - R0)) m0 0 ->
  (forall i, (1 <= i <= Z.to_nat (oc - (SL' - R0)))%nat ->
     0 < szfold (zset cnt0 SL' c0) R0 (SL' - R0) (2 ^ (SL' - R0)) i) ->
  m0 + 2 ^ oc
    <= dp_max (S (Z.to_nat (mx - len))) mx R0 (rem_syms cnt0 len mx)
         (kleft cnt0 len) len
         (fst (chain_at cnt0 R0 len)) (snd (chain_at cnt0 R0 len)).
Proof.
  intros cnt0 R0 mx len SL' c0 m0 oc Hnn0 Hmx Hmxz Hmxpos Hcomp HR0
         Hlen HSL Hc0 Hoc Hbase HFP.
  set (K := Z.to_nat (mx - len)).
  assert (Hwalk := dpm_walk_iter cnt0 mx R0 Hnn0 Hmx Hmxz Hmxpos Hcomp HR0
                     K K len Hlen
                     ltac:(unfold K; rewrite Z2Nat.id by (clear -HSL; lia);
                           clear; lia)
                     ltac:(clear; lia)).
  replace (len + Z.of_nat K) with mx in Hwalk
    by (unfold K; rewrite Z2Nat.id by (clear -HSL; lia); clear; lia).
  set (f' := (K - K)%nat) in *.
  assert (Hcmp : rem_syms cnt0 mx mx = kleft cnt0 mx)
    by (apply (syms_eq_left_mx cnt0 mx Hmx Hmxz Hcomp)).
  set (SBmx := 2 ^ (mx - R0)).
  assert (HSBmx : 0 < SBmx)
    by (unfold SBmx; apply Z.pow_pos_nonneg; clear -Hlen HSL HR0; lia).
  assert (Hrnn : 0 <= snd (chain_at cnt0 R0 mx))
    by (apply chain_at_rem_nonneg; clear -Hlen HSL; lia).
  assert (Hklmx : kleft cnt0 mx = cnt0 mx).
  { rewrite <- Hcmp. unfold rem_syms.
    replace (Z.to_nat (mx - mx + 1)) with 1%nat by (clear; lia).
    cbn [rem_syms_aux]. clear; lia. }
  destruct (drain (Z.to_nat (kleft cnt0 mx) + 2) SBmx (kleft cnt0 mx)
              (fst (chain_at cnt0 R0 mx)) (snd (chain_at cnt0 R0 mx)))
    as [[u1 m1] r1] eqn:Hd.
  assert (Hnode : dp_max (S f') mx R0 (rem_syms cnt0 mx mx)
                    (kleft cnt0 mx) mx
                    (fst (chain_at cnt0 R0 mx)) (snd (chain_at cnt0 R0 mx))
                  = m1).
  { apply (dp_max_complete f' mx R0 _ _ mx _ _ u1 m1 r1);
      [apply Z.eqb_eq; exact Hcmp | fold SBmx; exact Hd]. }
  pose proof (drain_chain SBmx (kleft cnt0 mx)
                (fst (chain_at cnt0 R0 mx)) (snd (chain_at cnt0 R0 mx))
                HSBmx Hrnn ltac:(rewrite Hklmx; clear -Hmxpos; lia)) as HDC.
  rewrite Hd in HDC. cbn [fst snd] in HDC.
  assert (HV : m1 = fst (chain_codes (Z.to_nat (kleft cnt0 mx)) SBmx
                           (fst (chain_at cnt0 R0 mx))
                           (snd (chain_at cnt0 R0 mx))))
    by (rewrite HDC; cbn [fst]; reflexivity).
  assert (Hfloor : m0 + 2 ^ oc <= m1).
  { rewrite HV.
    set (J := Z.to_nat (oc - (SL' - R0))).
    destruct (Nat.eq_dec J 0) as [HJ0 | HJpos].
    - assert (Hoceq : oc = SL' - R0)
        by (unfold J in HJ0; clear -HJ0 Hoc; lia).
      destruct (Z.eq_dec SL' mx) as [HSLe | HSLlt].
      + (* terminal level: the drained replay IS the base replay *)
        rewrite Hklmx.
        rewrite <- HSLe.
        unfold SBmx. rewrite <- HSLe.
        rewrite Hbase.
        pose proof (first_charge (Z.to_nat c0) (2 ^ (SL' - R0)) m0
                      ltac:(clear -Hc0; lia)
                      ltac:(apply Z.pow_nonneg; clear; lia)) as H.
        rewrite Hoceq.
        clear -H; lia.
      + (* one boundary past the open *)
        assert (Hstep1 : m0 + 2 ^ oc <= fst (chain_at cnt0 R0 (SL' + 1))).
        { rewrite (chain_at_step cnt0 R0 SL' ltac:(clear -HSL Hlen; lia)).
          cbv zeta.
          rewrite Hbase.
          destruct (chain_codes (Z.to_nat c0) (2 ^ (SL' - R0)) m0 0)
            as [mb rb] eqn:HKb.
          unfold chain_descend. cbn [fst].
          assert (Hfc : m0 + 2 ^ (SL' - R0) <= mb).
          { pose proof (first_charge (Z.to_nat c0) (2 ^ (SL' - R0)) m0
                          ltac:(clear -Hc0; lia)
                          ltac:(apply Z.pow_nonneg; clear; lia)) as H.
            rewrite HKb in H. cbn [fst] in H. exact H. }
          rewrite Hoceq.
          assert (Hif : 0 <= (if rb =? 0 then 0 else 2 ^ (SL' - R0))).
          { destruct (rb =? 0); [clear; lia|].
            apply Z.pow_nonneg; clear; lia. }
          clear -Hfc Hif; lia. }
        eapply Z.le_trans; [exact Hstep1|].
        eapply Z.le_trans;
          [apply (chain_at_mem_nonneg_mono cnt0 R0 (SL' + 1) mx
                    ltac:(clear -HSL Hlen HSLlt; lia) Hnn0)|].
        apply chain_codes_mem_mono.
        unfold SBmx; apply Z.pow_nonneg; clear; lia.
    - assert (HJ1 : (1 <= J)%nat) by (clear -HJpos; lia).
      pose proof (descend_mem cnt0 R0 SL' c0 m0 J HR0
                    ltac:(clear -HSL Hlen; lia) Hnn0 Hc0 Hbase HJ1
                    ltac:(intros i Hi; apply HFP; unfold J in *;
                          clear -Hi; lia))
        as HD.
      assert (HT : SL' + Z.of_nat J = R0 + oc)
        by (unfold J; rewrite Z2Nat.id by (clear -Hoc; lia); clear; lia).
      rewrite HT in HD.
      assert (Hfst : fst (chain_at cnt0 R0 (R0 + oc)) = m0 + 2 ^ oc).
      { rewrite HD. cbn [fst].
        replace (R0 + oc - R0) with oc by (clear; lia).
        reflexivity. }
      rewrite <- Hfst.
      eapply Z.le_trans;
        [apply (chain_at_mem_nonneg_mono cnt0 R0 (R0 + oc) mx
                  ltac:(clear -Hoc HSL Hlen; lia) Hnn0)|].
      apply chain_codes_mem_mono.
      unfold SBmx; apply Z.pow_nonneg; clear; lia. }
  rewrite Hnode in Hwalk.
  clear -Hwalk Hfloor; lia.
Qed.

(** The accounting in its applied spelling. *)
Lemma aj_acct_eq : forall cnt0 R0 st,
  aj_acct cnt0 R0 st
  = chain_codes (Z.to_nat (cnt0 (s_len st) - s_count st (s_len st)))
      (2 ^ (s_len st - R0))
      (fst (chain_at cnt0 R0 (s_len st)))
      (snd (chain_at cnt0 R0 (s_len st))).
Proof. intros. unfold aj_acct. cbv zeta. reflexivity. Qed.

(** The next length's count is live at a hit (cov_next_window's third
    conjunct, which gap_zeros_lem does not export). *)
Lemma gap_pos_lem : forall c cnt0 st,
  CovCtxOk c cnt0 -> CovInv c cnt0 st ->
  step_hit st = true ->
  (step_hit st && (s_len st =? x_max c))%bool = false ->
  0 < cnt0 (step_len c st).
Proof.
  intros c cnt0 st Hctx Hinv Hhit Hbrk.
  pose proof Hctx as Hctx2.
  destruct Hctx as (Hroot & Hmask & Hmx & Hmxnz & Hmxz & Hnn & _).
  destruct Hinv as (Hlen & Hhuff & HwinL & HwinU & Hcnt & Hpos & Hcov
                    & Hphase).
  assert (Hend : s_sym st + 1 = sw_offs cnt0 (s_len st) + cnt0 (s_len st)).
  { unfold step_hit, step_cnt in Hhit.
    rewrite zset_same in Hhit.
    apply Z.eqb_eq in Hhit.
    rewrite (Hcnt (s_len st) ltac:(clear -Hlen; lia)) in Hhit.
    rewrite Z.ltb_irrefl, Z.eqb_refl in Hhit.
    clear -Hhit; lia. }
  assert (Hnmx : s_len st <> x_max c).
  { rewrite Hhit in Hbrk. cbn [andb] in Hbrk.
    apply Z.eqb_neq in Hbrk. exact Hbrk. }
  destruct (Z.lt_ge_cases (s_sym st + 1) (sw_offs cnt0 15 + cnt0 15))
    as [Hnext|Hgone].
  - destruct (cov_next_window c cnt0 (s_len st) (s_sym st) Hctx2
                ltac:(clear -Hlen; lia)
                ltac:(clear -HwinL HwinU; lia) Hend Hnext)
      as (l1 & Hl1 & Hstart & Hpos1 & Hlens1 & Hzero).
    assert (Hsl : step_len c st = l1)
      by (unfold step_len; rewrite Hhit; exact Hlens1).
    rewrite Hsl. exact Hpos1.
  - exfalso.
    destruct (cov_exhausted c cnt0 (s_len st) (s_sym st) Hctx2
                ltac:(clear -Hlen; lia)
                ltac:(clear -HwinL HwinU; lia) Hgone) as [_ Hmxe].
    exact (Hnmx (eq_sym Hmxe)).
Qed.

Theorem open_future_lem : forall ty c cnt0 R0 st,
  x_root c = R0 ->
  CovCtxOk c cnt0 -> CovInv c cnt0 st ->
  SubLedger ty c cnt0 st ->
  AJ2 cnt0 R0 st -> AJP cnt0 R0 st -> AJW R0 st ->
  (forall j, 0 <= cnt0 j) ->
  wmass 15%nat 1 cnt0 = 2 ^ 15 ->
  (step_hit st && (s_len st =? x_max c))%bool = false ->
  open_guard c st = true ->
  s_drop st <> 0 ->
  fst (aj_acct cnt0 R0 st) + Z.shiftl 1 (open_curr c st)
    <= dp_max (S (Z.to_nat (x_max c - s_len st))) (x_max c) R0
         (rem_syms cnt0 (s_len st) (x_max c))
         (kleft cnt0 (s_len st)) (s_len st)
         (fst (chain_at cnt0 R0 (s_len st)))
         (snd (chain_at cnt0 R0 (s_len st))).
Proof.
  intros ty c cnt0 R0 st HR Hctx Hinv Hled HAJ HP HW Hnn0 Hcomp Hbrk Hop Hd.
  pose proof Hctx as Hctx2.
  pose proof Hinv as Hinv2.
  pose proof (aj_rem_one_at_open c cnt0 R0 st HR Hctx Hinv HP Hd Hbrk Hop)
    as Hone.
  pose proof (count_coh c cnt0 st Hctx Hinv) as [Hcc1 Hcck].
  pose proof (ajw_open c cnt0 R0 st HR Hctx Hinv Hbrk Hop) as HW'.
  pose proof (aj_off_zero_at_open c cnt0 R0 st HR Hctx Hinv Hbrk Hop)
    as Hoff0.
  destruct Hctx as (Hroot & Hmask & Hmx & Hmxnz & Hmxz & Hnn & _).
  destruct Hinv as (Hlen & Hhuff & HwinL & HwinU & Hcnt & Hpos & Hcov
                    & Hphase).
  destruct Hphase as [ (Habs & _) | (Hdr & Hrl & _) ];
    [exfalso; exact (Hd Habs)|].
  assert (HR0p : 1 <= R0) by (rewrite <- HR; clear -Hroot; lia).
  assert (Hlge : R0 + 1 <= s_len st) by (rewrite <- HR; clear -Hrl; lia).
  assert (Hlmx : s_len st <= x_max c).
  { destruct (Z.le_gt_cases (s_len st) (x_max c)) as [Hok|Hbad];
      [exact Hok | exfalso].
    rewrite (Hmxz (s_len st) ltac:(clear -Hbad Hlen; lia)) in Hcck.
    clear -Hcc1 Hcck; lia. }
  assert (Hmxpos : 1 <= cnt0 (x_max c))
    by (pose proof (Hnn0 (x_max c)); clear -Hmxnz H; lia).
  assert (Hod : open_drop c st = R0).
  { unfold open_drop.
    destruct (Z.eqb_spec (s_drop st) 0) as [He|_];
      [exfalso; exact (Hd He) | rewrite Hdr, HR; reflexivity]. }
  assert (HSLmx : step_len c st <= x_max c).
  { destruct (step_hit st) eqn:Hhit.
    - destruct (gap_zeros_lem c cnt0 st Hctx2 Hinv2 Hhit
                  ltac:(rewrite Hhit; exact Hbrk)) as [[_ Hj] _].
      exact Hj.
    - unfold step_len. rewrite Hhit. exact Hlmx. }
  set (oc := open_curr c st) in *.
  assert (Hocge : step_len c st - R0 <= oc).
  { unfold oc, open_curr.
    rewrite Hod.
    apply it_subsz_ge. }
  assert (Hocle : oc <= x_max c - R0).
  { unfold oc, open_curr.
    rewrite Hod.
    eapply Z.le_trans;
      [apply (it_subsz_le 16%nat (step_cnt st) R0 (x_max c)
                (step_len c st - R0)
                (Z.shiftl 1 (step_len c st - R0)))|].
    apply Z.max_lub; [clear -HSLmx; lia | clear; lia]. }
  set (m0 := fst (aj_acct cnt0 R0 st)).
  assert (HCC : chain_code (2 ^ (s_len st - R0)) (fst (aj_acct cnt0 R0 st))
                  (snd (aj_acct cnt0 R0 st))
                = (m0, 0)).
  { rewrite Hone. unfold chain_code.
    change (1 =? 0) with false. cbv iota.
    apply (f_equal2 (@pair Z Z)); [reflexivity | clear; lia]. }
  rewrite Z.shiftl_1_l.
  fold oc. fold m0.
  destruct HW' as [Habs | HW'].
  { exfalso. cbn [step_open_st s_drop] in Habs. rewrite Hod in Habs.
    clear -Habs HR0p; lia. }
  assert (Hleft' : aj_left R0 (step_open_st c st)
                   = 2 ^ (step_len c st - R0)).
  { unfold aj_left. rewrite Hoff0, Z.sub_0_r. reflexivity. }
  cbn [step_open_st s_curr s_len s_count s_drop] in HW'.
  rewrite Hleft' in HW'.
  destruct (step_hit st) eqn:Hhit.
  - (* HIT: the fresh unit opens at the jumped length *)
    assert (Hbrk2 : (step_hit st && (s_len st =? x_max c))%bool = false)
      by (rewrite Hhit; exact Hbrk).
    destruct (gap_zeros_lem c cnt0 st Hctx2 Hinv2 Hhit Hbrk2)
      as [[Hjl Hjmx] Hgz].
    pose proof (gap_pos_lem c cnt0 st Hctx2 Hinv2 Hhit Hbrk2) as Hc0pos.
    assert (Hone1 : s_count st (s_len st) = 1).
    { unfold step_hit, step_cnt in Hhit.
      rewrite zset_same in Hhit.
      apply Z.eqb_eq in Hhit. clear -Hhit; lia. }
    assert (HB0 : chain_at cnt0 R0 (step_len c st) = (m0, 0)).
    { replace (step_len c st)
        with ((s_len st + 1)
              + Z.of_nat (Z.to_nat (step_len c st - s_len st - 1)))
        at 1 by (rewrite Z2Nat.id by (clear -Hjl; lia); clear; lia).
      rewrite (chain_gap cnt0 R0 (s_len st + 1) _ ltac:(clear -Hlge; lia)).
      2:{ intros l Hl.
          rewrite Z2Nat.id in Hl by (clear -Hjl; lia).
          apply Hgz. clear -Hl; lia. }
      rewrite (chain_at_step cnt0 R0 (s_len st) ltac:(clear -Hlge; lia)).
      cbv zeta.
      replace (Z.to_nat (cnt0 (s_len st)))
        with (S (Z.to_nat (cnt0 (s_len st) - s_count st (s_len st))))
        by (clear -Hone1 Hcck; lia).
      rewrite chain_codes_tail.
      rewrite <- (aj_acct_eq cnt0 R0 st).
      rewrite HCC.
      cbn [fst snd].
      unfold chain_descend.
      change (0 =? 0) with true. cbv iota.
      cbn [fst snd].
      change (2 * 0 =? 0) with true. cbv iota.
      apply (f_equal2 (@pair Z Z)); [clear; lia | clear; lia]. }
    assert (Hbase : chain_codes (Z.to_nat (cnt0 (step_len c st)))
                      (2 ^ (step_len c st - R0))
                      (fst (chain_at cnt0 R0 (step_len c st)))
                      (snd (chain_at cnt0 R0 (step_len c st)))
                    = chain_codes (Z.to_nat (cnt0 (step_len c st)))
                        (2 ^ (step_len c st - R0)) m0 0)
      by (rewrite HB0; cbn [fst snd]; reflexivity).
    assert (HFP : forall i,
               (1 <= i <= Z.to_nat (oc - (step_len c st - R0)))%nat ->
               0 < szfold (zset cnt0 (step_len c st) (cnt0 (step_len c st)))
                     R0 (step_len c st - R0)
                     (2 ^ (step_len c st - R0)) i).
    { intros i Hi.
      destruct i as [|i']; [exfalso; clear -Hi; lia|].
      rewrite (szfold_ext_on (step_cnt st)
                 (zset cnt0 (step_len c st) (cnt0 (step_len c st)))
                 R0 (step_len c st - R0) (2 ^ (step_len c st - R0))
                 (S i')).
      2:{ intros i2 Hi2.
          destruct (Nat.eq_dec i2 0) as [-> | Hne2].
          - replace (step_len c st - R0 + Z.of_nat 0 + R0)
              with (step_len c st) by (clear; cbn; lia).
            rewrite zset_same.
            unfold step_cnt.
            rewrite zset_other by (clear -Hjl; lia).
            rewrite (Hcnt (step_len c st)
                       ltac:(clear -Hjl Hjmx Hmx Hlen; lia)).
            destruct (Z.ltb_spec (step_len c st) (s_len st)) as [Habs|_];
              [exfalso; clear -Habs Hjl; lia|].
            destruct (Z.eqb_spec (step_len c st) (s_len st)) as [Habs|_];
              [exfalso; clear -Habs Hjl; lia|].
            reflexivity.
          - replace (step_len c st - R0 + Z.of_nat i2 + R0)
              with (step_len c st + Z.of_nat i2) by (clear; lia).
            rewrite zset_other by (clear -Hne2; lia).
            unfold step_cnt.
            rewrite zset_other by (clear -Hjl Hne2; lia).
            rewrite (Hcnt (step_len c st + Z.of_nat i2)
                       ltac:(clear -Hi Hi2 Hocle Hmx Hjl Hlen; lia)).
            destruct (Z.ltb_spec (step_len c st + Z.of_nat i2) (s_len st))
              as [Habs|_]; [exfalso; clear -Habs Hjl; lia|].
            destruct (Z.eqb_spec (step_len c st + Z.of_nat i2) (s_len st))
              as [Habs|_]; [exfalso; clear -Habs Hjl; lia|].
            reflexivity. }
      apply HW'.
      clear -Hi; lia. }
    apply (open_future_core cnt0 R0 (x_max c) (s_len st) (step_len c st)
             (cnt0 (step_len c st)) m0 oc
             Hnn0 ltac:(clear -Hmx; lia) Hmxz Hmxpos Hcomp HR0p Hlge
             ltac:(clear -Hjl Hjmx; lia) ltac:(clear -Hc0pos; lia)
             ltac:(clear -Hocge Hocle; lia) Hbase HFP).
  - (* NO-HIT: the fresh unit opens at the same length *)
    assert (HSLeq : step_len c st = s_len st)
      by (unfold step_len; rewrite Hhit; reflexivity).
    rewrite HSLeq in HW', Hocge.
    assert (Hc01 : 1 <= s_count st (s_len st) - 1).
    { unfold step_hit, step_cnt in Hhit.
      rewrite zset_same in Hhit.
      apply Z.eqb_neq in Hhit.
      clear -Hhit Hcc1; lia. }
    assert (Hbase : chain_codes (Z.to_nat (cnt0 (s_len st)))
                      (2 ^ (s_len st - R0))
                      (fst (chain_at cnt0 R0 (s_len st)))
                      (snd (chain_at cnt0 R0 (s_len st)))
                    = chain_codes (Z.to_nat (s_count st (s_len st) - 1))
                        (2 ^ (s_len st - R0)) m0 0).
    { replace (Z.to_nat (cnt0 (s_len st)))
        with (S (Z.to_nat (cnt0 (s_len st) - s_count st (s_len st)))
              + Z.to_nat (s_count st (s_len st) - 1))%nat
        by (clear -Hcck Hcc1; lia).
      rewrite chain_codes_compose.
      assert (Hpre : chain_codes
                       (S (Z.to_nat (cnt0 (s_len st)
                                     - s_count st (s_len st))))
                       (2 ^ (s_len st - R0))
                       (fst (chain_at cnt0 R0 (s_len st)))
                       (snd (chain_at cnt0 R0 (s_len st)))
                     = (m0, 0)).
      { rewrite chain_codes_tail.
        rewrite <- (aj_acct_eq cnt0 R0 st).
        exact HCC. }
      rewrite Hpre.
      cbn [fst snd].
      reflexivity. }
    assert (HFP : forall i,
               (1 <= i <= Z.to_nat (oc - (s_len st - R0)))%nat ->
               0 < szfold (zset cnt0 (s_len st)
                             (s_count st (s_len st) - 1))
                     R0 (s_len st - R0) (2 ^ (s_len st - R0)) i).
    { intros i Hi.
      destruct i as [|i']; [exfalso; clear -Hi; lia|].
      rewrite (szfold_ext_on (step_cnt st)
                 (zset cnt0 (s_len st) (s_count st (s_len st) - 1))
                 R0 (s_len st - R0) (2 ^ (s_len st - R0)) (S i')).
      2:{ intros i2 Hi2.
          destruct (Nat.eq_dec i2 0) as [-> | Hne2].
          - replace (s_len st - R0 + Z.of_nat 0 + R0)
              with (s_len st) by (clear; cbn; lia).
            rewrite zset_same.
            unfold step_cnt.
            rewrite zset_same.
            reflexivity.
          - replace (s_len st - R0 + Z.of_nat i2 + R0)
              with (s_len st + Z.of_nat i2) by (clear; lia).
            rewrite zset_other by (clear -Hne2; lia).
            unfold step_cnt.
            rewrite zset_other by (clear -Hne2; lia).
            rewrite (Hcnt (s_len st + Z.of_nat i2)
                       ltac:(clear -Hi Hi2 Hocle Hmx Hlen Hlge; lia)).
            destruct (Z.ltb_spec (s_len st + Z.of_nat i2) (s_len st))
              as [Habs|_]; [exfalso; clear -Habs Hne2; lia|].
            destruct (Z.eqb_spec (s_len st + Z.of_nat i2) (s_len st))
              as [Habs|_]; [exfalso; clear -Habs Hne2; lia|].
            reflexivity. }
      apply HW'.
      clear -Hi; lia. }
    apply (open_future_core cnt0 R0 (x_max c) (s_len st) (s_len st)
             (s_count st (s_len st) - 1) m0 oc
             Hnn0 ltac:(clear -Hmx; lia) Hmxz Hmxpos Hcomp HR0p Hlge
             ltac:(clear -Hlmx; lia) Hc01
             ltac:(clear -Hocge Hocle; lia) Hbase HFP).
Qed.
