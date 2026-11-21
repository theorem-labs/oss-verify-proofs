(** * EnoughSplit — the enough.c table search, checked one range of n at a time.

    enough_phase walks every reachable (n, left) seed for n = 3..syms with
    ONE shared memo ([done], enough.c's been_here).  Evaluated in one go,
    enough_run 286 9 15 and enough_bound 286 9 14 take 926 s and 562 s in
    the VM.  This file proves that the walk may be cut into ranges of n,
    each started from a FRESH memo:

      enough_phase mx rt syms numm
        = Z.max (2 ^ rt) (max over the ranges of the range's own walk)

    ([enough_phase_segs]), so that each range is its own VM certificate in
    its own file (EnoughRng_*.v), every one under 5 minutes.

    The proof: the memo only skips states it has already counted.
    - [examine_upper]: a walk never exceeds the memo-free maximum
      [dp_max] (EnoughFitsB1) of what it starts from — skipping can only
      lower the result.
    - EnoughFitsB11.examine_sound: from a sound memo (MINV) it reaches it.
    - So each seed call returns exactly [Z.max large dp_max] ([call_eq]);
      the inner and outer loops therefore return the max of their input
      and of the same loops run from (0, empty) ([ein_eq], [eout_eq]),
      and a walk over consecutive ranges is the max of the ranges' walks
      ([seg_eq]).
    - [enough_run_open]: enough_run, with its guards computed, is the
      count phase ([cntR]) followed by enough_phase. *)

From Stdlib Require Import ZArith List Lia Bool FMapPositive.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import EnoughDP.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import EnoughFitsDesign EnoughFitsB1 EnoughFitsB9
  EnoughFitsB11 EnoughFitsB12.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   1.  A walk never exceeds the memo-free maximum.
   ========================================================================== *)

Lemma eloop_upper : forall f mxa rt syms left len subsz n use mem rem st acc,
  (forall s l L m r lg dn,
     fst (examineF f mxa rt s l L m r (lg, dn)) <= Z.max lg (dp_max f mxa rt s l L m r)) ->
  fst (eloopF f mxa rt syms left len subsz n use mem rem st)
  <= Z.max (fst st)
       (dpm_loop (fun u m r => dp_max f mxa rt (syms - u) (2 * (left - u)) (len + 1)
                                 (m + (if r =? 0 then 0 else subsz)) (2 * r))
                 subsz n use mem rem acc).
Proof.
  intros f mxa rt syms left len subsz n.
  induction n as [|n IH]; intros use mem rem st acc HU.
  - cbn [eloopF dpm_loop]. lia.
  - cbn [eloopF dpm_loop]. unfold chain_code. destruct st as [lg dn].
    destruct (rem =? 0); cbv beta iota;
      (eapply Z.le_trans; [eapply IH; exact HU|]);
      match goal with
      | |- Z.max (fst (examineF _ _ _ ?s ?l ?L ?m ?r (lg, dn))) (dpm_loop ?ch ?sz ?nn ?u ?mm ?rr ?ac1)
           <= Z.max _ (dpm_loop _ _ _ _ _ _ ?ac2) =>
          unify ac1 ac2;
          pose proof (HU s l L m r lg dn) as Hc;
          pose proof (dpm_loop_acc_le ch sz nn u mm rr ac2) as Hacc
      end;
      cbn [fst] in *; lia.
Qed.

Lemma examine_upper : forall f mxa rt syms left len mem rem lg dn,
  fst (examineF f mxa rt syms left len mem rem (lg, dn))
  <= Z.max lg (dp_max f mxa rt syms left len mem rem).
Proof.
  induction f as [|f IH]; intros mxa rt syms left len mem rem lg dn.
  - cbn [examineF dp_max fst]. lia.
  - destruct (syms =? left) eqn:Hc.
    + cbn [examineF dp_max]. rewrite Hc. cbv beta iota zeta.
      destruct (drain (Z.to_nat left + 2) (2 ^ (len - rt)) left mem rem) as [[u m1] r1].
      cbn [fst]. lia.
    + destruct (PM.find (key5 syms left len mem rem) dn) as [[]|] eqn:HF.
      * cbn [examineF]. rewrite Hc. cbv beta iota zeta. rewrite HF. cbn [fst]. lia.
      * rewrite (examineF_fresh_eq f mxa rt syms left len mem rem lg dn Hc HF).
        cbn [dp_max]. rewrite Hc. unfold dpm_least, dpm_most. cbv beta iota zeta.
        destruct (drain (Z.to_nat (Z.max 0 (2 * left - syms)) + 2) (2 ^ (len - rt))
                    (Z.max 0 (2 * left - syms)) mem rem) as [[u1 m1] r1].
        cbv beta iota.
        eapply Z.le_trans; [apply eloop_upper with (acc := 0); intros; apply IH|].
        cbn [fst]. lia.
Qed.

(* ==========================================================================
   2.  Each seed call returns exactly max(large, dp_max).
   ========================================================================== *)

Definition SEGH (mx rt B : Z) : Prop :=
  1 <= rt /\ rt <= mx <= 15 /\ B = mx + rt + 2 /\ rt + 1 <= mx - 1.

(** The phase's state invariant (EnoughFitsB12.PHINV, spelled out). *)
Definition SINV (mx rt B : Z) (st : Z * PM.t unit) : Prop :=
  0 <= fst st /\ MINV mx rt B (snd st) (fst st) (rt + 1).

Lemma minv_empty : forall mxa rt B large ell, MINV mxa rt B (PM.empty unit) large ell.
Proof.
  intros mxa rt B large ell s l L m r _ _ Hf. rewrite PM.gempty in Hf. discriminate.
Qed.

Lemma sinv_empty : forall mx rt B large, 0 <= large -> SINV mx rt B (large, PM.empty unit).
Proof. intros mx rt B large H. split; [exact H | apply minv_empty]. Qed.

Lemma efuel_link_s : forall mx rt B, SEGH mx rt B ->
  Z.of_nat (Z.to_nat mx + 1) = B - (rt + 1).
Proof.
  intros mx rt B (Hrt & Hmx & HB & Hlt).
  rewrite Nat2Z.inj_add, Z2Nat.id by lia. lia.
Qed.

Lemma doms_seed : forall mx rt B, SEGH mx rt B -> forall n left,
  0 <= n <= 2 ^ 21 -> 0 <= left <= n ->
  DOMS rt mx n left (rt + 1) (2 ^ rt) 0.
Proof.
  intros mx rt B (Hrt & Hmx & HB & Hlt) n left Hn Hl.
  unfold DOMS.
  assert (H15 : (2:Z) ^ 15 = 32768) by (vm_compute; reflexivity).
  assert (Hprt : 2 ^ rt <= 2 ^ 15) by (apply Z.pow_le_mono_r; lia).
  assert (Hprt0 : 0 < 2 ^ rt) by (apply Z.pow_pos_nonneg; lia).
  assert (Hp22 : 0 <= (rt + 1) * 2 ^ 22)
    by (apply Z.mul_nonneg_nonneg; [lia | apply Z.pow_nonneg; lia]).
  assert (Hsub0 : 0 <= 2 ^ (rt + 1 - rt)) by (apply Z.pow_nonneg; lia).
  split; [exact Hn|]. split; [exact Hl|]. split; [lia|].
  split; [left; lia|]. split; [lia|]. split; [lia | exact Hsub0].
Qed.

Lemma call_eq : forall mx rt B, SEGH mx rt B -> forall syms left st,
  0 <= syms <= 2 ^ 21 -> 0 <= left <= syms -> SINV mx rt B st ->
  fst (examineF (Z.to_nat mx + 1) mx rt syms left (rt + 1) (2 ^ rt) 0 st)
    = Z.max (fst st) (dp_max (Z.to_nat mx + 1) mx rt syms left (rt + 1) (2 ^ rt) 0)
  /\ SINV mx rt B (examineF (Z.to_nat mx + 1) mx rt syms left (rt + 1) (2 ^ rt) 0 st)
  /\ 0 <= dp_max (Z.to_nat mx + 1) mx rt syms left (rt + 1) (2 ^ rt) 0.
Proof.
  intros mx rt B HS syms left [lg dn] Hs Hl [Hg HM].
  cbn [fst snd] in Hg, HM.
  pose proof HS as (Hrt & Hmx & HB & Hlt).
  assert (Hd : DOMS rt mx syms left (rt + 1) (2 ^ rt) 0)
    by (apply (doms_seed mx rt B HS); lia).
  destruct (examine_sound (Z.to_nat mx + 1) rt mx B Hrt Hmx ltac:(lia)
              syms left (rt + 1) (2 ^ rt) 0 lg dn (efuel_link_s mx rt B HS) Hd Hg HM)
    as (Hga & HMc & _ & Hdp).
  pose proof (examine_upper (Z.to_nat mx + 1) mx rt syms left (rt + 1) (2 ^ rt) 0 lg dn) as Hup.
  pose proof (dp_nonneg (Z.to_nat mx + 1) mx rt syms left (rt + 1) (2 ^ rt) 0
                ltac:(apply Z.pow_nonneg; lia)) as Hnn.
  cbn [fst]. split; [lia|]. split; [split; [lia | exact HMc] | exact Hnn].
Qed.

(* ==========================================================================
   3.  The loops: the result is max(input, the same loop from (0, empty)).
   ========================================================================== *)

Definition ein_body (e : nat) (mx rt : Z) (numm : PM.t Z) (n left : Z) (st : Z * PM.t unit)
  : Z * PM.t unit :=
  let st1 :=
    if (rt + 1 <? mx) && memo_nonzero numm (key3 n left (rt + 1))
    then examineF e mx rt n left (rt + 1) (2 ^ rt) 0 st
    else st in
  if memo_nonzero numm (key3 n left rt) && (n <=? 2 * left)
  then examineF e mx rt (2 * (n - left)) (2 * (n - left)) (rt + 1) (2 ^ rt) 0 st1
  else st1.

Lemma einF_S : forall e mx rt numm n j left st,
  einF e mx rt numm n (S j) left st = einF e mx rt numm n j (left + 2) (ein_body e mx rt numm n left st).
Proof. reflexivity. Qed.

Lemma eoutF_S : forall e mx rt numm i n st,
  eoutF e mx rt numm (S i) n st
  = eoutF e mx rt numm i (n + 1) (einF e mx rt numm n (Z.to_nat ((n - 1) / 2)) 2 st).
Proof. reflexivity. Qed.

Lemma ein_body_eq : forall mx rt B numm, SEGH mx rt B -> forall n left st,
  3 <= n <= 2 ^ 20 -> 0 <= left <= n - 1 -> SINV mx rt B st ->
  fst (ein_body (Z.to_nat mx + 1) mx rt numm n left st)
    = Z.max (fst st) (fst (ein_body (Z.to_nat mx + 1) mx rt numm n left (0, PM.empty unit)))
  /\ SINV mx rt B (ein_body (Z.to_nat mx + 1) mx rt numm n left st)
  /\ SINV mx rt B (ein_body (Z.to_nat mx + 1) mx rt numm n left (0, PM.empty unit)).
Proof.
  intros mx rt B numm HS n left st Hn Hl HI.
  assert (H20 : (2:Z) ^ 20 = 1048576) by (vm_compute; reflexivity).
  assert (H21 : (2:Z) ^ 21 = 2097152) by (vm_compute; reflexivity).
  assert (HI0 : SINV mx rt B (0, PM.empty unit)) by (apply sinv_empty; lia).
  (* the first gated call, from st and from (0, empty) *)
  assert (H1 : forall s0, SINV mx rt B s0 ->
    exists x1, 0 <= x1
      /\ fst (if (rt + 1 <? mx) && memo_nonzero numm (key3 n left (rt + 1))
              then examineF (Z.to_nat mx + 1) mx rt n left (rt + 1) (2 ^ rt) 0 s0 else s0)
         = Z.max (fst s0) x1
      /\ SINV mx rt B (if (rt + 1 <? mx) && memo_nonzero numm (key3 n left (rt + 1))
                       then examineF (Z.to_nat mx + 1) mx rt n left (rt + 1) (2 ^ rt) 0 s0 else s0)
      /\ (forall s1, SINV mx rt B s1 ->
            fst (if (rt + 1 <? mx) && memo_nonzero numm (key3 n left (rt + 1))
                 then examineF (Z.to_nat mx + 1) mx rt n left (rt + 1) (2 ^ rt) 0 s1 else s1)
            = Z.max (fst s1) x1)).
  { intros s0 HI1.
    destruct ((rt + 1 <? mx) && memo_nonzero numm (key3 n left (rt + 1))).
    - destruct (call_eq mx rt B HS n left s0 ltac:(lia) ltac:(lia) HI1) as (E & HI2 & Hnn).
      eexists. split; [exact Hnn|]. split; [exact E|]. split; [exact HI2|].
      intros s1 HI3. exact (proj1 (call_eq mx rt B HS n left s1 ltac:(lia) ltac:(lia) HI3)).
    - exists 0. split; [lia|]. split; [destruct HI1 as [Hg _]; lia|]. split; [exact HI1|].
      intros s1 [Hg _]. lia. }
  (* the second gated call *)
  assert (H2 : forall s0, SINV mx rt B s0 ->
    exists x2, 0 <= x2
      /\ fst (if memo_nonzero numm (key3 n left rt) && (n <=? 2 * left)
              then examineF (Z.to_nat mx + 1) mx rt (2 * (n - left)) (2 * (n - left)) (rt + 1) (2 ^ rt) 0 s0
              else s0)
         = Z.max (fst s0) x2
      /\ SINV mx rt B (if memo_nonzero numm (key3 n left rt) && (n <=? 2 * left)
                       then examineF (Z.to_nat mx + 1) mx rt (2 * (n - left)) (2 * (n - left)) (rt + 1)
                              (2 ^ rt) 0 s0
                       else s0)
      /\ (forall s1, SINV mx rt B s1 ->
            fst (if memo_nonzero numm (key3 n left rt) && (n <=? 2 * left)
                 then examineF (Z.to_nat mx + 1) mx rt (2 * (n - left)) (2 * (n - left)) (rt + 1)
                        (2 ^ rt) 0 s1
                 else s1)
            = Z.max (fst s1) x2)).
  { intros s0 HI1.
    destruct (memo_nonzero numm (key3 n left rt) && (n <=? 2 * left)).
    - destruct (call_eq mx rt B HS (2 * (n - left)) (2 * (n - left)) s0 ltac:(lia) ltac:(lia) HI1)
        as (E & HI2 & Hnn).
      eexists. split; [exact Hnn|]. split; [exact E|]. split; [exact HI2|].
      intros s1 HI3.
      exact (proj1 (call_eq mx rt B HS (2 * (n - left)) (2 * (n - left)) s1 ltac:(lia) ltac:(lia) HI3)).
    - exists 0. split; [lia|]. split; [destruct HI1 as [Hg _]; lia|]. split; [exact HI1|].
      intros s1 [Hg _]. lia. }
  unfold ein_body. cbv zeta.
  destruct (H1 st HI) as (x1 & Hx1 & E1 & HI1 & F1).
  destruct (H2 _ HI1) as (x2 & Hx2 & E2 & HI2 & F2).
  destruct (H1 _ HI0) as (_ & _ & _ & HI1' & _).
  destruct (H2 _ HI1') as (_ & _ & _ & HI2' & _).
  split; [|split; [exact HI2 | exact HI2']].
  rewrite E2, (F2 _ HI1'), E1, (F1 _ HI0). cbn [fst]. lia.
Qed.

Lemma ein_eq : forall mx rt B numm, SEGH mx rt B -> forall j n left st,
  3 <= n <= 2 ^ 20 -> 0 <= left -> left + 2 * Z.of_nat j <= n + 1 -> SINV mx rt B st ->
  fst (einF (Z.to_nat mx + 1) mx rt numm n j left st)
    = Z.max (fst st) (fst (einF (Z.to_nat mx + 1) mx rt numm n j left (0, PM.empty unit)))
  /\ SINV mx rt B (einF (Z.to_nat mx + 1) mx rt numm n j left st)
  /\ SINV mx rt B (einF (Z.to_nat mx + 1) mx rt numm n j left (0, PM.empty unit)).
Proof.
  intros mx rt B numm HS.
  induction j as [|j IH]; intros n left st Hn Hl Hcap HI.
  - cbn [einF fst]. destruct HI as [Hg HM].
    split; [lia|]. split; [split; assumption | apply sinv_empty; lia].
  - rewrite !einF_S.
    destruct (ein_body_eq mx rt B numm HS n left st Hn ltac:(lia) HI) as (E & HB1 & HB0).
    destruct (IH n (left + 2) _ Hn ltac:(lia) ltac:(lia) HB1) as (E1 & HS1 & HS0).
    destruct (IH n (left + 2) _ Hn ltac:(lia) ltac:(lia) HB0) as (E0 & HS2 & _).
    split; [|split; [exact HS1 | exact HS2]].
    rewrite E1, E0, E. lia.
Qed.

Lemma eout_eq : forall mx rt B numm, SEGH mx rt B -> forall i n st,
  3 <= n -> n + Z.of_nat i <= 2 ^ 20 + 1 -> SINV mx rt B st ->
  fst (eoutF (Z.to_nat mx + 1) mx rt numm i n st)
    = Z.max (fst st) (fst (eoutF (Z.to_nat mx + 1) mx rt numm i n (0, PM.empty unit)))
  /\ SINV mx rt B (eoutF (Z.to_nat mx + 1) mx rt numm i n st)
  /\ SINV mx rt B (eoutF (Z.to_nat mx + 1) mx rt numm i n (0, PM.empty unit)).
Proof.
  intros mx rt B numm HS.
  induction i as [|i IH]; intros n st Hn Hcap HI.
  - cbn [eoutF fst]. destruct HI as [Hg HM].
    split; [lia|]. split; [split; assumption | apply sinv_empty; lia].
  - rewrite !eoutF_S.
    assert (Hjcap : 2 + 2 * Z.of_nat (Z.to_nat ((n - 1) / 2)) <= n + 1).
    { rewrite Z2Nat.id by (apply Z.div_pos; lia).
      pose proof (Z.mul_div_le (n - 1) 2 ltac:(lia)) as H. lia. }
    assert (HI0 : SINV mx rt B (0, PM.empty unit)) by (apply sinv_empty; lia).
    destruct (ein_eq mx rt B numm HS (Z.to_nat ((n - 1) / 2)) n 2 st ltac:(lia) ltac:(lia) Hjcap HI)
      as (E & HB1 & HB0).
    destruct (IH (n + 1) _ ltac:(lia) ltac:(lia) HB1) as (E1 & HS1 & HS0).
    destruct (IH (n + 1) _ ltac:(lia) ltac:(lia) HB0) as (E0 & HS2 & _).
    split; [|split; [exact HS1 | exact HS2]].
    rewrite E1, E0, E. lia.
Qed.

(* ==========================================================================
   4.  Consecutive ranges.
   ========================================================================== *)

Lemma eoutF_app : forall e mx rt numm i1 i2 n st,
  eoutF e mx rt numm (i1 + i2) n st
  = eoutF e mx rt numm i2 (n + Z.of_nat i1) (eoutF e mx rt numm i1 n st).
Proof.
  induction i1 as [|i1 IH]; intros i2 n st.
  - cbn [eoutF Nat.add]. rewrite Z.add_0_r. reflexivity.
  - rewrite Nat.add_succ_l, !eoutF_S, IH.
    replace (n + 1 + Z.of_nat i1) with (n + Z.of_nat (S i1)) by lia. reflexivity.
Qed.

(** A list of ranges (length, first n), and the max of their fresh walks. *)
Fixpoint seg_max (e : nat) (mx rt : Z) (numm : PM.t Z) (segs : list (nat * Z)) : Z :=
  match segs with
  | [] => 0
  | (i, n) :: segs' =>
      Z.max (fst (eoutF e mx rt numm i n (0, PM.empty unit))) (seg_max e mx rt numm segs')
  end.

Lemma seg_max_nil : forall e mx rt numm, seg_max e mx rt numm [] = 0.
Proof. reflexivity. Qed.

Lemma seg_max_cons : forall e mx rt numm i n segs,
  seg_max e mx rt numm ((i, n) :: segs)
  = Z.max (fst (eoutF e mx rt numm i n (0, PM.empty unit))) (seg_max e mx rt numm segs).
Proof. reflexivity. Qed.

Fixpoint seg_ok (segs : list (nat * Z)) (n : Z) : bool :=
  match segs with
  | [] => true
  | (i, n') :: segs' => (n =? n') && seg_ok segs' (n + Z.of_nat i)
  end.

Fixpoint seg_len (segs : list (nat * Z)) : nat :=
  match segs with
  | [] => O
  | (i, _) :: segs' => (i + seg_len segs')%nat
  end.

Lemma seg_eq : forall mx rt B numm, SEGH mx rt B -> forall segs n st,
  seg_ok segs n = true -> 3 <= n -> n + Z.of_nat (seg_len segs) <= 2 ^ 20 + 1 ->
  SINV mx rt B st ->
  fst (eoutF (Z.to_nat mx + 1) mx rt numm (seg_len segs) n st)
  = Z.max (fst st) (seg_max (Z.to_nat mx + 1) mx rt numm segs).
Proof.
  intros mx rt B numm HS.
  induction segs as [|[i n'] segs IH]; intros n st Hok Hn Hcap HI.
  - cbn [seg_len eoutF seg_max]. destruct HI as [Hg _]. lia.
  - cbn [seg_ok] in Hok. apply andb_prop in Hok as [Hn' Hok]. apply Z.eqb_eq in Hn'. subst n'.
    cbn [seg_len] in Hcap |- *. rewrite seg_max_cons, eoutF_app.
    destruct (eout_eq mx rt B numm HS i n st Hn ltac:(lia) HI) as (E & HS1 & _).
    rewrite (IH (n + Z.of_nat i) _ Hok ltac:(lia) ltac:(lia) HS1), E. lia.
Qed.

Theorem enough_phase_segs : forall mx rt syms numm segs,
  1 <= rt -> rt + 1 <= mx - 1 -> mx <= 15 -> 3 <= syms <= 1048576 ->
  seg_ok segs 3 = true -> seg_len segs = Z.to_nat (syms - 2) ->
  enough_phase mx rt syms numm = Z.max (2 ^ rt) (seg_max (Z.to_nat mx + 1) mx rt numm segs).
Proof.
  intros mx rt syms numm segs Hrt Hlt Hmx Hsy Hok Hlen.
  assert (HS : SEGH mx rt (mx + rt + 2)) by (unfold SEGH; lia).
  assert (H20 : (2:Z) ^ 20 = 1048576) by (vm_compute; reflexivity).
  rewrite enough_phase_eq by lia. rewrite <- Hlen.
  pose proof (seg_eq mx rt (mx + rt + 2) numm HS segs 3 (2 ^ rt, PM.empty unit) Hok ltac:(lia)
                ltac:(rewrite Hlen, Z2Nat.id; lia)
                (sinv_empty mx rt (mx + rt + 2) (2 ^ rt) ltac:(apply Z.pow_nonneg; lia))) as E.
  exact E.
Qed.

(* ==========================================================================
   5.  enough_run, opened: the count phase, then enough_phase.
   ========================================================================== *)

(** enough_run's count phase (its inline [cnt] loop), as a constant. *)
Definition cntR (mx syms : Z) : Z * PM.t Z :=
  (fix cnt (i : nat) (n sum : Z) (memo : PM.t Z) {struct i} : Z * PM.t Z :=
     match i with
     | O => (sum, memo)
     | S i' =>
         let '(got, memo') := countF (Z.to_nat mx + 1)%nat mx n 2 1 memo in
         cnt i' (n + 1) (sum + got) memo'
     end) (Z.to_nat (syms - 1)) 2 0 (PM.empty Z).

Lemma enough_run_open : forall syms root max mx rt,
  ((syms <? 2) || (root <? 1) || (max <? 1))%bool = false ->
  mx = Z.min max (syms - 1) ->
  (syms - 1 >? 2 ^ mx - 1) = false ->
  ((mx >? 32) || (root >? 32) || (syms >? 2 ^ 20))%bool = false ->
  rt = Z.min root mx ->
  (syms <? 2 ^ (rt + 1)) = true ->
  enough_run syms root max
  = Some (fst (cntR mx syms), Some (enough_phase mx rt syms (snd (cntR mx syms)))).
Proof.
  intros syms root max mx rt G1 Emx G2 G3 Ert G4.
  unfold enough_run. rewrite G1. cbv beta iota zeta.
  rewrite <- Emx, G2. cbv iota. rewrite G3. cbv iota. rewrite <- Ert.
  fold (cntR mx syms).
  destruct (cntR mx syms) as [total numm]. cbn [fst snd].
  rewrite G4. reflexivity.
Qed.
