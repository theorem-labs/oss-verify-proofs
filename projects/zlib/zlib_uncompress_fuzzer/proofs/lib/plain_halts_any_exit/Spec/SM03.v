(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Bool.
From Stdlib Require Lia.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.Spec Require Malloc.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.Spec Require SM01.
From stdpp Require gmap.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.Spec Require SM09.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.Spec Require SM08.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module MI_Cnt.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Bool. From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.Spec Require Import Malloc. Import SM01. Import SM01.MI_Arith.
Unset Lia Cache.
Unset Nia Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition zrange (lo n : Z) : list Z := map (fun i => lo + Z.of_nat i) (seq 0 (Z.to_nat n)).
Lemma in_zrange lo n x : 0 <= n -> (In x (zrange lo n) <-> lo <= x < lo + n).
Proof.
  intros Hn. unfold zrange. rewrite in_map_iff. split.
  - intros (i & <- & Hi). apply in_seq in Hi. lia.
  - intros H. exists (Z.to_nat (x - lo)). split; [lia|]. apply in_seq. lia.
Qed.
Lemma forallb_zrange f lo n x : forallb f (zrange lo n) = true -> 0 <= n -> lo <= x < lo + n -> f x = true.
Proof. intros H Hn Hx. rewrite forallb_forall in H. apply H. apply in_zrange; assumption. Qed.


Definition mono_f (a : Z) : bool := forallb (fun b => negb (a <? b) || (size_class a <? size_class b)) (zrange 0 48).
Lemma mono_b_true : forallb mono_f (zrange 0 48) = true. Proof. vm_compute. reflexivity. Qed.

Lemma size_class_lt a b : 0 <= a < 48 -> 0 <= b < 48 -> a < b -> size_class a < size_class b.
Proof.
  intros Ha Hb Hab. pose proof (forallb_zrange mono_f 0 48 a mono_b_true ltac:(lia) ltac:(lia)) as H. unfold mono_f in H.
  pose proof (forallb_zrange _ 0 48 b H ltac:(lia) ltac:(lia)) as H2. cbn beta in H2.
  apply orb_true_iff in H2. destruct H2 as [H2|H2]; [apply negb_true_iff in H2; apply Z.ltb_ge in H2; lia| apply Z.ltb_lt in H2; exact H2].
Qed.
Lemma size_class_le a b : 0 <= a < 48 -> 0 <= b < 48 -> a <= b -> size_class a <= size_class b.
Proof. intros. destruct (Z.eq_dec a b) as [->|]; [lia|]. pose proof (size_class_lt a b). lia. Qed.
Lemma size_class_lt_inv a b : 0 <= a < 48 -> 0 <= b < 48 -> size_class a < size_class b -> a < b.
Proof. intros. destruct (Z.lt_ge_cases a b); [assumption|]. pose proof (size_class_le b a). lia. Qed.

Definition stc_k (k : Z) : Z :=
  if k <? 10 then k else
  let n := k + 1 in
  let i := (28 - clz32 n) * 4 + 8 in
  let i := if size_class (i + 1) <? n then i + 2 else i in
  if size_class i <? n then i + 1 else i.
Lemma size_to_class_k n : size_to_class n = stc_k (Z.shiftr (n + IB - 1) 4).
Proof. reflexivity. Qed.

Definition stc_f (k : Z) : bool := let sc := stc_k k in (0 <=? sc) && (sc <? 48) && (k + 1 <=? size_class sc).
Lemma stc_ok_b_true : forallb stc_f (zrange 0 8191) = true. Proof. vm_compute. reflexivity. Qed.

Lemma size_to_class_ok n : 0 <= n < MMAP_THRESHOLD ->
  0 <= size_to_class n < 48 /\ n + IB <= UNIT * size_class (size_to_class n).
Proof.
  intros Hn. rewrite size_to_class_k. rewrite Z.shiftr_div_pow2 by lia. unfold IB, UNIT, MMAP_THRESHOLD in *.
  set (k := (n + 4 - 1) / 2 ^ 4).
  assert (Hk : 0 <= k < 8191) by (subst k; change (2 ^ 4) with 16; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  assert (Hk2 : 16 * k <= n + 3 < 16 * k + 16) by (subst k; change (2 ^ 4) with 16; pose proof (Z.div_mod (n + 4 - 1) 16 ltac:(lia)); pose proof (Z.mod_pos_bound (n + 4 - 1) 16 ltac:(lia)); lia).
  pose proof (forallb_zrange stc_f 0 8191 k stc_ok_b_true ltac:(lia) ltac:(lia)) as H. unfold stc_f in H. cbn zeta in H.
  apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3. lia.
Qed.

Lemma lor1_even sc : 0 <= sc -> Z.even sc = true -> Z.lor sc 1 = sc + 1.
Proof.
  intros H He. assert (HE : Z.Even sc) by (apply Z.even_spec; exact He). destruct HE as [m ->].
  apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec.
  destruct (Z.eq_dec i 0) as [->|NZ].
  - rewrite !Z.bit0_odd. replace (2 * m + 1) with (Z.succ (2 * m)) by lia. rewrite Z.odd_succ, He. change (Z.odd 1) with true. apply orb_true_r.
  - assert (T1 : forall k, 0 <= k -> Z.testbit 1 (Z.succ k) = false).
    { intros k Hk. change (Z.testbit 1) with (Z.testbit (2 * 0 + 1)). rewrite Z.testbit_odd_succ by exact Hk. apply Z.testbit_0_l. }
    replace i with (Z.succ (i - 1)) by lia. rewrite Z.testbit_even_succ, Z.testbit_odd_succ, T1 by lia.
    apply orb_false_r.
Qed.


Fixpoint he_list (f : nat) (c : Z) : list Z :=
  match f with
  | O => [c]
  | S f' => c :: (if Z.even c then he_list f' (Z.shiftr c 1) else [])
  end.
Lemma halve_even_in f : forall c u, In (halve_even f c u) (he_list f c).
Proof.
  induction f as [|f IH]; intros c u; cbn [halve_even he_list]; [left; reflexivity|].
  destruct (Z.even c); cbn [andb]; [| left; reflexivity].
  destruct (u <? 4 * c); [right; apply IH| left; reflexivity].
Qed.

Definition cnt0_list (sc : Z) : list Z :=
  let size := UNIT * size_class sc in
  if sc <? 9 then [small_cnt sc 0; small_cnt sc 1; small_cnt sc 2]
  else map (fun c => halve_big 8 c size) (he_list 8 (med_cnt (Z.land sc 3))).

Definition cnt0_of (sc u : Z) : Z :=
  if sc <? 9 then small_cnt_pick sc u
  else halve_big 8%nat (halve_even 8%nat (med_cnt (Z.land sc 3)) u) (UNIT * size_class sc).

Lemma cnt0_in sc u : In (cnt0_of sc u) (cnt0_list sc).
Proof.
  unfold cnt0_of, cnt0_list. destruct (sc <? 9).
  - unfold small_cnt_pick. destruct (negb (u <? 4 * small_cnt sc 0)); [left; reflexivity|].
    destruct (negb (u <? 4 * small_cnt sc 1)); [right; left; reflexivity| right; right; left; reflexivity].
  - apply (in_map (fun c => halve_big 8 c (UNIT * size_class sc))). apply halve_even_in.
Qed.

Definition bump (size c : Z) : Z := if (c =? 1) && (size * c + UNIT <=? PGSZ / 2) then 2 else c.

Definition adj (sc size cnt : Z) : Z :=
  if (Z.land sc 3 =? 1) && (8 * PGSZ <? size * cnt) then 2
  else if (Z.land sc 3 =? 2) && (4 * PGSZ <? size * cnt) then 3
  else if (Z.land sc 3 =? 0) && (8 * PGSZ <? size * cnt) then 3
  else if (Z.land sc 3 =? 0) && (2 * PGSZ <? size * cnt) then 5
  else cnt.

Definition grp_ok (sc cnt needed : Z) : bool :=
  let size := UNIT * size_class sc in
  let maplen := Z.shiftr needed 12 in
  let last := cnt - 1 in
  let stride := if (last =? 0) && negb (maplen =? 0) then maplen * 4096 - UNIT else size in
  (1 <=? cnt) && (cnt <=? 32) && (needed mod 4096 =? 0) && (4096 <=? needed) && (needed <=? 2 ^ 20)
  && (UNIT + stride * cnt <=? maplen * 4096)
  && ((stride <=? size) || (28 <=? sc))
  && (negb (last =? 0) || (27 <=? sc))
  && (stride * cnt <? 2 ^ 20) && (16 <=? stride) && (stride mod 16 =? 0).

Definition nest_ok (sc cnt : Z) : bool :=
  let size := UNIT * size_class sc in
  let n' := UNIT + cnt * size - IB in
  let j := size_to_class n' in
  (2 <=? cnt) && (cnt <=? 32) && (sc <? j) && (j <=? 23) && (UNIT + cnt * size <=? UNIT * size_class j) && (size * cnt <? 2 ^ 20)
  && (0 <=? n') && (n' + IB <=? 2048).

Definition qmax (sc : Z) : Z := (UNIT * size_class sc + UNIT + 4095) / 4096.

Definition ag_check_sc (sc : Z) : bool :=
  let size := UNIT * size_class sc in
  forallb (fun cnt0 =>
    let cnt1 := bump size cnt0 in
    if PGSZ / 2 <? size * cnt1 + UNIT then
      forallb (fun cnt2 =>
         grp_ok sc cnt2 (round_up_pg (size * cnt2 + UNIT))
         && (negb (cnt2 <=? 7)
             || forallb (fun q => negb ((q * 4096 <? size + UNIT) || (4 <=? q)) || (grp_ok sc 1 (q * 4096) && (28 <=? sc))) (zrange 1 (qmax sc))))
        [cnt1; adj sc size cnt1]
    else nest_ok sc cnt1)
  (cnt0_list sc).

Lemma ag_check_true : forallb ag_check_sc (zrange 0 48) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma grp_ok_sound sc cnt needed : grp_ok sc cnt needed = true ->
  let size := UNIT * size_class sc in
  let maplen := Z.shiftr needed 12 in
  let last := cnt - 1 in
  let stride := if (last =? 0) && negb (maplen =? 0) then maplen * 4096 - UNIT else size in
  1 <= cnt <= 32 /\ needed mod 4096 = 0 /\ 4096 <= needed <= 2 ^ 20 /\ maplen = needed / 4096 /\ 1 <= maplen <= 256
  /\ UNIT + stride * cnt <= maplen * 4096 /\ (stride <= size \/ 28 <= sc) /\ (last = 0 -> 27 <= sc)
  /\ stride * cnt < 2 ^ 20 /\ 16 <= stride /\ stride mod 16 = 0.
Proof.
  unfold grp_ok. intros H. cbn zeta. rewrite Z.shiftr_div_pow2 in * by lia. change (2 ^ 12) with 4096 in *.
  repeat (apply andb_true_iff in H as [H ?]).
  repeat match goal with
  | K : (_ <=? _) = true |- _ => apply Z.leb_le in K
  | K : (_ <? _) = true |- _ => apply Z.ltb_lt in K
  | K : (_ =? _) = true |- _ => apply Z.eqb_eq in K
  | K : (_ || _) = true |- _ => apply orb_true_iff in K
  end.
  assert (1 <= needed / 4096 <= 256) by (split; [apply Z.div_le_lower_bound; lia| apply Z.div_le_upper_bound; lia]).
  repeat split; try assumption; lia.
Qed.

Lemma nest_ok_sound sc cnt : nest_ok sc cnt = true ->
  let size := UNIT * size_class sc in
  let n' := UNIT + cnt * size - IB in
  let j := size_to_class n' in
  2 <= cnt <= 32 /\ sc < j <= 23 /\ UNIT + cnt * size <= UNIT * size_class j /\ size * cnt < 2 ^ 20 /\ 0 <= n' /\ n' + IB <= 2048.
Proof.
  unfold nest_ok. intros H. cbn zeta.
  repeat (apply andb_true_iff in H as [H ?]).
  repeat match goal with
  | K : (_ <=? _) = true |- _ => apply Z.leb_le in K
  | K : (_ <? _) = true |- _ => apply Z.ltb_lt in K
  end. repeat split; assumption.
Qed.

Lemma round_up_pg_spec x : x <= round_up_pg x < x + 4096 /\ round_up_pg x mod 4096 = 0.
Proof.
  unfold round_up_pg, PGSZ. change (4096 - 1) with (Z.pred (2 ^ 12)). rewrite <- Z.ones_equiv, Z.land_ones by lia.
  change (2 ^ 12) with 4096.
  pose proof (Z.mod_pos_bound (- x) 4096 ltac:(lia)) as B. pose proof (Z.div_mod (- x) 4096 ltac:(lia)) as D.
  split; [lia|]. replace (x + - x mod 4096) with ((- ((- x) / 4096)) * 4096) by lia. apply Z.mod_mul. lia.
Qed.

Lemma round_up_pg_pages x : 0 < x -> exists q, round_up_pg x = q * 4096 /\ 1 <= q /\ (q - 1) * 4096 < x <= q * 4096.
Proof.
  intros Hx. destruct (round_up_pg_spec x) as [A B].
  exists (round_up_pg x / 4096). pose proof (Z.div_mod (round_up_pg x) 4096 ltac:(lia)). rewrite B in H. nia.
Qed.

Theorem alloc_group_arith sc req u0 u1 (nosmall : bool) :
  0 <= sc < 48 -> 0 <= req -> req + IB <= UNIT * size_class sc ->
  let size := UNIT * size_class sc in
  let cnt0 := cnt0_of sc u0 in
  let cnt1 := if (cnt0 =? 1) && (size * cnt0 + UNIT <=? PGSZ / 2) then 2 else cnt0 in
  (PGSZ / 2 < size * cnt1 + UNIT ->
     let cnt2 :=
       if (u1 <? 4 * cnt1) && negb nosmall then
         if (Z.land sc 3 =? 1) && (8 * PGSZ <? size * cnt1) then 2
         else if (Z.land sc 3 =? 2) && (4 * PGSZ <? size * cnt1) then 3
         else if (Z.land sc 3 =? 0) && (8 * PGSZ <? size * cnt1) then 3
         else if (Z.land sc 3 =? 0) && (2 * PGSZ <? size * cnt1) then 5
         else cnt1
       else cnt1 in
     let needed := round_up_pg (size * cnt2 + UNIT) in
     let '(cnt3, needed3) :=
       if negb nosmall && (cnt2 <=? 7) then
         let req' := round_up_pg (req + IB + UNIT) in
         if (req' <? size + UNIT) || ((4 * PGSZ <=? req') && (u1 <? 2 * cnt2)) then (1, req') else (cnt2, needed)
       else (cnt2, needed) in
     grp_ok sc cnt3 needed3 = true
     /\ ((cnt3 = 1 /\ needed3 = round_up_pg (req + IB + UNIT) /\ 28 <= sc) \/ (cnt3 = cnt2 /\ needed3 = needed /\ size * cnt2 + UNIT <= needed)))
  /\ (size * cnt1 + UNIT <= PGSZ / 2 -> nest_ok sc cnt1 = true).
Proof.
  intros Hsc Hreq Hfit. cbn zeta.
  pose proof (forallb_zrange ag_check_sc 0 48 sc ag_check_true ltac:(lia) ltac:(lia)) as H. unfold ag_check_sc in H.
  rewrite forallb_forall in H. specialize (H _ (cnt0_in sc u0)). cbn beta in H. fold (bump (UNIT * size_class sc) (cnt0_of sc u0)) in H |- *.
  set (cnt1 := bump (UNIT * size_class sc) (cnt0_of sc u0)) in *. clearbody cnt1.
  split.
  - intros HB. rewrite (proj2 (Z.ltb_lt _ _) HB) in H. rewrite forallb_forall in H.
    set (cnt2 := if (u1 <? 4 * cnt1) && negb nosmall then _ else cnt1).
    assert (Hc2 : In cnt2 [cnt1; adj sc (UNIT * size_class sc) cnt1]).
    { subst cnt2. destruct ((u1 <? 4 * cnt1) && negb nosmall); [right; left; reflexivity| left; reflexivity]. }
    specialize (H _ Hc2). clearbody cnt2. apply andb_true_iff in H as [G1 G2].
    destruct (negb nosmall && (cnt2 <=? 7)) eqn:E7.
    + destruct ((round_up_pg (req + IB + UNIT) <? UNIT * size_class sc + UNIT) || ((4 * PGSZ <=? round_up_pg (req + IB + UNIT)) && (u1 <? 2 * cnt2))) eqn:ER.
      * apply andb_true_iff in E7 as [_ E7]. rewrite E7 in G2. cbn [negb orb] in G2. rewrite forallb_forall in G2.
        destruct (round_up_pg_pages (req + IB + UNIT) ltac:(unfold IB, UNIT; lia)) as (q & Eq & Hq1 & Hq2). rewrite Eq in *.
        assert (Hq : In q (zrange 1 (qmax sc))).
        { apply in_zrange; [unfold qmax, UNIT; apply Z.div_pos; [pose proof (size_class_bound sc Hsc); lia| lia]|].
          split; [lia|]. unfold qmax. unfold IB, UNIT, PGSZ in *.
          assert (q <= (16 * size_class sc + 16 + 4095) / 4096) by (apply Z.div_le_lower_bound; lia). lia. }
        specialize (G2 _ Hq). cbn beta in G2.
        assert (EC : (q * 4096 <? UNIT * size_class sc + UNIT) || (4 <=? q) = true).
        { apply orb_true_iff in ER. apply orb_true_iff. destruct ER as [ER|ER]; [left; exact ER| right].
          apply andb_true_iff in ER as [ER _]. apply Z.leb_le in ER. apply Z.leb_le. unfold PGSZ in ER. lia. }
        rewrite EC in G2. cbn [negb orb] in G2. apply andb_true_iff in G2 as [G2 G28]. apply Z.leb_le in G28.
        split; [exact G2| left; split; [reflexivity| split; [reflexivity| exact G28]]].
      * split; [exact G1| right; split; [reflexivity| split; [reflexivity| apply (proj1 (round_up_pg_spec _))]]].
    + split; [exact G1| right; split; [reflexivity| split; [reflexivity| apply (proj1 (round_up_pg_spec _))]]].
  - intros HN. assert (E : (PGSZ / 2 <? UNIT * size_class sc * cnt1 + UNIT) = false) by (apply Z.ltb_ge; lia).
    rewrite E in H. exact H.
Qed.

Lemma clamp_ai size cnt : 1 <= cnt ->
  let ai := (4096 - UNIT) / size - 1 in
  let ai := if cnt - 1 <? ai then cnt - 1 else ai in
  let ai := if ai <? 0 then 0 else ai in
  0 <= ai <= cnt - 1.
Proof.
  intros Hc. cbn zeta. destruct (Z.ltb_spec (cnt - 1) ((4096 - UNIT) / size - 1)).
  - destruct (Z.ltb_spec (cnt - 1) 0); lia.
  - destruct (Z.ltb_spec ((4096 - UNIT) / size - 1) 0); lia.
Qed.

Lemma created_masks ai last :
  0 <= ai <= last -> last <= 31 ->
  let avail := mask_upto ai in
  let freed := mask_upto last - avail in
  0 <= avail /\ 0 <= freed
  /\ (forall i, 0 <= i -> Z.testbit avail i = true -> i <= ai)
  /\ (forall i, 0 <= i -> Z.testbit freed i = true -> i <= last)
  /\ (forall i, 0 <= i -> Z.testbit avail i = true -> Z.testbit freed i = true -> False)
  /\ (forall i, ai < i <= last -> Z.testbit freed i = true)
  /\ (forall i, 0 <= i <= ai -> Z.testbit avail i = true)
  /\ freed = Z.ldiff (mask_upto last) (mask_upto ai).
Proof.
  intros Hai Hl. cbn zeta.
  assert (EF : mask_upto last - mask_upto ai = Z.ldiff (mask_upto last) (mask_upto ai)).
  { apply Z.sub_nocarry_ldiff. apply Z.bits_inj'. intros i Hi. rewrite Z.ldiff_spec, Z.bits_0, !testbit_mask_upto by lia.
    destruct (Z.leb_spec i ai); destruct (Z.leb_spec i last); cbn; try reflexivity. lia. }
  rewrite EF. pose proof (mask_upto_nonneg ai ltac:(lia)). pose proof (mask_upto_nonneg last ltac:(lia)).
  split; [assumption|]. split; [apply Z.ldiff_nonneg; left; assumption|].
  split; [intros i Hi Hb; rewrite testbit_mask_upto in Hb by lia; apply Z.leb_le in Hb; exact Hb|].
  split; [intros i Hi Hb; rewrite Z.ldiff_spec, !testbit_mask_upto in Hb by lia; destruct (Z.leb_spec i last); [lia| discriminate]|].
  split; [intros i Hi Ha Hb; rewrite Z.ldiff_spec, Ha in Hb; rewrite andb_false_r in Hb; discriminate|].
  split; [intros i Hi; rewrite Z.ldiff_spec, !testbit_mask_upto by lia; destruct (Z.leb_spec i last); destruct (Z.leb_spec i ai); cbn; try reflexivity; lia|].
  split; [intros i Hi; rewrite testbit_mask_upto by lia; apply Z.leb_le; lia| reflexivity].
Qed.
End MI_Cnt.

Module MI_Fuel.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Bool. From Stdlib Require Import Lia.
From stdpp Require Import gmap.
Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.Spec Require Import Malloc. Import SM08. Import SM08.MallocCtrl.
Import ListNotations.
Local Open Scope Z_scope.

Set Implicit Arguments.

Inductive tle {R : Type} : M R -> M R -> Prop :=
| tle_ret : forall r, tle (SRet r) (SRet r)
| tle_fuel : forall k t, tle (SVis (EUndef UFuel) k) t
| tle_vis : forall e k1 k2, (forall a, tle (k1 a) (k2 a)) -> tle (SVis e k1) (SVis e k2).

Lemma tle_refl {R} (t : M R) : tle t t.
Proof. induction t; constructor; auto. Qed.

Lemma tle_trans {R} (t1 t2 t3 : M R) : tle t1 t2 -> tle t2 t3 -> tle t1 t3.
Proof.
  intros H1. revert t3. induction H1 as [r|k t|e k1 k2 Hk IH]; intros t3 H2.
  - exact H2.
  - constructor.
  - inversion H2; subst.
    + constructor.
    + constructor. intros a. apply IH. auto.
Qed.

Lemma follow_tle {R} (t1 t2 : M R) : tle t1 t2 -> forall ans r, follow t1 ans = Some r -> follow t2 ans = Some r.
Proof.
  induction 1 as [r0|k t|e k1 k2 Hk IH]; intros ans r H.
  - exact H.
  - cbn [follow] in H. destruct ans; discriminate H.
  - cbn [follow] in H |- *. destruct e; try exact H; destruct ans as [|a ans']; try discriminate H; apply IH; exact H.
Qed.

Section PRUN.
Context {O : Type} (pans : O -> aptr -> Z -> Z -> Z) (pupd : O -> ev -> Z -> O).

Lemma prun_tle {R} (t1 t2 : M R) : tle t1 t2 -> forall o, tle (prun pans pupd o t1) (prun pans pupd o t2).
Proof.
  unfold prun. induction 1 as [r0|k t|e k1 k2 Hk IH]; intros o; cbn [eruns psel].
  - constructor.
  - constructor.
  - destruct e; cbn [psel]; try (constructor; intros a; apply IH). apply IH.
Qed.
End PRUN.


Definition kle {X Y R} (k k' : X -> Y -> M R) : Prop := forall x y, tle (k x y) (k' x y).
Definition kle1 {X R} (k k' : X -> M R) : Prop := forall x, tle (k x) (k' x).

Ltac mono_case :=
  lazymatch goal with
  | |- tle (match ?c with _ => _ end) _ => destruct c
  end.

Ltac mono_auto cal :=
  first [ apply tle_refl
        | cal
        | (apply tle_vis; intros ?); mono_auto cal
        | mono_case; mono_auto cal
        | progress (cbv zeta); mono_auto cal ].

Lemma guard_mono {R} tag c (k k' bail bail' : M R) :
  tle k k' -> tle bail bail' -> tle (guard tag c k bail) (guard tag c k' bail').
Proof. intros HK HB. unfold guard. destruct c; [exact HK|]. constructor. intros _. exact HB. Qed.

Lemma bad_answer_mono {R} (b b' : M R) : tle b b' -> tle (bad_answer b) (bad_answer b').
Proof. intros HB. unfold bad_answer. constructor. intros _. exact HB. Qed.

Lemma queue_mono {R} h m st (k k' : mstate -> M R) bail bail' :
  kle1 k k' -> tle bail bail' -> tle (queue h m st k bail) (queue h m st k' bail').
Proof.
  intros HK HB. unfold queue. apply guard_mono; [| exact HB]. apply guard_mono; [| exact HB].
  mono_auto ltac:(first [apply HK | exact HB]).
Qed.

Lemma free_meta_mono {R} m st (k k' : mstate -> M R) bail bail' :
  kle1 k k' -> tle bail bail' -> tle (free_meta m st k bail) (free_meta m st k' bail').
Proof. intros HK HB. unfold free_meta. apply queue_mono; assumption. Qed.

Lemma activate_group_mono {R} m st (k k' : mstate -> Z -> M R) bail bail' :
  kle k k' -> tle bail bail' -> tle (activate_group m st k bail) (activate_group m st k' bail').
Proof. intros HK HB. unfold activate_group. apply guard_mono; [| exact HB]. cbv zeta. apply HK. Qed.

Lemma am_take_mono {R} st (k k' : mstate -> optr -> M R) bail bail' :
  kle k k' -> tle bail bail' -> tle (am_take st k bail) (am_take st k' bail').
Proof. intros HK HB. unfold am_take. mono_auto ltac:(first [apply HK | exact HB]). Qed.

Lemma am_carve_mono {R} st p (k k' : mstate -> optr -> M R) bail bail' :
  kle k k' -> tle bail bail' -> tle (am_carve st p k bail) (am_carve st p k' bail').
Proof. intros HK HB. unfold am_carve. cbv zeta. apply am_take_mono; assumption. Qed.

Lemma am_finish_mono {R} st nu (k k' : mstate -> optr -> M R) bail bail' :
  kle k k' -> tle bail bail' -> tle (am_finish st nu k bail) (am_finish st nu k' bail').
Proof.
  intros HK HB. unfold am_finish.
  mono_auto ltac:(first [apply HK | exact HB | apply bad_answer_mono; exact HB | apply am_carve_mono; assumption]).
Qed.

Lemma am_after_brk_mono {R} st nu (k k' : mstate -> optr -> M R) bail bail' :
  kle k k' -> tle bail bail' -> tle (am_after_brk st nu k bail) (am_after_brk st nu k' bail').
Proof.
  intros HK HB. unfold am_after_brk.
  mono_auto ltac:(first [apply HK | exact HB | apply bad_answer_mono; exact HB | apply am_finish_mono; assumption]).
Qed.

Lemma alloc_meta_mono {R} st (k k' : mstate -> optr -> M R) bail bail' :
  kle k k' -> tle bail bail' -> tle (alloc_meta st k bail) (alloc_meta st k' bail').
Proof.
  intros HK HB. unfold alloc_meta.
  mono_auto ltac:(first [apply HK | exact HB | apply bad_answer_mono; exact HB | apply am_take_mono; assumption | apply am_after_brk_mono; assumption]).
Qed.

Lemma ta_fin_mono {R} st m mask (k k' : mstate -> Z -> M R) :
  kle k k' -> tle (ta_fin st m mask k) (ta_fin st m mask k').
Proof. intros HK. unfold ta_fin. cbv zeta. apply HK. Qed.

Lemma try_avail_mono {R} sc st (k k' : mstate -> Z -> M R) bail bail' :
  kle k k' -> tle bail bail' -> tle (try_avail sc st k bail) (try_avail sc st k' bail').
Proof.
  intros HK HB. unfold try_avail.
  destruct (active st sc) as [m|]; [| apply HK]. cbv zeta.
  destruct (negb (m_avail (get_meta_rec st m) =? 0)); [apply ta_fin_mono; exact HK|].
  mono_case.
  - destruct p as [st1 m1]. mono_case. destruct p as [st2 m2]. mono_case.
    apply activate_group_mono; [| exact HB]. intros st4 mask. apply guard_mono; [| exact HB]. apply ta_fin_mono. exact HK.
  - mono_case; [apply HK|]. constructor. intros _. exact HB.
Qed.

Lemma ag_tail_mono {R} lay st sc m p cnt ai (k k' : mstate -> optr -> M R) :
  kle k k' -> tle (ag_tail lay st sc m p cnt ai k) (ag_tail lay st sc m p cnt ai k').
Proof. intros HK. unfold ag_tail. cbv zeta. apply HK. Qed.

Section AG.
Variable R : Type.
Variable lay : layout_hook.
Variables rec rec' : mstate -> Z -> Z -> (mstate -> Z -> M R) -> M R -> M R.
Hypothesis rec_mono : forall st sc req (k k' : mstate -> Z -> M R) bail bail',
  kle k k' -> tle bail bail' -> tle (rec st sc req k bail) (rec' st sc req k' bail').

Lemma alloc_group_mono st sc req (k k' : mstate -> optr -> M R) bail bail' :
  kle k k' -> tle bail bail' ->
  tle (alloc_group R lay rec st sc req k bail) (alloc_group R lay rec' st sc req k' bail').
Proof.
  intros HK HB. unfold alloc_group. cbv zeta. apply alloc_meta_mono; [| exact HB].
  intros st' mo. destruct mo as [m|]; [| apply HK].
  mono_case.
  -
    match goal with |- tle (let '(_, _) := ?p in _) _ => destruct p as [cnt' needed] end.
    constructor. intros r. mono_case; [apply bad_answer_mono; exact HB|].
    mono_case; [apply free_meta_mono; [intros ?; apply HK| exact HB]|].
    mono_case. cbv zeta. apply ag_tail_mono. exact HK.
  -
    apply rec_mono; [| exact HB]. intros st1 idx.
    mono_case; [apply free_meta_mono; [intros ?; apply HK| exact HB]|].
    mono_case; [| constructor; intros _; exact HB]. cbv zeta. apply ag_tail_mono. exact HK.
Qed.
End AG.

Lemma alloc_slot_mono lay f : forall R st sc req (k k' : mstate -> Z -> M R) bail bail',
  kle k k' -> tle bail bail' ->
  tle (alloc_slot lay f st sc req k bail) (alloc_slot lay (S f) st sc req k' bail').
Proof.
  induction f as [|f IH]; intros R st sc req k k' bail bail' HK HB.
  - cbn [alloc_slot]. apply tle_fuel.
  - change (alloc_slot lay (S (S f)) st sc req k' bail') with
      (try_avail sc st (fun st1 first =>
         if negb (first =? 0) then k' st1 (ctz32 first)
         else alloc_group R lay (alloc_slot lay (S f)) st1 sc req (fun st2 go =>
                match go with
                | None => k' st2 (-1)
                | Some g => let st3 := upd_meta g (fun r => m_set_avail (m_avail r - 1) r) st2 in
                            queue (LActive sc) g st3 (fun st4 => k' st4 0) bail'
                end) bail') bail').
    cbn [alloc_slot]. apply try_avail_mono; [| exact HB]. intros st1 first.
    destruct (negb (first =? 0)); [apply HK|].
    apply (alloc_group_mono lay (alloc_slot lay f) (alloc_slot lay (S f))); [intros; apply IH; assumption| | exact HB].
    intros st2 go. destruct go as [g|]; [| apply HK]. cbv zeta. apply queue_mono; [intros ?; apply HK| exact HB].
Qed.

Lemma alloc_slot_mono_le lay f f' : (f <= f')%nat -> forall R st sc req (k : mstate -> Z -> M R) bail,
  tle (alloc_slot lay f st sc req k bail) (alloc_slot lay f' st sc req k bail).
Proof.
  induction 1 as [|f' H IH]; intros R st sc req k bail.
  - apply tle_refl.
  - eapply tle_trans; [apply IH|]. apply alloc_slot_mono; [intros ? ?; apply tle_refl| apply tle_refl].
Qed.

Section LEAF.
Context {O : Type} (pans : O -> aptr -> Z -> Z -> Z) (pupd : O -> ev -> Z -> O).
Lemma alloc_slot_follow_mono lay f f' R st sc req (k : mstate -> Z -> M R) bail o ans r :
  (f <= f')%nat ->
  follow (prun pans pupd o (alloc_slot lay f st sc req k bail)) ans = Some r ->
  follow (prun pans pupd o (alloc_slot lay f' st sc req k bail)) ans = Some r.
Proof. intros Hf H. eapply follow_tle; [apply prun_tle; apply alloc_slot_mono_le; exact Hf| exact H]. Qed.
End LEAF.
End MI_Fuel.
