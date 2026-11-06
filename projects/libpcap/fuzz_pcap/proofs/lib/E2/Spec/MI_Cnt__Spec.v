(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool Lia.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Malloc.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec.
From Stdlib Require Permutation.
From stdpp Require gmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree MI_Inv LB_Inv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module MI_Cnt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Malloc. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MI_Arith.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section WithCeil.
Context {CE : CEIL}.
Definition zrange (lo n : Z) : list Z := map (fun i => lo + Z.of_nat i) (seq 0 (Z.to_nat n)).
#[using="Type"] Lemma in_zrange lo n x : 0 <= n -> (In x (zrange lo n) <-> lo <= x < lo + n).
Proof.
  intros Hn. unfold zrange. rewrite in_map_iff. split.
  - intros (i & <- & Hi). apply in_seq in Hi. lia.
  - intros H. exists (Z.to_nat (x - lo)). split; [lia|]. apply in_seq. lia.
Qed.
#[using="Type"] Lemma forallb_zrange f lo n x : forallb f (zrange lo n) = true -> 0 <= n -> lo <= x < lo + n -> f x = true.
Proof. intros H Hn Hx. rewrite forallb_forall in H. apply H. apply in_zrange; assumption. Qed.
(* [comment removed for export] *)
Fixpoint zr_go (x : Z) (k : nat) : list Z := match k with O => [] | S k' => x :: zr_go (x + 1) k' end.
#[using="Type"] Lemma zr_go_seq lo k s : map (fun i => lo + Z.of_nat i) (seq s k) = zr_go (lo + Z.of_nat s) k.
Proof. revert s. induction k as [|k IH]; intros s; [reflexivity|]. cbn [seq map zr_go]. f_equal. rewrite IH. f_equal. lia. Qed.
#[using="Type"] Lemma zrange_go lo n : zrange lo n = zr_go lo (Z.to_nat n).
Proof. unfold zrange. rewrite zr_go_seq. f_equal. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mono_f (a : Z) : bool := forallb (fun b => negb (a <? b) || (size_class a <? size_class b)) (zrange 0 48).
#[using="Type"] Lemma mono_b_true : forallb mono_f (zrange 0 48) = true. Proof. vm_compute. reflexivity. Qed.

#[using="Type"] Lemma size_class_lt a b : 0 <= a < 48 -> 0 <= b < 48 -> a < b -> size_class a < size_class b.
Proof.
  intros Ha Hb Hab. pose proof (forallb_zrange mono_f 0 48 a mono_b_true ltac:(lia) ltac:(lia)) as H. unfold mono_f in H.
  pose proof (forallb_zrange _ 0 48 b H ltac:(lia) ltac:(lia)) as H2. cbn beta in H2.
  apply orb_true_iff in H2. destruct H2 as [H2|H2]; [apply negb_true_iff in H2; apply Z.ltb_ge in H2; lia| apply Z.ltb_lt in H2; exact H2].
Qed.
#[using="Type"] Lemma size_class_le a b : 0 <= a < 48 -> 0 <= b < 48 -> a <= b -> size_class a <= size_class b.
Proof. intros. destruct (Z.eq_dec a b) as [->|]; [lia|]. pose proof (size_class_lt a b). lia. Qed.
#[using="Type"] Lemma size_class_lt_inv a b : 0 <= a < 48 -> 0 <= b < 48 -> size_class a < size_class b -> a < b.
Proof. intros. destruct (Z.lt_ge_cases a b); [assumption|]. pose proof (size_class_le b a). lia. Qed.

(* [comment removed for export] *)
Definition stc_k (k : Z) : Z :=
  if k <? 10 then k else
  let n := k + 1 in
  let i := (28 - clz32 n) * 4 + 8 in
  let i := if size_class (i + 1) <? n then i + 2 else i in
  if size_class i <? n then i + 1 else i.
#[using="Type"] Lemma size_to_class_k n : size_to_class n = stc_k (Z.shiftr (n + IB - 1) 4).
Proof. reflexivity. Qed.

Definition stc_f (k : Z) : bool := let sc := stc_k k in (0 <=? sc) && (sc <? 48) && (k + 1 <=? size_class sc).
#[using="Type"] Lemma stc_ok_b_true : forallb stc_f (zrange 0 8191) = true.
Proof. rewrite zrange_go. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)

#[using="Type"] Lemma size_to_class_ok n : 0 <= n < MMAP_THRESHOLD ->
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

(* [comment removed for export] *)
#[using="Type"] Lemma lor1_even sc : 0 <= sc -> Z.even sc = true -> Z.lor sc 1 = sc + 1.
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint he_list (f : nat) (c : Z) : list Z :=
  match f with
  | O => [c]
  | S f' => c :: (if Z.even c then he_list f' (Z.shiftr c 1) else [])
  end.
#[using="Type"] Lemma halve_even_in f : forall c u, In (halve_even f c u) (he_list f c).
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

#[using="Type"] Lemma cnt0_in sc u : In (cnt0_of sc u) (cnt0_list sc).
Proof.
  unfold cnt0_of, cnt0_list. destruct (sc <? 9).
  - unfold small_cnt_pick. destruct (negb (u <? 4 * small_cnt sc 0)); [left; reflexivity|].
    destruct (negb (u <? 4 * small_cnt sc 1)); [right; left; reflexivity| right; right; left; reflexivity].
  - apply (in_map (fun c => halve_big 8 c (UNIT * size_class sc))). apply halve_even_in.
Qed.

Definition bump (size c : Z) : Z := if (c =? 1) && (size * c + UNIT <=? PGSZ / 2) then 2 else c.

(* [comment removed for export] *)
Definition adj (sc size cnt : Z) : Z :=
  if (Z.land sc 3 =? 1) && (8 * PGSZ <? size * cnt) then 2
  else if (Z.land sc 3 =? 2) && (4 * PGSZ <? size * cnt) then 3
  else if (Z.land sc 3 =? 0) && (8 * PGSZ <? size * cnt) then 3
  else if (Z.land sc 3 =? 0) && (2 * PGSZ <? size * cnt) then 5
  else cnt.

(* [comment removed for export] *)
Definition grp_ok (sc cnt needed : Z) : bool :=
  let size := UNIT * size_class sc in
  let maplen := Z.shiftr needed 12 in
  let last := cnt - 1 in
  let stride := if (last =? 0) && negb (maplen =? 0) then maplen * 4096 - UNIT else size in
  (1 <=? cnt) && (cnt <=? 32) && (needed mod 4096 =? 0) && (4096 <=? needed) && (needed <=? 2 ^ 20)
  && (UNIT + stride * cnt <=? maplen * 4096)
  && ((stride <=? size) || (28 <=? sc))
  && (negb (last =? 0) || (27 <=? sc))
  && (stride * cnt <? 2 ^ 20) && (16 <=? stride) && (stride mod 16 =? 0)
  (* [comment removed for export] *)
  && (negb (last =? 0) || (maplen * 4096 <=? size + UNIT) || ((34 <=? sc) && (maplen * 4096 <=? round_up_pg (size + UNIT)))).

(* [comment removed for export] *)
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

#[using="Type"] Lemma ag_check_true : forallb ag_check_sc (zrange 0 48) = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma grp_ok_sound sc cnt needed : grp_ok sc cnt needed = true ->
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

#[using="Type"] Lemma grp_ok_one sc cnt needed : grp_ok sc cnt needed = true -> cnt = 1 ->
  needed <= UNIT * size_class sc + UNIT \/ (34 <= sc /\ needed <= round_up_pg (UNIT * size_class sc + UNIT)).
Proof.
  unfold grp_ok. intros H Hc. cbn zeta in H. rewrite Z.shiftr_div_pow2 in H by lia. change (2 ^ 12) with 4096 in H.
  apply andb_true_iff in H as [H ONE]. subst cnt. change (1 - 1 =? 0) with true in ONE. cbn [negb orb] in ONE.
  assert (MOD : (needed mod 4096 =? 0) = true).
  { repeat (apply andb_true_iff in H as [H ?]). assumption. }
  apply Z.eqb_eq in MOD. assert (E : needed / 4096 * 4096 = needed) by (pose proof (Z_div_mod_eq_full needed 4096); lia).
  rewrite E in ONE. apply orb_true_iff in ONE. destruct ONE as [A|A].
  - apply Z.leb_le in A. left. exact A.
  - apply andb_true_iff in A as [A B]. apply Z.leb_le in A. apply Z.leb_le in B. right. split; assumption.
Qed.

#[using="Type"] Lemma nest_ok_sound sc cnt : nest_ok sc cnt = true ->
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

#[using="Type"] Lemma round_up_pg_spec x : x <= round_up_pg x < x + 4096 /\ round_up_pg x mod 4096 = 0.
Proof.
  unfold round_up_pg, PGSZ. change (4096 - 1) with (Z.pred (2 ^ 12)). rewrite <- Z.ones_equiv, Z.land_ones by lia.
  change (2 ^ 12) with 4096.
  pose proof (Z.mod_pos_bound (- x) 4096 ltac:(lia)) as B. pose proof (Z.div_mod (- x) 4096 ltac:(lia)) as D.
  split; [lia|]. replace (x + - x mod 4096) with ((- ((- x) / 4096)) * 4096) by lia. apply Z.mod_mul. lia.
Qed.

#[using="Type"] Lemma round_up_pg_pages x : 0 < x -> exists q, round_up_pg x = q * 4096 /\ 1 <= q /\ (q - 1) * 4096 < x <= q * 4096.
Proof.
  intros Hx. destruct (round_up_pg_spec x) as [A B].
  exists (round_up_pg x / 4096). pose proof (Z.div_mod (round_up_pg x) 4096 ltac:(lia)). rewrite B in H. nia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem alloc_group_arith sc req u0 u1 (nosmall : bool) :
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

(* [comment removed for export] *)
#[using="Type"] Lemma clamp_ai size cnt : 1 <= cnt ->
  let ai := (4096 - UNIT) / size - 1 in
  let ai := if cnt - 1 <? ai then cnt - 1 else ai in
  let ai := if ai <? 0 then 0 else ai in
  0 <= ai <= cnt - 1.
Proof.
  intros Hc. cbn zeta. destruct (Z.ltb_spec (cnt - 1) ((4096 - UNIT) / size - 1)).
  - destruct (Z.ltb_spec (cnt - 1) 0); lia.
  - destruct (Z.ltb_spec ((4096 - UNIT) / size - 1) 0); lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma created_masks ai last :
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

End WithCeil.
End MI_Cnt.

(* [comment removed for export] *)
Module LB_Sum.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree Malloc MI_Inv LB_Inv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCeil.
Context {CE : CEIL}.
#[using="Type"] Lemma zsum_nil : zsum [] = 0. Proof. reflexivity. Qed.
#[using="Type"] Lemma zsum_cons x l : zsum (x :: l) = x + zsum l. Proof. reflexivity. Qed.
#[using="Type"] Lemma zsum_app l1 l2 : zsum (l1 ++ l2) = zsum l1 + zsum l2.
Proof. induction l1 as [|x l1 IH]; [cbn [app]; rewrite zsum_nil; lia|]. cbn [app]. rewrite !zsum_cons, IH. lia. Qed.

#[using="Type"] Lemma zsum_perm l l' : Permutation l l' -> zsum l = zsum l'.
Proof. induction 1; rewrite ?zsum_cons; lia. Qed.

#[using="Type"] Lemma zsum_map_perm {A} (f : A -> Z) l l' : Permutation l l' -> zsum (map f l) = zsum (map f l').
Proof. intros P. apply zsum_perm. apply Permutation_map. exact P. Qed.

#[using="Type"] Lemma zsum_map_ext {A} (f g : A -> Z) l : (forall x, In x l -> f x = g x) -> zsum (map f l) = zsum (map g l).
Proof. intros H. f_equal. apply map_ext_in. exact H. Qed.

#[using="Type"] Lemma zsum_map_le {A} (f g : A -> Z) l : (forall x, In x l -> f x <= g x) -> zsum (map f l) <= zsum (map g l).
Proof.
  induction l as [|x l IH]; intros H; cbn [map]; [rewrite zsum_nil; lia|]. rewrite !zsum_cons.
  pose proof (H x (or_introl eq_refl)). assert (zsum (map f l) <= zsum (map g l)) by (apply IH; intros y Hy; apply H; right; exact Hy). lia.
Qed.

#[using="Type"] Lemma zsum_map_nonneg {A} (f : A -> Z) l : (forall x, In x l -> 0 <= f x) -> 0 <= zsum (map f l).
Proof. intros H. induction l as [|x l IH]; cbn [map]; [rewrite zsum_nil; lia|]. rewrite zsum_cons. pose proof (H x (or_introl eq_refl)). assert (0 <= zsum (map f l)) by (apply IH; intros y Hy; apply H; right; exact Hy). lia. Qed.

#[using="Type"] Lemma zsum_map_add {A} (f g : A -> Z) l : zsum (map (fun x => f x + g x) l) = zsum (map f l) + zsum (map g l).
Proof. induction l as [|x l IH]; cbn [map]; [rewrite !zsum_nil; reflexivity|]. rewrite !zsum_cons, IH. lia. Qed.

#[using="Type"] Lemma zsum_map_mul {A} (k : Z) (f : A -> Z) l : zsum (map (fun x => k * f x) l) = k * zsum (map f l).
Proof. induction l as [|x l IH]; cbn [map]; [rewrite !zsum_nil; lia|]. rewrite !zsum_cons, IH. lia. Qed.

#[using="Type"] Lemma zsum_map_const {A} (k : Z) (l : list A) : zsum (map (fun _ => k) l) = k * zlen l.
Proof. unfold zlen. induction l as [|x l IH]; cbn [map length]; [rewrite zsum_nil; lia|]. rewrite zsum_cons, IH. lia. Qed.

#[using="Type"] Lemma zsum_map_filter {A} (p : A -> bool) (f : A -> Z) l :
  zsum (map f (List.filter p l)) = zsum (map (fun x => if p x then f x else 0) l).
Proof. induction l as [|x l IH]; cbn [map List.filter]; [reflexivity|]. destruct (p x); cbn [map]; rewrite ?zsum_cons, IH; lia. Qed.

#[using="Type"] Lemma zsum_flat_map {A B} (g : A -> list B) (f : B -> Z) l :
  zsum (map f (flat_map g l)) = zsum (map (fun a => zsum (map f (g a))) l).
Proof. induction l as [|x l IH]; cbn [map flat_map]; [reflexivity|]. rewrite map_app, zsum_app, zsum_cons, IH. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma zsum_map_remove {A} (eq_dec : forall x y : A, {x = y} + {x <> y}) (g : A -> Z) y l :
  In y l -> (forall x, In x l -> 0 <= g x) -> exists l', Permutation l (y :: l') /\ zsum (map g l) = g y + zsum (map g l').
Proof.
  intros Hin Hg. apply in_split in Hin as (l1 & l2 & ->). exists (l1 ++ l2). split; [apply Permutation_sym; apply Permutation_middle|].
  rewrite !map_app, !zsum_app. cbn [map]. rewrite zsum_cons. lia.
Qed.

#[using="Type"] Lemma zsum_inj_le {A B} (eqB : forall x y : B, {x = y} + {x <> y}) (f : A -> Z) (g : B -> Z) (h : A -> B) :
  forall (l1 : list A) (l2 : list B),
  List.NoDup l1 -> (forall x, In x l1 -> In (h x) l2 /\ f x <= g (h x)) ->
  (forall x y, In x l1 -> In y l1 -> h x = h y -> x = y) ->
  (forall y, In y l2 -> 0 <= g y) ->
  zsum (map f l1) <= zsum (map g l2).
Proof.
  induction l1 as [|a l1 IH]; intros l2 ND H INJ POS; cbn [map].
  - rewrite zsum_nil. apply zsum_map_nonneg. exact POS.
  - rewrite zsum_cons. apply List.NoDup_cons_iff in ND as [NI ND].
    destruct (H a (or_introl eq_refl)) as [Hin Hle].
    destruct (zsum_map_remove eqB g (h a) l2 Hin POS) as (l2' & P & E). rewrite E.
    assert (IH' : zsum (map f l1) <= zsum (map g l2')).
    { apply IH; [exact ND| | intros x y Hx Hy; apply INJ; right; assumption| intros y Hy; apply POS; eapply Permutation_in; [apply Permutation_sym; exact P| right; exact Hy]].
      intros x Hx. destruct (H x (or_intror Hx)) as [Hin2 Hle2]. split; [| exact Hle2].
      pose proof (Permutation_in _ P Hin2) as [E2|Hin3]; [| exact Hin3].
      exfalso. apply NI. rewrite (INJ a x (or_introl eq_refl) (or_intror Hx) E2). exact Hx. }
    lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma zlen_nil {A} : zlen (@nil A) = 0. Proof. reflexivity. Qed.
#[using="Type"] Lemma zlen_cons {A} (x : A) l : zlen (x :: l) = 1 + zlen l. Proof. unfold zlen. cbn. lia. Qed.
#[using="Type"] Lemma zlen_app {A} (l1 l2 : list A) : zlen (l1 ++ l2) = zlen l1 + zlen l2. Proof. unfold zlen. rewrite length_app. lia. Qed.
#[using="Type"] Lemma zlen_nonneg {A} (l : list A) : 0 <= zlen l. Proof. unfold zlen. lia. Qed.
#[using="Type"] Lemma zlen_perm {A} (l l' : list A) : Permutation l l' -> zlen l = zlen l'. Proof. intros P. unfold zlen. rewrite (Permutation_length P). reflexivity. Qed.
#[using="Type"] Lemma zlen_map {A B} (f : A -> B) l : zlen (map f l) = zlen l. Proof. unfold zlen. rewrite length_map. reflexivity. Qed.

#[using="Type"] Lemma zcount_eq_zsum {A} (p : A -> bool) l : zcount p l = zsum (map (fun x => if p x then 1 else 0) l).
Proof. unfold zcount, zlen. induction l as [|x l IH]; cbn [map List.filter length]; [rewrite zsum_nil; reflexivity|]. destruct (p x); cbn [length]; rewrite ?zsum_cons, <- IH; lia. Qed.
#[using="Type"] Lemma zcount_nil {A} (p : A -> bool) : zcount p [] = 0. Proof. reflexivity. Qed.
#[using="Type"] Lemma zcount_cons {A} (p : A -> bool) x l : zcount p (x :: l) = (if p x then 1 else 0) + zcount p l.
Proof. rewrite !zcount_eq_zsum. cbn [map]. rewrite zsum_cons. reflexivity. Qed.
#[using="Type"] Lemma zcount_app {A} (p : A -> bool) l1 l2 : zcount p (l1 ++ l2) = zcount p l1 + zcount p l2.
Proof. rewrite !zcount_eq_zsum, map_app, zsum_app. reflexivity. Qed.
#[using="Type"] Lemma zcount_nonneg {A} (p : A -> bool) l : 0 <= zcount p l. Proof. unfold zcount. apply zlen_nonneg. Qed.
#[using="Type"] Lemma zcount_le_len {A} (p : A -> bool) l : zcount p l <= zlen l.
Proof. induction l as [|x l IH]; [cbv; discriminate|]. rewrite zcount_cons, zlen_cons. destruct (p x); lia. Qed.
#[using="Type"] Lemma zcount_perm {A} (p : A -> bool) l l' : Permutation l l' -> zcount p l = zcount p l'.
Proof. intros P. rewrite !zcount_eq_zsum. apply zsum_map_perm. exact P. Qed.
#[using="Type"] Lemma zcount_ext {A} (p q : A -> bool) l : (forall x, In x l -> p x = q x) -> zcount p l = zcount q l.
Proof. intros H. rewrite !zcount_eq_zsum. apply zsum_map_ext. intros x Hx. rewrite (H x Hx). reflexivity. Qed.
#[using="Type"] Lemma zcount_mono {A} (p q : A -> bool) l : (forall x, In x l -> p x = true -> q x = true) -> zcount p l <= zcount q l.
Proof.
  intros H. rewrite !zcount_eq_zsum. apply zsum_map_le. intros x Hx. specialize (H x Hx). destruct (p x); [rewrite H by reflexivity; lia| destruct (q x); lia].
Qed.
#[using="Type"] Lemma zcount_false {A} (p : A -> bool) l : (forall x, In x l -> p x = false) -> zcount p l = 0.
Proof. intros H. rewrite zcount_eq_zsum. induction l as [|x l IH]; cbn [map]; [apply zsum_nil|]. rewrite zsum_cons, (H x (or_introl eq_refl)), IH; [lia|]. intros y Hy; apply H; right; exact Hy. Qed.
#[using="Type"] Lemma zcount_In_pos {A} (p : A -> bool) l x : In x l -> p x = true -> 1 <= zcount p l.
Proof.
  intros Hin Hp. apply in_split in Hin as (l1 & l2 & ->). rewrite zcount_app, zcount_cons, Hp. pose proof (zcount_nonneg p l1). pose proof (zcount_nonneg p l2). lia.
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma zcount_inj_le {A B} (eqB : forall x y : B, {x = y} + {x <> y}) (p : A -> bool) (q : B -> bool) (h : A -> B) l1 l2 :
  List.NoDup l1 -> (forall x, In x l1 -> p x = true -> In (h x) l2 /\ q (h x) = true) ->
  (forall x y, In x l1 -> In y l1 -> p x = true -> p y = true -> h x = h y -> x = y) ->
  zcount p l1 <= zcount q l2.
Proof.
  intros ND H INJ. unfold zcount at 1. unfold zlen.
  transitivity (zsum (map (fun _ => 1) (List.filter p l1))); [rewrite zsum_map_const; unfold zlen; lia|].
  rewrite zcount_eq_zsum. apply (zsum_inj_le eqB (fun _ => 1) _ h).
  - apply List.NoDup_filter. exact ND.
  - intros x Hx. apply filter_In in Hx as [Hx Hp]. destruct (H x Hx Hp) as [Hin Hq]. rewrite Hq. auto with zarith.
  - intros x y Hx Hy. apply filter_In in Hx as [Hx Hp]. apply filter_In in Hy as [Hy Hq]. apply INJ; assumption.
  - intros y _. destruct (q y); lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section MTL.
Context `{Countable K} `{EqDecision K} {V : Type}.
Implicit Types m : gmap K V.

#[using="Type"] Lemma mtl_nodup m : List.NoDup (map_to_list m).
Proof. apply NoDup_ListNoDup. apply NoDup_map_to_list. Qed.
#[using="Type"] Lemma mtl_nodup_keys m : List.NoDup (map fst (map_to_list m)).
Proof. apply NoDup_ListNoDup. apply NoDup_fst_map_to_list. Qed.
#[using="Type"] Lemma mtl_in m k v : In (k, v) (map_to_list m) <-> m !! k = Some v.
Proof. rewrite <- list_elem_of_In. apply elem_of_map_to_list. Qed.
#[using="Type"] Lemma mtl_insert m k v : m !! k = None -> Permutation (map_to_list (<[k := v]> m)) ((k, v) :: map_to_list m).
Proof. intros Hk. apply map_to_list_insert. exact Hk. Qed.
#[using="Type"] Lemma mtl_delete m k v : m !! k = Some v -> Permutation (map_to_list m) ((k, v) :: map_to_list (delete k m)).
Proof. intros Hk. rewrite <- (insert_delete_id m k v Hk) at 1. apply map_to_list_insert. apply lookup_delete_eq. Qed.
#[using="Type"] Lemma mtl_insert_old m k v v0 : m !! k = Some v0 ->
  Permutation (map_to_list (<[k := v]> m)) ((k, v) :: map_to_list (delete k m)).
Proof. intros Hk. rewrite <- (insert_delete_eq m k v). apply map_to_list_insert. apply lookup_delete_eq. Qed.

(* [comment removed for export] *)
Definition msum (f : K * V -> Z) m : Z := zsum (map f (map_to_list m)).
#[using="Type"] Lemma msum_insert f m k v : m !! k = None -> msum f (<[k := v]> m) = f (k, v) + msum f m.
Proof. intros Hk. unfold msum. rewrite (zsum_map_perm f _ _ (mtl_insert m k v Hk)). cbn [map]. apply zsum_cons. Qed.
#[using="Type"] Lemma msum_delete f m k v : m !! k = Some v -> msum f m = f (k, v) + msum f (delete k m).
Proof. intros Hk. unfold msum. rewrite (zsum_map_perm f _ _ (mtl_delete m k v Hk)). cbn [map]. apply zsum_cons. Qed.
#[using="Type"] Lemma msum_insert_old f m k v v0 : m !! k = Some v0 -> msum f (<[k := v]> m) = f (k, v) + msum f m - f (k, v0).
Proof. intros Hk. unfold msum. rewrite (zsum_map_perm f _ _ (mtl_insert_old m k v v0 Hk)). cbn [map]. rewrite zsum_cons. pose proof (msum_delete f m k v0 Hk) as E. unfold msum in E. lia. Qed.
#[using="Type"] Lemma msum_ext f g m : (forall k v, m !! k = Some v -> f (k, v) = g (k, v)) -> msum f m = msum g m.
Proof. intros Hfg. unfold msum. apply zsum_map_ext. intros [k v] Hin. apply Hfg. apply mtl_in. exact Hin. Qed.
#[using="Type"] Lemma msum_nonneg f m : (forall k v, m !! k = Some v -> 0 <= f (k, v)) -> 0 <= msum f m.
Proof. intros Hf. unfold msum. apply zsum_map_nonneg. intros [k v] Hin. apply Hf. apply mtl_in. exact Hin. Qed.
#[using="Type"] Lemma msum_empty f : msum f (∅ : gmap K V) = 0.
Proof. unfold msum. rewrite map_to_list_empty. reflexivity. Qed.
End MTL.

End WithCeil.
End LB_Sum.

(* [comment removed for export] *)
Module LB_Caps.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Inv. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.MI_Cnt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.LB_Tables OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.LB_Sum.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Section WithCeil.
Context {CE : CEIL}.
#[using="Type"] Lemma cmax_pos_tab : forallb (fun c => 1 <=? cmax c) classes = true.
Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma cmax_pos c : In c classes -> 1 <= cmax c.
Proof. intros Hc. pose proof cmax_pos_tab as T. rewrite forallb_forall in T. apply Z.leb_le. apply T. exact Hc. Qed.
#[using="Type"] Lemma guests_classes c : In c guests -> In c classes.
Proof. unfold guests, classes. cbn. intros H. decompose [or] H; subst; auto 60; contradiction. Qed.

#[using="Type"] Lemma cap0_mono (P P' : Z -> Z) c : (forall c, P c <= P' c) -> CAP0 P c <= CAP0 P' c.
Proof. intros HP. unfold CAP0. pose proof (HP (c - 1)). pose proof (HP c). pose proof (HP (c + 1)). lia. Qed.
#[using="Type"] Lemma cap_mono (P P' : Z -> Z) c : (forall c, P c <= P' c) -> CAP P c <= CAP P' c.
Proof.
  intros HP. unfold CAP, HOSTSTD. pose proof (cap0_mono P P' c HP).
  enough (zsum (map (fun c' => if bighost c' =? c then (CAP0 P c' + 32) / cmax c' else 0) guests)
          <= zsum (map (fun c' => if bighost c' =? c then (CAP0 P' c' + 32) / cmax c' else 0) guests)) by lia.
  apply zsum_map_le. intros c' Hc'. destruct (bighost c' =? c); [| lia].
  apply Z.div_le_mono; [pose proof (cmax_pos c' (guests_classes c' Hc')); lia| pose proof (cap0_mono P P' c' HP); lia].
Qed.
#[using="Type"] Lemma ncap_mono (P P' : Z -> Z) : (forall c, P c <= P' c) -> NCAP P <= NCAP P'.
Proof.
  intros HP. unfold NCAP, NG. pose proof (HP 63).
  enough (zsum (map (fun c => (CAP P c + 32) / cmax c + 160) classes) <= zsum (map (fun c => (CAP P' c + 32) / cmax c + 160) classes)) by lia.
  apply zsum_map_le. intros c Hc. pose proof (cap_mono P P' c HP). pose proof (cmax_pos c Hc).
  enough ((CAP P c + 32) / cmax c <= (CAP P' c + 32) / cmax c) by lia. apply Z.div_le_mono; lia.
Qed.
Definition NCAPMAX : Z := 17196.
#[using="Type"] Lemma NCAP_PMAX : NCAP (fun _ => PMAX) = NCAPMAX.
Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma NCAP_max (P : Z -> Z) : (forall c, 0 <= P c <= PMAX) -> NCAP P <= NCAPMAX.
Proof. intros HP. rewrite <- NCAP_PMAX. apply ncap_mono. intros c. pose proof (HP c). lia. Qed.
#[using="Type"] Lemma AQ_NCAP st BL P : AQ st BL P -> NCAP P <= NCAPMAX.
Proof. intros A. apply NCAP_max. exact (aq_P _ _ _ A). Qed.

End WithCeil.
End LB_Caps.
