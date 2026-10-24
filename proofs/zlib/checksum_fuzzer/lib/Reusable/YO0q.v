(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i YO0f YO0g.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Local Infix "==>" := implb (at level 55, right associativity).
Lemma zseq_In lo n k : 0 <= n -> lo <= k < lo + n -> In k (zseq lo n).
Proof.
intros Hn Hk. unfold zseq. apply in_map_iff. exists (Z.to_nat (k - lo)). split; [lia|]. apply in_seq. lia.
Qed.
Tactic Notation "brute" constr(H) constr(k) "as" ident(T) :=
pose proof H as T; rewrite forallb_forall in T; specialize (T k);
match type of T with In _ (zseq ?lo ?n) -> _ =>
specialize (T (zseq_In lo n k ltac:(lia) ltac:(lia))); cbn beta in T end.
Lemma class_size_mono_tab :
forallb (fun a => forallb (fun b => (a <=? b) ==> (znth a size_classes <=? znth b size_classes)) (zseq 0 48)) (zseq 0 48) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma class_size_mono a b : 0 <= a -> a <= b -> b < 48 -> class_size a <= class_size b.
Proof.
intros Ha Hab Hb. brute class_size_mono_tab a as H. rewrite forallb_forall in H.
specialize (H b (zseq_In 0 48 b ltac:(lia) ltac:(lia))). cbn beta in H.
unfold implb in H. destruct (a <=? b) eqn:E; [|apply Z.leb_gt in E; lia]. cbn [negb orb] in H.
apply Z.leb_le in H. unfold class_size, UNIT. lia.
Qed.
Lemma class_size_tab :
forallb (fun a => (1 <=? znth a size_classes) && (znth a size_classes <=? 8191) &&
((znth a size_classes <=? 127) ==> (a <=? 23))) (zseq 0 48) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma class_size_bounds sc : 0 <= sc < 48 -> 16 <= class_size sc <= 131056.
Proof.
intros H. brute class_size_tab sc as H0. apply andb_prop in H0 as [H0 _]. apply andb_prop in H0 as [A B].
apply Z.leb_le in A. apply Z.leb_le in B. unfold class_size, UNIT. lia.
Qed.
Lemma class_le_23 sc : 0 <= sc < 48 -> class_size sc <= 2032 -> sc <= 23.
Proof.
intros H Hs. brute class_size_tab sc as H0. apply andb_prop in H0 as [_ C]. unfold implb in C.
destruct (znth sc size_classes <=? 127) eqn:E; cbn [negb orb] in C; [apply Z.leb_le in C; lia|].
apply Z.leb_gt in E. unfold class_size, UNIT in Hs. lia.
Qed.
Lemma class_of_units_small_tab :
forallb (fun k => class_of_units k <=? 24) (zseq 0 128) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma size_to_class_small n : 0 <= n <= 2044 -> size_to_class n <= 24.
Proof.
intros Hn. unfold size_to_class.
set (k := Z.shiftr (n + IB - 1) 4).
assert (Hk : 0 <= k < 128).
{ subst k. rewrite Z.shiftr_div_pow2 by lia. unfold IB.
split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
brute class_of_units_small_tab k as H. apply Z.leb_le in H. exact H.
Qed.
Lemma page_round_ge x : x <= page_round x.
Proof. unfold page_round, PGSZ. pose proof (Z_div_mod_eq_full (x + 4096 - 1) 4096). pose proof (Z.mod_pos_bound (x + 4096 - 1) 4096 ltac:(lia)). lia. Qed.
Lemma page_round_lt x : page_round x < x + PGSZ.
Proof. unfold page_round, PGSZ. pose proof (Z_div_mod_eq_full (x + 4096 - 1) 4096). pose proof (Z.mod_pos_bound (x + 4096 - 1) 4096 ltac:(lia)). lia. Qed.
Lemma page_round_mod x : page_round x mod PGSZ = 0.
Proof. unfold page_round. apply Z_mod_mult. Qed.
Lemma page_round_pages x : page_round x = page_round x / PGSZ * PGSZ.
Proof. unfold page_round, PGSZ. rewrite Z_div_mult by lia. reflexivity. Qed.
Lemma page_round_mono x y : x <= y -> page_round x <= page_round y.
Proof. intros H. unfold page_round, PGSZ. apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; lia. Qed.
Lemma page_round_fixed x : x mod PGSZ = 0 -> page_round x = x.
Proof.
intros H. unfold page_round. unfold PGSZ in *.
pose proof (Z_div_mod_eq_full x 4096). rewrite H in H0.
replace (x + 4096 - 1) with (4096 * (x / 4096) + 4095) by lia.
rewrite (Z.mul_comm 4096 (x / 4096)), Z.div_add_l by lia. replace (4095 / 4096) with 0 by reflexivity. lia.
Qed.
Fixpoint htrail (f : nat) (c : Z) : list Z :=
c :: match f with O => [] | S f' => if Z.even c then htrail f' (c / 2) else [] end.
Lemma halve_while_even_In f c u : In (halve_while_even f c u) (htrail f c).
Proof.
revert c. induction f as [|f IH]; intros c; cbn [halve_while_even htrail]; [left; reflexivity|].
destruct (Z.even c) eqn:E; cbn [andb].
- destruct (u <? 4 * c); [right; apply IH | left; reflexivity].
- left; reflexivity.
Qed.
Lemma small_cnt_In sc u :
In (small_cnt sc u) (let row := nth (Z.to_nat sc) small_cnt_tab [] in [znth 0 row; znth 1 row; znth 2 row]).
Proof.
unfold small_cnt. set (row := nth (Z.to_nat sc) small_cnt_tab []).
destruct (negb (u <? 4 * znth 0 row)); [left; reflexivity|].
destruct (negb (u <? 4 * znth 1 row)); [right; left; reflexivity|]. right; right; left; reflexivity.
Qed.
Definition icands (sc : Z) : list Z :=
map (fun cnt => if (cnt =? 1) && (class_size sc * cnt + UNIT <=? PGSZ / 2) then 2 else cnt)
(if sc <? 9 then (let row := nth (Z.to_nat sc) small_cnt_tab [] in [znth 0 row; znth 1 row; znth 2 row])
else map (fun c => halve_while_big 8%nat c (class_size sc)) (htrail 8%nat (znth (Z.land sc 3) med_cnt_tab))).
Lemma initial_cnt_In sc u : In (initial_cnt sc u) (icands sc).
Proof.
unfold initial_cnt, icands. apply in_map_iff. eexists. split; [reflexivity|].
destruct (sc <? 9).
- apply small_cnt_In.
- apply in_map_iff. eexists. split; [reflexivity|]. apply halve_while_even_In.
Qed.
Lemma icands_tab :
forallb (fun sc => forallb (fun cnt => (1 <=? cnt) && (cnt <=? 32) && (class_size sc * cnt <? 2 ^ 20) &&
((sc <=? 26) ==> (2 <=? cnt))) (icands sc)) (zseq 0 48) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma initial_cnt_facts sc u :
0 <= sc < 48 ->
1 <= initial_cnt sc u <= 32 /\ class_size sc * initial_cnt sc u < 2 ^ 20 /\ (sc <= 26 -> 2 <= initial_cnt sc u).
Proof.
intros Hsc. brute icands_tab sc as H. rewrite forallb_forall in H. specialize (H _ (initial_cnt_In sc u)).
apply andb_prop in H as [H D]. apply andb_prop in H as [H C]. apply andb_prop in H as [A B].
apply Z.leb_le in A. apply Z.leb_le in B. apply Z.ltb_lt in C. unfold implb in D.
split; [lia|]. split; [exact C|]. intros H26.
destruct (sc <=? 26) eqn:E; [|apply Z.leb_gt in E; lia]. cbn [negb orb] in D. apply Z.leb_le in D. exact D.
Qed.
Lemma mmap_plan_facts s sc req cnt0 u cnt needed :
0 <= sc < 48 -> 1 <= cnt0 <= 32 -> class_size sc * cnt0 < 2 ^ 20 ->
0 <= req -> req + IB <= class_size sc -> (sc <= 26 -> 2 <= cnt0) ->
mmap_plan s sc req cnt0 u = (cnt, needed) ->
1 <= cnt <= 32 /\ class_size sc * cnt < 2 ^ 20 /\ (sc <= 26 -> 2 <= cnt) /\
needed mod PGSZ = 0 /\ PGSZ <= needed /\ needed <= 2 ^ 20 /\
(2 <= cnt -> UNIT + class_size sc * cnt <= needed) /\ req + IB + UNIT <= needed /\
(cnt = 1 -> needed <= page_round (class_size sc + UNIT)).
Proof.
intros Hsc Hc0 Hsz Hreq Hfit H26 Hp.
pose proof (class_size_bounds sc Hsc) as [S16 Smax].
assert (Hz16 : exists z, class_size sc = 16 * z) by (unfold class_size, UNIT; eexists; reflexivity).
unfold mmap_plan in Hp.
set (size := class_size sc) in *.
set (nosmall := is_bouncing s sc) in *.
set (usage := if Z.even sc && (sc <? 32) then u + usage_of s (sc + 1) else u) in *.
match type of Hp with context [page_round (size * ?c + UNIT)] => set (cnt1 := c) in Hp end.
assert (Hc1 : 1 <= cnt1 <= 32 /\ size * cnt1 < 2 ^ 20 /\ (sc <= 26 -> 2 <= cnt1)).
{ subst cnt1.
destruct ((usage <? 4 * cnt0) && negb nosmall); [|split; [lia|split; [lia|exact H26]]].
destruct ((Z.land sc 3 =? 1) && (8 * PGSZ <? size * cnt0)); [lia|].
destruct ((Z.land sc 3 =? 2) && (4 * PGSZ <? size * cnt0)); [lia|].
destruct ((Z.land sc 3 =? 0) && (8 * PGSZ <? size * cnt0)); [lia|].
destruct ((Z.land sc 3 =? 0) && (2 * PGSZ <? size * cnt0)); [lia|].
lia. }
cbv zeta in Hp.
assert (HN : forall c, 1 <= c <= 32 -> size * c < 2 ^ 20 -> (sc <= 26 -> 2 <= c) ->
(c, page_round (size * c + UNIT)) = (cnt, needed) ->
1 <= cnt <= 32 /\ size * cnt < 2 ^ 20 /\ (sc <= 26 -> 2 <= cnt) /\ needed mod PGSZ = 0 /\ PGSZ <= needed /\ needed <= 2 ^ 20 /\
(2 <= cnt -> UNIT + size * cnt <= needed) /\ req + IB + UNIT <= needed /\
(cnt = 1 -> needed <= page_round (size + UNIT))).
{ intros c Hc Hcs Hc26 E. injection E as <- <-.
pose proof (page_round_ge (size * c + UNIT)). pose proof (page_round_lt (size * c + UNIT)).
pose proof (page_round_mod (size * c + UNIT)).
unfold UNIT, IB, PGSZ in *.
assert (A1 : 4096 <= page_round (size * c + 16)).
{ pose proof (Z_div_mod_eq_full (page_round (size * c + 16)) 4096). nia. }
assert (A2 : page_round (size * c + 16) <= 2 ^ 20).
{ destruct Hz16 as [z Ez]. rewrite Ez in Hcs.
assert (z * c <= 65535) by nia.
pose proof (page_round_mono (size * c + 16) (2 ^ 20) ltac:(nia)).
replace (page_round (2 ^ 20)) with (2 ^ 20) in H3 by reflexivity. lia. }
assert (A3 : size * 1 <= size * c) by nia.
repeat split; try lia. intros ->. rewrite Z.mul_1_r. lia. }
destruct Hc1 as (Hc1 & Hc1s & Hc126).
destruct (negb nosmall && (cnt1 <=? 7)) eqn:E7; [|exact (HN cnt1 Hc1 Hc1s Hc126 Hp)].
set (rq := page_round (req + IB + UNIT)) in Hp.
destruct ((rq <? size + UNIT) || ((4 * PGSZ <=? rq) && (usage <? 2 * cnt1))) eqn:E1; [|exact (HN cnt1 Hc1 Hc1s Hc126 Hp)].
injection Hp as <- <-. subst rq. unfold UNIT, IB, PGSZ in *.
pose proof (page_round_ge (req + 4 + 16)). pose proof (page_round_lt (req + 4 + 16)).
pose proof (page_round_mod (req + 4 + 16)). unfold PGSZ in *.
assert (Hrq : page_round (req + 4 + 16) <= 131072).
{ pose proof (page_round_mono (req + 4 + 16) 131072 ltac:(lia)).
replace (page_round 131072) with 131072 in H2 by reflexivity. lia. }
assert (A1 : 4096 <= page_round (req + 4 + 16)).
{ pose proof (Z_div_mod_eq_full (page_round (req + 4 + 16)) 4096). lia. }
assert (A2 : page_round (req + 4 + 16) <= page_round (size + 16)) by (apply page_round_mono; lia).
assert (Hn26 : ~ sc <= 26).
{ intros Hle. assert (size <= 3264).
{ subst size. pose proof (class_size_mono sc 26 ltac:(lia) Hle ltac:(lia)).
replace (class_size 26) with 3264 in H2 by reflexivity. lia. }
assert (page_round (req + 4 + 16) <= 4096).
{ pose proof (page_round_mono (req + 4 + 16) 4096 ltac:(lia)).
replace (page_round 4096) with 4096 in H3 by reflexivity. lia. }
apply orb_prop in E1. destruct E1 as [E1|E1].
- apply Z.ltb_lt in E1. lia.
- apply andb_prop in E1 as [E1 _]. apply Z.leb_le in E1. lia. }
repeat split; lia.
Qed.
Lemma nested_facts sc cnt0 :
0 <= sc < 48 -> 1 <= cnt0 -> (sc <= 26 -> 2 <= cnt0) ->
class_size sc * cnt0 + UNIT <= PGSZ / 2 ->
let total := UNIT + cnt0 * class_size sc - IB in
let j := size_to_class total in
sc <= 23 /\ 2 <= cnt0 /\ 0 <= total <= 2044 /\ sc < j <= 24 /\ 0 <= j < 48 /\ total + IB <= class_size j /\
class_size sc < class_size j.
Proof.
intros Hsc Hc H26 Hsmall total j.
replace (PGSZ / 2) with 2048 in Hsmall by reflexivity. unfold UNIT in Hsmall.
pose proof (class_size_bounds sc Hsc) as [S16 Smax].
assert (H23 : sc <= 23).
{ apply class_le_23; [exact Hsc|]. nia. }
assert (H2 : 2 <= cnt0) by (apply H26; lia).
assert (Ht : 0 <= total <= 2044).
{ subst total. unfold UNIT, IB. split; nia. }
pose proof (size_to_class_range total ltac:(unfold MMAP_THRESHOLD; lia)) as [Hj Hfit]. fold j in Hj, Hfit.
pose proof (size_to_class_small total Ht) as Hj24. fold j in Hj24.
assert (Hlt : class_size sc < class_size j).
{ subst total. unfold UNIT, IB in *. nia. }
assert (sc < j).
{ destruct (Z_lt_dec sc j) as [|Hge]; [assumption|]. exfalso.
pose proof (class_size_mono j sc ltac:(lia) ltac:(lia) ltac:(lia)). lia. }
repeat split; lia.
Qed.
Definition need (sc : Z) : nat := if sc <? 24 then Z.to_nat (2 * (24 - sc) + 2) else 2%nat.
Lemma need_ge2 sc : (2 <= need sc)%nat.
Proof. unfold need. destruct (sc <? 24) eqn:E; [apply Z.ltb_lt in E; lia | lia]. Qed.
Lemma need_nested sc j : sc <= 23 -> sc < j -> (need j + 2 <= need sc)%nat.
Proof.
intros H23 Hlt. unfold need. destruct (sc <? 24) eqn:E; [|apply Z.ltb_ge in E; lia].
destruct (j <? 24) eqn:Ej; [apply Z.ltb_lt in Ej | apply Z.ltb_ge in Ej]; lia.
Qed.
Lemma need_le_fuel sc : 0 <= sc -> (need sc <= NEST_FUEL)%nat.
Proof. intros H. unfold need, NEST_FUEL. destruct (sc <? 24); lia. Qed.
