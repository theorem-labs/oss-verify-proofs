(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount FseLemmas FseAbs FseReaderRT.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac cbnR := cbn [r_nc r_ip r_bitStream r_bitCount r_charnum r_remaining r_threshold r_nbBits r_previous0].
Ltac cbnR_in H := cbn [r_nc r_ip r_bitStream r_bitCount r_charnum r_remaining r_threshold r_nbBits r_previous0] in H.
Definition pws (l : list Z) (k : Z) : Z := wsum (firstn (Z.to_nat k) l).
Lemma pws_S l k : 0 <= k -> k < Zlength l -> pws l (k + 1) = pws l k + weight (Znth k l).
Proof.
intros. unfold pws, Znth, Zlength in *. replace (Z.to_nat (k + 1)) with (S (Z.to_nat k)) by lia.
apply (wsum_firstn_S 0). lia.
Qed.
Lemma pws_zeros l a b : 0 <= a <= b -> b <= Zlength l -> (forall i, a <= i < b -> Znth i l = 0) -> pws l b = pws l a.
Proof.
intros Hab Hb HZ.
assert (G : forall n : nat, a + Z.of_nat n <= b -> pws l (a + Z.of_nat n) = pws l a).
{ induction n; intros Hnb.
- rewrite Z.add_0_r. reflexivity.
- replace (a + Z.of_nat (S n)) with (a + Z.of_nat n + 1) by lia. rewrite pws_S by lia.
rewrite IHn by lia. rewrite HZ by lia. unfold weight. cbn. lia. }
replace b with (a + Z.of_nat (Z.to_nat (b - a))) by lia. apply G; lia.
Qed.
Lemma pws_upd_above l k j c : 0 <= k <= j -> pws (Zupd j c l) k = pws l k.
Proof.
intros. unfold pws.
assert (G : forall (n : nat) (i : nat) l', (n <= i)%nat -> firstn n (upd_nat i c l') = firstn n l').
{ induction n; intros i l' Hn; [reflexivity|]. destruct l' as [|x t]; [destruct i; reflexivity|].
destruct i; [lia|]. cbn. f_equal. apply IHn. lia. }
unfold Zupd. rewrite G by lia. reflexivity.
Qed.
Lemma to_short_id c : -32768 <= c <= 32767 -> to_short c = c.
Proof.
intros. unfold to_short. change (2^15) with 32768. change (2^16) with 65536.
destruct (Z_lt_le_dec c 0); [rewrite Z.mod_small by lia | rewrite Z.mod_small by lia]; lia.
Qed.
Lemma ctz_aux_low : forall f x, 0 <= x -> x mod 2^(ctz_aux f x) = 0.
Proof.
induction f as [|f IH]; intros x Hx; cbn [ctz_aux].
- rewrite Z.pow_0_r. apply Z.mod_1_r.
- destruct (Z.odd x) eqn:E.
+ rewrite Z.pow_0_r. apply Z.mod_1_r.
+ pose proof (ctz_aux_le f (Z.div2 x)) as HL.
rewrite Z.pow_add_r by lia. change (2^1) with 2. rewrite Z.div2_div in *.
assert (Hev : x = 2 * (x / 2)).
{ pose proof (Z.div_mod x 2 ltac:(lia)). pose proof (Zmod_odd x) as Ho. rewrite E in Ho. lia. }
rewrite Hev at 1. rewrite Z.mul_mod_distr_l by (try apply Z.pow_nonneg; lia). rewrite IH by (apply Z.div_pos; lia). lia.
Qed.
Lemma repeats_ge12_low24 bs q : 0 <= bs < 2^32 -> repeats_of bs = Ok q -> 12 <= q -> 2^24 - 1 <= bs.
Proof.
intros Hbs E Hq. unfold repeats_of, ctz32 in E.
destruct (repeats_arg_mod bs 24 Hbs ltac:(lia)) as [Hlow Hrange].
set (a := Z.lor (not32 bs) (2^31)) in *.
rewrite u32_id in E by lia. destruct (Z.eqb_spec a 0); [lia|]. cbn [bind] in E.
pose proof (ctz_aux_low 32 a ltac:(lia)) as HZ. pose proof (ctz_aux_le 32 a) as HcL. change (Z.of_nat 32) with 32 in HcL.
remember (ctz_aux 32 a) as c eqn:Ec. clear Ec.
assert (E' : c / 2 = q) by congruence. clear E.
assert (Hc : 24 <= c) by (pose proof (Z.div_mod c 2 ltac:(lia)); pose proof (Z.mod_pos_bound c 2 ltac:(lia)); lia).
assert (P24 : 0 < 2^(c-24)) by (apply Z.pow_pos_nonneg; lia).
assert (Pc : 2^c = 2^24 * 2^(c-24)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
assert (Ha24 : a mod 2^24 = 0).
{ pose proof (Z.div_mod a (2^c) ltac:(lia)) as D. rewrite HZ, Z.add_0_r in D.
rewrite D, Pc, <- Z.mul_assoc, Z.mul_comm. apply Z_mod_mult. }
pose proof (Z.mod_pos_bound bs (2^24) ltac:(lia)). pose proof (Z.div_mod bs (2^24) ltac:(lia)).
assert (0 <= bs / 2^24) by (apply Z.div_pos; lia). lia.
Qed.
Section S.
Variable buf : list Z.
Hypothesis Hbytes : all_bytes buf.
Let h : Z := Zlength buf.
Hypothesis H8 : 8 <= h.
Variable maxSV1 : Z.
Variable nc0 : list Z.
Hypothesis Hm1 : 1 <= maxSV1 <= Zlength nc0.
Variable tl : Z.
Hypothesis Htl : 5 <= tl <= 15.
Let P2tl : 32 <= 2^tl <= 32768.
Proof. split; [change 32 with (2^5) | change 32768 with (2^15)]; apply Z.pow_le_mono_r; lia. Qed.
Definition POS (s : rstate) : Prop :=
0 <= r_ip s /\ r_ip s + 4 <= h /\ 0 <= r_bitCount s /\ (r_bitCount s <= 7 \/ r_ip s = h - 4) /\
0 <= r_bitStream s < 2^32 /\ 4 <= 8 * r_ip s + r_bitCount s.
Definition CTL (s : rstate) : Prop :=
length (r_nc s) = length nc0 /\ 0 <= r_charnum s < maxSV1 /\
(forall i, r_charnum s <= i < maxSV1 -> Znth i (r_nc s) = 0) /\
(forall i, maxSV1 <= i -> Znth i (r_nc s) = Znth i nc0) /\
r_threshold s = 2^(r_nbBits s - 1) /\ 2 <= r_nbBits s <= tl + 1 /\
r_threshold s <= r_remaining s < 2 * r_threshold s /\ r_remaining s <= 2^tl + 1 /\
(tl <= 14 -> (forall i, 0 <= i < r_charnum s -> -1 <= Znth i (r_nc s)) /\
r_remaining s = 2^tl + 1 - pws (r_nc s) (r_charnum s)).
Definition BRK (s : rstate) : Prop :=
length (r_nc s) = length nc0 /\ 1 <= r_charnum s /\
0 <= r_ip s /\ r_ip s + 4 <= h /\ 0 <= r_bitCount s /\ 4 <= 8 * r_ip s + r_bitCount s /\
(r_charnum s <= maxSV1 ->
(forall i, r_charnum s <= i < maxSV1 -> Znth i (r_nc s) = 0) /\
(forall i, maxSV1 <= i -> Znth i (r_nc s) = Znth i nc0) /\
(tl <= 14 -> (forall i, 0 <= i < r_charnum s -> -1 <= Znth i (r_nc s)) /\
r_remaining s = 2^tl + 1 - pws (r_nc s) (r_charnum s))).
#[using="Hbytes tl"] Lemma readLE32_ok ip : 0 <= ip -> ip + 4 <= h -> exists w, readLE32 buf ip = Ok w /\ 0 <= w < 2^32.
Proof.
intros. rewrite (readLE32_val buf ip Hbytes) by (unfold h in *; lia).
eexists. split; [reflexivity|]. apply Z.mod_pos_bound. lia.
Qed.
#[using="Hbytes H8 tl Htl"] Lemma reload_total s :
0 <= r_ip s -> r_ip s + 4 <= h -> 0 <= r_bitCount s -> (r_ip s <= h - 7 -> r_bitCount s <= 31) ->
4 <= 8 * r_ip s + r_bitCount s ->
exists s', reload buf s = Ok s' /\ POS s' /\ r_bitCount s' < 32 /\
r_nc s' = r_nc s /\ r_charnum s' = r_charnum s /\ r_remaining s' = r_remaining s /\
r_threshold s' = r_threshold s /\ r_nbBits s' = r_nbBits s /\ r_previous0 s' = r_previous0 s.
Proof.
intros Hip Hip4 Hbc Hbc31 H4. unfold reload. fold h.
rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite land_7, land_31.
pose proof (Z.div_mod (r_bitCount s) 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (r_bitCount s) 8 ltac:(lia)) as MB.
assert (Hq : 0 <= r_bitCount s / 8) by (apply Z.div_pos; lia).
match goal with |- context [if ?c then _ else _] => destruct c eqn:EC end.
- assert (Hip' : r_ip s + r_bitCount s / 8 + 4 <= h).
{ apply Bool.orb_true_iff in EC. destruct EC as [EC|EC]; apply Z.leb_le in EC; [|lia].
assert (r_bitCount s / 8 < 4) by (apply Z.div_lt_upper_bound; lia). lia. }
destruct (readLE32_ok (r_ip s + r_bitCount s / 8) ltac:(lia) Hip') as (w & -> & Hw). cbn [bind].
rewrite shr32_ok by lia. cbn [bind]. eexists. split; [reflexivity|].
unfold POS; cbnR. pose proof (Z.mod_pos_bound (r_bitCount s) 8 ltac:(lia)).
assert (0 <= w / 2 ^ (r_bitCount s mod 8) < 2^32).
{ split; [apply Z.div_pos; [lia|apply pow2_pos; lia]|]. apply Z.div_lt_upper_bound; [apply pow2_pos; lia|].
pose proof (pow2_pos (r_bitCount s mod 8) ltac:(lia)). nia. }
repeat split; auto; try lia.
- apply Bool.orb_false_iff in EC. destruct EC as [E1 E2]. apply Z.leb_gt in E1. apply Z.leb_gt in E2.
destruct (readLE32_ok (h - 4) ltac:(lia) ltac:(lia)) as (w & -> & Hw). cbn [bind].
pose proof (Z.mod_pos_bound (r_bitCount s - 8 * (h - 4 - r_ip s)) 32 ltac:(lia)) as M32.
rewrite shr32_ok by lia. cbn [bind]. eexists. split; [reflexivity|].
unfold POS; cbnR.
assert (0 <= w / 2 ^ ((r_bitCount s - 8 * (h - 4 - r_ip s)) mod 32) < 2^32).
{ split; [apply Z.div_pos; [lia|apply pow2_pos; lia]|]. apply Z.div_lt_upper_bound; [apply pow2_pos; lia|].
pose proof (pow2_pos ((r_bitCount s - 8 * (h - 4 - r_ip s)) mod 32) ltac:(lia)). nia. }
repeat split; auto; try lia.
Qed.
Definition Rbc (bc : Z) : Z := if (8 <=? bc) && (bc <=? 16) then (if bc =? 16 then 3 else 2) else 1.
Definition mu (s : rstate) : Z :=
if r_ip s <=? h - 7 then h - 7 - r_ip s + 5 else if r_ip s <? h - 4 then 4 else Rbc (r_bitCount s).
#[using="buf h tl"] Lemma Rbc_range bc : 1 <= Rbc bc <= 3.
Proof. unfold Rbc. destruct (_ && _); [destruct (bc =? 16)|]; lia. Qed.
#[using="tl"] Lemma mu_pos s : POS s -> 1 <= mu s <= h - 2 \/ 1 <= mu s <= 4.
Proof.
intros (P1 & P2 & _). unfold mu. pose proof (Rbc_range (r_bitCount s)).
destruct (Z.leb_spec (r_ip s) (h - 7)); [lia|]. destruct (Z.ltb_spec (r_ip s) (h - 4)); lia.
Qed.
#[using="buf h tl Htl"] Lemma cont_bc_le8 w bc q : 0 <= w < 2^32 -> 0 <= bc < 32 -> repeats_of (w / 2^bc) = Ok q -> 12 <= q -> bc <= 8.
Proof.
intros Hw Hbc E Hq.
assert (Hr : 0 <= w / 2^bc < 2^32).
{ split; [apply Z.div_pos; [lia|apply pow2_pos; lia]|]. apply Z.div_lt_upper_bound; [apply pow2_pos; lia|].
pose proof (pow2_pos bc ltac:(lia)). nia. }
pose proof (repeats_ge12_low24 _ _ Hr E Hq) as HL.
destruct (Z_lt_le_dec 8 bc); [|lia]. exfalso.
assert (2^9 <= 2^bc) by (apply Z.pow_le_mono_r; lia).
assert (w / 2^bc <= w / 2^9) by (apply Z.div_le_compat_l; lia).
assert (w / 2^9 < 2^23) by (apply Z.div_lt_upper_bound; [lia|]; change (2^32) with (2^9 * 2^23) in Hw; lia).
change (2^24) with (2 * 2^23) in HL. lia.
Qed.
#[using="Hbytes H8 tl Htl"] Lemma rep_loop_total f : forall s rep,
POS s -> r_bitCount s < 32 -> 0 <= r_charnum s -> 0 <= rep <= 16 -> (0 < f)%nat -> (12 <= rep -> mu s < Z.of_nat f) ->
exists s1 rep1, rep_loop buf f s rep = Ok (s1, rep1) /\ 0 <= rep1 <= 11 /\
POS s1 /\ r_bitCount s1 < 32 /\ r_charnum s <= r_charnum s1 /\
r_nc s1 = r_nc s /\ r_remaining s1 = r_remaining s /\ r_threshold s1 = r_threshold s /\
r_nbBits s1 = r_nbBits s /\ r_previous0 s1 = r_previous0 s.
Proof.
induction f as [|f IH]; intros s rep HP Hbc32 Hcn Hrep Hf Hmu; [lia|].
pose proof HP as (P1 & P2 & P3 & P4 & P5 & P6).
cbn [rep_loop]. fold h.
destruct (Z.leb_spec 12 rep).
2:{ exists s, rep. split; [reflexivity|]. repeat split; auto; lia. }
specialize (Hmu ltac:(lia)). rewrite Nat2Z.inj_succ in Hmu.
set (ip' := if r_ip s <=? h - 7 then r_ip s + 3 else h - 4).
set (bc' := if r_ip s <=? h - 7 then r_bitCount s else Z.land (r_bitCount s - 8 * (h - 7 - r_ip s)) 31).
replace (if r_ip s <=? h - 7 then (r_ip s + 3, r_bitCount s) else (h - 4, Z.land (r_bitCount s - 8 * (h - 7 - r_ip s)) 31))
with (ip', bc') by (subst ip' bc'; destruct (r_ip s <=? h - 7); reflexivity).
assert (HB : 0 <= ip' /\ ip' + 4 <= h /\ 0 <= bc' < 32 /\ (bc' <= 7 \/ ip' = h - 4) /\ 3 <= ip' /\
(r_ip s <= h - 7 /\ ip' = r_ip s + 3 \/ h - 7 < r_ip s /\ ip' = h - 4 /\ bc' = (r_bitCount s - 8 * (h - 7 - r_ip s)) mod 32)).
{ subst ip' bc'. destruct (Z.leb_spec (r_ip s) (h - 7)).
- repeat split; try lia.
- rewrite land_31. pose proof (Z.mod_pos_bound (r_bitCount s - 8 * (h - 7 - r_ip s)) 32 ltac:(lia)). repeat split; try lia. }
destruct HB as (B1 & B2 & B3 & B4 & B5 & B6). clearbody ip' bc'.
destruct (readLE32_ok ip' B1 B2) as (w & -> & Hw). cbn [bind].
rewrite shr32_ok by lia. cbn [bind].
assert (Hbs' : 0 <= w / 2^bc' < 2^32).
{ split; [apply Z.div_pos; [lia|apply pow2_pos; lia]|]. apply Z.div_lt_upper_bound; [apply pow2_pos; lia|].
pose proof (pow2_pos bc' ltac:(lia)). nia. }
destruct (repeats_of_ok _ Hbs') as (q & Eq & Hq). rewrite Eq. cbn [bind].
match goal with |- context [rep_loop _ _ ?st _] => set (s' := st) end.
assert (HP' : POS s') by (unfold POS; subst s'; cbnR; repeat split; lia).
pose proof (mu_pos s HP) as MU0.
assert (Hmu' : 12 <= q -> mu s' < Z.of_nat f).
{ intros Hq12. pose proof (cont_bc_le8 w bc' q Hw ltac:(lia) Eq Hq12) as Hb8.
enough (mu s' <= mu s - 1) by lia.
unfold mu. subst s'; cbnR.
destruct B6 as [(C1 & C2) | (C1 & C2 & C3)].
+ replace (r_ip s <=? h - 7) with true by (symmetry; apply Z.leb_le; lia).
pose proof (Rbc_range bc').
destruct (Z.leb_spec ip' (h - 7)); [lia|]. destruct (Z.ltb_spec ip' (h - 4)); lia.
+ replace (r_ip s <=? h - 7) with false by (symmetry; apply Z.leb_gt; lia).
replace (ip' <=? h - 7) with false by (symmetry; apply Z.leb_gt; lia).
replace (ip' <? h - 4) with false by (symmetry; apply Z.ltb_ge; lia).
destruct (Z.ltb_spec (r_ip s) (h - 4)).
* pose proof (Rbc_range bc'). lia.
* assert (Eip : r_ip s = h - 4) by lia. rewrite Eip in C3.
replace (r_bitCount s - 8 * (h - 7 - (h - 4))) with (r_bitCount s + 24) in C3 by lia.
assert (CASE : 8 <= r_bitCount s <= 16 /\ bc' = r_bitCount s - 8).
{ destruct (Z_lt_le_dec (r_bitCount s) 8).
- exfalso. rewrite Z.mod_small in C3 by lia. lia.
- replace (r_bitCount s + 24) with ((r_bitCount s - 8) + 1 * 32) in C3 by lia.
rewrite Z.mod_add in C3 by lia. rewrite Z.mod_small in C3 by lia. lia. }
destruct CASE as [CR CE]. rewrite CE. unfold Rbc.
replace ((8 <=? r_bitCount s) && (r_bitCount s <=? 16)) with true by (symmetry; apply andb_true_intro; split; apply Z.leb_le; lia).
destruct (Z.eqb_spec (r_bitCount s) 16).
-- replace ((8 <=? r_bitCount s - 8) && (r_bitCount s - 8 <=? 16)) with true by (symmetry; apply andb_true_intro; split; apply Z.leb_le; lia).
replace (r_bitCount s - 8 =? 16) with false by (symmetry; apply Z.eqb_neq; lia). lia.
-- replace ((8 <=? r_bitCount s - 8) && (r_bitCount s - 8 <=? 16)) with false by (symmetry; apply Bool.andb_false_intro1; apply Z.leb_gt; lia). lia. }
destruct (IH s' q HP' ltac:(subst s'; cbnR; lia) ltac:(subst s'; cbnR; lia) Hq ltac:(lia) Hmu') as (s1 & rep1 & E1 & R1 & HP1 & Hb1 & Hc1 & N1 & RE1 & TH1 & NB1 & PZ1).
exists s1, rep1. rewrite E1. split; [reflexivity|]. subst s'; cbnR_in Hc1; cbnR_in N1; cbnR_in RE1; cbnR_in TH1; cbnR_in NB1; cbnR_in PZ1.
split; [exact R1|]. split; [exact HP1|]. split; [exact Hb1|]. split; [lia|]. repeat split; congruence.
Qed.
#[using="Hbytes H8 Hm1 Htl"] Lemma rzero_total s :
CTL s -> POS s -> r_bitCount s < 32 ->
exists fl, rzero_block buf maxSV1 s = Ok fl /\
match fl with
| Cont s' => CTL s' /\ POS s' /\ r_bitCount s' < 32 /\ r_charnum s <= r_charnum s'
| Brk s' => BRK s' /\ maxSV1 <= r_charnum s' /\ r_remaining s' = r_remaining s
end.
Proof.
intros HC HP Hb32.
pose proof HC as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9). pose proof HP as (P1 & P2 & P3 & P4 & P5 & P6).
unfold rzero_block. fold h.
destruct (repeats_of_ok (r_bitStream s) P5) as (rep & -> & Hrep). cbn [bind].
assert (Hmu : mu s < Z.of_nat (S (Z.to_nat h))).
{ pose proof (mu_pos s HP). rewrite Nat2Z.inj_succ, Z2Nat.id by lia. lia. }
destruct (rep_loop_total (S (Z.to_nat h)) s rep HP Hb32 ltac:(lia) Hrep ltac:(lia) ltac:(intros; exact Hmu))
as (s1 & rep1 & -> & R1 & HP1 & Hb1 & Hc1 & N1 & RE1 & TH1 & NB1 & PZ1). cbn [bind].
pose proof HP1 as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
rewrite shr32_ok by lia. cbn [bind].
set (bs' := r_bitStream s1 / 2 ^ (2 * rep1)).
assert (Hbs' : 0 <= bs' < 2^32).
{ subst bs'. split; [apply Z.div_pos; [lia|apply pow2_pos; lia]|]. apply Z.div_lt_upper_bound; [apply pow2_pos; lia|].
pose proof (pow2_pos (2 * rep1) ltac:(lia)). nia. }
assert (Hl3 : 0 <= Z.land bs' 3 < 4) by (rewrite land_3; apply Z.mod_pos_bound; lia).
set (cn' := r_charnum s1 + 3 * rep1 + Z.land bs' 3).
destruct (Z.leb_spec maxSV1 cn').
-
eexists. split; [reflexivity|]. cbn [r_charnum r_remaining]. split; [|split; [lia|exact RE1]].
unfold BRK; cbnR. rewrite N1, RE1. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
intros Hle. assert (Ecn : cn' = maxSV1) by lia.
split; [intros; lia|]. split; [exact C4|].
intros Htl14. destruct (C9 Htl14) as [G1 G2]. split.
+ intros i Hi. destruct (Z_lt_le_dec i (r_charnum s)); [apply G1; lia|]. rewrite C3 by lia. lia.
+ rewrite G2. f_equal. symmetry. apply pws_zeros; [lia | unfold Zlength; rewrite C1; unfold Zlength in Hm1; lia | intros; apply C3; lia].
-
destruct (reload_total (mkR (r_nc s1) (r_ip s1) bs' (r_bitCount s1 + 2 * rep1 + 2) cn' (r_remaining s1) (r_threshold s1) (r_nbBits s1) (r_previous0 s1)))
as (s3 & -> & HP3 & Hb3 & M1 & M2 & M3 & M4 & M5 & M6); cbnR; try lia.
cbnR_in M1. cbnR_in M2. cbnR_in M3. cbnR_in M4. cbnR_in M5. cbnR_in M6.
eexists. split; [reflexivity|]. cbn [r_charnum].
split; [| split; [exact HP3|]; split; [exact Hb3 | lia]].
unfold CTL. rewrite M1, M2, M3, M4, M5, N1, RE1, TH1, NB1.
split; [exact C1|]. split; [lia|]. split; [intros; apply C3; lia|]. split; [exact C4|].
split; [exact C5|]. split; [exact C6|]. split; [exact C7|]. split; [exact C8|].
intros Htl14. destruct (C9 Htl14) as [G1 G2]. split.
+ intros i Hi. destruct (Z_lt_le_dec i (r_charnum s)); [apply G1; lia|]. rewrite C3 by lia. lia.
+ rewrite G2. f_equal. symmetry. apply pws_zeros; [lia | unfold Zlength; rewrite C1; unfold Zlength in Hm1; lia | intros; apply C3; lia].
Qed.
#[using="Hbytes H8 Hm1 Htl"] Lemma rcount_total s :
CTL s -> POS s -> r_bitCount s < 32 ->
exists fl, rcount_block buf maxSV1 s = Ok fl /\
match fl with
| Cont s' => CTL s' /\ POS s' /\ r_bitCount s' < 32 /\ r_charnum s < r_charnum s'
| Brk s' => BRK s' /\ (r_charnum s' <= maxSV1) /\
(r_remaining s' = 1 -> tl <= 14 -> pws (r_nc s') (r_charnum s') = 2^tl)
end.
Proof.
intros HC HP Hb32.
pose proof HC as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9). pose proof HP as (P1 & P2 & P3 & P4 & P5 & P6).
assert (Pnb : 2 <= 2 ^ (r_nbBits s - 1) <= 2 ^ tl).
{ split; [change 2 with (2^1)|]; apply Z.pow_le_mono_r; lia. }
assert (Ptl1 : 2 ^ tl <= 2 ^ 15) by (apply Z.pow_le_mono_r; lia). change (2^15) with 32768 in Ptl1.
unfold rcount_block. fold h.
set (thr := r_threshold s) in *. set (rem := r_remaining s) in *. set (bs := r_bitStream s) in *. set (nb := r_nbBits s) in *.
rewrite (u32_id (2 * thr - 1 - rem)) by lia.
match goal with |- context [let '(count0, bc) := ?e in _] =>
assert (HD : exists count0 w, e = (count0, r_bitCount s + w) /\ 0 <= count0 <= Z.max (thr - 1) rem /\ 0 <= count0 /\ 1 <= w <= nb);
[| destruct HD as (count0 & w & ED & Hc0 & _ & Hw); rewrite ED] end.
{ assert (L1 : 0 <= Z.land bs (thr - 1) <= thr - 1).
{ rewrite C5. rewrite land_ones_mod by lia. pose proof (Z.mod_pos_bound bs (2 ^ (nb - 1)) ltac:(lia)). lia. }
assert (L2 : 0 <= Z.land bs (2 * thr - 1) <= 2 * thr - 1).
{ replace (2 * thr) with (2 ^ nb) by (rewrite C5, <- pow2_S by lia; f_equal; lia).
rewrite land_ones_mod by lia. pose proof (Z.mod_pos_bound bs (2 ^ nb) ltac:(apply pow2_pos; lia)). lia. }
destruct (Z.ltb_spec (Z.land bs (thr - 1)) (2 * thr - 1 - rem)).
- eexists _, (nb - 1). split; [reflexivity|]. lia.
- destruct (Z.leb_spec thr (Z.land bs (2 * thr - 1))); eexists _, nb; (split; [reflexivity|]); lia. }
set (count := count0 - 1).
set (rem' := if 0 <=? count then rem - count else rem + count).
assert (Hrem' : rem' = rem - Z.abs count /\ rem' <= rem) by (subst rem'; destruct (Z.leb_spec 0 count); lia).
destruct Hrem' as [Erem' Lrem']. clearbody rem'.
unfold store. replace ((0 <=? r_charnum s) && (r_charnum s <? Zlength (r_nc s))) with true
by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; unfold Zlength in *; rewrite ?C1; lia).
cbn [bind].
set (nc' := Zupd (r_charnum s) (to_short count) (r_nc s)).
assert (Hlen' : length nc' = length nc0) by (subst nc'; rewrite Zupd_length; exact C1).
assert (Hz' : forall i, r_charnum s + 1 <= i < maxSV1 -> Znth i nc' = 0).
{ intros i Hi. subst nc'. rewrite Znth_Zupd_other by lia. apply C3. lia. }
assert (Ha' : forall i, maxSV1 <= i -> Znth i nc' = Znth i nc0).
{ intros i Hi. subst nc'. rewrite Znth_Zupd_other by lia. apply C4. lia. }
assert (H14 : tl <= 14 -> (forall i, 0 <= i < r_charnum s + 1 -> -1 <= Znth i nc') /\ rem' = 2 ^ tl + 1 - pws nc' (r_charnum s + 1)).
{ intros Htl14. destruct (C9 Htl14) as [G1 G2].
assert (Pt14 : 2 ^ tl <= 2 ^ 14) by (apply Z.pow_le_mono_r; lia). change (2^14) with 16384 in Pt14.
assert (Ets : to_short count = count) by (apply to_short_id; subst count; lia).
split.
- intros i Hi. subst nc'. destruct (Z.eq_dec i (r_charnum s)).
+ subst i. rewrite Znth_Zupd_same by (unfold Zlength in *; rewrite ?C1; lia). rewrite Ets. subst count. lia.
+ rewrite Znth_Zupd_other by lia. apply G1. lia.
- rewrite pws_S by (unfold Zlength in *; rewrite ?Hlen'; lia).
subst nc'. rewrite pws_upd_above by lia. rewrite Znth_Zupd_same by (unfold Zlength in *; rewrite ?C1; lia).
rewrite Ets. rewrite <- (weight_abs 0) by (subst count; lia). fold rem in G2. lia. }
assert (HBRK : forall bc' thrx nbx p0, 0 <= bc' -> 4 <= 8 * r_ip s + bc' ->
BRK (mkR nc' (r_ip s) bs bc' (r_charnum s + 1) rem' thrx nbx p0)).
{ intros bc' thrx nbx p0 Hb0 Hb4. unfold BRK; cbnR. split; [exact Hlen'|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
intros Hle. split; [exact Hz'|]. split; [exact Ha'|]. exact H14. }
destruct (Z.ltb_spec rem' thr) as [Hlt|Hge].
- destruct (Z.leb_spec rem' 1) as [Hle1|Hgt1].
+
cbn [bind]. eexists. split; [reflexivity|]. cbn [r_charnum r_remaining r_nc].
split; [apply HBRK; lia | split; [lia | intros E1 Htl14; destruct (H14 Htl14) as [_ G2]; lia]].
+ unfold highbit32. replace ((0 <? rem') && (rem' <? 2 ^ 32)) with true
by (symmetry; apply andb_true_intro; split; apply Z.ltb_lt; lia). cbn [bind].
pose proof (Z.log2_spec rem' ltac:(lia)) as [LS1 LS2]. pose proof (Z.log2_nonneg rem') as LS0.
assert (LS3 : Z.log2 rem' < tl) by (apply Z.log2_lt_pow2; lia).
unfold assert. replace ((0 <=? Z.log2 rem' + 1 - 1) && (Z.log2 rem' + 1 - 1 <? 31)) with true
by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia). cbn [bind].
replace (Z.log2 rem' + 1 - 1) with (Z.log2 rem') by lia.
destruct (Z.leb_spec maxSV1 (r_charnum s + 1)).
* eexists. split; [reflexivity|]. cbn [r_charnum r_remaining r_nc].
split; [apply HBRK; lia | split; [lia | intros E1 Htl14; destruct (H14 Htl14) as [_ G2]; lia]].
* destruct (reload_total (mkR nc' (r_ip s) bs (r_bitCount s + w) (r_charnum s + 1) rem' (2 ^ Z.log2 rem') (Z.log2 rem' + 1) (count =? 0)))
as (s2 & -> & HP2 & Hb2 & M1 & M2 & M3 & M4 & M5 & M6); cbnR; try lia.
cbnR_in M1. cbnR_in M2. cbnR_in M3. cbnR_in M4. cbnR_in M5.
eexists. split; [reflexivity|].
split; [| split; [exact HP2 | split; [exact Hb2 | lia]]].
unfold CTL. rewrite M1, M2, M3, M4, M5. replace (Z.log2 rem' + 1 - 1) with (Z.log2 rem') by lia.
rewrite Z.pow_succ_r in LS2 by lia.
assert (LS4 : 1 <= Z.log2 rem') by (change 1 with (Z.log2 2); apply Z.log2_le_mono; lia).
split; [exact Hlen'|]. split; [lia|]. split; [exact Hz'|]. split; [exact Ha'|]. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. exact H14.
- cbn [bind]. destruct (Z.leb_spec maxSV1 (r_charnum s + 1)).
* eexists. split; [reflexivity|]. cbn [r_charnum r_remaining r_nc].
split; [apply HBRK; lia | split; [lia | intros E1 Htl14; destruct (H14 Htl14) as [_ G2]; lia]].
* destruct (reload_total (mkR nc' (r_ip s) bs (r_bitCount s + w) (r_charnum s + 1) rem' thr nb (count =? 0)))
as (s2 & -> & HP2 & Hb2 & M1 & M2 & M3 & M4 & M5 & M6); cbnR; try lia.
cbnR_in M1. cbnR_in M2. cbnR_in M3. cbnR_in M4. cbnR_in M5.
eexists. split; [reflexivity|].
split; [| split; [exact HP2 | split; [exact Hb2 | lia]]].
unfold CTL. rewrite M1, M2, M3, M4, M5.
split; [exact Hlen'|]. split; [lia|]. split; [exact Hz'|]. split; [exact Ha'|]. split; [exact C5|]. split; [exact C6|]. split; [lia|]. split; [lia|]. exact H14.
Qed.
#[using="Hbytes H8 Hm1 Htl"] Lemma rbody_total s :
CTL s -> POS s -> r_bitCount s < 32 ->
exists fl, rbody buf maxSV1 s = Ok fl /\
match fl with
| Cont s' => CTL s' /\ POS s' /\ r_bitCount s' < 32 /\ r_charnum s < r_charnum s'
| Brk s' => BRK s' /\ (r_remaining s' = 1 -> r_charnum s' <= maxSV1 /\ (tl <= 14 -> pws (r_nc s') (r_charnum s') = 2^tl))
end.
Proof.
intros HC HP Hb. unfold rbody.
assert (HZ : exists fl, (if r_previous0 s then rzero_block buf maxSV1 s else Ok (Cont s)) = Ok fl /\
match fl with
| Cont s1 => CTL s1 /\ POS s1 /\ r_bitCount s1 < 32 /\ r_charnum s <= r_charnum s1
| Brk s' => BRK s' /\ maxSV1 <= r_charnum s' /\ r_remaining s' = r_remaining s
end).
{ destruct (r_previous0 s).
- destruct (rzero_total s HC HP Hb) as (fl & E & Hfl). exists fl. split; [exact E|]. exact Hfl.
- exists (Cont s). split; [reflexivity|]. split; [exact HC|]. split; [exact HP|]. split; [exact Hb|lia]. }
destruct HZ as (fl & -> & Hfl). cbn [bind].
destruct fl as [s1|s1].
- destruct Hfl as (C1 & P1 & B1 & L1).
destruct (rcount_total s1 C1 P1 B1) as (fl2 & -> & Hfl2). exists fl2. split; [reflexivity|].
destruct fl2 as [s2|s2]; [destruct Hfl2 as (X1 & X2 & X3 & X4); split; [exact X1|]; split; [exact X2|]; split; [exact X3|lia]|].
destruct Hfl2 as (X1 & X2 & X3). split; [exact X1|]. intros E1. split; [exact X2|]. intros; apply X3; auto.
- destruct Hfl as (B1 & B2 & B3). eexists. split; [reflexivity|]. split; [exact B1|].
intros E1. exfalso. pose proof HC as (_ & _ & _ & _ & C5 & C6 & C7 & _).
assert (2 <= 2 ^ (r_nbBits s - 1)) by (change 2 with (2^1); apply Z.pow_le_mono_r; lia). lia.
Qed.
#[using="Hbytes H8 Hm1 Htl"] Lemma rloop_total f : forall s,
CTL s -> POS s -> r_bitCount s < 32 -> maxSV1 - r_charnum s < Z.of_nat f ->
exists s', rloop buf maxSV1 f s = Ok s' /\ BRK s' /\
(r_remaining s' = 1 -> r_charnum s' <= maxSV1 /\ (tl <= 14 -> pws (r_nc s') (r_charnum s') = 2^tl)).
Proof.
induction f as [|f IH]; intros s HC HP Hb Hf.
{ exfalso. pose proof HC as (_ & C2 & _). simpl in Hf. lia. }
cbn [rloop]. destruct (rbody_total s HC HP Hb) as (fl & -> & Hfl). cbn [bind].
destruct fl as [s1|s1].
- destruct Hfl as (C1 & P1 & B1 & L1). apply IH; auto. rewrite Nat2Z.inj_succ in Hf. lia.
- exists s1. split; [reflexivity|]. exact Hfl.
Qed.
End S.
Lemma read_ncount_body8_total buf maxSV1 nc0 :
all_bytes buf -> 8 <= Zlength buf -> 1 <= maxSV1 <= Zlength nc0 ->
(exists nc msv tlg n, read_ncount_body8 buf maxSV1 nc0 = Ok (nc, msv, tlg, n) /\
length nc = length nc0 /\ 0 <= msv /\ msv + 1 <= maxSV1 /\ 5 <= tlg <= 15 /\ 1 <= n <= Zlength buf /\
(forall i, msv < i < maxSV1 -> Znth i nc = 0) /\ (forall i, maxSV1 <= i -> Znth i nc = Znth i nc0) /\
(tlg <= 14 -> (forall i, 0 <= i <= msv -> -1 <= Znth i nc) /\ wsum (firstn (Z.to_nat (msv + 1)) nc) = 2^tlg))
\/ (exists e, read_ncount_body8 buf maxSV1 nc0 = Err e).
Proof.
intros HB H8 Hm1. unfold read_ncount_body8, assert.
replace (maxSV1 <=? Zlength nc0) with true by (symmetry; apply Z.leb_le; lia). cbn [bind].
rewrite (readLE32_val buf 0 HB) by lia. cbn [bind]. rewrite Z.mul_0_r, Z.pow_0_r, Z.div_1_r.
set (bs := bytes_val buf mod 2 ^ 32). pose proof (Z.mod_pos_bound (bytes_val buf) (2^32) ltac:(lia)) as Hbs. fold bs in Hbs.
unfold FSE_MIN_TABLELOG, FSE_TABLELOG_ABSOLUTE_MAX.
set (tlg := Z.land bs 15 + 5).
assert (Htlg0 : 5 <= tlg <= 20) by (subst tlg; change 15 with (2^4 - 1); rewrite land_ones_mod by lia; pose proof (Z.mod_pos_bound bs (2^4) ltac:(lia)); lia).
destruct (Z.ltb_spec 15 tlg) as [Hbig|Hok].
{ right. eexists. reflexivity. }
rewrite shr32_ok by lia. cbn [bind].
replace ((0 <=? tlg) && (tlg <? 31)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia). cbn [bind].
assert (Htlg : 5 <= tlg <= 15) by lia.
match goal with |- context [rloop _ _ _ ?st] => set (s0 := st) end.
assert (P2 : 2 ^ tlg < 2 ^ (tlg + 1)) by (apply Z.pow_lt_mono_r; lia).
assert (P5 : 32 <= 2 ^ tlg) by (change 32 with (2^5); apply Z.pow_le_mono_r; lia).
assert (HC0 : CTL maxSV1 nc0 tlg s0).
{ unfold CTL; subst s0; cbn [r_nc r_ip r_bitStream r_bitCount r_charnum r_remaining r_threshold r_nbBits r_previous0].
split; [apply zero_prefix_length|]. split; [lia|].
split. { intros i Hi. unfold Znth. rewrite zero_prefix_nth. replace (Z.to_nat i <? Z.to_nat maxSV1)%nat with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity. }
split. { intros i Hi. unfold Znth. rewrite zero_prefix_nth. replace (Z.to_nat i <? Z.to_nat maxSV1)%nat with false by (symmetry; apply Nat.ltb_ge; lia). reflexivity. }
split. { f_equal. lia. } split; [lia|]. rewrite Z.pow_add_r, Z.pow_1_r in P2 by lia. split; [lia|]. split; [lia|].
intros _. split; [intros; lia|]. unfold pws. cbn. lia. }
assert (HP0 : POS buf s0).
{ unfold POS; subst s0; cbn [r_nc r_ip r_bitStream r_bitCount r_charnum r_remaining r_threshold r_nbBits r_previous0].
assert (0 <= bs / 2^4 < 2^32) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]). repeat split; lia. }
destruct (rloop_total buf HB H8 maxSV1 nc0 Hm1 tlg Htlg (S (Z.to_nat maxSV1)) s0 HC0 HP0 ltac:(subst s0; cbn; lia)
ltac:(subst s0; cbn [r_charnum]; rewrite Nat2Z.inj_succ, Z2Nat.id by lia; lia)) as (s' & -> & HBR & HFIN). cbn [bind].
destruct (Z.eqb_spec (r_remaining s') 1) as [E1|N1]; cbn [negb]; [| right; eexists; reflexivity].
destruct (HFIN E1) as [Hcn Hsum].
destruct (Z.ltb_spec maxSV1 (r_charnum s')); [lia|].
destruct (Z.ltb_spec 32 (r_bitCount s')); [right; eexists; reflexivity|].
left. do 4 eexists. split; [reflexivity|].
destruct HBR as (B1 & B2 & B3 & B4 & B5 & B6 & B7). destruct (B7 Hcn) as (Z1 & Z2 & Z3).
rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
pose proof (Z.div_mod (r_bitCount s' + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (r_bitCount s' + 7) 8 ltac:(lia)).
split; [exact B1|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
split; [intros; apply Z1; lia|]. split; [exact Z2|].
intros H14. destruct (Z3 H14) as [G1 G2]. split; [intros; apply G1; lia|].
replace (r_charnum s' - 1 + 1) with (r_charnum s') by lia. exact (Hsum H14).
Qed.
