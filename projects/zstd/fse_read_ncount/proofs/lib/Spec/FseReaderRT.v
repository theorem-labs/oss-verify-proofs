(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount FseLemmas FseAbs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Lemma repeats_of_ok x : 0 <= x < 2^32 -> exists q, repeats_of x = Ok q /\ 0 <= q <= 16.
Proof.
intros Hx. unfold repeats_of, ctz32.
destruct (repeats_arg_mod x 0 Hx ltac:(lia)) as [_ Hrange].
set (a := Z.lor (not32 x) (2^31)) in *.
rewrite u32_id by lia. destruct (Z.eqb_spec a 0); [lia|]. cbn [bind].
eexists; split; [reflexivity|].
pose proof (ctz_aux_le 32 a). change (Z.of_nat 32) with 32 in H.
split. apply Z.div_pos; lia. apply Z.div_le_upper_bound; lia.
Qed.
Lemma bits_sub x p W v o w :
0 <= p -> 0 <= o -> 0 <= w -> o + w <= W -> bits x p W = v -> bits x (p + o) w = bits v o w.
Proof.
intros. subst v. unfold bits at 2 3.
rewrite mod_pow2_div_pow2 by lia. rewrite mod_pow2_mod_pow2 by lia.
rewrite div_pow2_div_pow2 by lia. reflexivity.
Qed.
Lemma ones_split a b : 0 <= a -> 0 <= b -> 2^(a+b) - 1 = (2^a - 1) + (2^b - 1) * 2^a.
Proof. intros. rewrite Z.pow_add_r by lia. nia. Qed.
Lemma bits_ones_lo a b w : 0 <= w <= a -> 0 <= b -> bits ((2^a - 1) + b * 2^a) 0 w = 2^w - 1.
Proof.
intros. unfold bits. rewrite Z.pow_0_r, Z.div_1_r.
rewrite mod_add_mul_pow2_le by lia.
replace a with (w + (a - w)) at 1 by lia. rewrite ones_split by lia.
rewrite mod_add_mul_pow2 by lia. apply Z.mod_small. pose proof (pow2_pos w). lia.
Qed.
Lemma bits_ones_hi a b p w : 0 <= p <= a -> 0 <= b -> 0 <= w ->
bits ((2^a - 1) + b * 2^a) p w = bits ((2^(a-p) - 1) + b * 2^(a-p)) 0 w.
Proof.
intros. unfold bits. rewrite Z.pow_0_r, Z.div_1_r. f_equal.
replace a with (p + (a - p)) at 1 2 by lia. rewrite ones_split by lia.
rewrite Z.pow_add_r by lia.
replace (2^p - 1 + (2^(a-p) - 1) * 2^p + b * (2^p * 2^(a-p)))
with ((2^p - 1) + ((2^(a-p) - 1) + b * 2^(a-p)) * 2^p) by lia.
rewrite div_add_mul_pow2 by lia. rewrite Z.div_small; [lia|]. pose proof (pow2_pos p). lia.
Qed.
Section R.
Variable nc : list Z.
Variable maxSV tableLog : Z.
Hypothesis V : valid_ncount nc maxSV tableLog.
Variable buf : list Z.
Hypothesis Hbytes : all_bytes buf.
Let hbSize := Zlength buf.
Hypothesis H8 : 8 <= hbSize.
Variable nc0 : list Z.
Variable maxSV1 : Z.
Hypothesis HmaxSV1 : maxSV + 1 <= maxSV1 <= Zlength nc0.
Let B := bytes_val buf.
Ltac cbnR := cbn [r_nc r_ip r_bitStream r_bitCount r_charnum r_remaining r_threshold r_nbBits r_previous0].
Ltac cbnR_all := cbn [r_nc r_ip r_bitStream r_bitCount r_charnum r_remaining r_threshold r_nbBits r_previous0] in *.
Definition rpos (s : rstate) (p : Z) : Prop :=
0 <= r_ip s /\ r_ip s + 4 <= hbSize /\ 0 <= r_bitCount s <= 32 /\
8 * r_ip s + r_bitCount s = p /\
(r_bitCount s <= 7 \/ r_ip s = hbSize - 4) /\
r_bitStream s = (B / 2^p) mod 2^(32 - r_bitCount s).
#[using="H8"] Lemma rpos_bits s p o w TF :
rpos s p -> 0 <= o -> 0 <= w -> o + w <= 25 -> p + o + w <= TF -> TF <= 8 * hbSize ->
bits (r_bitStream s) o w = bits B (p + o) w.
Proof.
intros (A1 & A2 & A3 & A4 & A5 & A6) Ho Hw How Hp HT.
rewrite A6. rewrite bits_mod; [|lia|lia|destruct A5; lia].
apply bits_shift; lia.
Qed.
#[using="H8"] Lemma rpos_bitStream_range s p : rpos s p -> 0 <= r_bitStream s < 2^32.
Proof.
intros (A1 & A2 & A3 & A4 & A5 & A6). rewrite A6.
pose proof (mod_pow2_range (B / 2^p) (32 - r_bitCount s) ltac:(lia)).
assert (2^(32 - r_bitCount s) <= 2^32) by (apply Z.pow_le_mono_r; lia). lia.
Qed.
#[using="Hbytes H8"] Lemma reload_ok s p TF :
0 <= r_ip s -> r_ip s + 4 <= hbSize -> 0 <= r_bitCount s ->
8 * r_ip s + r_bitCount s = p -> p < TF -> TF <= 8 * hbSize ->
(r_ip s <= hbSize - 7 -> r_bitCount s <= 31) ->
exists s', reload buf s = Ok s' /\ rpos s' p /\
r_nc s' = r_nc s /\ r_charnum s' = r_charnum s /\ r_remaining s' = r_remaining s /\
r_threshold s' = r_threshold s /\ r_nbBits s' = r_nbBits s /\ r_previous0 s' = r_previous0 s.
Proof.
intros Hip Hip4 Hbc Hp HpT HT H31. unfold reload. fold hbSize.
rewrite shiftr_3, land_7, land_31.
pose proof (Z.div_mod (r_bitCount s) 8 ltac:(lia)) as DM.
pose proof (Z.mod_pos_bound (r_bitCount s) 8 ltac:(lia)) as MB.
assert (0 <= r_bitCount s / 8) by (apply Z.div_pos; lia).
match goal with |- context [if ?c then _ else _] => destruct c eqn:HC end.
-
assert (Hip' : r_ip s + r_bitCount s / 8 + 4 <= hbSize).
{ apply Bool.orb_true_iff in HC. destruct HC as [HC|HC].
- apply Z.leb_le in HC. specialize (H31 HC).
assert (r_bitCount s / 8 < 4) by (apply Z.div_lt_upper_bound; lia). lia.
- apply Z.leb_le in HC. lia. }
rewrite readLE32_val by (auto; lia). cbn [bind].
rewrite shr32_ok by lia. cbn [bind].
eexists. split; [reflexivity|]. unfold rpos; cbnR. repeat split; try lia.
rewrite mod_pow2_div_pow2 by lia. rewrite div_pow2_div_pow2 by lia.
f_equal. f_equal. f_equal. lia.
-
apply Bool.orb_false_iff in HC. destruct HC as [HC1 HC2].
apply Z.leb_gt in HC1. apply Z.leb_gt in HC2.
set (v := r_bitCount s - 8 * (hbSize - 4 - r_ip s)).
assert (Hv : 0 <= v < 32) by (subst v; lia).
rewrite (Z.mod_small v 32) by lia.
rewrite readLE32_val by (auto; lia). cbn [bind].
rewrite shr32_ok by lia. cbn [bind].
eexists. split; [reflexivity|]. unfold rpos; cbnR. repeat split; try lia.
rewrite mod_pow2_div_pow2 by lia. rewrite div_pow2_div_pow2 by lia.
f_equal. f_equal. f_equal. lia.
Qed.
Definition same_rctl (s s' : rstate) : Prop :=
r_nc s' = r_nc s /\ r_remaining s' = r_remaining s /\ r_threshold s' = r_threshold s /\
r_nbBits s' = r_nbBits s /\ r_previous0 s' = r_previous0 s.
#[using="Hbytes H8"] Lemma rep_loop_ok f : forall s p m r TF repeats,
rpos s p -> TF <= 8 * hbSize ->
0 <= m -> 0 <= r <= 2 ->
bits B p (2*m + 2) = (2^(2*m) - 1) + r * 2^(2*m) ->
p + 2*m + 2 + 1 <= TF ->
repeats_of (r_bitStream s) = Ok repeats ->
m / 12 < Z.of_nat f ->
exists s', rep_loop buf f s repeats = Ok (s', m mod 12) /\
rpos s' (p + 24 * (m / 12)) /\ r_charnum s' = r_charnum s + 36 * (m / 12) /\
same_rctl s s'.
Proof.
induction f; intros s p m r TF repeats RP HT Hm Hr Hbits HpT Hrep Hf.
{ exfalso. simpl in Hf. assert (0 <= m / 12) by (apply Z.div_pos; lia). lia. }
pose proof RP as (A1 & A2 & A3 & A4 & A5 & A6).
pose proof (rpos_bitStream_range s p RP) as BSR.
assert (P2m : 0 < 2^(2*m)) by (apply pow2_pos; lia).
cbn [rep_loop]. fold hbSize.
destruct (Z_lt_le_dec m 12).
-
assert (Hbs : bits (r_bitStream s) 0 (2*m+2) = (2^(2*m) - 1) + r * 2^(2*m)).
{ rewrite (rpos_bits s p 0 (2*m+2) TF RP) by lia. rewrite Z.add_0_r. exact Hbits. }
unfold bits in Hbs. rewrite Z.pow_0_r, Z.div_1_r in Hbs.
rewrite (repeats_of_exact (r_bitStream s) m r BSR ltac:(lia) ltac:(lia) Hbs) in Hrep.
injection Hrep as <-.
destruct (Z.leb_spec 12 m); [lia|].
exists s. rewrite (Z.mod_small m 12), (Z.div_small m 12) by lia.
rewrite Z.mul_0_r, !Z.add_0_r. split; [reflexivity|]. split; [exact RP|]. split; [reflexivity|].
repeat split.
-
assert (Hbs : bits (r_bitStream s) 0 24 = 2^24 - 1).
{ rewrite (rpos_bits s p 0 24 TF RP) by lia. rewrite Z.add_0_r.
rewrite <- (Z.add_0_r p). rewrite (bits_sub B p (2*m+2) _ 0 24) by (try exact Hbits; lia).
apply bits_ones_lo; lia. }
unfold bits in Hbs. rewrite Z.pow_0_r, Z.div_1_r in Hbs.
destruct (repeats_of_ge12 (r_bitStream s) BSR Hbs) as (q & Eq & Hq).
rewrite Eq in Hrep. injection Hrep as <-.
destruct (Z.leb_spec 12 q); [|lia].
match goal with |- context [let '(ip', bc') := ?e in _] => set (ipbc := e) end.
assert (Hipbc : exists ip' bc', ipbc = (ip', bc') /\ 0 <= ip' /\ ip' + 4 <= hbSize /\ 0 <= bc' < 32 /\
8 * ip' + bc' = p + 24 /\ (bc' <= 7 \/ ip' = hbSize - 4)).
{ subst ipbc. destruct (Z.leb_spec (r_ip s) (hbSize - 7)).
- eexists _, _. split; [reflexivity|]. lia.
- rewrite land_31. set (v := r_bitCount s - 8 * (hbSize - 7 - r_ip s)).
assert (0 <= v < 32) by (subst v; lia).
rewrite (Z.mod_small v 32) by lia.
eexists _, _. split; [reflexivity|]. subst v. lia. }
destruct Hipbc as (ip' & bc' & -> & Q1 & Q2 & Q3 & Q4 & Q5).
rewrite readLE32_val by (auto; lia). cbn [bind].
rewrite shr32_ok by lia. cbn [bind]. fold B.
set (bs' := (B / 2^(8*ip')) mod 2^32 / 2^bc').
assert (Hbs' : bs' = (B / 2^(p+24)) mod 2^(32 - bc')).
{ subst bs'. rewrite mod_pow2_div_pow2 by lia. rewrite div_pow2_div_pow2 by lia. f_equal. f_equal. f_equal. lia. }
assert (BSR' : 0 <= bs' < 2^32).
{ rewrite Hbs'. pose proof (mod_pow2_range (B / 2^(p+24)) (32 - bc') ltac:(lia)).
assert (2^(32-bc') <= 2^32) by (apply Z.pow_le_mono_r; lia). lia. }
destruct (repeats_of_ok bs' BSR') as (rep' & Erep' & _).
rewrite Erep'. cbn [bind].
match goal with |- context [rep_loop _ _ ?st _] => set (s1 := st) end.
assert (RP1 : rpos s1 (p + 24)).
{ unfold rpos; subst s1; cbnR. repeat split; try lia. }
destruct (IHf s1 (p + 24) (m - 12) r TF rep' RP1 HT) as (s' & E' & RP' & CH' & SC'); try lia.
+ rewrite (bits_sub B p (2*m+2) _ 24 (2*(m-12)+2)) by (try exact Hbits; lia).
rewrite bits_ones_hi by lia.
replace (2*m - 24) with (2*(m-12)) by lia. apply bits_0_w; [lia|].
assert (0 < 2^(2*(m-12))) by (apply pow2_pos; lia).
replace (2*(m-12)+2) with (2*(m-12) + 2) by lia. rewrite Z.pow_add_r by lia. change (2^2) with 4. nia.
+ subst s1; cbnR. exact Erep'.
+ replace (m - 12) with (m + (-1) * 12) by lia. rewrite Z.div_add by lia. lia.
+ exists s'. rewrite E'.
replace ((m - 12) mod 12) with (m mod 12).
2:{ replace (m - 12) with (m + (-1) * 12) by lia. rewrite Z.mod_add by lia. reflexivity. }
split; [reflexivity|].
replace ((m - 12) / 12) with (m / 12 - 1) in RP', CH'.
2:{ replace (m - 12) with (m + (-1) * 12) by lia. rewrite Z.div_add by lia. lia. }
replace (p + 24 + 24 * (m / 12 - 1)) with (p + 24 * (m / 12)) in RP' by lia.
split; [exact RP'|]. subst s1; cbnR_all. split; [lia|].
unfold same_rctl in *; cbnR_all. exact SC'.
Qed.
Definition rncrel (l : list Z) (sym : Z) : Prop :=
length l = length nc0 /\
(forall i, 0 <= i < sym -> Znth i l = Znth i nc) /\
(forall i, sym <= i < maxSV1 -> Znth i l = 0) /\
(forall i, maxSV1 <= i -> Znth i l = Znth i nc0).
Definition rrel (s : rstate) (a : astate) : Prop :=
r_charnum s = a_sym a /\ r_remaining s = a_rem a /\ r_threshold s = a_thr a /\
r_nbBits s = a_nb a /\ r_previous0 s = a_p0 a /\ rpos s (a_T a) /\ rncrel (r_nc s) (a_sym a).
#[using="V Hbytes H8 HmaxSV1"] Lemma rzero_block_ok s a TF :
ainv nc maxSV tableLog a -> a_sym a <= maxSV -> a_p0 a = true -> rrel s a ->
TF <= 8 * hbSize ->
let '(j, N1, T1) := askip nc maxSV a in
bits B (a_T a) (T1 - a_T a) = runval (j - a_sym a) ->
T1 + 1 <= TF ->
exists s', rzero_block buf maxSV1 s = Ok (Cont s') /\ r_charnum s' = j /\ rpos s' T1 /\
same_rctl s s'.
Proof.
intros I Hs P0 R HT.
pose proof (askip_spec nc maxSV tableLog V a I Hs) as SK.
destruct (askip nc maxSV a) as [[j N1] T1] eqn:ESK.
destruct SK as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & _).
destruct (S7 P0) as (J1 & J2 & J3 & J4 & J5). clear S7.
intros Hbits HT1.
destruct R as (R1 & R2 & R3 & R4 & R5 & RP & RN).
destruct I as (A & B' & C & D & E & F & G). pose proof (V_msv _ _ _ V).
set (k := j - a_sym a) in *.
set (m := k / 3). set (r := k mod 3).
assert (Hm : 0 <= m <= 85). { subst m. split. apply Z.div_pos; lia. apply Z.div_le_upper_bound; lia. }
assert (Hr : 0 <= r < 3) by (subst r; apply Z.mod_pos_bound; lia).
assert (Hk : k = 3 * m + r) by (subst m r; rewrite (Z.div_mod k 3) at 1 by lia; lia).
assert (HT1e : T1 = a_T a + 2 * m + 2) by (rewrite J3; unfold runw; fold m; lia).
rewrite HT1e in Hbits. replace (a_T a + 2*m + 2 - a_T a) with (2*m+2) in Hbits by lia.
unfold runval in Hbits. fold m r in Hbits.
pose proof RP as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
pose proof (rpos_bitStream_range s _ RP) as BSR.
unfold rzero_block. fold hbSize.
destruct (repeats_of_ok (r_bitStream s) BSR) as (rep & Erep & _). rewrite Erep. cbn [bind].
assert (Hf : m / 12 < Z.of_nat (S (Z.to_nat hbSize))).
{ assert (m / 12 < 8) by (apply Z.div_lt_upper_bound; lia). lia. }
destruct (rep_loop_ok (S (Z.to_nat hbSize)) s (a_T a) m r TF rep RP HT ltac:(lia) ltac:(lia) Hbits ltac:(lia) Erep Hf)
as (s1 & E1 & RP1 & CH1 & SC1).
rewrite E1. cbn [bind].
set (m' := m mod 12) in *.
assert (Hm' : 0 <= m' < 12) by (subst m'; apply Z.mod_pos_bound; lia).
assert (Hmd : m = 12 * (m / 12) + m') by (subst m'; apply Z.div_mod; lia).
rewrite shr32_ok by lia. cbn [bind]. rewrite land_3.
pose proof RP1 as (P1 & P2 & P3 & P4 & P5 & P6).
assert (Hfin : (r_bitStream s1 / 2^(2*m')) mod 4 = r).
{ change 4 with (2^2). fold (bits (r_bitStream s1) (2*m') 2).
rewrite (rpos_bits s1 _ (2*m') 2 TF RP1) by lia.
replace (a_T a + 24 * (m / 12) + 2 * m') with (a_T a + 2 * m) by lia.
rewrite (bits_sub B (a_T a) (2*m+2) _ (2*m) 2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hbits).
rewrite bits_append_hi by (try lia; pose proof (pow2_pos (2*m)); lia).
rewrite Z.sub_diag. apply bits_0_w; [lia|]. change (2^2) with 4. lia. }
rewrite Hfin.
destruct (Z.leb_spec maxSV1 (r_charnum s1 + 3 * m' + r)); [lia|].
match goal with |- context [reload _ ?st] => set (s2 := st) end.
destruct (reload_ok s2 T1 TF) as (s3 & E3 & RP3 & N3 & C3 & RE3 & TH3 & NB3 & PZ3);
try (subst s2; cbnR; lia).
rewrite E3. exists s3. split; [reflexivity|].
subst s2; cbnR_all. split; [lia|]. split; [exact RP3|].
unfold same_rctl in *; cbnR_all. intuition congruence.
Qed.
#[using="buf hbSize B"] Lemma rncrel_skip l sym j :
rncrel l sym -> 0 <= sym <= j -> j < maxSV1 -> (forall i, sym <= i < j -> Znth i nc = 0) -> rncrel l j.
Proof.
intros (L1 & L2 & L3 & L4) Hj Hj1 Hz. unfold rncrel. repeat split; auto.
- intros i Hi. destruct (Z_lt_le_dec i sym). apply L2; lia. rewrite Hz by lia. apply L3; lia.
- intros i Hi. apply L3; lia.
Qed.
#[using="maxSV buf hbSize HmaxSV1 B"] Lemma rncrel_store l j c :
rncrel l j -> 0 <= j < maxSV1 -> c = Znth j nc -> rncrel (Zupd j c l) (j + 1).
Proof.
intros (L1 & L2 & L3 & L4) Hj Hc. unfold rncrel. unfold Zlength in HmaxSV1.
rewrite Zupd_length. repeat split; auto.
- intros i Hi. destruct (Z.eq_dec i j).
+ subst i. rewrite Znth_Zupd_same; auto. unfold Zlength. rewrite L1. lia.
+ rewrite Znth_Zupd_other by lia. apply L2. lia.
- intros i Hi. rewrite Znth_Zupd_other by lia. apply L3. lia.
- intros i Hi. rewrite Znth_Zupd_other by lia. apply L4. lia.
Qed.
Definition rfin (s : rstate) (T : Z) : Prop :=
r_remaining s = 1 /\ r_charnum s = maxSV + 1 /\ 0 <= r_ip s /\ 0 <= r_bitCount s <= 32 /\
8 * r_ip s + r_bitCount s = T /\ rncrel (r_nc s) (maxSV + 1).
#[using="buf hbSize B"] Lemma to_short_small c : -32768 <= c <= 32767 -> to_short c = c.
Proof.
intros. unfold to_short. change (2^15) with 32768. change (2^16) with 65536.
destruct (Z_lt_le_dec c 0).
- rewrite (Z.mod_small) by lia. lia.
- rewrite Z.mod_small by lia. lia.
Qed.
#[using="V Hbytes H8 HmaxSV1"] Lemma rcount_block_ok s1 a TF :
ainv nc maxSV tableLog a -> a_sym a <= maxSV ->
let '(j, N1, T1) := askip nc maxSV a in
let a' := astep nc maxSV a in
r_charnum s1 = j -> rpos s1 T1 -> r_remaining s1 = a_rem a -> r_threshold s1 = a_thr a ->
r_nbBits s1 = a_nb a -> rncrel (r_nc s1) j ->
TF <= 8 * hbSize -> a_T a' <= TF ->
bits B T1 (a_T a' - T1) = cval (Znth j nc) (a_rem a) (a_thr a) ->
(j < maxSV -> a_T a' < TF ->
exists s2, rcount_block buf maxSV1 s1 = Ok (Cont s2) /\ rrel s2 a')
/\
(j = maxSV ->
exists s2, rcount_block buf maxSV1 s1 = Ok (Brk s2) /\ rfin s2 (a_T a')).
Proof.
intros I Hs.
pose proof (askip_spec nc maxSV tableLog V a I Hs) as SK.
unfold astep.
destruct (askip nc maxSV a) as [[j N1] T1] eqn:ESK.
destruct SK as (S1 & S2 & S3 & S4 & S5 & S6 & _ & _).
pose proof (acount_pre nc maxSV tableLog V a j I ltac:(lia) S2) as CP. cbv zeta in CP.
destruct CP as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13).
pose proof (count_code_ok (Znth j nc) (a_rem a) (a_thr a) (a_nb a) C9 C10 C11 C4 C1 C3) as CC.
cbv zeta in CC. destruct CC as (K1 & K2 & K3 & K4 & K5 & K6).
set (c := Znth j nc) in *.
set (v := cval c (a_rem a) (a_thr a)) in *.
set (w := cwidth c (a_rem a) (a_thr a) (a_nb a)) in *.
pose proof (norm_spec (a_rem a - Z.abs c) (a_thr a) (a_nb a) C6 C9 C10 ltac:(lia)) as NS.
destruct (norm (a_rem a - Z.abs c) (a_thr a) (a_nb a)) as [t' nb'] eqn:EN.
destruct NS as (N1' & N2' & N3').
cbn [a_sym a_rem a_thr a_nb a_p0 a_N a_T].
intros CH RP RE TH NB RN HT HTa Hbits.
replace (T1 + w - T1) with w in Hbits by lia.
destruct I as (A & B' & C & D & E & F & G).
pose proof (V_msv _ _ _ V). pose proof (V_tl _ _ _ V). unfold Zlength in HmaxSV1.
pose proof RP as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
pose proof (rpos_bitStream_range s1 _ RP) as BSR.
pose proof RN as (L1 & L2 & L3 & L4).
assert (Hw13 : w <= 13) by lia.
assert (Hx : r_bitStream s1 mod 2^w = v).
{ rewrite <- Hbits. rewrite <- (Z.add_0_r T1). rewrite <- (rpos_bits s1 T1 0 w TF RP) by lia.
unfold bits. rewrite Z.pow_0_r, Z.div_1_r. reflexivity. }
specialize (K6 (r_bitStream s1) ltac:(lia) Hx).
assert (Htnb : 2 * a_thr a = 2^(a_nb a)).
{ rewrite C10. replace (a_nb a) with ((a_nb a - 1) + 1) at 2 by lia. rewrite pow2_S by lia. reflexivity. }
assert (HL1 : Z.land (r_bitStream s1) (a_thr a - 1) = r_bitStream s1 mod a_thr a).
{ rewrite C10 at 1. rewrite land_ones_mod by lia. rewrite <- C10. reflexivity. }
assert (HL2 : Z.land (r_bitStream s1) (2 * a_thr a - 1) = r_bitStream s1 mod 2^(a_nb a)).
{ rewrite Htnb. apply land_ones_mod. lia. }
assert (Hthr : a_thr a <= 4096) by (rewrite C10; change 4096 with (2^12); apply Z.pow_le_mono_r; lia).
assert (HU : u32 (2 * a_thr a - 1 - a_rem a) = cmax (a_rem a) (a_thr a)).
{ pose proof K1 as K1'. unfold cmax in K1' |- *. apply u32_id. change (2^32) with 4294967296; lia. }
unfold rcount_block. rewrite CH, RE, TH, NB. rewrite !HL1, !HL2, !HU.
fold (cmax (a_rem a) (a_thr a)).
match goal with |- context [let '(count0, bc) := ?e in _] =>
replace e with (c + 1, r_bitCount s1 + w) end.
2:{ destruct (Z.ltb_spec (r_bitStream s1 mod a_thr a) (cmax (a_rem a) (a_thr a))).
- injection K6 as E1 E2. rewrite E1, <- E2. reflexivity.
- injection K6 as E1 E2. rewrite E1, <- E2. reflexivity. }
replace (c + 1 - 1) with c by lia.
replace (if 0 <=? c then a_rem a - c else a_rem a + c) with (a_rem a - Z.abs c) by (destruct (Z.leb_spec 0 c); lia).
rewrite zstore_ok by (unfold Zlength; rewrite L1; lia). cbn [bind].
rewrite to_short_small by (assert (2^tableLog <= 2^12) by (apply Z.pow_le_mono_r; lia); change (2^12) with 4096 in *; lia).
assert (Hp0 : (c =? 0) = (v =? 1)).
{ destruct (Z.eqb_spec c 0), (Z.eqb_spec v 1); auto; exfalso; tauto. }
rewrite Hp0.
pose proof (rncrel_store (r_nc s1) j c RN ltac:(lia) eq_refl) as RN'.
split.
-
intros Hj HTlt. specialize (C7 Hj).
match goal with |- context [bind ?u _] =>
replace u with (Ok (Some (t', nb')) : res (option (Z * Z))) end.
2:{ unfold norm in EN. destruct (Z.ltb_spec (a_rem a - Z.abs c) (a_thr a)).
- destruct (Z.leb_spec (a_rem a - Z.abs c) 1); [lia|].
unfold highbit32. destruct (Z.ltb_spec 0 (a_rem a - Z.abs c)); [|lia].
assert (a_rem a - Z.abs c < 2^32).
{ assert (2^(a_nb a - 1) <= 2^12) by (apply Z.pow_le_mono_r; lia). change (2^32) with 4294967296. change (2^12) with 4096 in *. lia. }
destruct (Z.ltb_spec (a_rem a - Z.abs c) (2^32)); [|lia]. cbn [andb bind].
pose proof (Z.log2_nonneg (a_rem a - Z.abs c)).
assert (Z.log2 (a_rem a - Z.abs c) < a_nb a - 1).
{ apply Z.log2_lt_pow2; [lia|]. rewrite <- C10. lia. }
unfold assert. destruct (Z.leb_spec 0 (Z.log2 (a_rem a - Z.abs c) + 1 - 1)); [|lia].
destruct (Z.ltb_spec (Z.log2 (a_rem a - Z.abs c) + 1 - 1) 31); [|lia]. cbn [andb bind].
injection EN as <- <-. f_equal. f_equal. f_equal. f_equal. lia.
- congruence. }
cbn [bind]. destruct (Z.leb_spec maxSV1 (j + 1)); [lia|].
match goal with |- context [reload _ ?st] => set (s1' := st) end.
destruct (reload_ok s1' (T1 + w) TF) as (s2 & E2 & RP2 & N2 & CH2 & RE2 & TH2 & NB2 & PZ2);
try (subst s1'; cbnR; lia).
rewrite E2. exists s2. split; [reflexivity|].
subst s1'; cbnR_all. unfold rrel; cbn [a_sym a_rem a_thr a_nb a_p0 a_T].
split; [congruence|]. split; [congruence|]. split; [congruence|]. split; [congruence|].
split; [congruence|]. split; [exact RP2|]. rewrite N2. exact RN'.
-
intros Hj. assert (HR1 : a_rem a - Z.abs c = 1) by (apply C8; auto).
rewrite HR1. destruct (Z.ltb_spec 1 (a_thr a)); [|lia]. cbn [Z.leb bind].
eexists. split; [reflexivity|]. unfold rfin; cbnR.
split; [reflexivity|]. split; [lia|]. split; [lia|]. split.
{ split; [lia|]. destruct Q5; [lia|].
lia. }
split; [lia|]. rewrite <- Hj. exact RN'.
Qed.
#[using="V Hbytes H8 HmaxSV1"] Lemma rbody_ok s a NF TF :
ainv nc maxSV tableLog a -> a_sym a <= maxSV -> rrel s a -> TF <= 8 * hbSize -> B mod 2^TF = NF ->
let a' := astep nc maxSV a in
a_T a' <= TF -> NF mod 2^(a_T a') = a_N a' ->
(a_sym a' <= maxSV -> a_T a' < TF -> exists s2, rbody buf maxSV1 s = Ok (Cont s2) /\ rrel s2 a') /\
(a_sym a' = maxSV + 1 -> exists s2, rbody buf maxSV1 s = Ok (Brk s2) /\ rfin s2 (a_T a')).
Proof.
intros I Hs R HT HB.
pose proof (askip_spec nc maxSV tableLog V a I Hs) as SK.
pose proof (rzero_block_ok s a TF I Hs) as ZB.
pose proof (rcount_block_ok) as CB.
pose proof (V_msv _ _ _ V).
assert (AS : let '(j, N1, T1) := askip nc maxSV a in
a_sym (astep nc maxSV a) = j + 1 /\
a_N (astep nc maxSV a) = N1 + cval (Znth j nc) (a_rem a) (a_thr a) * 2^T1 /\
a_T (astep nc maxSV a) = T1 + cwidth (Znth j nc) (a_rem a) (a_thr a) (a_nb a) /\
0 <= cval (Znth j nc) (a_rem a) (a_thr a) < 2^(cwidth (Znth j nc) (a_rem a) (a_thr a) (a_nb a)) /\
1 <= cwidth (Znth j nc) (a_rem a) (a_thr a) (a_nb a)).
{ unfold astep. destruct (askip nc maxSV a) as [[j N1] T1] eqn:ESK.
destruct SK as (S1 & S2 & _).
pose proof (acount_pre nc maxSV tableLog V a j I ltac:(lia) S2) as CP. cbv zeta in CP.
destruct CP as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13).
pose proof (count_code_ok (Znth j nc) (a_rem a) (a_thr a) (a_nb a) C9 C10 C11 C4 C1 C3) as CC.
cbv zeta in CC. destruct CC as (K1 & K2 & K3 & K4 & K5 & K6).
destruct (norm _ _ _) as [t' nb']. cbn [a_sym a_N a_T]. repeat split; lia. }
cbv zeta. intros HTa HN.
destruct (askip nc maxSV a) as [[j N1] T1] eqn:ESK.
destruct SK as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8).
destruct AS as (E1 & E2 & E3 & E4 & E5).
set (a' := astep nc maxSV a) in *.
set (c := Znth j nc) in *. set (v := cval c (a_rem a) (a_thr a)) in *.
set (w := cwidth c (a_rem a) (a_thr a) (a_nb a)) in *.
destruct I as (A & B' & C & D & E & F & G) eqn:EI. clear EI.
assert (HbN1 : forall p ww, 0 <= p -> 0 <= ww -> p + ww <= T1 -> bits B p ww = bits N1 p ww).
{ intros p ww Hp Hww Hpw. rewrite <- (bits_mod B TF) by lia. rewrite HB.
rewrite <- (bits_mod NF (a_T a')) by lia. rewrite HN, E2.
apply bits_append_lo; lia. }
assert (Hrun : a_p0 a = true -> bits B (a_T a) (T1 - a_T a) = runval (j - a_sym a)).
{ intros P0. destruct (S7 P0) as (J1 & J2 & J3 & J4 & J5).
pose proof (runval_range (j - a_sym a) ltac:(lia)). pose proof (runw_pos (j - a_sym a) ltac:(lia)).
rewrite HbN1 by lia. rewrite J2, J3. replace (a_T a + runw (j - a_sym a) - a_T a) with (runw (j - a_sym a)) by lia.
rewrite bits_append_hi by lia. rewrite Z.sub_diag. apply bits_0_w; lia. }
assert (Hcnt : bits B T1 (a_T a' - T1) = v).
{ rewrite E3. replace (T1 + w - T1) with w by lia.
rewrite <- (bits_mod B TF) by lia. rewrite HB.
rewrite <- (bits_mod NF (a_T a')) by lia. rewrite HN, E2.
rewrite bits_append_hi by lia. rewrite Z.sub_diag. apply bits_0_w; lia. }
pose proof R as (R1 & R2 & R3 & R4 & R5 & RP & RN).
assert (exists s1, (if r_previous0 s then rzero_block buf maxSV1 s else Ok (Cont s)) = Ok (Cont s1)
/\ r_charnum s1 = j /\ rpos s1 T1 /\ same_rctl s s1)
as (s1 & Es1 & CH1 & RP1 & SC1).
{ rewrite R5. destruct (a_p0 a) eqn:P0.
- destruct (ZB eq_refl R HT (Hrun eq_refl) ltac:(lia)) as (s1 & Es1 & CH1 & RP1 & SC1).
exists s1. auto.
- destruct (S8 eq_refl) as (-> & _ & ->). exists s. split; [reflexivity|]. split; [auto|]. split; [exact RP|].
repeat split. }
unfold rbody. rewrite Es1. cbn [bind].
destruct SC1 as (N1' & RE1 & TH1 & NB1 & PZ1).
assert (RN1 : rncrel (r_nc s1) j).
{ rewrite N1'. apply (rncrel_skip _ (a_sym a)); auto; try lia.
destruct (a_p0 a) eqn:P0. apply (S7 eq_refl). destruct (S8 eq_refl) as (-> & _). intros; lia. }
specialize (CB s1 a TF ltac:(repeat split; auto; lia) Hs). rewrite ESK in CB. cbv zeta in CB.
fold a' in CB.
destruct (CB CH1 RP1 ltac:(congruence) ltac:(congruence) ltac:(congruence) RN1 HT HTa Hcnt) as [CBc CBb].
split.
- intros Hs' HTlt. apply CBc; lia.
- intros Hs'. apply CBb; lia.
Qed.
#[using="V Hbytes H8 HmaxSV1"] Lemma rloop_ok f : forall s a,
ainv nc maxSV tableLog a -> a_sym a <= maxSV -> rrel s a ->
let AF := arun nc maxSV f (astep nc maxSV a) in
acond maxSV AF = false ->
a_T AF <= 8 * hbSize -> B mod 2^(a_T AF) = a_N AF ->
exists sF, rloop buf maxSV1 (S f) s = Ok sF /\ rfin sF (a_T AF).
Proof.
induction f; intros s a I Hs R; cbv zeta; intros DONE HT HB.
- cbn [arun] in *. cbn [rloop].
pose proof (astep_ainv nc maxSV tableLog V a I Hs) as (I' & Q1 & Q2 & Q3).
pose proof (acond_false nc maxSV tableLog V _ I' DONE) as [SY _].
destruct (rbody_ok s a (a_N (astep nc maxSV a)) (a_T (astep nc maxSV a)) I Hs R HT HB) as [_ RB].
{ lia. } { apply Z.mod_small. destruct I' as (_ & _ & _ & _ & _ & F' & _). lia. }
destruct (RB SY) as (s2 & E2 & RF). rewrite E2. cbn [bind]. exists s2. auto.
- cbn [rloop].
pose proof (astep_ainv nc maxSV tableLog V a I Hs) as (I' & Q1 & Q2 & Q3).
set (a' := astep nc maxSV a) in *.
pose proof (arun_prefix nc maxSV tableLog V (S f) a' I') as (P1 & P2 & P3).
destruct (rbody_ok s a _ _ I Hs R HT HB) as [RC RB]. { fold a'. lia. } { exact P2. }
fold a' in RC, RB. cbn [arun] in *.
destruct (acond maxSV a') eqn:C'.
+
pose proof (proj1 (acond_true nc maxSV tableLog V a' I') C') as Hs'.
pose proof (astep_ainv nc maxSV tableLog V a' I' Hs') as (I'' & _ & Q2' & _).
pose proof (arun_prefix nc maxSV tableLog V f (astep nc maxSV a') I'') as (P1' & _).
destruct (RC Hs' ltac:(lia)) as (s2 & E2 & R2).
rewrite E2. cbn [bind]. apply (IHf s2 a' I' Hs' R2 DONE HT HB).
+
pose proof (acond_false nc maxSV tableLog V _ I' C') as [SY _].
destruct (RB SY) as (s2 & E2 & RF). rewrite E2. cbn [bind]. exists s2. auto.
Qed.
#[using="Type"] Lemma zero_prefix_length n l : length (zero_prefix n l) = length l.
Proof. revert l; induction n; intros [|x l]; simpl; auto. Qed.
#[using="Type"] Lemma zero_prefix_nth n l i : nth i (zero_prefix n l) 0 = if (i <? n)%nat then 0 else nth i l 0.
Proof.
revert l i; induction n; intros [|x l] [|i]; simpl; auto.
destruct (S i <? S n)%nat; reflexivity.
Qed.
#[using="V Hbytes H8 HmaxSV1"] Theorem read_body8_ok :
let TF := a_T (afinal nc maxSV tableLog) in
let NF := a_N (afinal nc maxSV tableLog) in
TF <= 8 * hbSize -> B mod 2^TF = NF ->
exists ncF, read_ncount_body8 buf maxSV1 nc0 = Ok (ncF, maxSV, tableLog, (TF + 7) / 8) /\
rncrel ncF (maxSV + 1).
Proof.
cbv zeta. intros HT HB.
pose proof (V_msv _ _ _ V). pose proof (V_tl _ _ _ V). unfold Zlength in HmaxSV1.
pose proof (afinal_spec nc maxSV tableLog V) as (IF & SYF & REMF & CF & TBF & NBF).
pose proof (ainv_a0 nc maxSV tableLog V) as I0.
pose proof (arun_prefix nc maxSV tableLog V (S (Z.to_nat (maxSV + 1))) (a0 tableLog) I0) as (P1 & P2 & P3).
fold (afinal nc maxSV tableLog) in P1, P2, P3. cbn [a0 a_T a_N] in P1, P2.
assert (HB4 : B mod 2^4 = tableLog - 5).
{ rewrite <- (mod_pow2_mod_pow2 B (a_T (afinal nc maxSV tableLog)) 4) by lia. rewrite HB. exact P2. }
unfold read_ncount_body8. fold hbSize.
unfold assert at 1. destruct (Z.leb_spec maxSV1 (Zlength nc0)); [|unfold Zlength in *; lia]. cbn [bind].
rewrite readLE32_val by (auto; lia). cbn [bind]. fold B.
rewrite Z.mul_0_r, Z.pow_0_r, Z.div_1_r.
rewrite land_15. change 16 with (2^4). rewrite mod_pow2_mod_pow2 by lia. rewrite HB4.
unfold FSE_MIN_TABLELOG, FSE_TABLELOG_ABSOLUTE_MAX. replace (tableLog - 5 + 5) with tableLog by lia.
destruct (Z.ltb_spec 15 tableLog); [lia|].
rewrite shr32_ok by lia. cbn [bind].
unfold assert. destruct (Z.leb_spec 0 tableLog); [|lia]. destruct (Z.ltb_spec tableLog 31); [|lia]. cbn [andb bind].
match goal with |- context [rloop _ _ _ ?st] => set (s0 := st) end.
assert (R0 : rrel s0 (a0 tableLog)).
{ unfold rrel, rpos, rncrel, a0; subst s0; cbnR; cbn [a_sym a_rem a_thr a_nb a_p0 a_T].
repeat split; try lia.
- rewrite mod_pow2_div_pow2 by lia. reflexivity.
- apply zero_prefix_length.
- intros i Hi. unfold Znth. rewrite zero_prefix_nth. destruct (Nat.ltb_spec (Z.to_nat i) (Z.to_nat maxSV1)); [auto|lia].
- intros i Hi. unfold Znth. rewrite zero_prefix_nth. destruct (Nat.ltb_spec (Z.to_nat i) (Z.to_nat maxSV1)); [lia|auto]. }
assert (C0 : acond maxSV (a0 tableLog) = true).
{ apply (acond_true nc maxSV tableLog V); auto. cbn [a0 a_sym]. lia. }
assert (EAF : arun nc maxSV (Z.to_nat maxSV1) (astep nc maxSV (a0 tableLog)) = afinal nc maxSV tableLog).
{ rewrite <- (arun_afinal nc maxSV tableLog V (S (Z.to_nat maxSV1))) by lia. cbn [arun]. rewrite C0. reflexivity. }
destruct (rloop_ok (Z.to_nat maxSV1) s0 (a0 tableLog) I0 ltac:(cbn [a0 a_sym]; lia) R0) as (sF & EF & RF);
rewrite ?EAF; auto.
rewrite EF. cbn [bind]. rewrite EAF in RF.
destruct RF as (F1 & F2 & F3 & F4 & F5 & F6).
rewrite F1, F2. cbn [Z.eqb Pos.eqb negb].
destruct (Z.ltb_spec maxSV1 (maxSV + 1)); [lia|].
destruct (Z.ltb_spec 32 (r_bitCount sF)); [lia|].
exists (r_nc sF). split; [|exact F6].
replace (maxSV + 1 - 1) with maxSV by lia.
rewrite shiftr_3. rewrite <- F5.
replace (8 * r_ip sF + r_bitCount sF + 7) with (r_ip sF * 8 + (r_bitCount sF + 7)) by lia.
rewrite Z.div_add_l by lia. reflexivity.
Qed.
End R.
Lemma all_bytes_app_zeros l n : all_bytes l -> all_bytes (l ++ repeat 0 n).
Proof.
intros H. apply Forall_all_bytes. apply Forall_app. split.
- apply all_bytes_Forall; auto.
- apply Forall_forall. intros x Hx. apply repeat_spec in Hx. lia.
Qed.
Lemma bytes_val_zeros n : bytes_val (repeat 0 n) = 0.
Proof. induction n; cbn [repeat bytes_val]; lia. Qed.
Theorem read_ncount_ok nc maxSV tableLog buf nc0 maxSVin :
valid_ncount nc maxSV tableLog ->
all_bytes buf -> maxSV <= maxSVin -> maxSVin + 1 <= Zlength nc0 ->
let TF := a_T (afinal nc maxSV tableLog) in
let NF := a_N (afinal nc maxSV tableLog) in
(TF + 7) / 8 <= Zlength buf -> bytes_val buf mod 2^TF = NF ->
exists ncF, read_ncount nc0 maxSVin buf = Ok (ncF, maxSV, tableLog, (TF + 7) / 8) /\
length ncF = length nc0 /\
(forall i, 0 <= i <= maxSV -> Znth i ncF = Znth i nc) /\
(forall i, maxSV < i <= maxSVin -> Znth i ncF = 0) /\
(forall i, maxSVin < i -> Znth i ncF = Znth i nc0).
Proof.
cbv zeta. intros V HB Hm Hlen Hsz Hmod.
pose proof (afinal_spec nc maxSV tableLog V) as (IF & SYF & REMF & CF & TBF & NBF).
set (TF := a_T (afinal nc maxSV tableLog)) in *.
assert (HTF : TF <= 8 * Zlength buf).
{ pose proof (Z.div_mod (TF + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (TF + 7) 8 ltac:(lia)). lia. }
unfold read_ncount.
destruct (Z.ltb_spec (Zlength buf) 8).
-
set (buffer := buf ++ repeat 0 (Z.to_nat (8 - Zlength buf))).
assert (HL : Zlength buffer = 8).
{ subst buffer. unfold Zlength in *. rewrite length_app, repeat_length. lia. }
assert (HBv : bytes_val buffer = bytes_val buf).
{ subst buffer. rewrite bytes_val_app, bytes_val_zeros. lia. }
destruct (read_body8_ok nc maxSV tableLog V buffer (all_bytes_app_zeros _ _ HB) ltac:(lia) nc0 (maxSVin + 1) ltac:(lia))
as (ncF & E & RN); [lia| rewrite HBv; exact Hmod |].
rewrite E. cbn [bind]. fold TF. destruct (Z.ltb_spec (Zlength buf) ((TF + 7) / 8)); [lia|].
exists ncF. split; [reflexivity|]. destruct RN as (L1 & L2 & L3 & L4).
repeat split; auto; intros; [apply L2 | apply L3 | apply L4]; lia.
- destruct (read_body8_ok nc maxSV tableLog V buf HB ltac:(lia) nc0 (maxSVin + 1) ltac:(lia))
as (ncF & E & RN); [lia| exact Hmod |].
rewrite E. fold TF. exists ncF. split; [reflexivity|]. destruct RN as (L1 & L2 & L3 & L4).
repeat split; auto; intros; [apply L2 | apply L3 | apply L4]; lia.
Qed.
