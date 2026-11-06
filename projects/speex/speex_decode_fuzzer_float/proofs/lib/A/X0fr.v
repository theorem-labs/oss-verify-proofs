(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cy X1cp X1cj X1dd X1cg X1cs X1da.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X0j1 X0gi X0hr X0j3 X0hi
X0hn X0j0 X0hh X0hb X0il X0gp X0h2 X0j4 X0hf X0fy X0fg X0da
X0g4 X0d8 X0fq.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X173 X18c X19m X183 X188 X19k X182 X17w X196 X17a X17n X19n X180 X16j X161 X13v X16p X13t X16b.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X173 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19m OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X183 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X188 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19k OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X182 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17w OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X196 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17a OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17n OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19n OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X180 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16j OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X161 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13v OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16p OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13t OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16b.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CompStk.
Variables (Σ : rtsA) (m : mem) (W : list ivl).
Hypothesis HA : ART_A Σ m.
#[local] Notation L := (lay Σ).
#[local] Notation SB := (l_SB (lay Σ)).

Hypothesis R_img : forall a n, 0x10000 <= a -> a + n <= SEGTOP_A -> disjoint_from CS_W a n -> disjoint_from W a n.
Hypothesis R_grant : forall b gn a n, In (b, gn) (startup_grants L) -> apart b gn (l_PRB L) 0x2000011000 -> apart b gn (l_FSB L) 0xb09000 ->
b <= a -> a + n <= b + gn -> disjoint_from W a n.
Hypothesis R_shad : forall lo hi a n, lo mod 8 = 0 -> hi mod 8 = 0 -> 0 <= lo -> hi <= 2 ^ 47 -> shad lo <= a -> a + n <= shad hi ->
(forall f k, In (f, k) (frames Σ) -> hi <= f \/ f + fs_size k <= lo) ->
(hi <= l_FSB L \/ l_FSB L + 0xb09000 <= lo) -> hi <= l_ACEIL L -> disjoint_from W a n.
Hypothesis R_prb : forall a n, l_PRB L <= a -> a + n <= l_PRB L + 0x2000011000 ->
(forall c i n', 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some (CkAlloc n') ->
a + n <= p_ubeg SB c i n' \/ p_ubeg SB c i n' + n' <= a) -> disjoint_from W a n.
Hypothesis R_secmap : forall k0 s0 a n, nth_error (sec Σ) k0 = Some s0 -> s_mb s0 <= a -> a + n <= s_mb s0 + smsz (s_n s0) ->
(s_quar s0 = false -> a + n <= s_ubeg s0 \/ s_ubeg s0 + s_n s0 <= a) -> disjoint_from W a n.

Lemma slot_geo : forall c i st, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some st ->
rb SB c <= p_abeg SB c i /\ p_abeg SB c i + ClassSize c <= rb SB c + r_muser (pr Σ c) /\ r_muser (pr Σ c) <= kUserCap
/\ 32 <= ClassSize c /\ ClassSize c mod 32 = 0.
Proof.
intros c i st Hc Hn. pose proof (geo_wf Σ m HA) as (_ & HR & _). destruct HR as (HR & _).
pose proof (HR c Hc) as (W1 & _ & W3 & _). pose proof (ClassSize_range c Hc) as (Hcs & Hm).
pose proof (proj1 (nth_error_Some (r_st (pr Σ c)) i) ltac:(rewrite Hn; discriminate)) as Hlt.
unfold p_abeg, rb in *.
assert (Hx : Z.of_nat i * ClassSize c + ClassSize c <= ClassSize c * Z.of_nat (length (r_st (pr Σ c)))).
{ replace (ClassSize c * Z.of_nat (length (r_st (pr Σ c)))) with (Z.of_nat (length (r_st (pr Σ c))) * ClassSize c) by ring.
replace (Z.of_nat i * ClassSize c + ClassSize c) with ((Z.of_nat i + 1) * ClassSize c) by ring.
apply Z.mul_le_mono_nonneg_r; lia. }
assert (0 <= Z.of_nat i * ClassSize c) by (apply Z.mul_nonneg_nonneg; lia). repeat split; lia.
Qed.

Lemma slot_apart : forall c i c' i' st st', 1 <= c <= 31 -> 1 <= c' <= 31 -> nth_error (r_st (pr Σ c)) i = Some st ->
nth_error (r_st (pr Σ c')) i' = Some st' -> (c <> c' \/ i <> i') ->
p_abeg SB c i + ClassSize c <= p_abeg SB c' i' \/ p_abeg SB c' i' + ClassSize c' <= p_abeg SB c i.
Proof.
intros c i c' i' st st' Hc Hc' Hn Hn' Hne.
pose proof (slot_geo c i st Hc Hn) as (A1 & A2 & A3 & _). pose proof (slot_geo c' i' st' Hc' Hn') as (B1 & B2 & B3 & _).
destruct (Z.eq_dec c c') as [<-|Hcc].
- destruct Hne as [Hne|Hne]; [lia|]. unfold p_abeg. pose proof (ClassSize_range c Hc) as (Hcs & _).
destruct (Nat.lt_ge_cases i i') as [Hl|Hl].
+ left. assert (Z.of_nat i * ClassSize c + ClassSize c <= Z.of_nat i' * ClassSize c).
{ replace (Z.of_nat i * ClassSize c + ClassSize c) with ((Z.of_nat i + 1) * ClassSize c) by ring. apply Z.mul_le_mono_nonneg_r; lia. }
lia.
+ right. assert (Z.of_nat i' * ClassSize c + ClassSize c <= Z.of_nat i * ClassSize c).
{ replace (Z.of_nat i' * ClassSize c + ClassSize c) with ((Z.of_nat i' + 1) * ClassSize c) by ring. apply Z.mul_le_mono_nonneg_r; lia. }
lia.
- unfold rb, kUserCap in *. lia.
Qed.

Lemma live_in_slot : forall c i n', 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some (CkAlloc n') ->
p_abeg SB c i + rz_size n' = p_ubeg SB c i n' /\ 16 <= rz_size n' /\ rz_size n' + n' <= ClassSize c /\ 0 <= n'.
Proof.
intros c i n' Hc Hn. pose proof (geo_wf Σ m HA) as (_ & HR & _). destruct HR as (HR & _).
pose proof (HR c Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & W10 & _).
pose proof (proj1 (Forall_forall _ _) W10 _ (nth_error_In _ _ Hn)) as (Hn0 & Hfit & _). cbv beta iota in Hn0, Hfit.
split; [reflexivity|]. split; [|lia].
unfold rz_size. pose proof (Z.pow_pos_nonneg 2 (rz_log n') ltac:(lia) ltac:(unfold rz_log; repeat destruct (_ <=? _); lia)). lia.
Qed.

Lemma ac_slot : forall c i st a n, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some st -> p_abeg SB c i <= a ->
a + n <= p_abeg SB c i + ClassSize c ->
(forall n', st = CkAlloc n' -> a + n <= p_ubeg SB c i n') -> disjoint_from W a n.
Proof.
intros c i st a n Hc Hn H1 H2 HU. pose proof (slot_geo c i st Hc Hn) as (S1 & S2 & S3 & _).
pose proof (geo_prb Σ m HA) as (P1 & P2 & P3).
apply R_prb; [unfold rb in *; lia | unfold rb, kUserCap in *; assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by lia; lia|].
intros c' i' n' Hc' Hn'. destruct (Z.eq_dec c c') as [<-|Hne]; [destruct (Nat.eq_dec i i') as [<-|Hne]|].
- rewrite Hn in Hn'. injection Hn' as ->. left. exact (HU n' eq_refl).
- destruct (slot_apart c i c i' st (CkAlloc n') Hc Hc' Hn Hn' (or_intror Hne)) as [X|X];
pose proof (live_in_slot c i' n' Hc' Hn') as (Y1 & Y2 & Y3 & _); lia.
- destruct (slot_apart c i c' i' st (CkAlloc n') Hc Hc' Hn Hn' (or_introl Hne)) as [X|X];
pose proof (live_in_slot c' i' n' Hc' Hn') as (Y1 & Y2 & Y3 & _); lia.
Qed.

Fixpoint dsjb (V : list ivl) (a n : Z) : bool :=
match V with [] => true | (lo, hi) :: V' => ((a + n <=? lo) || (hi <=? a)) && dsjb V' a n end.
Lemma dsjb_sound : forall V a n, dsjb V a n = true -> disjoint_from V a n.
Proof.
induction V as [|[lo hi] V IH]; intros a n H; [exact I|]. cbn [dsjb] in H. apply andb_prop in H as [H1 H2].
split; [|exact (IH _ _ H2)]. apply orb_prop in H1 as [X|X]; [left; apply Z.leb_le; exact X | right; apply Z.leb_le; exact X].
Qed.
Definition img_ok (r : Z * Z) : bool := ((0x10000 <=? fst r) && (fst r + snd r <=? SEGTOP_A) && dsjb CS_W (fst r) (snd r))%bool.
Lemma ac_lits : forall l, forallb img_ok l = true -> dsjl W l.
Proof.
intros l H. apply Forall_forall. intros [a n] Hin. pose proof (proj1 (forallb_forall _ _) H _ Hin) as X. unfold img_ok in X.
cbn [fst snd] in *. apply andb_prop in X as [X X3]. apply andb_prop in X as [X1 X2]. apply Z.leb_le in X1, X2.
exact (R_img a n X1 X2 (dsjb_sound _ _ _ X3)).
Qed.

Lemma ac_T : forall a n, l_T L <= a -> a + n <= l_T L + 4096 -> disjoint_from W a n.
Proof.
intros a n H1 H2. apply (R_grant (l_T L) 4096); [unfold startup_grants; right; right; left; reflexivity | | | exact H1 | exact H2].
- pose proof (geo_apart Σ m HA 0 2 _ _ ltac:(lia) eq_refl eq_refl) as X. cbn [fst snd] in X. unfold apart in *. lia.
- pose proof (geo_apart Σ m HA 2 5 _ _ ltac:(lia) eq_refl eq_refl) as X. cbn [fst snd] in X. exact X.
Qed.
Lemma ac_TCX : forall a n, l_TCX L <= a -> a + n <= l_TCX L + 0x10000 -> disjoint_from W a n.
Proof.
intros a n H1 H2. apply (R_grant (l_TCX L) 0x10000); [unfold startup_grants; right; right; right; left; reflexivity | | | exact H1 | exact H2].
- pose proof (geo_apart Σ m HA 0 3 _ _ ltac:(lia) eq_refl eq_refl) as X. cbn [fst snd] in X. unfold apart in *. lia.
- pose proof (geo_apart Σ m HA 3 5 _ _ ltac:(lia) eq_refl eq_refl) as X. cbn [fst snd] in X. exact X.
Qed.
Lemma ac_DTV : forall a n, l_DTV L <= a -> a + n <= l_DTV L + 4096 -> disjoint_from W a n.
Proof.
intros a n H1 H2. apply (R_grant (l_DTV L) 4096); [unfold startup_grants; right; right; right; right; left; reflexivity | | | exact H1 | exact H2].
- pose proof (geo_apart Σ m HA 0 4 _ _ ltac:(lia) eq_refl eq_refl) as X. cbn [fst snd] in X. unfold apart in *. lia.
- pose proof (geo_apart Σ m HA 4 5 _ _ ltac:(lia) eq_refl eq_refl) as X. cbn [fst snd] in X. exact X.
Qed.
Lemma ac_PAB : forall a n, l_PAB L <= a -> a + n <= l_PAB L + 0x800000 -> disjoint_from W a n.
Proof.
intros a n H1 H2. apply (R_grant (l_PAB L) 0x800000); [unfold startup_grants; right; left; reflexivity | | | exact H1 | exact H2].
- pose proof (geo_apart Σ m HA 0 1 _ _ ltac:(lia) eq_refl eq_refl) as X. cbn [fst snd] in X. unfold apart in *. lia.
- pose proof (geo_apart Σ m HA 1 5 _ _ ltac:(lia) eq_refl eq_refl) as X. cbn [fst snd] in X. exact X.
Qed.
Lemma ac_DNB : forall a n, l_DNB L <= a -> a + n <= l_DNB L + 0x100000 -> disjoint_from W a n.
Proof.
intros a n H1 H2. apply (R_grant (l_DNB L) 0x100000); [unfold startup_grants; do 6 right; left; reflexivity | | | exact H1 | exact H2].
- pose proof (geo_apart Σ m HA 0 6 _ _ ltac:(lia) eq_refl eq_refl) as X. cbn [fst snd] in X. unfold apart in *. lia.
- pose proof (geo_apart Σ m HA 5 6 _ _ ltac:(lia) eq_refl eq_refl) as X. cbn [fst snd] in X. unfold apart in *. lia.
Qed.
Lemma ac_SSB : forall a n, l_SSB L <= a -> a + n <= l_SSB L + 0x800000 -> disjoint_from W a n.
Proof.
intros a n H1 H2. apply (R_grant (l_SSB L) 0x800000); [unfold startup_grants; do 7 right; left; reflexivity | | | exact H1 | exact H2].
- pose proof (geo_apart Σ m HA 0 7 _ _ ltac:(lia) eq_refl eq_refl) as X. cbn [fst snd] in X. unfold apart in *. lia.
- pose proof (geo_apart Σ m HA 5 7 _ _ ltac:(lia) eq_refl eq_refl) as X. cbn [fst snd] in X. unfold apart in *. lia.
Qed.

Lemma av_consts : consts_avoid W L.
Proof.
unfold consts_avoid, consts_rngs. unfold_consts.
repeat (apply Forall_cons; [cbn [fst snd];
first [ apply R_img; [lia | unfold SEGTOP_A; lia | apply dsjb_sound; vm_compute; reflexivity] | apply ac_T; lia | apply ac_TCX; lia ] |]).
apply Forall_nil.
Qed.

Lemma av_reg : forall c, 1 <= c <= 31 -> reg_avoid W SB c (pr Σ c) /\ pclass_avoid W (l_T L) c.
Proof.
intros c Hc. pose proof (geo_prb Σ m HA) as (P1 & P2 & P3). pose proof (geo_wf Σ m HA) as (_ & HR & _). destruct HR as (HR & _).
pose proof (HR c Hc) as (W1 & W2 & W3 & W4 & W5 & W6 & _). pose proof (ClassSize_range c Hc) as (Hcs & Hm32).
split; [|unfold pclass_avoid, pc_addr, cacheT; apply ac_T; lia].
unfold reg_avoid. split; [|split].
-   apply R_prb; [unfold rinfo, RIS_of; lia | unfold rinfo, RIS_of; lia|].
intros c' i' n' Hc' Hn'. pose proof (slot_geo c' i' _ Hc' Hn') as (S1 & S2 & S3 & _).
pose proof (live_in_slot c' i' n' Hc' Hn') as (Y1 & Y2 & Y3 & _). right. unfold rinfo, RIS_of, rb, kUserCap in *.
assert (c' * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by lia. lia.
-   apply R_prb; [unfold fa, rb; lia | unfold fa, rb, kFaCap in *; assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by lia; lia|].
intros c' i' n' Hc' Hn'. pose proof (slot_geo c' i' _ Hc' Hn') as (S1 & S2 & S3 & _).
pose proof (live_in_slot c' i' n' Hc' Hn') as (Y1 & Y2 & Y3 & _). unfold fa, rb, kUserCap, kFaCap in *.
destruct (Z.eq_dec c c') as [<-|Hne]; [right; lia|]. destruct (Z_lt_le_dec c c'); [left | right]; lia.
-
set (auser := ClassSize c * Z.of_nat (length (r_st (pr Σ c)))).
assert (Hau : auser mod 8 = 0).
{ unfold auser. rewrite Z.mul_comm. apply Z.mod_divide; [lia|]. apply Z.divide_mul_r. apply Z.mod_divide in Hm32; [|lia].
apply (Z.divide_trans 8 32); [exists 4; reflexivity | exact Hm32]. }
assert (Hrb : rb SB c mod 8 = 0) by (unfold rb; apply Z.mod_divide; [lia|]; apply Z.divide_add_r;
[apply Z.mod_divide in P3; [|lia]; apply (Z.divide_trans 8 (2 ^ 16)); [exists 8192; reflexivity | exact P3] | exists (c * 2 ^ 29); lia]).
assert (Hmu : r_muser (pr Σ c) mod 8 = 0) by (unfold kUMap in W2; apply Z.mod_divide; [lia|]; apply Z.mod_divide in W2; [|lia];
apply (Z.divide_trans 8 0x40000); [exists 0x8000; reflexivity | exact W2]).
apply (R_shad (rb SB c + auser) (rb SB c + r_muser (pr Σ c))).
+ rewrite Z.add_mod by lia. rewrite Hrb, Hau. reflexivity.
+ rewrite Z.add_mod by lia. rewrite Hrb, Hmu. reflexivity.
+ pose proof (geo_grant Σ m HA (l_PRB L) 0x2000011000 ltac:(unfold startup_grants; left; reflexivity)) as (G1 & _).
unfold rb. assert (0 <= auser) by (unfold auser; apply Z.mul_nonneg_nonneg; lia). lia.
+ pose proof (geo_grant Σ m HA (l_PRB L) 0x2000011000 ltac:(unfold startup_grants; left; reflexivity)) as (_ & _ & G3 & _).
pose proof (rta_sp0 Σ m HA) as ((X1 & X2) & _). unfold l_ACEIL, rtA_sp0, sp_window_hi, STACK_WIN, rb, kUserCap in *.
assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by lia. lia.
+ lia.
+ assert (shad (rb SB c + auser) + Z.max 0 ((r_muser (pr Σ c) - auser) / 8) = shad (rb SB c + r_muser (pr Σ c))); [|lia].
unfold shad. rewrite Z.max_r by (apply Z.div_pos; lia).
replace (rb SB c + r_muser (pr Σ c)) with ((rb SB c + auser) + (r_muser (pr Σ c) - auser)) by lia.
assert (E1 : (rb SB c + auser) mod 8 = 0) by (rewrite Z.add_mod by lia; rewrite Hrb, Hau; reflexivity).
assert (E2 : (r_muser (pr Σ c) - auser) mod 8 = 0) by (rewrite Zminus_mod, Hmu, Hau; reflexivity).
apply Z.mod_divide in E1, E2; try (clear; lia). destruct E1 as [q1 E1]. destruct E2 as [q2 E2]. rewrite E1, E2.
replace (q1 * 8 + q2 * 8) with ((q1 + q2) * 8) by ring. rewrite !Z.div_mul by lia. lia.
+ intros f k Hin. destruct (sep_frame Σ m HA f k Hin) as (X & Y & _).
pose proof (geo_apart Σ m HA 0 5 _ _ ltac:(lia) eq_refl eq_refl) as Ha. cbn [fst snd] in Ha. unfold apart, rb, kUserCap in *.
assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by lia. lia.
+ pose proof (geo_apart Σ m HA 0 5 _ _ ltac:(lia) eq_refl eq_refl) as Ha. cbn [fst snd] in Ha. unfold apart, rb, kUserCap in *.
assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by lia. lia.
+ pose proof (geo_grant Σ m HA (l_PRB L) 0x2000011000 ltac:(unfold startup_grants; left; reflexivity)) as (_ & _ & G3 & _).
unfold rb, kUserCap in *. assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by lia. lia.
Qed.

Lemma mod8_of : forall z k, 0 < k -> z mod k = 0 -> (8 | k) -> z mod 8 = 0.
Proof. intros z k Hk H D. apply Z.mod_divide; [lia|]. apply Z.mod_divide in H; [|lia]. exact (Z.divide_trans _ _ _ D H). Qed.

Lemma abeg_mod8 : forall c i, 1 <= c <= 31 -> p_abeg SB c i mod 8 = 0.
Proof.
intros c i Hc. pose proof (geo_prb Σ m HA) as (_ & _ & P3). pose proof (ClassSize_range c Hc) as (_ & Hm).
unfold p_abeg. apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [apply Z.divide_add_r|].
- apply Z.mod_divide in P3; [|lia]. apply (Z.divide_trans 8 (2 ^ 16)); [exists 8192; reflexivity | exact P3].
- exists (c * 2 ^ 29). lia.
- apply Z.divide_mul_r. apply Z.mod_divide in Hm; [|lia]. apply (Z.divide_trans 8 32); [exists 4; reflexivity | exact Hm].
Qed.

Lemma ac_slot_shad : forall c i st a n, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some st ->
shad (p_abeg SB c i) <= a -> a + n <= shad (p_abeg SB c i) + ClassSize c / 8 -> disjoint_from W a n.
Proof.
intros c i st a n Hc Hn H1 H2. pose proof (slot_geo c i st Hc Hn) as (S1 & S2 & S3 & S4 & S5).
pose proof (abeg_mod8 c i Hc) as M1. pose proof (geo_prb Σ m HA) as (P1 & P2 & P3).
pose proof (geo_grant Σ m HA (l_PRB L) 0x2000011000 ltac:(unfold startup_grants; left; reflexivity)) as (G1 & _ & G3 & _).
assert (M2 : ClassSize c mod 8 = 0) by (apply (mod8_of _ 32 ltac:(lia) S5); exists 4; reflexivity).
assert (E : shad (p_abeg SB c i + ClassSize c) = shad (p_abeg SB c i) + ClassSize c / 8).
{ unfold shad. apply Z.mod_divide in M1, M2; try (clear; lia). destruct M1 as [q1 E1]. destruct M2 as [q2 E2].
rewrite E1, E2. replace (q1 * 8 + q2 * 8) with ((q1 + q2) * 8) by ring. rewrite !Z.div_mul by lia. lia. }
apply (R_shad (p_abeg SB c i) (p_abeg SB c i + ClassSize c)); [exact M1 | rewrite Z.add_mod, M1, M2 by lia; reflexivity | | | exact H1 | rewrite E; exact H2 | | |].
- unfold rb in S1. lia.
- pose proof (rta_sp0 Σ m HA) as ((X1 & X2) & _). unfold l_ACEIL, rtA_sp0, sp_window_hi, STACK_WIN, rb, kUserCap in *.
assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by lia. lia.
- intros f k Hin. destruct (sep_frame Σ m HA f k Hin) as (X & Y & _).
pose proof (geo_apart Σ m HA 0 5 _ _ ltac:(lia) eq_refl eq_refl) as Ha. cbn [fst snd] in Ha. unfold apart, rb, kUserCap in *.
assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by lia. lia.
- pose proof (geo_apart Σ m HA 0 5 _ _ ltac:(lia) eq_refl eq_refl) as Ha. cbn [fst snd] in Ha. unfold apart, rb, kUserCap in *.
assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by lia. lia.
- unfold rb, kUserCap in *. assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by lia. lia.
Qed.

Lemma rz_facts : forall n, rz_size n mod 16 = 0 /\ 16 <= rz_size n.
Proof.
intros n. unfold rz_size. pose proof (Z.pow_pos_nonneg 2 (rz_log n) ltac:(lia) ltac:(unfold rz_log; repeat destruct (_ <=? _); lia)).
split; [rewrite Z.mul_comm; apply Z.mod_mul; lia | lia].
Qed.

Lemma slot_room : forall c n, 1 <= c <= 31 -> 0 <= n -> rz_size n + n <= ClassSize c ->
rz_size n + ru8 n <= ClassSize c /\ rz_size n + 16 <= ClassSize c.
Proof.
intros c n Hc Hn H. pose proof (ClassSize_range c Hc) as (Hcs & Hm). pose proof (rz_facts n) as (R1 & R2).
assert (Hd : exists k, ClassSize c - rz_size n = 16 * k).
{ exists ((ClassSize c - rz_size n) / 16). pose proof (Z.div_mod (ClassSize c - rz_size n) 16 ltac:(lia)) as D.
assert ((ClassSize c - rz_size n) mod 16 = 0); [|lia]. rewrite Zminus_mod. rewrite R1.
replace (ClassSize c mod 16) with 0; [reflexivity|]. symmetry. (apply Z.mod_divide; [lia|]; apply Z.mod_divide in Hm; [|lia]; apply (Z.divide_trans 16 32); [exists 2; reflexivity | exact Hm]). }
destruct Hd as [k Hk]. unfold ru8. split.
- assert (8 * ((n + 7) / 8) <= 16 * k); [|lia]. assert ((n + 7) / 8 < 2 * k + 1); [|lia]. apply Z.div_lt_upper_bound; lia.
- destruct (Z_le_dec n 0) as [Hz|Hz].
+ assert (n = 0) by lia. subst n. unfold rz_size, rz_log in *. cbn in *. lia.
+ lia.
Qed.

Lemma ushadow_len : forall n, 0 <= n -> Z.of_nat (length (ushadow n)) = ru8 n / 8.
Proof.
intros n Hn. unfold ushadow, ru8. rewrite length_app, repeat_length. replace (8 * ((n + 7) / 8) / 8) with ((n + 7) / 8) by (rewrite Z.mul_comm, Z.div_mul; lia).
destruct (Z.eqb_spec (n mod 8) 0) as [E|E]; cbn [length].
- pose proof (Z.div_mod n 8 ltac:(lia)) as D. rewrite E in D. rewrite Nat.add_0_r, Z2Nat.id by (apply Z.div_pos; lia).
replace (n + 7) with ((n / 8) * 8 + 7) by lia. rewrite Z.div_add_l by lia. change (7 / 8) with 0. lia.
- pose proof (Z.div_mod n 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as B.
rewrite Nat2Z.inj_add, Z2Nat.id by (apply Z.div_pos; lia). cbn [Z.of_nat Pos.of_succ_nat].
replace (n + 7) with ((n / 8 + 1) * 8 + (n mod 8 - 1)) by lia. rewrite Z.div_add_l by lia. rewrite (Z.div_small (n mod 8 - 1) 8) by lia. lia.
Qed.

Lemma av_pchunk : forall c i st, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some st -> pchunk_avoid W SB c i st.
Proof.
intros c i st Hc Hn. unfold pchunk_avoid. pose proof (slot_geo c i st Hc Hn) as (S1 & S2 & S3 & S4 & S5).
assert (Hfit : forall n, st = CkAlloc n \/ st = CkQuar n -> rz_size n + n <= ClassSize c /\ 0 <= n).
{ intros n Hs. pose proof (geo_wf Σ m HA) as (_ & HR & _). destruct HR as (HR & _).
pose proof (HR c Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & W10 & _).
pose proof (proj1 (Forall_forall _ _) W10 _ (nth_error_In _ _ Hn)) as X. destruct Hs as [->| ->]; cbv beta iota in X; lia. }
pose proof (abeg_mod8 c i Hc) as M1. apply Z.mod_divide in M1; [|lia]. destruct M1 as [a0 E1].
apply Z.mod_divide in S5; [|lia]. destruct S5 as [s1 E4].
assert (ES : ClassSize c / 8 = 4 * s1) by (rewrite E4; replace (s1 * 32) with ((4 * s1) * 8) by ring; apply Z.div_mul; lia).
assert (EA : shad (p_abeg SB c i) = a0 + SHB) by (unfold shad; rewrite E1, Z.div_mul by lia; reflexivity).
destruct st as [|n|n|].
- apply (ac_slot_shad c i CkIdle); [exact Hc | exact Hn | lia | lia].
- destruct (Hfit n (or_introl eq_refl)) as (F1 & F2). destruct (slot_room c n Hc F2 F1) as (R1 & R2). pose proof (rz_facts n) as (R3 & R4).
pose proof (ushadow_len n F2) as U. rewrite length_app, Nat2Z.inj_add, farun_len, U.
apply Z.mod_divide in R3; [|lia]. destruct R3 as [r1 E2]. set (u0 := (n + 7) / 8). assert (E3 : ru8 n = u0 * 8) by (unfold ru8, u0; ring).
assert (ER : rz_size n / 8 = 2 * r1) by (rewrite E2; replace (r1 * 16) with ((2 * r1) * 8) by ring; apply Z.div_mul; lia).
assert (EU : ru8 n / 8 = u0) by (rewrite E3; apply Z.div_mul; lia).
split; [apply (ac_slot c i (CkAlloc n)); [exact Hc | exact Hn | lia | lia | intros n' E; injection E as <-; unfold p_ubeg; lia]|].
split; [intros Hr; apply (ac_slot c i (CkAlloc n)); [exact Hc | exact Hn | lia | lia | intros n' E; injection E as <-; unfold p_ubeg; lia]|].
split; [apply (ac_slot_shad c i (CkAlloc n)); [exact Hc | exact Hn | lia | rewrite ER, EU, ES, EA; lia]|].
assert (EB : shad (p_abeg SB c i + rz_size n + ru8 n) = a0 + 2 * r1 + u0 + SHB).
{ unfold shad. rewrite E1, E2, E3. replace (a0 * 8 + r1 * 16 + u0 * 8) with ((a0 + 2 * r1 + u0) * 8) by ring. rewrite Z.div_mul by lia. reflexivity. }
assert (EC : (ClassSize c - rz_size n - ru8 n) / 8 = 4 * s1 - 2 * r1 - u0).
{ rewrite E4, E2, E3. replace (s1 * 32 - r1 * 16 - u0 * 8) with ((4 * s1 - 2 * r1 - u0) * 8) by ring. apply Z.div_mul. lia. }
apply (ac_slot_shad c i (CkAlloc n)); [exact Hc | exact Hn | rewrite EB, EA; lia | rewrite EB, EC, ES, EA; lia].
- destruct (Hfit n (or_intror eq_refl)) as (F1 & F2). destruct (slot_room c n Hc F2 F1) as (R1 & R2). pose proof (rz_facts n) as (R3 & R4).
rewrite !length_app, !Nat2Z.inj_add, !farun_len, fdrun_len.
apply Z.mod_divide in R3; [|lia]. destruct R3 as [r1 E2]. set (u0 := (n + 7) / 8). assert (E3 : ru8 n = u0 * 8) by (unfold ru8, u0; ring).
assert (ER : rz_size n / 8 = 2 * r1) by (rewrite E2; replace (r1 * 16) with ((2 * r1) * 8) by ring; apply Z.div_mul; lia).
assert (EU : ru8 n / 8 = u0) by (rewrite E3; apply Z.div_mul; lia).
assert (EC : (ClassSize c - rz_size n - ru8 n) / 8 = 4 * s1 - 2 * r1 - u0).
{ rewrite E4, E2, E3. replace (s1 * 32 - r1 * 16 - u0 * 8) with ((4 * s1 - 2 * r1 - u0) * 8) by ring. apply Z.div_mul. lia. }
split; [apply (ac_slot c i (CkQuar n)); [exact Hc | exact Hn | lia | lia | intros n' E; discriminate E]|].
split; [intros Hr; apply (ac_slot c i (CkQuar n)); [exact Hc | exact Hn | lia | lia | intros n' E; discriminate E]|].
apply (ac_slot_shad c i (CkQuar n)); [exact Hc | exact Hn | lia | rewrite ER, EU, EC, ES, EA; lia].
- apply (ac_slot_shad c i CkBatch); [exact Hc | exact Hn | lia | lia].
Qed.

Lemma map_geo : forall k s, nth_error (sec Σ) k = Some s ->
64513 <= s_n s <= 0x8000000 /\ grant_ok L (s_mb s) (smsz (s_n s)) /\ apart (s_mb s) (smsz (s_n s)) (l_FSB L) 0xb09000
/\ smsz (s_n s) mod 4096 = 0 /\ 6144 + ru8 (s_n s) <= smsz (s_n s).
Proof.
intros k s Hk. pose proof (geo_wf Σ m HA) as (_ & _ & _ & HS & _). destruct HS as (_ & _ & _ & HSF & _).
pose proof (proj1 (Forall_forall _ _) HSF s (nth_error_In _ _ Hk)) as (Hn & G & _ & Hf & _).
split; [exact Hn|]. split; [exact G|]. split; [exact Hf|]. split.
- unfold smsz, pg_up. rewrite Z.add_mod by lia. rewrite Z.mod_mul by lia. reflexivity.
- unfold smsz, pg_up, needed, rounded, ru8. rewrite (rz_size_big (s_n s)) by lia. rewrite Z.max_l by lia. rewrite Z.max_l by lia.
assert (8 * ((s_n s + 7) / 8) + 2048 + 2048 <= (8 * ((s_n s + 7) / 8) + 2048 + 2048 + 4095) / 4096 * 4096); [|lia].
pose proof (Z.mod_pos_bound (8 * ((s_n s + 7) / 8) + 2048 + 2048 + 4095) 4096 ltac:(lia)).
pose proof (Z.div_mod (8 * ((s_n s + 7) / 8) + 2048 + 2048 + 4095) 4096 ltac:(lia)). lia.
Qed.

Lemma ac_map_shad : forall k s a n, nth_error (sec Σ) k = Some s ->
shad (s_mb s) <= a -> a + n <= shad (s_mb s) + smsz (s_n s) / 8 -> disjoint_from W a n.
Proof.
intros k s a n Hk H1 H2. destruct (map_geo k s Hk) as (Hn & (G1 & G2 & G3 & G4 & G5) & Hf & M2 & _).
assert (M1 : s_mb s mod 8 = 0) by (apply (mod8_of _ 4096 ltac:(lia) G2); exists 512; reflexivity).
assert (M3 : smsz (s_n s) mod 8 = 0) by (apply (mod8_of _ 4096 ltac:(lia) M2); exists 512; reflexivity).
assert (E : shad (s_mb s + smsz (s_n s)) = shad (s_mb s) + smsz (s_n s) / 8).
{ unfold shad. apply Z.mod_divide in M1, M3; try (clear; lia). destruct M1 as [q1 E1]. destruct M3 as [q2 E2].
rewrite E1, E2. replace (q1 * 8 + q2 * 8) with ((q1 + q2) * 8) by ring. rewrite !Z.div_mul by lia. lia. }
apply (R_shad (s_mb s) (s_mb s + smsz (s_n s))); [exact M1 | rewrite Z.add_mod, M1, M3 by lia; reflexivity | lia | | exact H1 | rewrite E; exact H2 | | |].
- pose proof (rta_sp0 Σ m HA) as ((X1 & X2) & _). unfold l_ACEIL, rtA_sp0, sp_window_hi, STACK_WIN in *. lia.
- intros f k' Hin. destruct (sep_frame Σ m HA f k' Hin) as (X & Y & _). unfold apart in Hf. lia.
- unfold apart in Hf. lia.
- lia.
Qed.

Lemma av_schunk : forall k s, nth_error (sec Σ) k = Some s -> schunk_avoid W s.
Proof.
intros k s Hk. unfold schunk_avoid. destruct (map_geo k s Hk) as (Hn & (G1 & G2 & G3 & G4 & G5) & Hf & M2 & Hroom).
assert (M1 : s_mb s mod 8 = 0) by (apply (mod8_of _ 4096 ltac:(lia) G2); exists 512; reflexivity).
apply Z.mod_divide in M1; [|lia]. destruct M1 as [a0 E1]. apply Z.mod_divide in M2; [|lia]. destruct M2 as [q E2].
set (u0 := (s_n s + 7) / 8). assert (E3 : ru8 (s_n s) = u0 * 8) by (unfold ru8, u0; ring).
assert (Hu0 : 0 <= u0) by (apply Z.div_pos; lia).
assert (EA : shad (s_mb s) = a0 + SHB) by (unfold shad; rewrite E1, Z.div_mul by lia; reflexivity).
assert (EM : smsz (s_n s) / 8 = 512 * q) by (rewrite E2; replace (q * 4096) with ((512 * q) * 8) by ring; apply Z.div_mul; lia).
assert (EU : ru8 (s_n s) / 8 = u0) by (rewrite E3; apply Z.div_mul; lia).
assert (Eb : shad (s_mb s + 4096 + 2048) = a0 + 768 + SHB).
{ unfold shad. rewrite E1. replace (a0 * 8 + 4096 + 2048) with ((a0 + 768) * 8) by ring. rewrite Z.div_mul by lia. reflexivity. }
assert (Ec : shad (s_mb s + 4096 + 2048 + ru8 (s_n s)) = a0 + 768 + u0 + SHB).
{ unfold shad. rewrite E1, E3. replace (a0 * 8 + 4096 + 2048 + u0 * 8) with ((a0 + 768 + u0) * 8) by ring. rewrite Z.div_mul by lia. reflexivity. }
assert (Ed : (smsz (s_n s) - 4096 - 2048 - ru8 (s_n s)) / 8 = 512 * q - 768 - u0).
{ rewrite E2, E3. replace (q * 4096 - 4096 - 2048 - u0 * 8) with ((512 * q - 768 - u0) * 8) by ring. apply Z.div_mul. lia. }
unfold s_ubeg in *.
split; [apply (R_secmap k s); [exact Hk | lia | lia | intros _; unfold s_ubeg; lia]|].
split; [apply (R_secmap k s); [exact Hk | lia | lia | intros _; unfold s_ubeg; lia]|].
split; [apply (R_secmap k s); [exact Hk | lia | destruct (s_quar s); lia | intros Hq; rewrite Hq; unfold s_ubeg; lia]|].
split; [apply (ac_map_shad k s); [exact Hk | lia | rewrite EM, EA; change ((4096 + 2048) / 8) with 768; lia]|].
split; [apply (ac_map_shad k s); [exact Hk | rewrite Eb, EA; lia |]|].
- destruct (s_quar s); [rewrite fdrun_len, EU | rewrite (ushadow_len (s_n s) ltac:(lia)), EU]; rewrite Eb, EM, EA; lia.
- apply (ac_map_shad k s); [exact Hk | rewrite Ec, EA; lia | rewrite Ec, Ed, EM, EA; lia].
Qed.

Lemma av_sec : sec_avoid W Σ.
Proof.
split; [apply ac_lits; vm_compute; reflexivity|]. pose proof (geo_wf Σ m HA) as (_ & _ & _ & HS & _). destruct HS as (_ & Hn & _).
apply ac_PAB; lia.
Qed.

Lemma av_quar : quar_avoid W Σ.
Proof.
split; [unfold qcacheT; apply ac_T; lia|]. split; [apply ac_lits; vm_compute; reflexivity|].
pose proof (geo_wf Σ m HA) as (_ & _ & _ & _ & HQ & _). destruct HQ as (_ & _ & HB & _).
apply Forall_forall. intros b Hb. destruct (proj1 (Forall_forall _ _) HB b Hb) as (i & Hi & ->).
apply (ac_slot 24 i CkBatch); [lia | exact Hi | lia | change (ClassSize 24) with 8192; lia | intros n' E; discriminate E].
Qed.

Lemma av_dep : dep_avoid W L.
Proof. split; [apply ac_lits; vm_compute; reflexivity|]. split; [apply ac_DNB | apply ac_SSB]; lia. Qed.

Lemma av_ia : dsjl W ia_lits.
Proof. apply ac_lits. vm_compute. reflexivity. Qed.

Lemma av_static_shad : Forall (fun r => disjoint_from W (shad (fst r)) (shad (snd r - 1) + 1 - shad (fst r))) CS_ACC.
Proof.
apply Forall_forall. intros r Hr.
assert (Hlh : 0x10000 <= fst r /\ fst r < snd r /\ snd r <= 0x65a578) by (unfold CS_ACC in Hr; repeat (destruct Hr as [Hr|Hr]; [subst r; cbn; lia|]); destruct Hr).
pose proof (geo_grant Σ m HA (l_FSB L) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as (_ & _ & _ & _ & G5).
apply (R_shad 0x10000 SEGTOP_A); [reflexivity | reflexivity | lia | unfold SEGTOP_A; lia | | | | |].
- unfold shad. apply Z.add_le_mono_r. apply Z.div_le_mono; lia.
- unfold shad, SEGTOP_A. assert ((snd r - 1) / 8 < 0xcb600) by (apply Z.div_lt_upper_bound; lia). change (0x65b000 / 8) with 0xcb600. lia.
- intros f k Hin. destruct (sep_frame Σ m HA f k Hin) as (X & Y & _). unfold SEGTOP_A in *. lia.
- unfold SEGTOP_A in *. lia.
- pose proof (rta_sp0_range Σ m HA) as HrS. unfold l_ACEIL, rtA_sp0 in *. lia.
Qed.

End CompStk.
End B_TWIN.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CompStk.
Variables (Σ : rtsA) (m : mem) (W : list ivl).
Hypothesis HA : ART_A Σ m.
#[local] Notation L := (lay Σ).
#[local] Notation SB := (l_SB (lay Σ)).

Hypothesis R_img : forall a n, 0x10000 <= a -> a + n <= SEGTOP_A -> disjoint_from CS_W a n -> disjoint_from W a n.
Hypothesis R_grant : forall b gn a n, In (b, gn) (startup_grants L) -> apart b gn (l_PRB L) 0x2000011000 -> apart b gn (l_FSB L) 0xb09000 ->
b <= a -> a + n <= b + gn -> disjoint_from W a n.
Hypothesis R_shad : forall lo hi a n, lo mod 8 = 0 -> hi mod 8 = 0 -> 0 <= lo -> hi <= 2 ^ 47 -> shad lo <= a -> a + n <= shad hi ->
(forall f k, In (f, k) (frames Σ) -> hi <= f \/ f + fs_size k <= lo) ->
(hi <= l_FSB L \/ l_FSB L + 0xb09000 <= lo) -> hi <= l_ACEIL L -> disjoint_from W a n.
Hypothesis R_prb : forall a n, l_PRB L <= a -> a + n <= l_PRB L + 0x2000011000 ->
(forall c i n', 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some (CkAlloc n') ->
a + n <= p_ubeg SB c i n' \/ p_ubeg SB c i n' + n' <= a) -> disjoint_from W a n.
Hypothesis R_secmap : forall k0 s0 a n, nth_error (sec Σ) k0 = Some s0 -> s_mb s0 <= a -> a + n <= s_mb s0 + smsz (s_n s0) ->
(s_quar s0 = false -> a + n <= s_ubeg s0 \/ s_ubeg s0 + s_n s0 <= a) -> disjoint_from W a n.

Lemma slot_geo : forall c i st, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some st ->
rb SB c <= p_abeg SB c i /\ p_abeg SB c i + ClassSize c <= rb SB c + r_muser (pr Σ c) /\ r_muser (pr Σ c) <= kUserCap
/\ 32 <= ClassSize c /\ ClassSize c mod 32 = 0.
Proof.
intros c i st Hc Hn. pose proof (geo_wf Σ m HA) as (_ & HR & _). destruct HR as (HR & _).
pose proof (HR c Hc) as (W1 & _ & W3 & _). pose proof (ClassSize_range c Hc) as (Hcs & Hm).
pose proof (proj1 (nth_error_Some (r_st (pr Σ c)) i) ltac:(rewrite Hn; discriminate)) as Hlt.
unfold p_abeg, rb in *.
assert (Hx : Z.of_nat i * ClassSize c + ClassSize c <= ClassSize c * Z.of_nat (length (r_st (pr Σ c)))).
{ replace (ClassSize c * Z.of_nat (length (r_st (pr Σ c)))) with (Z.of_nat (length (r_st (pr Σ c))) * ClassSize c) by ring.
replace (Z.of_nat i * ClassSize c + ClassSize c) with ((Z.of_nat i + 1) * ClassSize c) by ring.
apply Z.mul_le_mono_nonneg_r; lia. }
assert (0 <= Z.of_nat i * ClassSize c) by (apply Z.mul_nonneg_nonneg; lia). repeat split; lia.
Qed.

Lemma slot_apart : forall c i c' i' st st', 1 <= c <= 31 -> 1 <= c' <= 31 -> nth_error (r_st (pr Σ c)) i = Some st ->
nth_error (r_st (pr Σ c')) i' = Some st' -> (c <> c' \/ i <> i') ->
p_abeg SB c i + ClassSize c <= p_abeg SB c' i' \/ p_abeg SB c' i' + ClassSize c' <= p_abeg SB c i.
Proof.
intros c i c' i' st st' Hc Hc' Hn Hn' Hne.
pose proof (slot_geo c i st Hc Hn) as (A1 & A2 & A3 & _). pose proof (slot_geo c' i' st' Hc' Hn') as (B1 & B2 & B3 & _).
destruct (Z.eq_dec c c') as [<-|Hcc].
- destruct Hne as [Hne|Hne]; [lia|]. unfold p_abeg. pose proof (ClassSize_range c Hc) as (Hcs & _).
destruct (Nat.lt_ge_cases i i') as [Hl|Hl].
+ left. assert (Z.of_nat i * ClassSize c + ClassSize c <= Z.of_nat i' * ClassSize c).
{ replace (Z.of_nat i * ClassSize c + ClassSize c) with ((Z.of_nat i + 1) * ClassSize c) by ring. apply Z.mul_le_mono_nonneg_r; lia. }
lia.
+ right. assert (Z.of_nat i' * ClassSize c + ClassSize c <= Z.of_nat i * ClassSize c).
{ replace (Z.of_nat i' * ClassSize c + ClassSize c) with ((Z.of_nat i' + 1) * ClassSize c) by ring. apply Z.mul_le_mono_nonneg_r; lia. }
lia.
- unfold rb, kUserCap in *. lia.
Qed.

Lemma live_in_slot : forall c i n', 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some (CkAlloc n') ->
p_abeg SB c i + rz_size n' = p_ubeg SB c i n' /\ 16 <= rz_size n' /\ rz_size n' + n' <= ClassSize c /\ 0 <= n'.
Proof.
intros c i n' Hc Hn. pose proof (geo_wf Σ m HA) as (_ & HR & _). destruct HR as (HR & _).
pose proof (HR c Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & W10 & _).
pose proof (proj1 (Forall_forall _ _) W10 _ (nth_error_In _ _ Hn)) as (Hn0 & Hfit & _). cbv beta iota in Hn0, Hfit.
split; [reflexivity|]. split; [|lia].
unfold rz_size. pose proof (Z.pow_pos_nonneg 2 (rz_log n') ltac:(lia) ltac:(unfold rz_log; repeat destruct (_ <=? _); lia)). lia.
Qed.

Lemma ac_slot : forall c i st a n, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some st -> p_abeg SB c i <= a ->
a + n <= p_abeg SB c i + ClassSize c ->
(forall n', st = CkAlloc n' -> a + n <= p_ubeg SB c i n') -> disjoint_from W a n.
Proof.
intros c i st a n Hc Hn H1 H2 HU. pose proof (slot_geo c i st Hc Hn) as (S1 & S2 & S3 & _).
pose proof (geo_prb Σ m HA) as (P1 & P2 & P3).
apply R_prb; [unfold rb in *; lia | unfold rb, kUserCap in *; assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by lia; lia|].
intros c' i' n' Hc' Hn'. destruct (Z.eq_dec c c') as [<-|Hne]; [destruct (Nat.eq_dec i i') as [<-|Hne]|].
- rewrite Hn in Hn'. injection Hn' as ->. left. exact (HU n' eq_refl).
- destruct (slot_apart c i c i' st (CkAlloc n') Hc Hc' Hn Hn' (or_intror Hne)) as [X|X];
pose proof (live_in_slot c i' n' Hc' Hn') as (Y1 & Y2 & Y3 & _); lia.
- destruct (slot_apart c i c' i' st (CkAlloc n') Hc Hc' Hn Hn' (or_introl Hne)) as [X|X];
pose proof (live_in_slot c' i' n' Hc' Hn') as (Y1 & Y2 & Y3 & _); lia.
Qed.

Fixpoint dsjb (V : list ivl) (a n : Z) : bool :=
match V with [] => true | (lo, hi) :: V' => ((a + n <=? lo) || (hi <=? a)) && dsjb V' a n end.
Lemma dsjb_sound : forall V a n, dsjb V a n = true -> disjoint_from V a n.
Proof.
induction V as [|[lo hi] V IH]; intros a n H; [exact I|]. cbn [dsjb] in H. apply andb_prop in H as [H1 H2].
split; [|exact (IH _ _ H2)]. apply orb_prop in H1 as [X|X]; [left; apply Z.leb_le; exact X | right; apply Z.leb_le; exact X].
Qed.
Definition img_ok (r : Z * Z) : bool := ((0x10000 <=? fst r) && (fst r + snd r <=? SEGTOP_A) && dsjb CS_W (fst r) (snd r))%bool.
Lemma ac_lits : forall l, forallb img_ok l = true -> dsjl W l.
Proof.
intros l H. apply Forall_forall. intros [a n] Hin. pose proof (proj1 (forallb_forall _ _) H _ Hin) as X. unfold img_ok in X.
cbn [fst snd] in *. apply andb_prop in X as [X X3]. apply andb_prop in X as [X1 X2]. apply Z.leb_le in X1, X2.
exact (R_img a n X1 X2 (dsjb_sound _ _ _ X3)).
Qed.

Lemma ac_T : forall a n, l_T L <= a -> a + n <= l_T L + 4096 -> disjoint_from W a n.
Proof.
intros a n H1 H2. apply (R_grant (l_T L) 4096); [unfold startup_grants; right; right; left; reflexivity | | | exact H1 | exact H2].
- pose proof (geo_apart Σ m HA 0 2 _ _ ltac:(lia) eq_refl eq_refl) as X. cbn [fst snd] in X. unfold apart in *. lia.
- pose proof (geo_apart Σ m HA 2 5 _ _ ltac:(lia) eq_refl eq_refl) as X. cbn [fst snd] in X. exact X.
Qed.
Lemma ac_TCX : forall a n, l_TCX L <= a -> a + n <= l_TCX L + 0x10000 -> disjoint_from W a n.
Proof.
intros a n H1 H2. apply (R_grant (l_TCX L) 0x10000); [unfold startup_grants; right; right; right; left; reflexivity | | | exact H1 | exact H2].
- pose proof (geo_apart Σ m HA 0 3 _ _ ltac:(lia) eq_refl eq_refl) as X. cbn [fst snd] in X. unfold apart in *. lia.
- pose proof (geo_apart Σ m HA 3 5 _ _ ltac:(lia) eq_refl eq_refl) as X. cbn [fst snd] in X. exact X.
Qed.
Lemma ac_DTV : forall a n, l_DTV L <= a -> a + n <= l_DTV L + 4096 -> disjoint_from W a n.
Proof.
intros a n H1 H2. apply (R_grant (l_DTV L) 4096); [unfold startup_grants; right; right; right; right; left; reflexivity | | | exact H1 | exact H2].
- pose proof (geo_apart Σ m HA 0 4 _ _ ltac:(lia) eq_refl eq_refl) as X. cbn [fst snd] in X. unfold apart in *. lia.
- pose proof (geo_apart Σ m HA 4 5 _ _ ltac:(lia) eq_refl eq_refl) as X. cbn [fst snd] in X. exact X.
Qed.
Lemma ac_PAB : forall a n, l_PAB L <= a -> a + n <= l_PAB L + 0x800000 -> disjoint_from W a n.
Proof.
intros a n H1 H2. apply (R_grant (l_PAB L) 0x800000); [unfold startup_grants; right; left; reflexivity | | | exact H1 | exact H2].
- pose proof (geo_apart Σ m HA 0 1 _ _ ltac:(lia) eq_refl eq_refl) as X. cbn [fst snd] in X. unfold apart in *. lia.
- pose proof (geo_apart Σ m HA 1 5 _ _ ltac:(lia) eq_refl eq_refl) as X. cbn [fst snd] in X. exact X.
Qed.
Lemma ac_DNB : forall a n, l_DNB L <= a -> a + n <= l_DNB L + 0x100000 -> disjoint_from W a n.
Proof.
intros a n H1 H2. apply (R_grant (l_DNB L) 0x100000); [unfold startup_grants; do 6 right; left; reflexivity | | | exact H1 | exact H2].
- pose proof (geo_apart Σ m HA 0 6 _ _ ltac:(lia) eq_refl eq_refl) as X. cbn [fst snd] in X. unfold apart in *. lia.
- pose proof (geo_apart Σ m HA 5 6 _ _ ltac:(lia) eq_refl eq_refl) as X. cbn [fst snd] in X. unfold apart in *. lia.
Qed.
Lemma ac_SSB : forall a n, l_SSB L <= a -> a + n <= l_SSB L + 0x800000 -> disjoint_from W a n.
Proof.
intros a n H1 H2. apply (R_grant (l_SSB L) 0x800000); [unfold startup_grants; do 7 right; left; reflexivity | | | exact H1 | exact H2].
- pose proof (geo_apart Σ m HA 0 7 _ _ ltac:(lia) eq_refl eq_refl) as X. cbn [fst snd] in X. unfold apart in *. lia.
- pose proof (geo_apart Σ m HA 5 7 _ _ ltac:(lia) eq_refl eq_refl) as X. cbn [fst snd] in X. unfold apart in *. lia.
Qed.

Lemma av_consts : consts_avoid W L.
Proof.
unfold consts_avoid, consts_rngs. unfold_consts.
repeat (apply Forall_cons; [cbn [fst snd];
first [ apply R_img; [lia | unfold SEGTOP_A; lia | apply dsjb_sound; vm_compute; reflexivity] | apply ac_T; lia | apply ac_TCX; lia ] |]).
apply Forall_nil.
Qed.

Lemma av_reg : forall c, 1 <= c <= 31 -> reg_avoid W SB c (pr Σ c) /\ pclass_avoid W (l_T L) c.
Proof.
intros c Hc. pose proof (geo_prb Σ m HA) as (P1 & P2 & P3). pose proof (geo_wf Σ m HA) as (_ & HR & _). destruct HR as (HR & _).
pose proof (HR c Hc) as (W1 & W2 & W3 & W4 & W5 & W6 & _). pose proof (ClassSize_range c Hc) as (Hcs & Hm32).
split; [|unfold pclass_avoid, pc_addr, cacheT; apply ac_T; lia].
unfold reg_avoid. split; [|split].
-   apply R_prb; [unfold rinfo, RIS_of; lia | unfold rinfo, RIS_of; lia|].
intros c' i' n' Hc' Hn'. pose proof (slot_geo c' i' _ Hc' Hn') as (S1 & S2 & S3 & _).
pose proof (live_in_slot c' i' n' Hc' Hn') as (Y1 & Y2 & Y3 & _). right. unfold rinfo, RIS_of, rb, kUserCap in *.
assert (c' * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by lia. lia.
-   apply R_prb; [unfold fa, rb; lia | unfold fa, rb, kFaCap in *; assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by lia; lia|].
intros c' i' n' Hc' Hn'. pose proof (slot_geo c' i' _ Hc' Hn') as (S1 & S2 & S3 & _).
pose proof (live_in_slot c' i' n' Hc' Hn') as (Y1 & Y2 & Y3 & _). unfold fa, rb, kUserCap, kFaCap in *.
destruct (Z.eq_dec c c') as [<-|Hne]; [right; lia|]. destruct (Z_lt_le_dec c c'); [left | right]; lia.
-
set (auser := ClassSize c * Z.of_nat (length (r_st (pr Σ c)))).
assert (Hau : auser mod 8 = 0).
{ unfold auser. rewrite Z.mul_comm. apply Z.mod_divide; [lia|]. apply Z.divide_mul_r. apply Z.mod_divide in Hm32; [|lia].
apply (Z.divide_trans 8 32); [exists 4; reflexivity | exact Hm32]. }
assert (Hrb : rb SB c mod 8 = 0) by (unfold rb; apply Z.mod_divide; [lia|]; apply Z.divide_add_r;
[apply Z.mod_divide in P3; [|lia]; apply (Z.divide_trans 8 (2 ^ 16)); [exists 8192; reflexivity | exact P3] | exists (c * 2 ^ 29); lia]).
assert (Hmu : r_muser (pr Σ c) mod 8 = 0) by (unfold kUMap in W2; apply Z.mod_divide; [lia|]; apply Z.mod_divide in W2; [|lia];
apply (Z.divide_trans 8 0x40000); [exists 0x8000; reflexivity | exact W2]).
apply (R_shad (rb SB c + auser) (rb SB c + r_muser (pr Σ c))).
+ rewrite Z.add_mod by lia. rewrite Hrb, Hau. reflexivity.
+ rewrite Z.add_mod by lia. rewrite Hrb, Hmu. reflexivity.
+ pose proof (geo_grant Σ m HA (l_PRB L) 0x2000011000 ltac:(unfold startup_grants; left; reflexivity)) as (G1 & _).
unfold rb. assert (0 <= auser) by (unfold auser; apply Z.mul_nonneg_nonneg; lia). lia.
+ pose proof (geo_grant Σ m HA (l_PRB L) 0x2000011000 ltac:(unfold startup_grants; left; reflexivity)) as (_ & _ & G3 & _).
pose proof (rta_sp0 Σ m HA) as ((X1 & X2) & _). unfold l_ACEIL, rtA_sp0, sp_window_hi, STACK_WIN, rb, kUserCap in *.
assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by lia. lia.
+ lia.
+ assert (shad (rb SB c + auser) + Z.max 0 ((r_muser (pr Σ c) - auser) / 8) = shad (rb SB c + r_muser (pr Σ c))); [|lia].
unfold shad. rewrite Z.max_r by (apply Z.div_pos; lia).
replace (rb SB c + r_muser (pr Σ c)) with ((rb SB c + auser) + (r_muser (pr Σ c) - auser)) by lia.
assert (E1 : (rb SB c + auser) mod 8 = 0) by (rewrite Z.add_mod by lia; rewrite Hrb, Hau; reflexivity).
assert (E2 : (r_muser (pr Σ c) - auser) mod 8 = 0) by (rewrite Zminus_mod, Hmu, Hau; reflexivity).
apply Z.mod_divide in E1, E2; try (clear; lia). destruct E1 as [q1 E1]. destruct E2 as [q2 E2]. rewrite E1, E2.
replace (q1 * 8 + q2 * 8) with ((q1 + q2) * 8) by ring. rewrite !Z.div_mul by lia. lia.
+ intros f k Hin. destruct (sep_frame Σ m HA f k Hin) as (X & Y & _).
pose proof (geo_apart Σ m HA 0 5 _ _ ltac:(lia) eq_refl eq_refl) as Ha. cbn [fst snd] in Ha. unfold apart, rb, kUserCap in *.
assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by lia. lia.
+ pose proof (geo_apart Σ m HA 0 5 _ _ ltac:(lia) eq_refl eq_refl) as Ha. cbn [fst snd] in Ha. unfold apart, rb, kUserCap in *.
assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by lia. lia.
+ pose proof (geo_grant Σ m HA (l_PRB L) 0x2000011000 ltac:(unfold startup_grants; left; reflexivity)) as (_ & _ & G3 & _).
unfold rb, kUserCap in *. assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by lia. lia.
Qed.

Lemma mod8_of : forall z k, 0 < k -> z mod k = 0 -> (8 | k) -> z mod 8 = 0.
Proof. intros z k Hk H D. apply Z.mod_divide; [lia|]. apply Z.mod_divide in H; [|lia]. exact (Z.divide_trans _ _ _ D H). Qed.

Lemma abeg_mod8 : forall c i, 1 <= c <= 31 -> p_abeg SB c i mod 8 = 0.
Proof.
intros c i Hc. pose proof (geo_prb Σ m HA) as (_ & _ & P3). pose proof (ClassSize_range c Hc) as (_ & Hm).
unfold p_abeg. apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [apply Z.divide_add_r|].
- apply Z.mod_divide in P3; [|lia]. apply (Z.divide_trans 8 (2 ^ 16)); [exists 8192; reflexivity | exact P3].
- exists (c * 2 ^ 29). lia.
- apply Z.divide_mul_r. apply Z.mod_divide in Hm; [|lia]. apply (Z.divide_trans 8 32); [exists 4; reflexivity | exact Hm].
Qed.

Lemma ac_slot_shad : forall c i st a n, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some st ->
shad (p_abeg SB c i) <= a -> a + n <= shad (p_abeg SB c i) + ClassSize c / 8 -> disjoint_from W a n.
Proof.
intros c i st a n Hc Hn H1 H2. pose proof (slot_geo c i st Hc Hn) as (S1 & S2 & S3 & S4 & S5).
pose proof (abeg_mod8 c i Hc) as M1. pose proof (geo_prb Σ m HA) as (P1 & P2 & P3).
pose proof (geo_grant Σ m HA (l_PRB L) 0x2000011000 ltac:(unfold startup_grants; left; reflexivity)) as (G1 & _ & G3 & _).
assert (M2 : ClassSize c mod 8 = 0) by (apply (mod8_of _ 32 ltac:(lia) S5); exists 4; reflexivity).
assert (E : shad (p_abeg SB c i + ClassSize c) = shad (p_abeg SB c i) + ClassSize c / 8).
{ unfold shad. apply Z.mod_divide in M1, M2; try (clear; lia). destruct M1 as [q1 E1]. destruct M2 as [q2 E2].
rewrite E1, E2. replace (q1 * 8 + q2 * 8) with ((q1 + q2) * 8) by ring. rewrite !Z.div_mul by lia. lia. }
apply (R_shad (p_abeg SB c i) (p_abeg SB c i + ClassSize c)); [exact M1 | rewrite Z.add_mod, M1, M2 by lia; reflexivity | | | exact H1 | rewrite E; exact H2 | | |].
- unfold rb in S1. lia.
- pose proof (rta_sp0 Σ m HA) as ((X1 & X2) & _). unfold l_ACEIL, rtA_sp0, sp_window_hi, STACK_WIN, rb, kUserCap in *.
assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by lia. lia.
- intros f k Hin. destruct (sep_frame Σ m HA f k Hin) as (X & Y & _).
pose proof (geo_apart Σ m HA 0 5 _ _ ltac:(lia) eq_refl eq_refl) as Ha. cbn [fst snd] in Ha. unfold apart, rb, kUserCap in *.
assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by lia. lia.
- pose proof (geo_apart Σ m HA 0 5 _ _ ltac:(lia) eq_refl eq_refl) as Ha. cbn [fst snd] in Ha. unfold apart, rb, kUserCap in *.
assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by lia. lia.
- unfold rb, kUserCap in *. assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by lia. lia.
Qed.

Lemma rz_facts : forall n, rz_size n mod 16 = 0 /\ 16 <= rz_size n.
Proof.
intros n. unfold rz_size. pose proof (Z.pow_pos_nonneg 2 (rz_log n) ltac:(lia) ltac:(unfold rz_log; repeat destruct (_ <=? _); lia)).
split; [rewrite Z.mul_comm; apply Z.mod_mul; lia | lia].
Qed.

Lemma slot_room : forall c n, 1 <= c <= 31 -> 0 <= n -> rz_size n + n <= ClassSize c ->
rz_size n + ru8 n <= ClassSize c /\ rz_size n + 16 <= ClassSize c.
Proof.
intros c n Hc Hn H. pose proof (ClassSize_range c Hc) as (Hcs & Hm). pose proof (rz_facts n) as (R1 & R2).
assert (Hd : exists k, ClassSize c - rz_size n = 16 * k).
{ exists ((ClassSize c - rz_size n) / 16). pose proof (Z.div_mod (ClassSize c - rz_size n) 16 ltac:(lia)) as D.
assert ((ClassSize c - rz_size n) mod 16 = 0); [|lia]. rewrite Zminus_mod. rewrite R1.
replace (ClassSize c mod 16) with 0; [reflexivity|]. symmetry. (apply Z.mod_divide; [lia|]; apply Z.mod_divide in Hm; [|lia]; apply (Z.divide_trans 16 32); [exists 2; reflexivity | exact Hm]). }
destruct Hd as [k Hk]. unfold ru8. split.
- assert (8 * ((n + 7) / 8) <= 16 * k); [|lia]. assert ((n + 7) / 8 < 2 * k + 1); [|lia]. apply Z.div_lt_upper_bound; lia.
- destruct (Z_le_dec n 0) as [Hz|Hz].
+ assert (n = 0) by lia. subst n. unfold rz_size, rz_log in *. cbn in *. lia.
+ lia.
Qed.

Lemma ushadow_len : forall n, 0 <= n -> Z.of_nat (length (ushadow n)) = ru8 n / 8.
Proof.
intros n Hn. unfold ushadow, ru8. rewrite length_app, repeat_length. replace (8 * ((n + 7) / 8) / 8) with ((n + 7) / 8) by (rewrite Z.mul_comm, Z.div_mul; lia).
destruct (Z.eqb_spec (n mod 8) 0) as [E|E]; cbn [length].
- pose proof (Z.div_mod n 8 ltac:(lia)) as D. rewrite E in D. rewrite Nat.add_0_r, Z2Nat.id by (apply Z.div_pos; lia).
replace (n + 7) with ((n / 8) * 8 + 7) by lia. rewrite Z.div_add_l by lia. change (7 / 8) with 0. lia.
- pose proof (Z.div_mod n 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as B.
rewrite Nat2Z.inj_add, Z2Nat.id by (apply Z.div_pos; lia). cbn [Z.of_nat Pos.of_succ_nat].
replace (n + 7) with ((n / 8 + 1) * 8 + (n mod 8 - 1)) by lia. rewrite Z.div_add_l by lia. rewrite (Z.div_small (n mod 8 - 1) 8) by lia. lia.
Qed.

Lemma av_pchunk : forall c i st, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some st -> pchunk_avoid W SB c i st.
Proof.
intros c i st Hc Hn. unfold pchunk_avoid. pose proof (slot_geo c i st Hc Hn) as (S1 & S2 & S3 & S4 & S5).
assert (Hfit : forall n, st = CkAlloc n \/ st = CkQuar n -> rz_size n + n <= ClassSize c /\ 0 <= n).
{ intros n Hs. pose proof (geo_wf Σ m HA) as (_ & HR & _). destruct HR as (HR & _).
pose proof (HR c Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & W10 & _).
pose proof (proj1 (Forall_forall _ _) W10 _ (nth_error_In _ _ Hn)) as X. destruct Hs as [->| ->]; cbv beta iota in X; lia. }
pose proof (abeg_mod8 c i Hc) as M1. apply Z.mod_divide in M1; [|lia]. destruct M1 as [a0 E1].
apply Z.mod_divide in S5; [|lia]. destruct S5 as [s1 E4].
assert (ES : ClassSize c / 8 = 4 * s1) by (rewrite E4; replace (s1 * 32) with ((4 * s1) * 8) by ring; apply Z.div_mul; lia).
assert (EA : shad (p_abeg SB c i) = a0 + SHB) by (unfold shad; rewrite E1, Z.div_mul by lia; reflexivity).
destruct st as [|n|n|].
- apply (ac_slot_shad c i CkIdle); [exact Hc | exact Hn | lia | lia].
- destruct (Hfit n (or_introl eq_refl)) as (F1 & F2). destruct (slot_room c n Hc F2 F1) as (R1 & R2). pose proof (rz_facts n) as (R3 & R4).
pose proof (ushadow_len n F2) as U. rewrite length_app, Nat2Z.inj_add, farun_len, U.
apply Z.mod_divide in R3; [|lia]. destruct R3 as [r1 E2]. set (u0 := (n + 7) / 8). assert (E3 : ru8 n = u0 * 8) by (unfold ru8, u0; ring).
assert (ER : rz_size n / 8 = 2 * r1) by (rewrite E2; replace (r1 * 16) with ((2 * r1) * 8) by ring; apply Z.div_mul; lia).
assert (EU : ru8 n / 8 = u0) by (rewrite E3; apply Z.div_mul; lia).
split; [apply (ac_slot c i (CkAlloc n)); [exact Hc | exact Hn | lia | lia | intros n' E; injection E as <-; unfold p_ubeg; lia]|].
split; [intros Hr; apply (ac_slot c i (CkAlloc n)); [exact Hc | exact Hn | lia | lia | intros n' E; injection E as <-; unfold p_ubeg; lia]|].
split; [apply (ac_slot_shad c i (CkAlloc n)); [exact Hc | exact Hn | lia | rewrite ER, EU, ES, EA; lia]|].
assert (EB : shad (p_abeg SB c i + rz_size n + ru8 n) = a0 + 2 * r1 + u0 + SHB).
{ unfold shad. rewrite E1, E2, E3. replace (a0 * 8 + r1 * 16 + u0 * 8) with ((a0 + 2 * r1 + u0) * 8) by ring. rewrite Z.div_mul by lia. reflexivity. }
assert (EC : (ClassSize c - rz_size n - ru8 n) / 8 = 4 * s1 - 2 * r1 - u0).
{ rewrite E4, E2, E3. replace (s1 * 32 - r1 * 16 - u0 * 8) with ((4 * s1 - 2 * r1 - u0) * 8) by ring. apply Z.div_mul. lia. }
apply (ac_slot_shad c i (CkAlloc n)); [exact Hc | exact Hn | rewrite EB, EA; lia | rewrite EB, EC, ES, EA; lia].
- destruct (Hfit n (or_intror eq_refl)) as (F1 & F2). destruct (slot_room c n Hc F2 F1) as (R1 & R2). pose proof (rz_facts n) as (R3 & R4).
rewrite !length_app, !Nat2Z.inj_add, !farun_len, fdrun_len.
apply Z.mod_divide in R3; [|lia]. destruct R3 as [r1 E2]. set (u0 := (n + 7) / 8). assert (E3 : ru8 n = u0 * 8) by (unfold ru8, u0; ring).
assert (ER : rz_size n / 8 = 2 * r1) by (rewrite E2; replace (r1 * 16) with ((2 * r1) * 8) by ring; apply Z.div_mul; lia).
assert (EU : ru8 n / 8 = u0) by (rewrite E3; apply Z.div_mul; lia).
assert (EC : (ClassSize c - rz_size n - ru8 n) / 8 = 4 * s1 - 2 * r1 - u0).
{ rewrite E4, E2, E3. replace (s1 * 32 - r1 * 16 - u0 * 8) with ((4 * s1 - 2 * r1 - u0) * 8) by ring. apply Z.div_mul. lia. }
split; [apply (ac_slot c i (CkQuar n)); [exact Hc | exact Hn | lia | lia | intros n' E; discriminate E]|].
split; [intros Hr; apply (ac_slot c i (CkQuar n)); [exact Hc | exact Hn | lia | lia | intros n' E; discriminate E]|].
apply (ac_slot_shad c i (CkQuar n)); [exact Hc | exact Hn | lia | rewrite ER, EU, EC, ES, EA; lia].
- apply (ac_slot_shad c i CkBatch); [exact Hc | exact Hn | lia | lia].
Qed.

Lemma map_geo : forall k s, nth_error (sec Σ) k = Some s ->
64513 <= s_n s <= 0x8000000 /\ grant_ok L (s_mb s) (smsz (s_n s)) /\ apart (s_mb s) (smsz (s_n s)) (l_FSB L) 0xb09000
/\ smsz (s_n s) mod 4096 = 0 /\ 6144 + ru8 (s_n s) <= smsz (s_n s).
Proof.
intros k s Hk. pose proof (geo_wf Σ m HA) as (_ & _ & _ & HS & _). destruct HS as (_ & _ & _ & HSF & _).
pose proof (proj1 (Forall_forall _ _) HSF s (nth_error_In _ _ Hk)) as (Hn & G & _ & Hf & _).
split; [exact Hn|]. split; [exact G|]. split; [exact Hf|]. split.
- unfold smsz, pg_up. rewrite Z.add_mod by lia. rewrite Z.mod_mul by lia. reflexivity.
- unfold smsz, pg_up, needed, rounded, ru8. rewrite (rz_size_big (s_n s)) by lia. rewrite Z.max_l by lia. rewrite Z.max_l by lia.
assert (8 * ((s_n s + 7) / 8) + 2048 + 2048 <= (8 * ((s_n s + 7) / 8) + 2048 + 2048 + 4095) / 4096 * 4096); [|lia].
pose proof (Z.mod_pos_bound (8 * ((s_n s + 7) / 8) + 2048 + 2048 + 4095) 4096 ltac:(lia)).
pose proof (Z.div_mod (8 * ((s_n s + 7) / 8) + 2048 + 2048 + 4095) 4096 ltac:(lia)). lia.
Qed.

Lemma ac_map_shad : forall k s a n, nth_error (sec Σ) k = Some s ->
shad (s_mb s) <= a -> a + n <= shad (s_mb s) + smsz (s_n s) / 8 -> disjoint_from W a n.
Proof.
intros k s a n Hk H1 H2. destruct (map_geo k s Hk) as (Hn & (G1 & G2 & G3 & G4 & G5) & Hf & M2 & _).
assert (M1 : s_mb s mod 8 = 0) by (apply (mod8_of _ 4096 ltac:(lia) G2); exists 512; reflexivity).
assert (M3 : smsz (s_n s) mod 8 = 0) by (apply (mod8_of _ 4096 ltac:(lia) M2); exists 512; reflexivity).
assert (E : shad (s_mb s + smsz (s_n s)) = shad (s_mb s) + smsz (s_n s) / 8).
{ unfold shad. apply Z.mod_divide in M1, M3; try (clear; lia). destruct M1 as [q1 E1]. destruct M3 as [q2 E2].
rewrite E1, E2. replace (q1 * 8 + q2 * 8) with ((q1 + q2) * 8) by ring. rewrite !Z.div_mul by lia. lia. }
apply (R_shad (s_mb s) (s_mb s + smsz (s_n s))); [exact M1 | rewrite Z.add_mod, M1, M3 by lia; reflexivity | lia | | exact H1 | rewrite E; exact H2 | | |].
- pose proof (rta_sp0 Σ m HA) as ((X1 & X2) & _). unfold l_ACEIL, rtA_sp0, sp_window_hi, STACK_WIN in *. lia.
- intros f k' Hin. destruct (sep_frame Σ m HA f k' Hin) as (X & Y & _). unfold apart in Hf. lia.
- unfold apart in Hf. lia.
- lia.
Qed.

Lemma av_schunk : forall k s, nth_error (sec Σ) k = Some s -> schunk_avoid W s.
Proof.
intros k s Hk. unfold schunk_avoid. destruct (map_geo k s Hk) as (Hn & (G1 & G2 & G3 & G4 & G5) & Hf & M2 & Hroom).
assert (M1 : s_mb s mod 8 = 0) by (apply (mod8_of _ 4096 ltac:(lia) G2); exists 512; reflexivity).
apply Z.mod_divide in M1; [|lia]. destruct M1 as [a0 E1]. apply Z.mod_divide in M2; [|lia]. destruct M2 as [q E2].
set (u0 := (s_n s + 7) / 8). assert (E3 : ru8 (s_n s) = u0 * 8) by (unfold ru8, u0; ring).
assert (Hu0 : 0 <= u0) by (apply Z.div_pos; lia).
assert (EA : shad (s_mb s) = a0 + SHB) by (unfold shad; rewrite E1, Z.div_mul by lia; reflexivity).
assert (EM : smsz (s_n s) / 8 = 512 * q) by (rewrite E2; replace (q * 4096) with ((512 * q) * 8) by ring; apply Z.div_mul; lia).
assert (EU : ru8 (s_n s) / 8 = u0) by (rewrite E3; apply Z.div_mul; lia).
assert (Eb : shad (s_mb s + 4096 + 2048) = a0 + 768 + SHB).
{ unfold shad. rewrite E1. replace (a0 * 8 + 4096 + 2048) with ((a0 + 768) * 8) by ring. rewrite Z.div_mul by lia. reflexivity. }
assert (Ec : shad (s_mb s + 4096 + 2048 + ru8 (s_n s)) = a0 + 768 + u0 + SHB).
{ unfold shad. rewrite E1, E3. replace (a0 * 8 + 4096 + 2048 + u0 * 8) with ((a0 + 768 + u0) * 8) by ring. rewrite Z.div_mul by lia. reflexivity. }
assert (Ed : (smsz (s_n s) - 4096 - 2048 - ru8 (s_n s)) / 8 = 512 * q - 768 - u0).
{ rewrite E2, E3. replace (q * 4096 - 4096 - 2048 - u0 * 8) with ((512 * q - 768 - u0) * 8) by ring. apply Z.div_mul. lia. }
unfold s_ubeg in *.
split; [apply (R_secmap k s); [exact Hk | lia | lia | intros _; unfold s_ubeg; lia]|].
split; [apply (R_secmap k s); [exact Hk | lia | lia | intros _; unfold s_ubeg; lia]|].
split; [apply (R_secmap k s); [exact Hk | lia | destruct (s_quar s); lia | intros Hq; rewrite Hq; unfold s_ubeg; lia]|].
split; [apply (ac_map_shad k s); [exact Hk | lia | rewrite EM, EA; change ((4096 + 2048) / 8) with 768; lia]|].
split; [apply (ac_map_shad k s); [exact Hk | rewrite Eb, EA; lia |]|].
- destruct (s_quar s); [rewrite fdrun_len, EU | rewrite (ushadow_len (s_n s) ltac:(lia)), EU]; rewrite Eb, EM, EA; lia.
- apply (ac_map_shad k s); [exact Hk | rewrite Ec, EA; lia | rewrite Ec, Ed, EM, EA; lia].
Qed.

Lemma av_sec : sec_avoid W Σ.
Proof.
split; [apply ac_lits; vm_compute; reflexivity|]. pose proof (geo_wf Σ m HA) as (_ & _ & _ & HS & _). destruct HS as (_ & Hn & _).
apply ac_PAB; lia.
Qed.

Lemma av_quar : quar_avoid W Σ.
Proof.
split; [unfold qcacheT; apply ac_T; lia|]. split; [apply ac_lits; vm_compute; reflexivity|].
pose proof (geo_wf Σ m HA) as (_ & _ & _ & _ & HQ & _). destruct HQ as (_ & _ & HB & _).
apply Forall_forall. intros b Hb. destruct (proj1 (Forall_forall _ _) HB b Hb) as (i & Hi & ->).
apply (ac_slot 24 i CkBatch); [lia | exact Hi | lia | change (ClassSize 24) with 8192; lia | intros n' E; discriminate E].
Qed.

Lemma av_dep : dep_avoid W L.
Proof. split; [apply ac_lits; vm_compute; reflexivity|]. split; [apply ac_DNB | apply ac_SSB]; lia. Qed.

Lemma av_ia : dsjl W ia_lits.
Proof. apply ac_lits. vm_compute. reflexivity. Qed.

Lemma av_static_shad : Forall (fun r => disjoint_from W (shad (fst r)) (shad (snd r - 1) + 1 - shad (fst r))) CS_ACC.
Proof.
apply Forall_forall. intros r Hr.
assert (Hlh : 0x10000 <= fst r /\ fst r < snd r /\ snd r <= 0x651d38) by (unfold CS_ACC in Hr; repeat (destruct Hr as [Hr|Hr]; [subst r; cbn; lia|]); destruct Hr).
pose proof (geo_grant Σ m HA (l_FSB L) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as (_ & _ & _ & _ & G5).
apply (R_shad 0x10000 SEGTOP_A); [reflexivity | reflexivity | lia | unfold SEGTOP_A; lia | | | | |].
- unfold shad. apply Z.add_le_mono_r. apply Z.div_le_mono; lia.
- unfold shad, SEGTOP_A. assert ((snd r - 1) / 8 < 0xca400) by (apply Z.div_lt_upper_bound; lia). change (0x652000 / 8) with 0xca400. lia.
- intros f k Hin. destruct (sep_frame Σ m HA f k Hin) as (X & Y & _). unfold SEGTOP_A in *. lia.
- unfold SEGTOP_A in *. lia.
- pose proof (rta_sp0_range Σ m HA) as HrS. unfold l_ACEIL, rtA_sp0 in *. lia.
Qed.

End CompStk.
