(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cy X1cp X1cj X1dd X1cg X1cs X1cm X1da.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X00b X0j1 X0gi X0hr
X0j3 X0hi X0hh X0hn X0j0 X0hb X0il X0gp X0h2 X0j4 X0hf
X0fy X0fg X0da X0g4 X0d8 X0fq X0e4 X0e8.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r0 X0ra X173 X18c X19m X183 X182 X188 X19k X17w X196 X17a X17n X19n X180 X16j X161 X13v X16p X13t X16b X14p X14t.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X173 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19m OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X183 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X182 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X188 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19k OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17w OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X196 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17a OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17n OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19n OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X180 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16j OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X161 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13v OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16p OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13t OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16b OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14p OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14t.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Definition CONSTS_LITS : list (Z * Z) :=
[ (1057912, 1057936); (1057936, 1057937); (0xfc0f8, 0xfc100); (0xfc108, 0xfc110); (0x195560, 0x195568); (0x197678, 0x197680);
(0x1976ec, 0x1976ed); (0x105320, 0x105321); (0x105324, 0x105328); (0x638c40, 0x638c48); (0x65a040, 0x65a048);
(0xfc118, 0xfc138); (0x105ab8, 0x105ac0); (0x1067a0, 0x1067b8); (0xfc138, 0xfc140); (0xfe040, 0xfe048); (0x10531c, 0x10531d);
(0x197660, 0x197668); (1032472, 1032480); (1071800, 1071808); (1032560, 1032568); (1071808, 1071812);
(0x1976dd, 0x1976de); (0x1976e4, 0x1976e5); (0xfc110, 0xfc118); (0xfc140, 0xfc148); (0xfe038, 0xfe040); (0x1032d5, 0x1032d6);
(0x1067bc, 0x1067c0); (0x19760a, 0x19760b); (0xfce58, 0xfce60); (0xfce58, 0xfce60); (0xfcc80, 0xfcc88); (0x106799, 0x10679a);
(0xfdef8, 0xfdf00); (0xfdfe8, 0xfdff0); (0xfded0, 0xfded8); (0x1976e3, 0x1976e4); (0x103278, 0x103280); (0x103280, 0x103284);
(0x187d22, 0x187d23); (0x1032e4, 0x1032e8); (0x1032ec, 0x1032f0); (0x10330d, 0x10330e); (0x638ca8, 0x638cac); (0xfcd70, 0xfcd78);
(0x197580, 0x197588); (0x197588, 0x197590); (0x102770, 0x102788); (0x1032e8, 0x1032ec);
(0xfdf08, 0xfdf18); (0x103370, 0x103378); (0xf7f78, 0xf7f88); (0xfc010, 0xfc018); (0xfc0e8, 0xfc0f8); (0xfcd78, 0xfcd88);
(0xfce00, 0xfce10); (0xfce88, 0xfce98); (0xfdec8, 0xfded0); (0xfdf28, 0xfdf40); (0x1032d0, 0x1032d4); (0x19763c, 0x19763d);
(0x197960, 0x197961);

(0xfc158, 0xfc160); (0x1976c3, 0x1976c4); (0x1976dc, 0x1976dd); (0x658f58, 0x658f60);

(0xfdee8, 0xfdef8); (0x1976e6, 0x1976e8);

(0xf8380, 0xf8450); (0xf8480, 0xf84e0); (0xf8500, 0xf8558); (0xf8580, 0xf85d8); (0xf8600, 0xf8658); (0xf8680, 0xf86d8);
(0xf8700, 0xf8758); (0xf8780, 0xf87d8); (0xf8800, 0xf8858); (0xf8880, 0xf88d8); (0xf8900, 0xf8910); (0xf8920, 0xf8938);
(0xf8960, 0xf8970); (0xf8980, 0xf8998); (0xf89c0, 0xf89d0); (0xf89e0, 0xf89f8); (0xf8a20, 0xf8a30); (0xf8a40, 0xf8a58);
(0xf8a80, 0xf8a98); (0xf8ac0, 0xf8ad8); (0xf8b00, 0xf8b60); (0xf8b80, 0xf8be0); (0xf8c00, 0xf8c18); (0xf8c40, 0xf8c98);
(0xf8cc0, 0xf8d18); (0xf8d40, 0xf8d98); (0xf8dc0, 0xf8e18); (0xf8e40, 0xf8f18); (0xf8f40, 0xf8f58); (0xf8f80, 0xf8f98);
(0xf8fc0, 0xf9098); (0xfcd90, 0xfcd98); (0xfcd98, 0xfcda0); (0xfcda0, 0xfcda8); (0xfcda8, 0xfcdb0); (0xfcdb0, 0xfcdb8);
(0xfcdb8, 0xfcdc0); (0xfcdc0, 0xfcdc8); (0xfcdc8, 0xfcdd0); (0xfcdd0, 0xfcdd8); (0xfcdd8, 0xfcde0); (0xfcde0, 0xfcde8);
(0xfcde8, 0xfcdf0); (0xfcdf0, 0xfcdf8); (0xfcdf8, 0xfce00) ].

Local Lemma In_CONSTS_LITS_b : forall e : Z * Z,
existsb (fun p => andb (Z.eqb (fst p) (fst e)) (Z.eqb (snd p) (snd e))) CONSTS_LITS = true -> In e CONSTS_LITS.
Proof.
intros [x y] H. apply existsb_exists in H. destruct H as ([a b] & Hin & Hb). apply andb_true_iff in Hb.
destruct Hb as [H1 H2]. cbn [fst snd] in H1, H2. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst a b. exact Hin.
Qed.

Lemma consts_rngs_kind : forall L r, In r (consts_rngs L) ->
In r CONSTS_LITS \/ (l_T L <= fst r /\ snd r <= l_T L + 0x30) \/ r = (l_T L + 0xc60, l_T L + 0xc60 + 1)
\/ (l_TCX L <= fst r /\ snd r <= l_TCX L + 0x10000).
Proof.
intros L r Hr. unfold consts_rngs in Hr. unfold_consts.

repeat (destruct Hr as [<-|Hr]; [first [solve [left; lazymatch goal with |- In ?e _ =>
lazymatch e with context [L] => fail | _ => idtac end end;
apply In_CONSTS_LITS_b; vm_compute; reflexivity]
| solve [right; left; cbn [fst snd]; lia] | solve [right; right; left; reflexivity]
| solve [right; right; right; cbn [fst snd]; lia]] |]).
destruct Hr.
Qed.

Lemma dsjb_all : forall V l, forallb (fun r => dsjb V (fst r) (snd r - fst r)) l = true ->
Forall (fun r => disjoint_from V (fst r) (snd r - fst r)) l.
Proof.
intros V l H. apply Forall_forall. intros r Hr. exact (dsjb_sound _ _ _ (proj1 (forallb_forall _ _) H r Hr)).
Qed.
Lemma dsjb_all' : forall V l, forallb (fun r => dsjb V (fst r) (snd r)) l = true -> Forall (fun r => disjoint_from V (fst r) (snd r)) l.
Proof.
intros V l H. apply Forall_forall. intros r Hr. exact (dsjb_sound _ _ _ (proj1 (forallb_forall _ _) H r Hr)).
Qed.

Lemma outside_dsj1 : forall V x, outside V x -> disjoint_from V x 1.
Proof. induction V as [|[lo hi] V IH]; intros x H; cbn in *; [exact I|]. destruct H as [H1 H2]. split; [lia | exact (IH x H2)]. Qed.

Definition DEP_LITS : list (Z * Z) :=
[(0x1e7998, 0x5e7998 + 4 - 0x1e7998); (0x5e79a8, 8); (0x1d7988, 8); (0x1d7998, 0x1d79a0 + 4 - 0x1d7998)].

Lemma ris_of_whole : forall SB (W : list ivl) (DC : list Z), (forall a n, RIS_of SB <= a -> a + n <= RIS_of SB + 4096 -> disjoint_from W a n) ->
forall c a n, 1 <= c <= 31 -> ~ In c DC -> rinfo (RIS_of SB) c <= a -> a + n <= rinfo (RIS_of SB) c + 120 -> disjoint_from W a n.
Proof. intros SB W DC H c a n Hc _ H1 H2. apply H; unfold rinfo in *; lia. Qed.

Section FKit.
Variables (Σ : rtsA) (m : mem) (W : list ivl) (D : list (Z * nat)) (DS : list nat) (TZ IZ : list ivl) (usp : Z) (DC : list Z).
Hypothesis HG : geo_ok Σ.
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation SB := (l_SB (lay Σ)).

Hypothesis HW_img : forall a n, 0x10000 <= a -> a + n <= SEGTOP_A -> disjoint_from IZ a n -> disjoint_from W a n.
Hypothesis HW_T : forall a n, T <= a -> a + n <= T + 4096 -> disjoint_from TZ a n -> disjoint_from W a n.
Hypothesis HW_grant : forall i b gn a n, nth_error (startup_grants L) i = Some (b, gn) -> (i = 1 \/ i = 3 \/ i = 4 \/ i = 5)%nat ->
b <= a -> a + n <= b + gn -> disjoint_from W a n.

Hypothesis HW_ris : forall c a n, 1 <= c <= 31 -> ~ In c DC -> rinfo (RIS_of SB) c <= a -> a + n <= rinfo (RIS_of SB) c + 120 ->
disjoint_from W a n.
Hypothesis HW_fa : forall c a n, 1 <= c <= 31 -> ~ In c DC -> fa SB c <= a -> a + n <= fa SB c + kFaCap -> disjoint_from W a n.
Hypothesis HW_slot : forall c i st a n, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some st -> ~ In (c, i) D ->
p_abeg SB c i <= a -> a + n <= p_abeg SB c i + ClassSize c -> disjoint_from W a n.
Hypothesis HW_shad_slot : forall c i st a n, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some st -> ~ In (c, i) D ->
shad (p_abeg SB c i) <= a -> a + n <= shad (p_abeg SB c i + ClassSize c) -> disjoint_from W a n.
Hypothesis HW_shad_reg : forall c a n, 1 <= c <= 31 -> ~ In c DC -> shad (rb SB c + ClassSize c * Z.of_nat (length (r_st (pr Σ c)))) <= a ->
a + n <= shad (rb SB c + 2 ^ 32) -> disjoint_from W a n.
Hypothesis HW_shad_app : forall lo hi a n, 0 <= lo -> hi <= 2 ^ 47 -> (hi <= l_PRB L \/ l_PRB L + 0x2000011000 <= lo) ->
(forall k s, nth_error (sec Σ) k = Some s -> In k DS -> hi <= s_mb s \/ s_mb s + smsz (s_n s) <= lo) ->
shad lo <= a -> a + n <= shad hi -> disjoint_from W a n.
Hypothesis HW_secmap : forall k s a n, nth_error (sec Σ) k = Some s -> ~ In k DS -> s_mb s <= a -> a + n <= s_mb s + smsz (s_n s) ->
disjoint_from W a n.

Lemma fk_aceil : 2 ^ 44 + SHB <= l_ACEIL L /\ l_ACEIL L <= 2 ^ 47.
Proof. pose proof (g_aceil Σ HG) as (X & Y & _). lia. Qed.

Lemma fk_prb : 0 < l_PRB L /\ l_PRB L + 0x2000011000 <= l_ACEIL L /\ SEGTOP_A <= l_PRB L /\ l_PRB L <= SB
/\ SB + 2 ^ 37 + 4096 <= l_PRB L + 0x2000011000.
Proof.
pose proof (g_prb Σ HG) as (P1 & P2 & P3).
pose proof (g_grant Σ HG (l_PRB L) 0x2000011000 ltac:(unfold startup_grants; left; reflexivity)) as (G1 & _ & G3 & _ & G5).
unfold SEGTOP_A in *. repeat split; lia.
Qed.

Lemma fk_slot : forall c i st, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some st ->
rb SB c <= p_abeg SB c i /\ p_abeg SB c i + ClassSize c <= rb SB c + ClassSize c * Z.of_nat (length (r_st (pr Σ c)))
/\ ClassSize c * Z.of_nat (length (r_st (pr Σ c))) <= r_muser (pr Σ c) <= kUserCap /\ 32 <= ClassSize c.
Proof.
intros c i st Hc Hn. pose proof HG as (_ & HR & _). destruct HR as (HR & _).
pose proof (HR c Hc) as (W1 & _ & W3 & _). pose proof (ClassSize_range c Hc) as (Hcs & Hm).
pose proof (proj1 (nth_error_Some (r_st (pr Σ c)) i) ltac:(rewrite Hn; discriminate)) as Hlt.
assert (Hx : Z.of_nat i * ClassSize c + ClassSize c <= ClassSize c * Z.of_nat (length (r_st (pr Σ c)))).
{ replace (ClassSize c * Z.of_nat (length (r_st (pr Σ c)))) with (Z.of_nat (length (r_st (pr Σ c))) * ClassSize c) by ring.
replace (Z.of_nat i * ClassSize c + ClassSize c) with ((Z.of_nat i + 1) * ClassSize c) by ring.
apply Z.mul_le_mono_nonneg_r; lia. }
assert (0 <= Z.of_nat i * ClassSize c) by (apply Z.mul_nonneg_nonneg; lia).
unfold p_abeg, rb in *. repeat split; lia.
Qed.

Lemma kv_reg : forall c, 1 <= c <= 31 -> ~ In c DC -> reg_avoid W SB c (pr Σ c).
Proof.
intros c Hc HDC. pose proof fk_prb as (P0 & P1 & P2 & P3 & P4). pose proof HG as (_ & HR & _). destruct HR as (HR & _).
pose proof (HR c Hc) as (W1 & W2 & W3 & W4 & W5 & W6 & _). pose proof (ClassSize_range c Hc) as (Hcs & Hm32).
assert (Hau : 0 <= ClassSize c * Z.of_nat (length (r_st (pr Σ c)))) by (apply Z.mul_nonneg_nonneg; lia).
unfold reg_avoid. split; [|split].
- apply (HW_ris c); [exact Hc | exact HDC | lia | lia].
- apply (HW_fa c); [exact Hc | exact HDC | lia | unfold kFaCap in *; lia].
- apply (HW_shad_reg c); [exact Hc | exact HDC | lia|].
pose proof (div8_add (rb SB c + ClassSize c * Z.of_nat (length (r_st (pr Σ c)))) (r_muser (pr Σ c) - ClassSize c * Z.of_nat (length (r_st (pr Σ c))))
ltac:(unfold rb; lia) ltac:(lia)) as X.
assert ((rb SB c + r_muser (pr Σ c)) / 8 <= (rb SB c + 2 ^ 32) / 8) by (apply Z.div_le_mono; unfold kUserCap in *; lia).
pose proof (Z.div_pos (r_muser (pr Σ c) - ClassSize c * Z.of_nat (length (r_st (pr Σ c)))) 8 ltac:(lia) ltac:(lia)).
replace (rb SB c + ClassSize c * Z.of_nat (length (r_st (pr Σ c))) + (r_muser (pr Σ c) - ClassSize c * Z.of_nat (length (r_st (pr Σ c)))))
with (rb SB c + r_muser (pr Σ c)) in X by ring.
unfold shad. lia.
Qed.

Lemma kv_pclass : forall c, 1 <= c <= 31 -> disjoint_from TZ (pc_addr T c) 80 -> pclass_avoid W T c.
Proof. intros c Hc HZ. unfold pclass_avoid. apply HW_T; [unfold pc_addr; lia | unfold pc_addr; lia | exact HZ]. Qed.

Lemma fk_shad_le : forall a x y, 0 <= a -> 0 <= x -> 0 <= y -> shad a + x / 8 + y / 8 <= shad (a + x + y).
Proof. intros a x y Ha Hx Hy. unfold shad. pose proof (div8_add3 a x y Ha Hx Hy). pose proof (Z.div_pos a 8 ltac:(lia) ltac:(lia)). lia. Qed.

Lemma fk_shad_le2 : forall a x, 0 <= a -> 0 <= x -> shad a + x / 8 <= shad (a + x).
Proof. intros a x Ha Hx. unfold shad. pose proof (div8_add a x Ha Hx). lia. Qed.

Lemma fk_shad_mono : forall a b, a <= b -> shad a <= shad b.
Proof. intros a b H. unfold shad. apply Z.add_le_mono_r. apply Z.div_le_mono; lia. Qed.

Lemma kv_pchunk_gen : forall c i st st', 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some st -> ~ In (c, i) D ->
(forall n, st' = CkAlloc n \/ st' = CkQuar n -> rz_size n + n <= ClassSize c /\ 0 <= n) -> pchunk_avoid W SB c i st'.
Proof.
intros c i st st' Hc Hn HD Hfit. pose proof (fk_slot c i st Hc Hn) as (S1 & S2 & S3 & S4). pose proof fk_prb as (P0 & _ & _ & P3 & _).
unfold pchunk_avoid. set (AB := p_abeg SB c i) in *. set (S := ClassSize c) in *.
assert (HAB : 0 <= AB) by (unfold rb in S1; lia).
assert (HS0 : 0 <= S / 8) by (apply Z.div_pos; lia).
assert (HSE : shad AB + S / 8 <= shad (AB + S)) by exact (fk_shad_le2 AB S HAB ltac:(lia)).
assert (SHS : forall a k, shad AB <= a -> a + k <= shad (AB + S) -> disjoint_from W a k) by (intros a k H1 H2; exact (HW_shad_slot c i st a k Hc Hn HD H1 H2)).
assert (SL : forall a k, AB <= a -> a + k <= AB + S -> disjoint_from W a k) by (intros a k H1 H2; exact (HW_slot c i st a k Hc Hn HD H1 H2)).
clear HD. destruct st' as [|n|n|].
- apply SHS; lia.
- destruct (Hfit n (or_introl eq_refl)) as (F1 & F2). destruct (fl_slot_room c n Hc F2 F1) as (R1 & R2). pose proof (fl_rz_facts n) as (R3 & R4).
pose proof (fl_ushadow_len n F2) as U. assert (Hu : 0 <= ru8 n) by (unfold ru8; pose proof (Z.div_pos (n + 7) 8 ltac:(lia) ltac:(lia)); lia).
assert (Hr8 : 0 <= rz_size n / 8) by (apply Z.div_pos; lia).
split; [apply SL; lia|].
split; [intros _; apply SL; lia|].
pose proof (fk_shad_le AB (rz_size n) (ru8 n) HAB ltac:(lia) Hu) as E1.
pose proof (fk_shad_mono (AB + rz_size n + ru8 n) (AB + S) ltac:(lia)) as E2.
split.
+ rewrite length_app, Nat2Z.inj_add, farun_lenZ, U by lia.
apply SHS; lia.
+ pose proof (fk_shad_le2 (AB + rz_size n + ru8 n) (S - rz_size n - ru8 n) ltac:(lia) ltac:(lia)) as E3.
replace (AB + rz_size n + ru8 n + (S - rz_size n - ru8 n)) with (AB + S) in E3 by ring.
pose proof (fk_shad_mono AB (AB + rz_size n + ru8 n) ltac:(lia)) as E4.
assert (0 <= (S - rz_size n - ru8 n) / 8) by (apply Z.div_pos; lia).
apply SHS; lia.
- destruct (Hfit n (or_intror eq_refl)) as (F1 & F2). destruct (fl_slot_room c n Hc F2 F1) as (R1 & R2). pose proof (fl_rz_facts n) as (R3 & R4).
assert (Hu : 0 <= ru8 n) by (unfold ru8; pose proof (Z.div_pos (n + 7) 8 ltac:(lia) ltac:(lia)); lia).
assert (Hr8 : 0 <= rz_size n / 8) by (apply Z.div_pos; lia). assert (Hu8 : 0 <= ru8 n / 8) by (apply Z.div_pos; lia).
assert (Hd8 : 0 <= (S - rz_size n - ru8 n) / 8) by (apply Z.div_pos; lia).
split; [apply SL; lia|].
split; [intros _; apply SL; lia|].
rewrite !length_app, !Nat2Z.inj_add, !farun_lenZ, fdrun_lenZ by lia.
pose proof (div8_add3 (rz_size n) (ru8 n) (S - rz_size n - ru8 n) ltac:(lia) Hu ltac:(lia)) as X.
replace (rz_size n + ru8 n + (S - rz_size n - ru8 n)) with S in X by ring.
apply SHS; lia.
- apply SHS; lia.
Qed.

Lemma kv_pchunk : forall c i st, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some st -> ~ In (c, i) D -> pchunk_avoid W SB c i st.
Proof.
intros c i st Hc Hn HD. apply (kv_pchunk_gen c i st st Hc Hn HD).
intros n Hs. pose proof HG as (_ & HR & _). destruct HR as (HR & _).
pose proof (HR c Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & W10 & _).
pose proof (proj1 (Forall_forall _ _) W10 _ (nth_error_In _ _ Hn)) as X. destruct Hs as [->| ->]; cbv beta iota in X; lia.
Qed.

Lemma fk_map : forall k s, nth_error (sec Σ) k = Some s ->
64513 <= s_n s /\ 0 < s_mb s /\ s_mb s + smsz (s_n s) <= l_ACEIL L /\ (s_mb s + smsz (s_n s) <= 0x10000 \/ SEGTOP_A <= s_mb s)
/\ apart (s_mb s) (smsz (s_n s)) (l_PRB L) 0x2000011000 /\ apart (s_mb s) (smsz (s_n s)) (l_FSB L) 0xb09000
/\ Forall (fun g => apart (s_mb s) (smsz (s_n s)) (fst g) (snd g)) (startup_grants L)
/\ 6144 + ru8 (s_n s) <= smsz (s_n s) /\ s_n s <= ru8 (s_n s)
/\ (forall k' s', nth_error (sec Σ) k' = Some s' -> k' <> k -> apart (s_mb s) (smsz (s_n s)) (s_mb s') (smsz (s_n s'))).
Proof.
intros k s Hk. pose proof HG as (_ & _ & HS & _). destruct HS as (_ & _ & _ & HSF & HSP & _).
pose proof (proj1 (Forall_forall _ _) HSF s (nth_error_In _ _ Hk)) as (Hn & (G1 & G2 & G3 & G4 & G5) & Hp & Hf & HGs).
assert (Hroom : 6144 + ru8 (s_n s) <= smsz (s_n s)).
{ unfold smsz, pg_up, needed, rounded, ru8. rewrite (rz_size_big (s_n s)) by lia. rewrite Z.max_l by lia. rewrite Z.max_l by lia.
assert (8 * ((s_n s + 7) / 8) + 2048 + 2048 <= (8 * ((s_n s + 7) / 8) + 2048 + 2048 + 4095) / 4096 * 4096); [|lia].
pose proof (Z.mod_pos_bound (8 * ((s_n s + 7) / 8) + 2048 + 2048 + 4095) 4096 ltac:(lia)).
pose proof (Z.div_mod (8 * ((s_n s + 7) / 8) + 2048 + 2048 + 4095) 4096 ltac:(lia)). lia. }
assert (Hu : s_n s <= ru8 (s_n s)) by (unfold ru8; pose proof (Z.div_mod (s_n s + 7) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (s_n s + 7) 8 ltac:(lia)); lia).
split; [lia|]. split; [exact G1|]. split; [exact G3|]. split; [exact G5|]. split; [exact Hp|]. split; [exact Hf|]. split; [exact HGs|].
split; [exact Hroom|]. split; [exact Hu|]. intros k' s' Hk' Hne. exact (HSP k k' s s' Hk Hk' (fun E => Hne (eq_sym E))).
Qed.

Lemma kv_schunk : forall k s, nth_error (sec Σ) k = Some s -> ~ In k DS -> schunk_avoid W s.
Proof.
intros k s Hk HD. pose proof (fk_map k s Hk) as (Hn & G1 & G3 & G5 & Hp & _ & _ & Hroom & Hu & HSP). pose proof fk_aceil as (_ & X).
assert (HDS : forall k' s', nth_error (sec Σ) k' = Some s' -> In k' DS -> s_mb s + smsz (s_n s) <= s_mb s' \/ s_mb s' + smsz (s_n s') <= s_mb s).
{ intros k' s' Hk' Hin. assert (k' <> k) by (intros ->; exact (HD Hin)). pose proof (HSP k' s' Hk' H) as Ha. unfold apart in Ha. lia. }
assert (Hoff : s_mb s + smsz (s_n s) <= l_PRB L \/ l_PRB L + 0x2000011000 <= s_mb s) by (unfold apart in Hp; lia).
assert (SH : forall a n, shad (s_mb s) <= a -> a + n <= shad (s_mb s + smsz (s_n s)) -> disjoint_from W a n).
{ intros a n H1 H2. apply (HW_shad_app (s_mb s) (s_mb s + smsz (s_n s))); [lia | lia | exact Hoff | exact HDS | exact H1 | exact H2]. }
assert (Hu8 : 0 <= ru8 (s_n s)) by lia.
unfold schunk_avoid.
split; [apply (HW_secmap k s); [exact Hk | exact HD | lia | lia]|].
split; [apply (HW_secmap k s); [exact Hk | exact HD | lia | lia]|].
split; [apply (HW_secmap k s); [exact Hk | exact HD | lia | destruct (s_quar s); lia]|].
pose proof (fk_shad_le2 (s_mb s) 6144 ltac:(lia) ltac:(lia)) as E1. change (6144 / 8) with 768 in E1.
pose proof (fk_shad_le2 (s_mb s + 6144) (ru8 (s_n s)) ltac:(lia) Hu8) as E2.
pose proof (fk_shad_le2 (s_mb s + 6144 + ru8 (s_n s)) (smsz (s_n s) - 6144 - ru8 (s_n s)) ltac:(lia) ltac:(lia)) as E3.
replace (s_mb s + 6144 + ru8 (s_n s) + (smsz (s_n s) - 6144 - ru8 (s_n s))) with (s_mb s + smsz (s_n s)) in E3 by ring.
assert (0 <= (smsz (s_n s) - 6144 - ru8 (s_n s)) / 8) by (apply Z.div_pos; lia). assert (0 <= ru8 (s_n s) / 8) by (apply Z.div_pos; lia).
pose proof (fk_shad_mono (s_mb s + 6144 + ru8 (s_n s)) (s_mb s + smsz (s_n s)) ltac:(lia)) as E4.
pose proof (fk_shad_mono (s_mb s) (s_mb s + 6144) ltac:(lia)) as E5.
pose proof (fk_shad_mono (s_mb s + 6144) (s_mb s + 6144 + ru8 (s_n s)) ltac:(lia)) as E6.
replace (s_mb s + 4096 + 2048) with (s_mb s + 6144) by ring.
split; [change ((4096 + 2048) / 8) with 768; apply SH; [lia | rewrite Z.max_r by lia; lia]|].
split.
- apply SH; [lia|]. destruct (s_quar s); [rewrite fdrun_lenZ by (apply Z.div_pos; lia) | rewrite (fl_ushadow_len (s_n s)) by lia]; lia.
- apply SH; [lia | ]. replace (smsz (s_n s) - 4096 - 2048 - ru8 (s_n s)) with (smsz (s_n s) - 6144 - ru8 (s_n s)) by ring.
rewrite Z.max_r by (apply Z.div_pos; lia). lia.
Qed.

Lemma kv_sec : Forall (fun r => disjoint_from IZ (fst r) (snd r)) sec_lits -> sec_avoid W Σ.
Proof.
intros HZ. split.
- apply Forall_forall. intros r Hr. apply HW_img; [| | exact (proj1 (Forall_forall _ _) HZ r Hr)];
unfold sec_lits in Hr; repeat (destruct Hr as [<-|Hr]; [cbn [fst snd]; unfold i_sec_chunks, i_sec_nres, i_sec_mutex, i_sec_page,
i_sec_range, i_sec_sorted, i_sec_bylog, i_gstat_alloc, INST, g_instance, SEGTOP_A; lia|]); destruct Hr.
- pose proof HG as (_ & _ & HS & _). destruct HS as (_ & Hn & _).
apply (HW_grant 1 (l_PAB L) 0x800000); [reflexivity | lia | lia | lia].
Qed.

Lemma kv_quar : disjoint_from TZ (qcacheT T) 32 -> Forall (fun r => disjoint_from IZ (fst r) (snd r)) [(i_q_global, 32); (i_q_cmutex, 4)] ->
(forall i, nth_error (r_st (pr Σ 24)) i = Some CkBatch -> ~ In (24, i) D) ->
Forall (fun b => exists i, nth_error (r_st (pr Σ 24)) i = Some CkBatch /\ fst b = p_abeg (l_SB (lay Σ)) 24 i) (ql Σ ++ qg Σ) ->
quar_avoid W Σ.
Proof.
intros HZ HI HB HBt. split; [apply HW_T; [unfold qcacheT; lia | unfold qcacheT; lia | exact HZ]|].
split.
- apply Forall_forall. intros r Hr. apply HW_img; [| | exact (proj1 (Forall_forall _ _) HI r Hr)];
destruct Hr as [<-|[<-|[]]]; cbn [fst snd]; unfold i_q_global, i_q_cmutex, INST, g_instance, SEGTOP_A; lia.
-
apply Forall_forall. intros b Hb. destruct (proj1 (Forall_forall _ _) HBt b Hb) as (i & Hi & E). rewrite E.
pose proof (fk_slot 24 i CkBatch ltac:(lia) Hi) as (S1 & S2 & S3 & S4). change (ClassSize 24) with 8192 in *.
apply (HW_slot 24 i CkBatch); [lia | exact Hi | exact (HB i Hi) | lia | change (ClassSize 24) with 8192; lia].
Qed.

Lemma kv_dep : Forall (fun r => disjoint_from IZ (fst r) (snd r)) DEP_LITS ->
(forall i b gn a n, nth_error (startup_grants L) i = Some (b, gn) -> (i = 6 \/ i = 7)%nat -> b <= a -> a + n <= b + gn -> disjoint_from W a n) ->
dep_avoid W L.
Proof.
intros HZ HD. split.
- apply Forall_forall. intros r Hr. apply HW_img; [| | exact (proj1 (Forall_forall _ _) HZ r Hr)];
unfold DEP_LITS in Hr; repeat (destruct Hr as [<-|Hr]; [cbn [fst snd]; unfold SEGTOP_A; lia|]); destruct Hr.
- split; [apply (HD 6%nat (l_DNB L) 0x100000); [reflexivity | lia | lia | lia]|].
apply (HD 7%nat (l_SSB L) 0x800000); [reflexivity | lia | lia | lia].
Qed.

Lemma kv_ia : Forall (fun r => disjoint_from IZ (fst r) (snd r)) ia_lits -> dsjl W ia_lits.
Proof.
intros HZ. apply Forall_forall. intros r Hr. apply HW_img; [| | exact (proj1 (Forall_forall _ _) HZ r Hr)];
unfold ia_lits in Hr; repeat (destruct Hr as [<-|Hr]; [cbn [fst snd]; unfold g_ia_word, IAP, SEGTOP_A; lia|]); destruct Hr.
Qed.

Lemma fk_fsb : forall a n, l_FSB L <= a -> a + n <= l_FSB L + 0xb09000 -> disjoint_from W a n.
Proof. intros a n H1 H2. exact (HW_grant 5 (l_FSB L) 0xb09000 a n eq_refl ltac:(lia) H1 H2). Qed.

Lemma fk_fsb_off : l_FSB L + 0xb09000 <= l_PRB L \/ l_PRB L + 0x2000011000 <= l_FSB L.
Proof. pose proof (g_apart Σ HG 0 5 _ _ ltac:(lia) eq_refl eq_refl) as X. cbn [fst snd] in X. unfold apart in X. lia. Qed.

Lemma fk_fsb_maps : forall k s, nth_error (sec Σ) k = Some s -> l_FSB L + 0xb09000 <= s_mb s \/ s_mb s + smsz (s_n s) <= l_FSB L.
Proof. intros k s Hk. pose proof (fk_map k s Hk) as (_ & _ & _ & _ & _ & Hf & _). unfold apart in Hf. lia. Qed.

Lemma kv_fs_cls : forall k, (k = 0 \/ k = 2 \/ k = 4 \/ k = 5 \/ k = 8)%nat -> fs_cls_avoid W (l_FSB L) (Z.of_nat k) (fs_of Σ k).
Proof.
intros k Hk. pose proof HG as (_ & _ & _ & HF). destruct HF as (F0 & F2 & F4 & _).
assert (Hwf : flags_ok (Z.of_nat k) (fss_flags (fs_of Σ k))) by (destruct Hk as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; [exact (proj1 F0) | exact (proj1 F2) | exact (proj1 (proj1 F4)) | exact (proj1 (proj1 (proj2 F4))) | exact (proj1 (proj2 (proj2 F4)))]).
destruct Hwf as [Hlen _].
assert (Hc : Z.of_nat k = 0 \/ Z.of_nat k = 2 \/ Z.of_nat k = 4 \/ Z.of_nat k = 5 \/ Z.of_nat k = 8) by (destruct Hk as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; cbn; lia).
pose proof (g_grant Σ HG (l_FSB L) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as (G1 & G2 & G3 & G4 & G5).
pose proof fk_aceil as (_ & X). pose proof (fl_flags_range _ Hc) as (R1 & R2). pose proof fk_fsb_off as Off.
unfold fs_cls_avoid. split; [apply fk_fsb; destruct Hc as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; lia|]. split.
- rewrite Hlen. apply fk_fsb; unfold fl_base; lia.
- intros p Hp _. pose proof (frame_addr_range (l_FSB L) (Z.of_nat k) p Hc Hp) as (A1 & A2). unfold kFakeStackSize in A2.
assert (Hfz : 0 < fsz (Z.of_nat k)) by (unfold fsz; destruct Hc as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; cbn; lia).
split; [apply fk_fsb; lia|].
pose proof (fk_shad_le2 (frame_addr (l_FSB L) (Z.of_nat k) p) (fsz (Z.of_nat k)) ltac:(lia) ltac:(lia)) as E.
apply (HW_shad_app (frame_addr (l_FSB L) (Z.of_nat k) p) (frame_addr (l_FSB L) (Z.of_nat k) p + fsz (Z.of_nat k))); [lia | lia | lia | | lia | lia].
intros k' s' Hk' _. pose proof (fk_fsb_maps k' s' Hk'). lia.
Qed.

Lemma kv_fs : Forall (fun r => disjoint_from IZ (fst r) (snd r)) fs_lits -> disjoint_from TZ (T + 48) 16 -> fs_avoid W Σ.
Proof.
intros HZ HT. pose proof (g_grant Σ HG (l_FSB L) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as (G1 & _).
unfold fs_avoid. split; [apply fk_fsb; lia|].
split; [exact (kv_fs_cls 0%nat ltac:(lia))|]. split; [exact (kv_fs_cls 2%nat ltac:(lia))|]. split; [split; [exact (kv_fs_cls 4%nat ltac:(lia))| split; [exact (kv_fs_cls 5%nat ltac:(lia))| exact (kv_fs_cls 8%nat ltac:(lia))]]|].
split.
{ apply Forall_forall. intros r Hr. apply HW_img; [| | exact (proj1 (Forall_forall _ _) HZ r Hr)];
unfold fs_lits in Hr; repeat (destruct Hr as [<-|Hr]; [cbn [fst snd]; unfold tpA, g_real_tls_get_addr, g_dtv_ptr, g_dtv1,
g_got_common_flags, g_intercept_tls_get_addr, g_got_verbosity, g_current_verbosity, g_tls_index, g_got_dtls_off, g_tls_dtls, SEGTOP_A; lia|]);
destruct Hr. }
split; [apply (HW_grant 4 (l_DTV L) 4096); [reflexivity | lia | lia | lia]|].
split; [apply HW_T; [lia | lia | exact HT]|].
apply Forall_forall. intros [f k] Hin. cbn [fst snd]. destruct (g_frame Σ HG f k Hin) as (X1 & X2 & X3). apply fk_fsb; lia.
Qed.

Lemma kv_shadow : shadow_avoid W L.
Proof.
pose proof fk_aceil as (X1 & X2). pose proof fk_prb as (P0 & P1 & P2 & _).
split.
- pose proof (fk_shad_le2 (l_ACEIL L) (2 ^ 47 - l_ACEIL L) ltac:(unfold SHB in *; lia) ltac:(lia)) as E.
replace (l_ACEIL L + (2 ^ 47 - l_ACEIL L)) with (2 ^ 47) in E by ring.
assert (0 <= (2 ^ 47 - l_ACEIL L) / 8) by (apply Z.div_pos; lia).
apply (HW_shad_app (l_ACEIL L) (2 ^ 47)); [unfold SHB in *; lia | lia | lia | | lia | rewrite Z.max_r by (apply Z.div_pos; lia); lia].
intros k s Hk _. pose proof (fk_map k s Hk) as (_ & _ & G3 & _). lia.
- apply Forall_forall. intros r Hr.
assert (Hlh : 0x10000 <= fst r /\ fst r < snd r /\ snd r <= 0x65a578) by (unfold CS_ACC in Hr; repeat (destruct Hr as [Hr|Hr]; [subst r; cbn; lia|]); destruct Hr).
apply (HW_shad_app 0x10000 SEGTOP_A); [lia | unfold SEGTOP_A; lia | unfold SEGTOP_A in *; lia | | apply fk_shad_mono; lia | ].
+ intros k s Hk _. pose proof (fk_map k s Hk) as (Hn & G1 & _ & G5 & _ & _ & _ & Hroom & Hu & _). unfold SEGTOP_A in *. lia.
+ assert ((snd r - 1) / 8 < 833024) by (apply Z.div_lt_upper_bound; lia).
assert (shad (snd r - 1) + 1 <= shad SEGTOP_A) by (unfold shad, SEGTOP_A; change (0x65b000 / 8) with 833024; lia). lia.
Qed.

Lemma kv_consts : Forall (fun r => disjoint_from IZ (fst r) (snd r - fst r)) CONSTS_LITS -> disjoint_from TZ T 0x30 ->
forall x, in_rngs (consts_rngs L) x -> x <> T + 0xc60 -> outside W x.
Proof.
intros HZ HTZ x Hx Hne. unfold in_rngs in Hx. apply Exists_exists in Hx as (r & Hr & Hrx). cbv beta in Hrx.
destruct (consts_rngs_kind L r Hr) as [Hl|[(H1 & H2)|[Er|(H1 & H2)]]].
- pose proof (proj1 (Forall_forall _ _) HZ r Hl) as Dr.
assert (Hrng : 0x10000 <= fst r /\ snd r <= SEGTOP_A) by (unfold CONSTS_LITS in Hl; repeat (destruct Hl as [<-|Hl]; [cbn; unfold SEGTOP_A; lia|]); destruct Hl).
apply (disjoint_outside W (fst r) (snd r - fst r)); [apply HW_img; [lia | lia | exact Dr] | lia].
- apply (disjoint_outside W x 1); [apply HW_T; [lia | lia | exact (dsj_sub TZ T 0x30 x 1 HTZ ltac:(lia) ltac:(lia))] | lia].
- rewrite Er in Hrx. cbn [fst snd] in Hrx. lia.
- apply (disjoint_outside W x 1); [|lia].
apply (HW_grant 3 (l_TCX L) 0x10000); [reflexivity | lia | lia | lia].
Qed.

Hypothesis HW_stack : forall a n, usp <= a -> a + n <= USTACK_TOP -> disjoint_from W a n.

Lemma kv_client : Forall (fun r => disjoint_from IZ (fst r) (snd r - fst r)) CLIENT_STATIC ->
forall (L' : list (Z * Z)), (forall p n, In (p, n) L' ->
(exists c i, 1 <= c <= 31 /\ nth_error (r_st (pr Σ c)) i = Some (CkAlloc n) /\ p = p_ubeg SB c i n /\ ~ In (c, i) D)
\/ (exists k s, nth_error (sec Σ) k = Some s /\ s_quar s = false /\ s_n s = n /\ p = s_ubeg s /\ ~ In k DS)) ->
forall x, aclient L' (frames Σ) usp x -> outside W x.
Proof.
intros HCS L' HL' x Hx. destruct Hx as [H|[H|[H|[H|H]]]].
- apply (disjoint_outside W x 1); [apply HW_stack; lia | lia].
- destruct H as ((lo & hi & Hin & Hlh) & _). pose proof (proj1 (Forall_forall _ _) HCS (lo, hi) Hin) as Dr. cbn [fst snd] in Dr.
apply (disjoint_outside W lo (hi - lo)); [|lia].
apply HW_img; [| | exact Dr]; unfold CLIENT_STATIC in Hin; destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; unfold SEGTOP_A; lia.
- destruct H as (p & n & Hin & Hpx). apply (disjoint_outside W p n); [|lia].
destruct (HL' p n Hin) as [(c & i & Hc & Hn & -> & HD)|(k & s & Hk & Hq & Hn' & -> & HD)].
+ pose proof (fk_slot c i _ Hc Hn) as (S1 & S2 & S3 & S4).
assert (Hfit : rz_size n + n <= ClassSize c /\ 0 <= n).
{ pose proof HG as (_ & HR & _). destruct HR as (HR & _).
pose proof (HR c Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & W10 & _).
pose proof (proj1 (Forall_forall _ _) W10 _ (nth_error_In _ _ Hn)) as X. cbv beta iota in X. lia. }
pose proof (fl_rz_facts n) as (R1 & R2).
apply (HW_slot c i (CkAlloc n)); [exact Hc | exact Hn | exact HD | unfold p_ubeg; lia | unfold p_ubeg; lia].
+ pose proof (fk_map k s Hk) as (_ & _ & _ & _ & _ & _ & _ & Hroom & Hu & _).
apply (HW_secmap k s); [exact Hk | exact HD | unfold s_ubeg; lia | unfold s_ubeg; rewrite <- Hn'; lia].
- destruct H as (f & k & Hin & Hfx). apply (disjoint_outside W f (fs_size k - 8)); [|lia].
destruct (g_frame Σ HG f k Hin) as (Y1 & Y2 & Y3). apply fk_fsb; lia.
- destruct H as (f & k & Hin & Hfx). apply (disjoint_outside W (shad f) (shad (f + fs_size k) - shad f)); [|lia].
destruct (g_frame Σ HG f k Hin) as (Y1 & Y2 & Y3). pose proof fk_fsb_off as Off.
pose proof (g_grant Σ HG (l_FSB L) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as (G1 & _ & G3 & _).
pose proof fk_aceil as (_ & X).
apply (HW_shad_app f (f + fs_size k)); [lia | lia | lia | | lia | lia].
intros k' s' Hk' _. pose proof (fk_fsb_maps k' s' Hk'). lia.
Qed.

End FKit.
End B_TWIN.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Definition CONSTS_LITS : list (Z * Z) :=
[ (1023032, 1023056); (1023056, 1023057); (0xf3878, 0xf3880); (0xf3888, 0xf3890); (0x18cd20, 0x18cd28); (0x18ee38, 0x18ee40);
(0x18eeac, 0x18eead); (0xfcae0, 0xfcae1); (0xfcae4, 0xfcae8); (0x630400, 0x630408); (0x651800, 0x651808);
(0xf3898, 0xf38b8); (0xfd278, 0xfd280); (0xfdf60, 0xfdf78); (0xf38b8, 0xf38c0); (0xf57c0, 0xf57c8); (0xfcadc, 0xfcadd);
(0x18ee20, 0x18ee28); (997528, 997536); (1036920, 1036928); (997616, 997624); (1036928, 1036932);
(0x18ee9d, 0x18ee9e); (0x18eea4, 0x18eea5); (0xf3890, 0xf3898); (0xf38c0, 0xf38c8); (0xf57b8, 0xf57c0); (0xfaa95, 0xfaa96);
(0xfdf7c, 0xfdf80); (0x18edca, 0x18edcb); (0xf45d8, 0xf45e0); (0xf45d8, 0xf45e0); (0xf4400, 0xf4408); (0xfdf59, 0xfdf5a);
(0xf5678, 0xf5680); (0xf5768, 0xf5770); (0xf5650, 0xf5658); (0x18eea3, 0x18eea4); (0xfaa38, 0xfaa40); (0xfaa40, 0xfaa44);
(0x17f4e2, 0x17f4e3); (0xfaaa4, 0xfaaa8); (0xfaaac, 0xfaab0); (0xfaacd, 0xfaace); (0x630468, 0x63046c); (0xf44f0, 0xf44f8);
(0x18ed40, 0x18ed48); (0x18ed48, 0x18ed50); (0xf9f30, 0xf9f48); (0xfaaa8, 0xfaaac);
(0xf5688, 0xf5698); (0xfab30, 0xfab38); (0xef708, 0xef718); (0xf3790, 0xf3798); (0xf3868, 0xf3878); (0xf44f8, 0xf4508);
(0xf4580, 0xf4590); (0xf4608, 0xf4618); (0xf5648, 0xf5650); (0xf56a8, 0xf56c0); (0xfaa90, 0xfaa94); (0x18edfc, 0x18edfd);
(0x18f120, 0x18f121);

(0xf38d8, 0xf38e0); (0x18ee83, 0x18ee84); (0x18ee9c, 0x18ee9d); (0x650718, 0x650720);

(0xf5668, 0xf5678); (0x18eea6, 0x18eea8);

(0xefb00, 0xefbd0); (0xefc00, 0xefc60); (0xefc80, 0xefcd8); (0xefd00, 0xefd58); (0xefd80, 0xefdd8); (0xefe00, 0xefe58);
(0xefe80, 0xefed8); (0xeff00, 0xeff58); (0xeff80, 0xeffd8); (0xf0000, 0xf0058); (0xf0080, 0xf0090); (0xf00a0, 0xf00b8);
(0xf00e0, 0xf00f0); (0xf0100, 0xf0118); (0xf0140, 0xf0150); (0xf0160, 0xf0178); (0xf01a0, 0xf01b0); (0xf01c0, 0xf01d8);
(0xf0200, 0xf0218); (0xf0240, 0xf0258); (0xf0280, 0xf02e0); (0xf0300, 0xf0360); (0xf0380, 0xf0398); (0xf03c0, 0xf0418);
(0xf0440, 0xf0498); (0xf04c0, 0xf0518); (0xf0540, 0xf0598); (0xf05c0, 0xf0698); (0xf06c0, 0xf06d8); (0xf0700, 0xf0718);
(0xf0740, 0xf0818); (0xf4510, 0xf4518); (0xf4518, 0xf4520); (0xf4520, 0xf4528); (0xf4528, 0xf4530); (0xf4530, 0xf4538);
(0xf4538, 0xf4540); (0xf4540, 0xf4548); (0xf4548, 0xf4550); (0xf4550, 0xf4558); (0xf4558, 0xf4560); (0xf4560, 0xf4568);
(0xf4568, 0xf4570); (0xf4570, 0xf4578); (0xf4578, 0xf4580) ].

Local Lemma In_CONSTS_LITS_b : forall e : Z * Z,
existsb (fun p => andb (Z.eqb (fst p) (fst e)) (Z.eqb (snd p) (snd e))) CONSTS_LITS = true -> In e CONSTS_LITS.
Proof.
intros [x y] H. apply existsb_exists in H. destruct H as ([a b] & Hin & Hb). apply andb_true_iff in Hb.
destruct Hb as [H1 H2]. cbn [fst snd] in H1, H2. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst a b. exact Hin.
Qed.

Lemma consts_rngs_kind : forall L r, In r (consts_rngs L) ->
In r CONSTS_LITS \/ (l_T L <= fst r /\ snd r <= l_T L + 0x30) \/ r = (l_T L + 0xc60, l_T L + 0xc60 + 1)
\/ (l_TCX L <= fst r /\ snd r <= l_TCX L + 0x10000).
Proof.
intros L r Hr. unfold consts_rngs in Hr. unfold_consts.

repeat (destruct Hr as [<-|Hr]; [first [solve [left; lazymatch goal with |- In ?e _ =>
lazymatch e with context [L] => fail | _ => idtac end end;
apply In_CONSTS_LITS_b; vm_compute; reflexivity]
| solve [right; left; cbn [fst snd]; lia] | solve [right; right; left; reflexivity]
| solve [right; right; right; cbn [fst snd]; lia]] |]).
destruct Hr.
Qed.

Lemma dsjb_all : forall V l, forallb (fun r => dsjb V (fst r) (snd r - fst r)) l = true ->
Forall (fun r => disjoint_from V (fst r) (snd r - fst r)) l.
Proof.
intros V l H. apply Forall_forall. intros r Hr. exact (dsjb_sound _ _ _ (proj1 (forallb_forall _ _) H r Hr)).
Qed.
Lemma dsjb_all' : forall V l, forallb (fun r => dsjb V (fst r) (snd r)) l = true -> Forall (fun r => disjoint_from V (fst r) (snd r)) l.
Proof.
intros V l H. apply Forall_forall. intros r Hr. exact (dsjb_sound _ _ _ (proj1 (forallb_forall _ _) H r Hr)).
Qed.

Lemma outside_dsj1 : forall V x, outside V x -> disjoint_from V x 1.
Proof. induction V as [|[lo hi] V IH]; intros x H; cbn in *; [exact I|]. destruct H as [H1 H2]. split; [lia | exact (IH x H2)]. Qed.

Definition DEP_LITS : list (Z * Z) :=
[(0x1df158, 0x5df158 + 4 - 0x1df158); (0x5df168, 8); (0x1cf148, 8); (0x1cf158, 0x1cf160 + 4 - 0x1cf158)].

Lemma ris_of_whole : forall SB (W : list ivl) (DC : list Z), (forall a n, RIS_of SB <= a -> a + n <= RIS_of SB + 4096 -> disjoint_from W a n) ->
forall c a n, 1 <= c <= 31 -> ~ In c DC -> rinfo (RIS_of SB) c <= a -> a + n <= rinfo (RIS_of SB) c + 120 -> disjoint_from W a n.
Proof. intros SB W DC H c a n Hc _ H1 H2. apply H; unfold rinfo in *; lia. Qed.

Section FKit.
Variables (Σ : rtsA) (m : mem) (W : list ivl) (D : list (Z * nat)) (DS : list nat) (TZ IZ : list ivl) (usp : Z) (DC : list Z).
Hypothesis HG : geo_ok Σ.
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation SB := (l_SB (lay Σ)).

Hypothesis HW_img : forall a n, 0x10000 <= a -> a + n <= SEGTOP_A -> disjoint_from IZ a n -> disjoint_from W a n.
Hypothesis HW_T : forall a n, T <= a -> a + n <= T + 4096 -> disjoint_from TZ a n -> disjoint_from W a n.
Hypothesis HW_grant : forall i b gn a n, nth_error (startup_grants L) i = Some (b, gn) -> (i = 1 \/ i = 3 \/ i = 4 \/ i = 5)%nat ->
b <= a -> a + n <= b + gn -> disjoint_from W a n.

Hypothesis HW_ris : forall c a n, 1 <= c <= 31 -> ~ In c DC -> rinfo (RIS_of SB) c <= a -> a + n <= rinfo (RIS_of SB) c + 120 ->
disjoint_from W a n.
Hypothesis HW_fa : forall c a n, 1 <= c <= 31 -> ~ In c DC -> fa SB c <= a -> a + n <= fa SB c + kFaCap -> disjoint_from W a n.
Hypothesis HW_slot : forall c i st a n, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some st -> ~ In (c, i) D ->
p_abeg SB c i <= a -> a + n <= p_abeg SB c i + ClassSize c -> disjoint_from W a n.
Hypothesis HW_shad_slot : forall c i st a n, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some st -> ~ In (c, i) D ->
shad (p_abeg SB c i) <= a -> a + n <= shad (p_abeg SB c i + ClassSize c) -> disjoint_from W a n.
Hypothesis HW_shad_reg : forall c a n, 1 <= c <= 31 -> ~ In c DC -> shad (rb SB c + ClassSize c * Z.of_nat (length (r_st (pr Σ c)))) <= a ->
a + n <= shad (rb SB c + 2 ^ 32) -> disjoint_from W a n.
Hypothesis HW_shad_app : forall lo hi a n, 0 <= lo -> hi <= 2 ^ 47 -> (hi <= l_PRB L \/ l_PRB L + 0x2000011000 <= lo) ->
(forall k s, nth_error (sec Σ) k = Some s -> In k DS -> hi <= s_mb s \/ s_mb s + smsz (s_n s) <= lo) ->
shad lo <= a -> a + n <= shad hi -> disjoint_from W a n.
Hypothesis HW_secmap : forall k s a n, nth_error (sec Σ) k = Some s -> ~ In k DS -> s_mb s <= a -> a + n <= s_mb s + smsz (s_n s) ->
disjoint_from W a n.

Lemma fk_aceil : 2 ^ 44 + SHB <= l_ACEIL L /\ l_ACEIL L <= 2 ^ 47.
Proof. pose proof (g_aceil Σ HG) as (X & Y & _). lia. Qed.

Lemma fk_prb : 0 < l_PRB L /\ l_PRB L + 0x2000011000 <= l_ACEIL L /\ SEGTOP_A <= l_PRB L /\ l_PRB L <= SB
/\ SB + 2 ^ 37 + 4096 <= l_PRB L + 0x2000011000.
Proof.
pose proof (g_prb Σ HG) as (P1 & P2 & P3).
pose proof (g_grant Σ HG (l_PRB L) 0x2000011000 ltac:(unfold startup_grants; left; reflexivity)) as (G1 & _ & G3 & _ & G5).
unfold SEGTOP_A in *. repeat split; lia.
Qed.

Lemma fk_slot : forall c i st, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some st ->
rb SB c <= p_abeg SB c i /\ p_abeg SB c i + ClassSize c <= rb SB c + ClassSize c * Z.of_nat (length (r_st (pr Σ c)))
/\ ClassSize c * Z.of_nat (length (r_st (pr Σ c))) <= r_muser (pr Σ c) <= kUserCap /\ 32 <= ClassSize c.
Proof.
intros c i st Hc Hn. pose proof HG as (_ & HR & _). destruct HR as (HR & _).
pose proof (HR c Hc) as (W1 & _ & W3 & _). pose proof (ClassSize_range c Hc) as (Hcs & Hm).
pose proof (proj1 (nth_error_Some (r_st (pr Σ c)) i) ltac:(rewrite Hn; discriminate)) as Hlt.
assert (Hx : Z.of_nat i * ClassSize c + ClassSize c <= ClassSize c * Z.of_nat (length (r_st (pr Σ c)))).
{ replace (ClassSize c * Z.of_nat (length (r_st (pr Σ c)))) with (Z.of_nat (length (r_st (pr Σ c))) * ClassSize c) by ring.
replace (Z.of_nat i * ClassSize c + ClassSize c) with ((Z.of_nat i + 1) * ClassSize c) by ring.
apply Z.mul_le_mono_nonneg_r; lia. }
assert (0 <= Z.of_nat i * ClassSize c) by (apply Z.mul_nonneg_nonneg; lia).
unfold p_abeg, rb in *. repeat split; lia.
Qed.

Lemma kv_reg : forall c, 1 <= c <= 31 -> ~ In c DC -> reg_avoid W SB c (pr Σ c).
Proof.
intros c Hc HDC. pose proof fk_prb as (P0 & P1 & P2 & P3 & P4). pose proof HG as (_ & HR & _). destruct HR as (HR & _).
pose proof (HR c Hc) as (W1 & W2 & W3 & W4 & W5 & W6 & _). pose proof (ClassSize_range c Hc) as (Hcs & Hm32).
assert (Hau : 0 <= ClassSize c * Z.of_nat (length (r_st (pr Σ c)))) by (apply Z.mul_nonneg_nonneg; lia).
unfold reg_avoid. split; [|split].
- apply (HW_ris c); [exact Hc | exact HDC | lia | lia].
- apply (HW_fa c); [exact Hc | exact HDC | lia | unfold kFaCap in *; lia].
- apply (HW_shad_reg c); [exact Hc | exact HDC | lia|].
pose proof (div8_add (rb SB c + ClassSize c * Z.of_nat (length (r_st (pr Σ c)))) (r_muser (pr Σ c) - ClassSize c * Z.of_nat (length (r_st (pr Σ c))))
ltac:(unfold rb; lia) ltac:(lia)) as X.
assert ((rb SB c + r_muser (pr Σ c)) / 8 <= (rb SB c + 2 ^ 32) / 8) by (apply Z.div_le_mono; unfold kUserCap in *; lia).
pose proof (Z.div_pos (r_muser (pr Σ c) - ClassSize c * Z.of_nat (length (r_st (pr Σ c)))) 8 ltac:(lia) ltac:(lia)).
replace (rb SB c + ClassSize c * Z.of_nat (length (r_st (pr Σ c))) + (r_muser (pr Σ c) - ClassSize c * Z.of_nat (length (r_st (pr Σ c)))))
with (rb SB c + r_muser (pr Σ c)) in X by ring.
unfold shad. lia.
Qed.

Lemma kv_pclass : forall c, 1 <= c <= 31 -> disjoint_from TZ (pc_addr T c) 80 -> pclass_avoid W T c.
Proof. intros c Hc HZ. unfold pclass_avoid. apply HW_T; [unfold pc_addr; lia | unfold pc_addr; lia | exact HZ]. Qed.

Lemma fk_shad_le : forall a x y, 0 <= a -> 0 <= x -> 0 <= y -> shad a + x / 8 + y / 8 <= shad (a + x + y).
Proof. intros a x y Ha Hx Hy. unfold shad. pose proof (div8_add3 a x y Ha Hx Hy). pose proof (Z.div_pos a 8 ltac:(lia) ltac:(lia)). lia. Qed.

Lemma fk_shad_le2 : forall a x, 0 <= a -> 0 <= x -> shad a + x / 8 <= shad (a + x).
Proof. intros a x Ha Hx. unfold shad. pose proof (div8_add a x Ha Hx). lia. Qed.

Lemma fk_shad_mono : forall a b, a <= b -> shad a <= shad b.
Proof. intros a b H. unfold shad. apply Z.add_le_mono_r. apply Z.div_le_mono; lia. Qed.

Lemma kv_pchunk_gen : forall c i st st', 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some st -> ~ In (c, i) D ->
(forall n, st' = CkAlloc n \/ st' = CkQuar n -> rz_size n + n <= ClassSize c /\ 0 <= n) -> pchunk_avoid W SB c i st'.
Proof.
intros c i st st' Hc Hn HD Hfit. pose proof (fk_slot c i st Hc Hn) as (S1 & S2 & S3 & S4). pose proof fk_prb as (P0 & _ & _ & P3 & _).
unfold pchunk_avoid. set (AB := p_abeg SB c i) in *. set (S := ClassSize c) in *.
assert (HAB : 0 <= AB) by (unfold rb in S1; lia).
assert (HS0 : 0 <= S / 8) by (apply Z.div_pos; lia).
assert (HSE : shad AB + S / 8 <= shad (AB + S)) by exact (fk_shad_le2 AB S HAB ltac:(lia)).
assert (SHS : forall a k, shad AB <= a -> a + k <= shad (AB + S) -> disjoint_from W a k) by (intros a k H1 H2; exact (HW_shad_slot c i st a k Hc Hn HD H1 H2)).
assert (SL : forall a k, AB <= a -> a + k <= AB + S -> disjoint_from W a k) by (intros a k H1 H2; exact (HW_slot c i st a k Hc Hn HD H1 H2)).
clear HD. destruct st' as [|n|n|].
- apply SHS; lia.
- destruct (Hfit n (or_introl eq_refl)) as (F1 & F2). destruct (fl_slot_room c n Hc F2 F1) as (R1 & R2). pose proof (fl_rz_facts n) as (R3 & R4).
pose proof (fl_ushadow_len n F2) as U. assert (Hu : 0 <= ru8 n) by (unfold ru8; pose proof (Z.div_pos (n + 7) 8 ltac:(lia) ltac:(lia)); lia).
assert (Hr8 : 0 <= rz_size n / 8) by (apply Z.div_pos; lia).
split; [apply SL; lia|].
split; [intros _; apply SL; lia|].
pose proof (fk_shad_le AB (rz_size n) (ru8 n) HAB ltac:(lia) Hu) as E1.
pose proof (fk_shad_mono (AB + rz_size n + ru8 n) (AB + S) ltac:(lia)) as E2.
split.
+ rewrite length_app, Nat2Z.inj_add, farun_lenZ, U by lia.
apply SHS; lia.
+ pose proof (fk_shad_le2 (AB + rz_size n + ru8 n) (S - rz_size n - ru8 n) ltac:(lia) ltac:(lia)) as E3.
replace (AB + rz_size n + ru8 n + (S - rz_size n - ru8 n)) with (AB + S) in E3 by ring.
pose proof (fk_shad_mono AB (AB + rz_size n + ru8 n) ltac:(lia)) as E4.
assert (0 <= (S - rz_size n - ru8 n) / 8) by (apply Z.div_pos; lia).
apply SHS; lia.
- destruct (Hfit n (or_intror eq_refl)) as (F1 & F2). destruct (fl_slot_room c n Hc F2 F1) as (R1 & R2). pose proof (fl_rz_facts n) as (R3 & R4).
assert (Hu : 0 <= ru8 n) by (unfold ru8; pose proof (Z.div_pos (n + 7) 8 ltac:(lia) ltac:(lia)); lia).
assert (Hr8 : 0 <= rz_size n / 8) by (apply Z.div_pos; lia). assert (Hu8 : 0 <= ru8 n / 8) by (apply Z.div_pos; lia).
assert (Hd8 : 0 <= (S - rz_size n - ru8 n) / 8) by (apply Z.div_pos; lia).
split; [apply SL; lia|].
split; [intros _; apply SL; lia|].
rewrite !length_app, !Nat2Z.inj_add, !farun_lenZ, fdrun_lenZ by lia.
pose proof (div8_add3 (rz_size n) (ru8 n) (S - rz_size n - ru8 n) ltac:(lia) Hu ltac:(lia)) as X.
replace (rz_size n + ru8 n + (S - rz_size n - ru8 n)) with S in X by ring.
apply SHS; lia.
- apply SHS; lia.
Qed.

Lemma kv_pchunk : forall c i st, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some st -> ~ In (c, i) D -> pchunk_avoid W SB c i st.
Proof.
intros c i st Hc Hn HD. apply (kv_pchunk_gen c i st st Hc Hn HD).
intros n Hs. pose proof HG as (_ & HR & _). destruct HR as (HR & _).
pose proof (HR c Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & W10 & _).
pose proof (proj1 (Forall_forall _ _) W10 _ (nth_error_In _ _ Hn)) as X. destruct Hs as [->| ->]; cbv beta iota in X; lia.
Qed.

Lemma fk_map : forall k s, nth_error (sec Σ) k = Some s ->
64513 <= s_n s /\ 0 < s_mb s /\ s_mb s + smsz (s_n s) <= l_ACEIL L /\ (s_mb s + smsz (s_n s) <= 0x10000 \/ SEGTOP_A <= s_mb s)
/\ apart (s_mb s) (smsz (s_n s)) (l_PRB L) 0x2000011000 /\ apart (s_mb s) (smsz (s_n s)) (l_FSB L) 0xb09000
/\ Forall (fun g => apart (s_mb s) (smsz (s_n s)) (fst g) (snd g)) (startup_grants L)
/\ 6144 + ru8 (s_n s) <= smsz (s_n s) /\ s_n s <= ru8 (s_n s)
/\ (forall k' s', nth_error (sec Σ) k' = Some s' -> k' <> k -> apart (s_mb s) (smsz (s_n s)) (s_mb s') (smsz (s_n s'))).
Proof.
intros k s Hk. pose proof HG as (_ & _ & HS & _). destruct HS as (_ & _ & _ & HSF & HSP & _).
pose proof (proj1 (Forall_forall _ _) HSF s (nth_error_In _ _ Hk)) as (Hn & (G1 & G2 & G3 & G4 & G5) & Hp & Hf & HGs).
assert (Hroom : 6144 + ru8 (s_n s) <= smsz (s_n s)).
{ unfold smsz, pg_up, needed, rounded, ru8. rewrite (rz_size_big (s_n s)) by lia. rewrite Z.max_l by lia. rewrite Z.max_l by lia.
assert (8 * ((s_n s + 7) / 8) + 2048 + 2048 <= (8 * ((s_n s + 7) / 8) + 2048 + 2048 + 4095) / 4096 * 4096); [|lia].
pose proof (Z.mod_pos_bound (8 * ((s_n s + 7) / 8) + 2048 + 2048 + 4095) 4096 ltac:(lia)).
pose proof (Z.div_mod (8 * ((s_n s + 7) / 8) + 2048 + 2048 + 4095) 4096 ltac:(lia)). lia. }
assert (Hu : s_n s <= ru8 (s_n s)) by (unfold ru8; pose proof (Z.div_mod (s_n s + 7) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (s_n s + 7) 8 ltac:(lia)); lia).
split; [lia|]. split; [exact G1|]. split; [exact G3|]. split; [exact G5|]. split; [exact Hp|]. split; [exact Hf|]. split; [exact HGs|].
split; [exact Hroom|]. split; [exact Hu|]. intros k' s' Hk' Hne. exact (HSP k k' s s' Hk Hk' (fun E => Hne (eq_sym E))).
Qed.

Lemma kv_schunk : forall k s, nth_error (sec Σ) k = Some s -> ~ In k DS -> schunk_avoid W s.
Proof.
intros k s Hk HD. pose proof (fk_map k s Hk) as (Hn & G1 & G3 & G5 & Hp & _ & _ & Hroom & Hu & HSP). pose proof fk_aceil as (_ & X).
assert (HDS : forall k' s', nth_error (sec Σ) k' = Some s' -> In k' DS -> s_mb s + smsz (s_n s) <= s_mb s' \/ s_mb s' + smsz (s_n s') <= s_mb s).
{ intros k' s' Hk' Hin. assert (k' <> k) by (intros ->; exact (HD Hin)). pose proof (HSP k' s' Hk' H) as Ha. unfold apart in Ha. lia. }
assert (Hoff : s_mb s + smsz (s_n s) <= l_PRB L \/ l_PRB L + 0x2000011000 <= s_mb s) by (unfold apart in Hp; lia).
assert (SH : forall a n, shad (s_mb s) <= a -> a + n <= shad (s_mb s + smsz (s_n s)) -> disjoint_from W a n).
{ intros a n H1 H2. apply (HW_shad_app (s_mb s) (s_mb s + smsz (s_n s))); [lia | lia | exact Hoff | exact HDS | exact H1 | exact H2]. }
assert (Hu8 : 0 <= ru8 (s_n s)) by lia.
unfold schunk_avoid.
split; [apply (HW_secmap k s); [exact Hk | exact HD | lia | lia]|].
split; [apply (HW_secmap k s); [exact Hk | exact HD | lia | lia]|].
split; [apply (HW_secmap k s); [exact Hk | exact HD | lia | destruct (s_quar s); lia]|].
pose proof (fk_shad_le2 (s_mb s) 6144 ltac:(lia) ltac:(lia)) as E1. change (6144 / 8) with 768 in E1.
pose proof (fk_shad_le2 (s_mb s + 6144) (ru8 (s_n s)) ltac:(lia) Hu8) as E2.
pose proof (fk_shad_le2 (s_mb s + 6144 + ru8 (s_n s)) (smsz (s_n s) - 6144 - ru8 (s_n s)) ltac:(lia) ltac:(lia)) as E3.
replace (s_mb s + 6144 + ru8 (s_n s) + (smsz (s_n s) - 6144 - ru8 (s_n s))) with (s_mb s + smsz (s_n s)) in E3 by ring.
assert (0 <= (smsz (s_n s) - 6144 - ru8 (s_n s)) / 8) by (apply Z.div_pos; lia). assert (0 <= ru8 (s_n s) / 8) by (apply Z.div_pos; lia).
pose proof (fk_shad_mono (s_mb s + 6144 + ru8 (s_n s)) (s_mb s + smsz (s_n s)) ltac:(lia)) as E4.
pose proof (fk_shad_mono (s_mb s) (s_mb s + 6144) ltac:(lia)) as E5.
pose proof (fk_shad_mono (s_mb s + 6144) (s_mb s + 6144 + ru8 (s_n s)) ltac:(lia)) as E6.
replace (s_mb s + 4096 + 2048) with (s_mb s + 6144) by ring.
split; [change ((4096 + 2048) / 8) with 768; apply SH; [lia | rewrite Z.max_r by lia; lia]|].
split.
- apply SH; [lia|]. destruct (s_quar s); [rewrite fdrun_lenZ by (apply Z.div_pos; lia) | rewrite (fl_ushadow_len (s_n s)) by lia]; lia.
- apply SH; [lia | ]. replace (smsz (s_n s) - 4096 - 2048 - ru8 (s_n s)) with (smsz (s_n s) - 6144 - ru8 (s_n s)) by ring.
rewrite Z.max_r by (apply Z.div_pos; lia). lia.
Qed.

Lemma kv_sec : Forall (fun r => disjoint_from IZ (fst r) (snd r)) sec_lits -> sec_avoid W Σ.
Proof.
intros HZ. split.
- apply Forall_forall. intros r Hr. apply HW_img; [| | exact (proj1 (Forall_forall _ _) HZ r Hr)];
unfold sec_lits in Hr; repeat (destruct Hr as [<-|Hr]; [cbn [fst snd]; unfold i_sec_chunks, i_sec_nres, i_sec_mutex, i_sec_page,
i_sec_range, i_sec_sorted, i_sec_bylog, i_gstat_alloc, INST, g_instance, SEGTOP_A; lia|]); destruct Hr.
- pose proof HG as (_ & _ & HS & _). destruct HS as (_ & Hn & _).
apply (HW_grant 1 (l_PAB L) 0x800000); [reflexivity | lia | lia | lia].
Qed.

Lemma kv_quar : disjoint_from TZ (qcacheT T) 32 -> Forall (fun r => disjoint_from IZ (fst r) (snd r)) [(i_q_global, 32); (i_q_cmutex, 4)] ->
(forall i, nth_error (r_st (pr Σ 24)) i = Some CkBatch -> ~ In (24, i) D) ->
Forall (fun b => exists i, nth_error (r_st (pr Σ 24)) i = Some CkBatch /\ fst b = p_abeg (l_SB (lay Σ)) 24 i) (ql Σ ++ qg Σ) ->
quar_avoid W Σ.
Proof.
intros HZ HI HB HBt. split; [apply HW_T; [unfold qcacheT; lia | unfold qcacheT; lia | exact HZ]|].
split.
- apply Forall_forall. intros r Hr. apply HW_img; [| | exact (proj1 (Forall_forall _ _) HI r Hr)];
destruct Hr as [<-|[<-|[]]]; cbn [fst snd]; unfold i_q_global, i_q_cmutex, INST, g_instance, SEGTOP_A; lia.
-
apply Forall_forall. intros b Hb. destruct (proj1 (Forall_forall _ _) HBt b Hb) as (i & Hi & E). rewrite E.
pose proof (fk_slot 24 i CkBatch ltac:(lia) Hi) as (S1 & S2 & S3 & S4). change (ClassSize 24) with 8192 in *.
apply (HW_slot 24 i CkBatch); [lia | exact Hi | exact (HB i Hi) | lia | change (ClassSize 24) with 8192; lia].
Qed.

Lemma kv_dep : Forall (fun r => disjoint_from IZ (fst r) (snd r)) DEP_LITS ->
(forall i b gn a n, nth_error (startup_grants L) i = Some (b, gn) -> (i = 6 \/ i = 7)%nat -> b <= a -> a + n <= b + gn -> disjoint_from W a n) ->
dep_avoid W L.
Proof.
intros HZ HD. split.
- apply Forall_forall. intros r Hr. apply HW_img; [| | exact (proj1 (Forall_forall _ _) HZ r Hr)];
unfold DEP_LITS in Hr; repeat (destruct Hr as [<-|Hr]; [cbn [fst snd]; unfold SEGTOP_A; lia|]); destruct Hr.
- split; [apply (HD 6%nat (l_DNB L) 0x100000); [reflexivity | lia | lia | lia]|].
apply (HD 7%nat (l_SSB L) 0x800000); [reflexivity | lia | lia | lia].
Qed.

Lemma kv_ia : Forall (fun r => disjoint_from IZ (fst r) (snd r)) ia_lits -> dsjl W ia_lits.
Proof.
intros HZ. apply Forall_forall. intros r Hr. apply HW_img; [| | exact (proj1 (Forall_forall _ _) HZ r Hr)];
unfold ia_lits in Hr; repeat (destruct Hr as [<-|Hr]; [cbn [fst snd]; unfold g_ia_word, IAP, SEGTOP_A; lia|]); destruct Hr.
Qed.

Lemma fk_fsb : forall a n, l_FSB L <= a -> a + n <= l_FSB L + 0xb09000 -> disjoint_from W a n.
Proof. intros a n H1 H2. exact (HW_grant 5 (l_FSB L) 0xb09000 a n eq_refl ltac:(lia) H1 H2). Qed.

Lemma fk_fsb_off : l_FSB L + 0xb09000 <= l_PRB L \/ l_PRB L + 0x2000011000 <= l_FSB L.
Proof. pose proof (g_apart Σ HG 0 5 _ _ ltac:(lia) eq_refl eq_refl) as X. cbn [fst snd] in X. unfold apart in X. lia. Qed.

Lemma fk_fsb_maps : forall k s, nth_error (sec Σ) k = Some s -> l_FSB L + 0xb09000 <= s_mb s \/ s_mb s + smsz (s_n s) <= l_FSB L.
Proof. intros k s Hk. pose proof (fk_map k s Hk) as (_ & _ & _ & _ & _ & Hf & _). unfold apart in Hf. lia. Qed.

Lemma kv_fs_cls : forall k, (k = 0 \/ k = 2 \/ k = 4 \/ k = 5 \/ k = 8)%nat -> fs_cls_avoid W (l_FSB L) (Z.of_nat k) (fs_of Σ k).
Proof.
intros k Hk. pose proof HG as (_ & _ & _ & HF). destruct HF as (F0 & F2 & F4 & _).
assert (Hwf : flags_ok (Z.of_nat k) (fss_flags (fs_of Σ k))) by (destruct Hk as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; [exact (proj1 F0) | exact (proj1 F2) | exact (proj1 (proj1 F4)) | exact (proj1 (proj1 (proj2 F4))) | exact (proj1 (proj2 (proj2 F4)))]).
destruct Hwf as [Hlen _].
assert (Hc : Z.of_nat k = 0 \/ Z.of_nat k = 2 \/ Z.of_nat k = 4 \/ Z.of_nat k = 5 \/ Z.of_nat k = 8) by (destruct Hk as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; cbn; lia).
pose proof (g_grant Σ HG (l_FSB L) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as (G1 & G2 & G3 & G4 & G5).
pose proof fk_aceil as (_ & X). pose proof (fl_flags_range _ Hc) as (R1 & R2). pose proof fk_fsb_off as Off.
unfold fs_cls_avoid. split; [apply fk_fsb; destruct Hc as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; lia|]. split.
- rewrite Hlen. apply fk_fsb; unfold fl_base; lia.
- intros p Hp _. pose proof (frame_addr_range (l_FSB L) (Z.of_nat k) p Hc Hp) as (A1 & A2). unfold kFakeStackSize in A2.
assert (Hfz : 0 < fsz (Z.of_nat k)) by (unfold fsz; destruct Hc as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; cbn; lia).
split; [apply fk_fsb; lia|].
pose proof (fk_shad_le2 (frame_addr (l_FSB L) (Z.of_nat k) p) (fsz (Z.of_nat k)) ltac:(lia) ltac:(lia)) as E.
apply (HW_shad_app (frame_addr (l_FSB L) (Z.of_nat k) p) (frame_addr (l_FSB L) (Z.of_nat k) p + fsz (Z.of_nat k))); [lia | lia | lia | | lia | lia].
intros k' s' Hk' _. pose proof (fk_fsb_maps k' s' Hk'). lia.
Qed.

Lemma kv_fs : Forall (fun r => disjoint_from IZ (fst r) (snd r)) fs_lits -> disjoint_from TZ (T + 48) 16 -> fs_avoid W Σ.
Proof.
intros HZ HT. pose proof (g_grant Σ HG (l_FSB L) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as (G1 & _).
unfold fs_avoid. split; [apply fk_fsb; lia|].
split; [exact (kv_fs_cls 0%nat ltac:(lia))|]. split; [exact (kv_fs_cls 2%nat ltac:(lia))|]. split; [split; [exact (kv_fs_cls 4%nat ltac:(lia))| split; [exact (kv_fs_cls 5%nat ltac:(lia))| exact (kv_fs_cls 8%nat ltac:(lia))]]|].
split.
{ apply Forall_forall. intros r Hr. apply HW_img; [| | exact (proj1 (Forall_forall _ _) HZ r Hr)];
unfold fs_lits in Hr; repeat (destruct Hr as [<-|Hr]; [cbn [fst snd]; unfold tpA, g_real_tls_get_addr, g_dtv_ptr, g_dtv1,
g_got_common_flags, g_intercept_tls_get_addr, g_got_verbosity, g_current_verbosity, g_tls_index, g_got_dtls_off, g_tls_dtls, SEGTOP_A; lia|]);
destruct Hr. }
split; [apply (HW_grant 4 (l_DTV L) 4096); [reflexivity | lia | lia | lia]|].
split; [apply HW_T; [lia | lia | exact HT]|].
apply Forall_forall. intros [f k] Hin. cbn [fst snd]. destruct (g_frame Σ HG f k Hin) as (X1 & X2 & X3). apply fk_fsb; lia.
Qed.

Lemma kv_shadow : shadow_avoid W L.
Proof.
pose proof fk_aceil as (X1 & X2). pose proof fk_prb as (P0 & P1 & P2 & _).
split.
- pose proof (fk_shad_le2 (l_ACEIL L) (2 ^ 47 - l_ACEIL L) ltac:(unfold SHB in *; lia) ltac:(lia)) as E.
replace (l_ACEIL L + (2 ^ 47 - l_ACEIL L)) with (2 ^ 47) in E by ring.
assert (0 <= (2 ^ 47 - l_ACEIL L) / 8) by (apply Z.div_pos; lia).
apply (HW_shad_app (l_ACEIL L) (2 ^ 47)); [unfold SHB in *; lia | lia | lia | | lia | rewrite Z.max_r by (apply Z.div_pos; lia); lia].
intros k s Hk _. pose proof (fk_map k s Hk) as (_ & _ & G3 & _). lia.
- apply Forall_forall. intros r Hr.
assert (Hlh : 0x10000 <= fst r /\ fst r < snd r /\ snd r <= 0x651d38) by (unfold CS_ACC in Hr; repeat (destruct Hr as [Hr|Hr]; [subst r; cbn; lia|]); destruct Hr).
apply (HW_shad_app 0x10000 SEGTOP_A); [lia | unfold SEGTOP_A; lia | unfold SEGTOP_A in *; lia | | apply fk_shad_mono; lia | ].
+ intros k s Hk _. pose proof (fk_map k s Hk) as (Hn & G1 & _ & G5 & _ & _ & _ & Hroom & Hu & _). unfold SEGTOP_A in *. lia.
+ assert ((snd r - 1) / 8 < 828416) by (apply Z.div_lt_upper_bound; lia).
assert (shad (snd r - 1) + 1 <= shad SEGTOP_A) by (unfold shad, SEGTOP_A; change (0x652000 / 8) with 828416; lia). lia.
Qed.

Lemma kv_consts : Forall (fun r => disjoint_from IZ (fst r) (snd r - fst r)) CONSTS_LITS -> disjoint_from TZ T 0x30 ->
forall x, in_rngs (consts_rngs L) x -> x <> T + 0xc60 -> outside W x.
Proof.
intros HZ HTZ x Hx Hne. unfold in_rngs in Hx. apply Exists_exists in Hx as (r & Hr & Hrx). cbv beta in Hrx.
destruct (consts_rngs_kind L r Hr) as [Hl|[(H1 & H2)|[Er|(H1 & H2)]]].
- pose proof (proj1 (Forall_forall _ _) HZ r Hl) as Dr.
assert (Hrng : 0x10000 <= fst r /\ snd r <= SEGTOP_A) by (unfold CONSTS_LITS in Hl; repeat (destruct Hl as [<-|Hl]; [cbn; unfold SEGTOP_A; lia|]); destruct Hl).
apply (disjoint_outside W (fst r) (snd r - fst r)); [apply HW_img; [lia | lia | exact Dr] | lia].
- apply (disjoint_outside W x 1); [apply HW_T; [lia | lia | exact (dsj_sub TZ T 0x30 x 1 HTZ ltac:(lia) ltac:(lia))] | lia].
- rewrite Er in Hrx. cbn [fst snd] in Hrx. lia.
- apply (disjoint_outside W x 1); [|lia].
apply (HW_grant 3 (l_TCX L) 0x10000); [reflexivity | lia | lia | lia].
Qed.

Hypothesis HW_stack : forall a n, usp <= a -> a + n <= USTACK_TOP -> disjoint_from W a n.

Lemma kv_client : Forall (fun r => disjoint_from IZ (fst r) (snd r - fst r)) CLIENT_STATIC ->
forall (L' : list (Z * Z)), (forall p n, In (p, n) L' ->
(exists c i, 1 <= c <= 31 /\ nth_error (r_st (pr Σ c)) i = Some (CkAlloc n) /\ p = p_ubeg SB c i n /\ ~ In (c, i) D)
\/ (exists k s, nth_error (sec Σ) k = Some s /\ s_quar s = false /\ s_n s = n /\ p = s_ubeg s /\ ~ In k DS)) ->
forall x, aclient L' (frames Σ) usp x -> outside W x.
Proof.
intros HCS L' HL' x Hx. destruct Hx as [H|[H|[H|[H|H]]]].
- apply (disjoint_outside W x 1); [apply HW_stack; lia | lia].
- destruct H as ((lo & hi & Hin & Hlh) & _). pose proof (proj1 (Forall_forall _ _) HCS (lo, hi) Hin) as Dr. cbn [fst snd] in Dr.
apply (disjoint_outside W lo (hi - lo)); [|lia].
apply HW_img; [| | exact Dr]; unfold CLIENT_STATIC in Hin; destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; unfold SEGTOP_A; lia.
- destruct H as (p & n & Hin & Hpx). apply (disjoint_outside W p n); [|lia].
destruct (HL' p n Hin) as [(c & i & Hc & Hn & -> & HD)|(k & s & Hk & Hq & Hn' & -> & HD)].
+ pose proof (fk_slot c i _ Hc Hn) as (S1 & S2 & S3 & S4).
assert (Hfit : rz_size n + n <= ClassSize c /\ 0 <= n).
{ pose proof HG as (_ & HR & _). destruct HR as (HR & _).
pose proof (HR c Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & W10 & _).
pose proof (proj1 (Forall_forall _ _) W10 _ (nth_error_In _ _ Hn)) as X. cbv beta iota in X. lia. }
pose proof (fl_rz_facts n) as (R1 & R2).
apply (HW_slot c i (CkAlloc n)); [exact Hc | exact Hn | exact HD | unfold p_ubeg; lia | unfold p_ubeg; lia].
+ pose proof (fk_map k s Hk) as (_ & _ & _ & _ & _ & _ & _ & Hroom & Hu & _).
apply (HW_secmap k s); [exact Hk | exact HD | unfold s_ubeg; lia | unfold s_ubeg; rewrite <- Hn'; lia].
- destruct H as (f & k & Hin & Hfx). apply (disjoint_outside W f (fs_size k - 8)); [|lia].
destruct (g_frame Σ HG f k Hin) as (Y1 & Y2 & Y3). apply fk_fsb; lia.
- destruct H as (f & k & Hin & Hfx). apply (disjoint_outside W (shad f) (shad (f + fs_size k) - shad f)); [|lia].
destruct (g_frame Σ HG f k Hin) as (Y1 & Y2 & Y3). pose proof fk_fsb_off as Off.
pose proof (g_grant Σ HG (l_FSB L) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as (G1 & _ & G3 & _).
pose proof fk_aceil as (_ & X).
apply (HW_shad_app f (f + fs_size k)); [lia | lia | lia | | lia | lia].
intros k' s' Hk' _. pose proof (fk_fsb_maps k' s' Hk'). lia.
Qed.

End FKit.
