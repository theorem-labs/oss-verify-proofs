(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YI59.v, with its module paths changed. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YO07 YO08.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Lemma rd_cases : forall (s : list Z) (n : Z),
(Z.of_nat (length s) < n /\ YO07.rd s n = (true, [], [])) \/
(n <= Z.of_nat (length s) /\ YO07.rd s n = (false, firstn (Z.to_nat n) s, skipn (Z.to_nat n) s)).
Proof.
intros s n. unfold YO07.rd. destruct (Z.ltb_spec (Z.of_nat (length s)) n) as [H|H]; [left|right]; split; auto; lia.
Qed.
Lemma rd_ok : forall (s : list Z) (n : Z), n <= Z.of_nat (length s) ->
YO07.rd s n = (false, firstn (Z.to_nat n) s, skipn (Z.to_nat n) s).
Proof. intros s n H. unfold YO07.rd. destruct (Z.ltb_spec (Z.of_nat (length s)) n); [lia | reflexivity]. Qed.
Lemma rd_short : forall (s : list Z) (n : Z), Z.of_nat (length s) < n -> YO07.rd s n = (true, [], []).
Proof. intros s n H. unfold YO07.rd. destruct (Z.ltb_spec (Z.of_nat (length s)) n); [reflexivity | lia]. Qed.
Lemma rd_rest_length : forall (s : list Z) (n : Z), (length (snd (YO07.rd s n)) <= length s)%nat.
Proof.
intros s n. destruct (rd_cases s n) as [[_ ->]|[_ ->]]; cbn; [lia|]. rewrite length_skipn. lia.
Qed.
Lemma rd_fails_short : forall (s : list Z) (n : Z), Z.of_nat (length s) < n -> fst (fst (YO07.rd s n)) = true.
Proof. intros s n H. rewrite rd_short by exact H. reflexivity. Qed.
Lemma skipn_skipn_Z : forall (l : list Z) (a b : Z), 0 <= a -> 0 <= b ->
skipn (Z.to_nat a) (skipn (Z.to_nat b) l) = skipn (Z.to_nat (b + a)) l.
Proof. intros l a b Ha Hb. rewrite skipn_skipn. f_equal. lia. Qed.
Lemma nth_skipn' : forall (l : list Z) (i j : nat), nth i (skipn j l) 0 = nth (j + i) l 0.
Proof.
intros l i j. revert l. induction j as [|j IH]; intros l; [reflexivity|].
destruct l as [|x l]; cbn; [destruct i; reflexivity | apply IH].
Qed.
Lemma le_bytes_2 : forall a b, YO07.le_bytes [a; b] = a + 256 * b.
Proof. intros a b. unfold YO07.le_bytes. cbn [fold_right]. lia. Qed.
Lemma le_bytes_1 : forall a, YO07.le_bytes [a] = a.
Proof. intros a. unfold YO07.le_bytes. cbn [fold_right]. lia. Qed.
Lemma firstn_2_at : forall (l : list Z) (j : nat), (j + 2 <= length l)%nat ->
firstn 2 (skipn j l) = [nth j l 0; nth (j + 1) l 0].
Proof.
intros l j Hj. revert l Hj. induction j as [|j IH]; intros l Hj.
- destruct l as [|x [|y l]]; cbn in *; try lia. reflexivity.
- destruct l as [|x l]; cbn in *; [lia|]. rewrite IH by lia. reflexivity.
Qed.
Lemma firstn_1_at : forall (l : list Z) (j : nat), (j + 1 <= length l)%nat ->
firstn 1 (skipn j l) = [nth j l 0].
Proof.
intros l j Hj. revert l Hj. induction j as [|j IH]; intros l Hj.
- destruct l as [|x l]; cbn in *; try lia. reflexivity.
- destruct l as [|x l]; cbn in *; [lia|]. rewrite IH by lia. reflexivity.
Qed.
Lemma le_bytes_at2 : forall (l : list Z) (j : nat), (j + 2 <= length l)%nat ->
YO07.le_bytes (firstn 2 (skipn j l)) = nth j l 0 + 256 * nth (j + 1) l 0.
Proof. intros l j Hj. rewrite firstn_2_at by exact Hj. apply le_bytes_2. Qed.
Section f.
Definition hdr_at (P : list Z) (cur : Z) (b0 b1 b2 b3 b4 b5 b6 b7 b8 : Z) : Prop :=
nth (Z.to_nat cur) P 0 = b0 /\ nth (Z.to_nat (cur + 1)) P 0 = b1 /\ nth (Z.to_nat (cur + 2)) P 0 = b2 /\
nth (Z.to_nat (cur + 3)) P 0 = b3 /\ nth (Z.to_nat (cur + 4)) P 0 = b4 /\ nth (Z.to_nat (cur + 5)) P 0 = b5 /\
nth (Z.to_nat (cur + 6)) P 0 = b6 /\ nth (Z.to_nat (cur + 7)) P 0 = b7 /\ nth (Z.to_nat (cur + 8)) P 0 = b8.
Definition hdr_palsz (b0 b1 b7 b8 : Z) : Z := if YO07.flag (b0 + 256 * b1) 1 then 3 * (b7 + 256 * b8) else 0.
Lemma hdr_palsz_nonneg : forall b0 b1 b7 b8, 0 <= b7 + 256 * b8 -> 0 <= hdr_palsz b0 b1 b7 b8.
Proof. intros. unfold hdr_palsz. destruct (YO07.flag _ _); lia. Qed.
Lemma rd2_at : forall P c x y, 0 <= c -> c + 2 <= Z.of_nat (length P) ->
nth (Z.to_nat c) P 0 = x -> nth (Z.to_nat (c + 1)) P 0 = y ->
YO07.rd (skipn (Z.to_nat c) P) 2 = (false, [x; y], skipn (Z.to_nat (c + 2)) P).
Proof.
intros P c x y Hc Hl <- <-. rewrite rd_ok by (rewrite length_skipn; lia).
rewrite firstn_2_at by lia. rewrite skipn_skipn_Z by lia.
replace (Z.to_nat c + 1)%nat with (Z.to_nat (c + 1)) by lia. reflexivity.
Qed.
Lemma rd1_at : forall P c x, 0 <= c -> c + 1 <= Z.of_nat (length P) -> nth (Z.to_nat c) P 0 = x ->
YO07.rd (skipn (Z.to_nat c) P) 1 = (false, [x], skipn (Z.to_nat (c + 1)) P).
Proof.
intros P c x Hc Hl <-. rewrite rd_ok by (rewrite length_skipn; lia).
rewrite firstn_1_at by lia. rewrite skipn_skipn_Z by lia. reflexivity.
Qed.
Lemma hdr_reads : forall P cur b0 b1 b2 b3 b4 b5 b6 b7 b8,
0 <= cur -> hdr_at P cur b0 b1 b2 b3 b4 b5 b6 b7 b8 -> cur + 9 <= Z.of_nat (length P) ->
YO07.rd (skipn (Z.to_nat cur) P) 2 = (false, [b0; b1], skipn (Z.to_nat (cur + 2)) P) /\
YO07.rd (skipn (Z.to_nat (cur + 2)) P) 2 = (false, [b2; b3], skipn (Z.to_nat (cur + 4)) P) /\
YO07.rd (skipn (Z.to_nat (cur + 4)) P) 2 = (false, [b4; b5], skipn (Z.to_nat (cur + 6)) P) /\
YO07.rd (skipn (Z.to_nat (cur + 6)) P) 1 = (false, [b6], skipn (Z.to_nat (cur + 7)) P) /\
YO07.rd (skipn (Z.to_nat (cur + 7)) P) 2 = (false, [b7; b8], skipn (Z.to_nat (cur + 9)) P).
Proof.
intros P cur b0 b1 b2 b3 b4 b5 b6 b7 b8 Hcur (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8) Hlen.
split; [apply rd2_at; [lia | lia | exact E0 | exact E1] |].
split; [replace (cur + 4) with (cur + 2 + 2) by lia; apply rd2_at; [lia | lia | exact E2 | rewrite <- E3; f_equal; lia] |].
split; [replace (cur + 6) with (cur + 4 + 2) by lia; apply rd2_at; [lia | lia | exact E4 | rewrite <- E5; f_equal; lia] |].
split; [replace (cur + 7) with (cur + 6 + 1) by lia; apply rd1_at; [lia | lia | exact E6] |].
replace (cur + 9) with (cur + 7 + 2) by lia; apply rd2_at; [lia | lia | exact E7 | rewrite <- E8; f_equal; lia].
Qed.
Lemma parse_frameN_ok : forall N P cur b0 b1 b2 b3 b4 b5 b6 b7 b8,
0 <= cur -> 1 <= N -> hdr_at P cur b0 b1 b2 b3 b4 b5 b6 b7 b8 -> 0 <= b7 + 256 * b8 ->
cur + 9 + hdr_palsz b0 b1 b7 b8 + N <= Z.of_nat (length P) ->
YO08.parse_frameN N (skipn (Z.to_nat cur) P)
= (true, (b0 + 256 * b1, b2 + 256 * b3, b4 + 256 * b5, b6, b7 + 256 * b8,
firstn (Z.to_nat (hdr_palsz b0 b1 b7 b8)) (skipn (Z.to_nat (cur + 9)) P),
firstn (Z.to_nat N) (skipn (Z.to_nat (cur + 9 + hdr_palsz b0 b1 b7 b8)) P)),
skipn (Z.to_nat (cur + 9 + hdr_palsz b0 b1 b7 b8 + N)) P).
Proof.
intros N P cur b0 b1 b2 b3 b4 b5 b6 b7 b8 Hcur HN HAT Hnlp Hlen.
pose proof (hdr_palsz_nonneg b0 b1 b7 b8 Hnlp) as Hps.
destruct (hdr_reads P cur b0 b1 b2 b3 b4 b5 b6 b7 b8 Hcur HAT ltac:(lia)) as (Q1 & Q2 & Q3 & Q4 & Q5).
unfold YO08.parse_frameN. rewrite Q1, Q2, Q3, Q4, Q5. rewrite !le_bytes_2, le_bytes_1.
unfold hdr_palsz in *. destruct (YO07.flag (b0 + 256 * b1) 1).
- rewrite (rd_ok (skipn (Z.to_nat (cur + 9)) P) ((b7 + 256 * b8) * 3)) by (rewrite length_skipn; lia).
rewrite skipn_skipn_Z by lia.
replace (cur + 9 + (b7 + 256 * b8) * 3) with (cur + 9 + 3 * (b7 + 256 * b8)) by lia.
rewrite (rd_ok (skipn (Z.to_nat (cur + 9 + 3 * (b7 + 256 * b8))) P) N) by (rewrite length_skipn; lia).
rewrite skipn_skipn_Z by lia. cbn [orb negb].
replace (Z.to_nat ((b7 + 256 * b8) * 3)) with (Z.to_nat (3 * (b7 + 256 * b8))) by lia. reflexivity.
- rewrite (rd_ok (skipn (Z.to_nat (cur + 9)) P) N) by (rewrite length_skipn; lia).
rewrite skipn_skipn_Z by lia. cbn [orb negb].
replace (cur + 9 + 0) with (cur + 9) by lia. reflexivity.
Qed.
Let tail5 (s : list Z) :=
let '(e1, a, s1) := YO07.rd s 2 in let '(e2, ge, s2) := YO07.rd s1 2 in let '(e3, d, s3) := YO07.rd s2 2 in
let '(e4, t, s4) := YO07.rd s3 1 in let '(e5, n, s5) := YO07.rd s4 2 in (e1 || e2 || e3 || e4 || e5, a, n, s5).
Lemma parse_frameN_tail : forall N s,
fst (fst (YO08.parse_frameN N s)) =
(let '(e, a, n, s5) := tail5 s in
let '(e6, lpal, s6) := (if YO07.flag (YO07.le_bytes a) 1 then YO07.rd s5 (YO07.le_bytes n * 3) else (false, [], s5)) in
let '(e7, img, s7) := YO07.rd s6 N in negb (e || e6 || e7)).
Proof.
intros N s. unfold YO08.parse_frameN, tail5.
destruct (YO07.rd s 2) as [[e1 a] s1]. destruct (YO07.rd s1 2) as [[e2 ge] s2]. destruct (YO07.rd s2 2) as [[e3 d] s3].
destruct (YO07.rd s3 1) as [[e4 t] s4]. destruct (YO07.rd s4 2) as [[e5 n] s5].
destruct (YO07.flag (YO07.le_bytes a) 1); [destruct (YO07.rd s5 _) as [[e6 lpal] s6]|]; destruct (YO07.rd _ N) as [[e7 img] s7]; reflexivity.
Qed.
Lemma tail5_length : forall s, let '(e, a, n, s5) := tail5 s in (length s5 <= length s)%nat.
Proof.
intros s. unfold tail5.
pose proof (rd_rest_length s 2) as L1. destruct (YO07.rd s 2) as [[e1 a] s1]. cbn in L1.
pose proof (rd_rest_length s1 2) as L2. destruct (YO07.rd s1 2) as [[e2 ge] s2]. cbn in L2.
pose proof (rd_rest_length s2 2) as L3. destruct (YO07.rd s2 2) as [[e3 d] s3]. cbn in L3.
pose proof (rd_rest_length s3 1) as L4. destruct (YO07.rd s3 1) as [[e4 t] s4]. cbn in L4.
pose proof (rd_rest_length s4 2) as L5. destruct (YO07.rd s4 2) as [[e5 n] s5]. cbn in L5. lia.
Qed.
Lemma tail5_short : forall s, (Z.of_nat (length s) < 9) -> let '(e, a, n, s5) := tail5 s in e = true /\ s5 = [] \/ e = true.
Proof.
intros s Hs. unfold tail5.
destruct (rd_cases s 2) as [[L1 ->]|[L1 ->]]; [cbn; left; auto|].
destruct (rd_cases (skipn (Z.to_nat 2) s) 2) as [[L2 E2]|[L2 E2]]; rewrite E2; rewrite ?length_skipn in L2; [cbn; left; auto|].
destruct (rd_cases (skipn (Z.to_nat 2) (skipn (Z.to_nat 2) s)) 2) as [[L3 E3]|[L3 E3]]; rewrite E3; rewrite ?length_skipn in L3;
[cbn; rewrite ?orb_true_r; left; auto|].
destruct (rd_cases (skipn (Z.to_nat 2) (skipn (Z.to_nat 2) (skipn (Z.to_nat 2) s))) 1) as [[L4 E4]|[L4 E4]]; rewrite E4;
rewrite ?length_skipn in L4; [cbn; rewrite ?orb_true_r; left; auto|].
destruct (rd_cases (skipn (Z.to_nat 1) (skipn (Z.to_nat 2) (skipn (Z.to_nat 2) (skipn (Z.to_nat 2) s)))) 2) as [[L5 E5]|[L5 E5]];
rewrite E5; rewrite ?length_skipn in L5; [cbn; rewrite ?orb_true_r; left; auto|].
exfalso. lia.
Qed.
Lemma parse_frameN_fail : forall N P cur b0 b1 b2 b3 b4 b5 b6 b7 b8,
0 <= cur -> 1 <= N ->
Z.of_nat (length P) < cur + 9 \/
(hdr_at P cur b0 b1 b2 b3 b4 b5 b6 b7 b8 /\ 0 <= b7 + 256 * b8 /\ Z.of_nat (length P) < cur + 9 + hdr_palsz b0 b1 b7 b8 + N) ->
fst (fst (YO08.parse_frameN N (skipn (Z.to_nat cur) P))) = false.
Proof.
intros N P cur b0 b1 b2 b3 b4 b5 b6 b7 b8 Hcur HN H.
rewrite parse_frameN_tail.
assert (DONE : forall (a n s5 : list Z),
(let '(e6, lpal, s6) := (if YO07.flag (YO07.le_bytes a) 1 then YO07.rd s5 (YO07.le_bytes n * 3) else (false, [], s5)) in
let '(e7, img, s7) := YO07.rd s6 N in negb (true || e6 || e7)) = false).
{ intros a n s5. destruct (YO07.flag _ 1); [destruct (YO07.rd s5 _) as [[e6 lpal] s6]|]; destruct (YO07.rd _ N) as [[e7 img] s7]; reflexivity. }
assert (IMG : forall (e : bool) (a n s5 : list Z),
Z.of_nat (length s5) < (if YO07.flag (YO07.le_bytes a) 1 then Z.max 0 (YO07.le_bytes n * 3) else 0) + N ->
(let '(e6, lpal, s6) := (if YO07.flag (YO07.le_bytes a) 1 then YO07.rd s5 (YO07.le_bytes n * 3) else (false, [], s5)) in
let '(e7, img, s7) := YO07.rd s6 N in negb (e || e6 || e7)) = false).
{ intros e a n s5 Hs. destruct (YO07.flag (YO07.le_bytes a) 1).
- destruct (rd_cases s5 (YO07.le_bytes n * 3)) as [[L6 ->]|[L6 ->]].
+ destruct (YO07.rd [] N) as [[e7 img] s7]. rewrite orb_true_r. reflexivity.
+ rewrite (rd_short (skipn _ s5) N) by (rewrite length_skipn; lia). rewrite !orb_true_r. reflexivity.
- rewrite (rd_short s5 N) by lia. rewrite !orb_true_r. reflexivity. }
destruct (Z.lt_ge_cases (Z.of_nat (length P)) (cur + 9)) as [Hs9 | Hs9].
-
pose proof (tail5_short (skipn (Z.to_nat cur) P) ltac:(rewrite length_skipn; lia)) as T.
destruct (tail5 (skipn (Z.to_nat cur) P)) as [[[e a] n] s5]. cbv beta iota zeta. destruct T as [[-> ->] | ->]; apply DONE.
- destruct H as [Hshort | (HAT & Hnlp & Hlen)]; [exfalso; lia|].
destruct (hdr_reads P cur b0 b1 b2 b3 b4 b5 b6 b7 b8 Hcur HAT Hs9) as (Q1 & Q2 & Q3 & Q4 & Q5).
unfold tail5. rewrite Q1, Q2, Q3, Q4, Q5. cbv beta iota zeta. apply IMG.
rewrite !le_bytes_2, length_skipn. unfold hdr_palsz in Hlen. destruct (YO07.flag (b0 + 256 * b1) 1); lia.
Qed.
End f.
