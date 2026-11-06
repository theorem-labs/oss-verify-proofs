(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import BigModel BigRun BigFactsBase BigFactsOps BigFactsDiv.
Import ListNotations.
Unset Lia Cache. Unset Nra Cache. Unset Nia Cache.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__BigFactsRun () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.BigFactsBase."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.BigFactsOps."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.BigFactsRun."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.BigModel."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.BigModel.W."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.BigRun."; "Stdlib.ZArith.BinInt.Z."], [["0B"; "1O"; "1S"; "1bool"; "1cons"; "1fst"; "1length"; "1list"; "1nat"; "1nil"; "1snd"; "1true"; "2and"; "2eq"; "3add"; "3mul"]; ["4le"; "5Forall"; "6Z"; "0L"; "0N"; "7val"; "8BB"; "8mspec"; "8okN"; "8reduced"; "9NW"; "9a_sto"; "9all_digits"; "9dec"; "9dec_acc"; "9parse_post"]; [":EAlloc"; ":EFree"; ":ParseOk"; ":SiteReserve"; ":SiteString"; ";M"; ":event"; ":lit_a"; ":num_words_est"; ":parse_outcome"; ":s_words"; ":size"; ":skip_zeros"; ":st"; ":st_evs"; ":st_next"]; [":sto"; ":sto_empty"; ":to_bigint"; ":to_bigint_detail"; "<payload_events"; "<str_alloc_bytes"; "=add"; "=le"; "=lor"; "=lt"; "=mul"; "=of_nat"; "=pow"; "0Wd"; "0a"; "0acc"]; ["0b"; "0c"; "0cs"; "0fuel"; "0n"; "0neg"; "0p"; "0r"; "0s0"; "0v"; "0value"]]).
Fixpoint dec_acc (acc : Z) (cs : list Z) : Z :=
match cs with [] => acc | c :: t => dec_acc (acc * 10 + (c - 48)) t end.
Definition dec (cs : list Z) : Z := dec_acc 0 cs.
Definition all_digits (cs : list Z) : bool := forallb is_digit cs.
Lemma dec_acc_bound : ltac2:(TCodec.tc2 tcn__BigFactsRun "Q7'B'7%112&QGzr2%3221'='3&L%115(;%53421'<&QJr4&QL+:&QK&6r3%22E1%411%7261%:291&N%12;6%H231&QI&QF+1%22@1%B219%5271%E271p0G1p0N1pT6Q31pT0Q61").
Proof. intros acc cs.
revert acc; induction cs as [|c t IH]; intros acc Hacc Hd; simpl dec_acc; simpl length.
- simpl. lia.
- simpl in Hd. apply andb_prop in Hd. destruct Hd as [Hc Ht]. unfold is_digit in Hc. apply andb_prop in Hc. destruct Hc as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2.
specialize (IH (acc * 10 + (c - 48)) ltac:(lia) Ht). rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
pose proof (Z.pow_pos_nonneg 10 (Z.of_nat (length t))). nia.
Qed.
Lemma dec_bound : ltac2:(TCodec.tc2 tcn__BigFactsRun "M'7'B%211'='3&Lr1%211(;%63521'<&QGz&Mr2%211%5241&QI&QL+:&QK&6%12E8%311%6251%82:1%@2:1p0B1pT6J1").
Proof. intros cs. intros. unfold dec. pose proof (dec_acc_bound 0 cs ltac:(lia) H). lia. Qed.
Section Parse.
Variable N : nat.
Variable Wd : nat.
Variable L : nat.
Hypothesis HWd : 10 ^ Z.of_nat L < W.M ^ Z.of_nat Wd.
Hypothesis HN : (Wd + 1 <= N)%nat.
Lemma size_of_small : ltac2:(TCodec.tc2 tcn__BigFactsRun "Q4'Q@&HvDr1%3221&Ir2%211'<&QGz&E&Q:r3%211%411%7261&QI&QL+:&QKvC%211%5241%7291%A291'@&Q;r4%211vQM%5221p071p0J1p0N1pTDQ31").
Proof. intros v. intros Hv Hr Hval. unfold size. apply size_le_of_val; auto. apply (okN_words N); auto. lia. Qed.
Lemma digit_loop_mspec : forall fuel cs v acc (done : nat),
(length cs <= fuel)%nat -> (done + length cs = L)%nat ->
okN N v -> reduced v -> s_neg v = false ->
val (s_words v) = acc -> 0 <= acc < 10 ^ Z.of_nat done ->
mspec (digit_loop fuel cs v)
(fun r => match r with
| Some v' => all_digits cs = true /\ okN N v' /\ reduced v' /\ s_neg v' = false /\
val (s_words v') = dec_acc acc cs /\ (size v' <= Wd)%nat /\ (capacity v <= capacity v')%nat
| None => all_digits cs = false end)
(2 * length cs) (BB N).
Proof.
induction fuel as [|f IH]; intros cs v acc done Hf Hdone Hv Hr Hneg Hval Hacc.
- destruct cs; simpl in Hf; try lia. cbn [digit_loop]. apply mspec_ret. simpl in Hdone. splits; auto.
apply size_of_small; auto. rewrite Hval. rewrite Nat.add_0_r in Hdone. subst done. lia.
- destruct cs as [|c t].
+ cbn [digit_loop]. apply mspec_ret. simpl in Hdone. splits; auto.
apply size_of_small; auto. rewrite Hval. rewrite Nat.add_0_r in Hdone. subst done. lia.
+ cbn [digit_loop length]. simpl in Hdone, Hf.
assert (P10: 10 ^ Z.of_nat done * 10 <= 10 ^ Z.of_nat L).
{ rewrite Z.mul_comm, <- Z.pow_succ_r by lia. apply Z.pow_le_mono_r; lia. }
assert (Sv: (size v <= Wd)%nat). { apply size_of_small; auto. rewrite Hval. pose proof (Z.pow_pos_nonneg 10 (Z.of_nat done)). lia. }
destruct (is_digit c) eqn:Hc.
* unfold is_digit in Hc. apply andb_prop in Hc. destruct Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
eapply mspec_bind' with (K1 := 1%nat). apply mul_word_mspec; eauto. unfold wordZ; rewrite M_val; lia. lia. 2: lia.
intros v1 (Hv1 & Rv1 & Vv1 & Sv1 & Nv1 & Cv1).
assert (Sv1': (size v1 <= Wd)%nat). { apply size_of_small; auto. rewrite Vv1, Hval. lia. }
eapply mspec_bind' with (K1 := 1%nat). apply add_word_mspec; eauto. unfold wordZ; rewrite M_val; lia. lia. 2: lia.
intros v2 (Hv2 & Rv2 & Vv2 & Sv2 & Nv2 & Cv2).
assert (NEG: s_neg v2 = false). { rewrite Nv2. destruct (size v2 =? 0)%nat; auto. rewrite Nv1. destruct (size v1 =? 0)%nat; auto. }
assert (VAL: val (s_words v2) = acc * 10 + (c - 48)). { rewrite Vv2, Vv1, Hval. reflexivity. }
assert (ACC: 0 <= acc * 10 + (c - 48) < 10 ^ Z.of_nat (S done)). { rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia. }
pose proof (IH t v2 (acc * 10 + (c - 48)) (S done) ltac:(lia) ltac:(lia) Hv2 Rv2 NEG VAL ACC) as IH'.
eapply mspec_weaken. exact IH'. 2: lia. 2: lia.
intros r Hr'. destruct r as [v'|]; simpl; simpl in Hr'.
2:{ rewrite Hr'. apply andb_false_r. }
destruct Hr' as (A1 & A2 & A3 & A4 & A5 & A6 & A7).
splits; auto. unfold is_digit. rewrite (proj2 (Z.leb_le _ _) H1), (proj2 (Z.leb_le _ _) H2). simpl. exact A1. lia.
* eapply mspec_bind' with (K1 := 0%nat). apply destroy_mspec with (P := fun _ => True); auto. 2: lia.
intros _ _. apply mspec_ret. simpl. rewrite Hc. reflexivity.
Qed.
End Parse.
Lemma skip_zeros_le : ltac2:(TCodec.tc2 tcn__BigFactsRun ">'8'7'B%211'@&Q<r2r1%3221&6%1283%7231pT691pT8=1").
Proof. intros fuel cs. revert cs; induction fuel; intros [|c t]; simpl; try lia. destruct (c =? 48); simpl; try lia. specialize (IHfuel t). lia. Qed.
Lemma skip_zeros_all : ltac2:(TCodec.tc2 tcn__BigFactsRun "I'8'7'B%211'@&6r1%2251r2%5221'=&Q<r3%2215%92<6%53?21'A+Q@%83@<1qT4A1%43B18p061p0=1pT6D1pT8H1").
Proof. intros fuel cs. revert cs; induction fuel; intros [|c t] Hf Hs; simpl in *; try lia; try constructor.
destruct (Z.eqb_spec c 48). auto. simpl in Hs. lia. destruct (Z.eqb_spec c 48). apply IHfuel. lia. lia. simpl in Hs; lia. Qed.
Lemma dec_acc_zeros : ltac2:(TCodec.tc2 tcn__BigFactsRun "K'B'7%112'A'=r1+Q@%33721qT481%63914&Nr3r2%3221&QJ&QL+:&QK&6%12C7%311%6251%82;1%C3G:1p0?1pT6G1pT0J1").
Proof. intros acc cs. revert acc; induction cs as [|c t IH]; intros acc Hf. simpl. lia. inversion Hf; subst. cbn [dec_acc length]. rewrite IH by auto.
rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia. Qed.
Lemma num_words_est_mono : ltac2:(TCodec.tc2 tcn__BigFactsRun "='8'@r2r1%3221&Q8r3%211%316%8221p061pT2;1pSN<1").
Proof. intros a b.
intros. unfold num_words_est.
assert (M1: Z.of_nat a * 3402 / 1024 <= Z.of_nat b * 3402 / 1024). { apply Z.div_le_mono. lia. lia. }
assert (M2: (Z.of_nat a * 3402 / 1024 + 1 + 63) / 64 <= (Z.of_nat b * 3402 / 1024 + 1 + 63) / 64). { apply Z.div_le_mono. lia. lia. }
assert (P1: 1 <= (Z.of_nat b * 3402 / 1024 + 1 + 63) / 64). { apply Z.div_le_lower_bound. lia. pose proof (Z.div_pos (Z.of_nat b * 3402) 1024). lia. }
pose proof (Z.div_pos (Z.of_nat a * 3402) 1024). assert (0 <= (Z.of_nat a * 3402 / 1024 + 1 + 63) / 64) by (apply Z.div_pos; lia).
destruct (Nat.ltb_spec a 10); destruct (Nat.ltb_spec b 10); try lia.
all: apply Nat2Z.inj_le; rewrite ?Z2Nat.id; simpl; lia.
Qed.
Lemma num_words_est_4999 : ltac2:(TCodec.tc2 tcn__BigFactsRun "<'8'@r1uTl7%3221&Q8r2%211uX4%8221p061pT:;1").
Proof. intros n. intros. apply Nat.le_trans with (num_words_est 4999). apply num_words_est_mono; auto. vm_compute. lia. Qed.
Lemma pow10_le_words : ltac2:(TCodec.tc2 tcn__BigFactsRun "C'8'@r1uTl7%3221&QI&QL+:&QKr2%211%5241&Q5uX4%611%9231%;251p0=1pT:B1").
Proof. intros n. intros. apply Z.le_lt_trans with (10 ^ 4999). apply Z.pow_le_mono_r; lia. vm_compute. reflexivity. Qed.
Definition parse_post N Wd (neg : bool) (cs : list Z) (r : parse_outcome) : Prop :=
match r with
| ParseOk v => okN N v /\ reduced v /\ (size v <= Wd)%nat /\ val (s_words v) = dec cs /\ all_digits cs = true
/\ ((0 < size v)%nat -> s_neg v = neg)
| ParseErr => cs = [] \/ all_digits cs = false
end.
Lemma to_bigint_detail_mspec : ltac2:(TCodec.tc2 tcn__BigFactsRun "R2'8'7'B%211'3'Q@&Hr5r1%3221'=&Q;r2%211(1%53?21&QI&QL+:&QK&6%12C>%311%6251&Q5r6%711%:231%<251'@&>r7u1%3221r8%6221&Q8%A2Q36%211r9%;221&G'Q9&QC%13:=C&Or:%2418@=&?u2%N2Q@@%3221%F213&F%118%>5=;831p0@1p0F1p0N1p0Q<1p0QC1pTFQH1pT<QJ1pT6QL1pSLR01pQ:R11").
Proof. intros N Wd cs neg value.
intros Hv Sv HWd HN Hnw. unfold to_bigint_detail.
destruct (Nat.eqb_spec (length cs) 0).
{ apply mspec_ret. simpl. left. apply length_zero_iff_nil; auto. }
destruct (Nat.eqb_spec (skip_zeros (length cs) cs) (length cs)).
{ eapply mspec_bind' with (K1 := 1%nat). apply assign_mspec; eauto. apply okN_of_word. unfold wordZ; rewrite M_val; lia.
rewrite size_of_word. simpl. lia. 2: lia.
intros v1 (Hv1 & Wv1 & Sv1 & Nv1 & _). apply mspec_ret. simpl.
pose proof (skip_zeros_all (length cs) cs ltac:(lia) e) as AZ.
assert (AD: all_digits cs = true). { unfold all_digits. apply forallb_forall. intros x Hx. eapply Forall_forall in AZ; eauto. subst x. reflexivity. }
rewrite size_of_word in Sv1. simpl in Sv1. unfold sto_of_word in Wv1. simpl in Wv1.
splits; auto; try lia; try (intros; lia).
all: try (unfold reduced; rewrite Wv1; left; reflexivity).
all: rewrite Wv1; unfold dec; rewrite dec_acc_zeros; auto; cbn [val]; lia. }
eapply mspec_bind' with (K1 := 1%nat). apply reserve_mspec. apply okN_empty. auto. 2: lia.
intros v (Hvv & Wv & Nv & _ & _).
eapply mspec_bind' with (K1 := (2 * length cs)%nat).
{ apply (digit_loop_mspec N Wd (length cs) HWd HN (length cs) cs v 0 0); auto; try lia.
all: try (unfold reduced; rewrite Wv; left; auto). all: try (rewrite Wv; reflexivity). all: simpl; lia. }
2: lia.
intros r Hr. destruct r as [v1|]; simpl in Hr.
- destruct Hr as (AD & Hv1 & Rv1 & Nv1 & Vv1 & Sv1 & _).
set (v2 := if neg then set_neg v1 true else v1).
assert (Hv2: okN N v2) by (destruct neg; [apply okN_set_neg|]; auto).
assert (Wv2: s_words v2 = s_words v1) by (destruct neg; reflexivity).
assert (Sv2: size v2 = size v1) by (destruct neg; reflexivity).
eapply mspec_bind' with (K1 := 1%nat). apply assign_mspec; eauto. lia. 2: lia.
intros value1 (Hval1 & Wval1 & Sval1 & Nval1 & _).
eapply mspec_bind' with (K1 := 0%nat). apply destroy_mspec with (P := fun _ => True); auto. 2: lia. intros _ _.
apply mspec_ret. simpl. splits; auto.
+ unfold reduced. rewrite Wval1, Wv2. exact Rv1.
+ lia.
+ rewrite Wval1, Wv2, Vv1. reflexivity.
+ intros Hs. rewrite Nval1, Sv2. destruct (Nat.ltb_spec 0 (size v1)). destruct neg; simpl; auto. lia.
- eapply mspec_ret. simpl. auto.
Qed.
Lemma to_bigint_mspec N Wd cs value :
okN N value -> (size value = 0)%nat ->
10 ^ Z.of_nat (length cs) < W.M ^ Z.of_nat Wd -> (Wd + 1 <= N)%nat -> (num_words_est (length cs) <= N)%nat ->
mspec (to_bigint cs value)
(fun r => match r with
| ParseOk v => okN N v /\ reduced v /\ (size v <= Wd)%nat
| ParseErr => True end)
(2 * length cs + 2) (BB N).
Proof.
intros Hv Sv HWd HN Hnw. unfold to_bigint. destruct cs as [|c t]. apply mspec_ret; auto.
assert (HWd': 10 ^ Z.of_nat (length t) < W.M ^ Z.of_nat Wd).
{ apply Z.le_lt_trans with (10 ^ Z.of_nat (length (c :: t))); auto. apply Z.pow_le_mono_r. lia. simpl length; lia. }
assert (Hnw': (num_words_est (length t) <= N)%nat). { apply Nat.le_trans with (num_words_est (length (c :: t))); auto. apply num_words_est_mono. simpl; lia. }
destruct (Z.eqb_spec c 45).
- eapply mspec_weaken. apply (to_bigint_detail_mspec N Wd t true value); eauto.
intros r Hr; destruct r; simpl in *; tauto. simpl length; lia. lia.
- eapply mspec_weaken. apply (to_bigint_detail_mspec N Wd (c :: t) false value); eauto.
intros r Hr; destruct r; simpl in *; tauto. lia. lia.
Qed.
Definition a_sto := Sto false false [1634696772344632213; 3071233077104388850] inlined_capacity 0.
Lemma parse_a : ltac2:(TCodec.tc2 tcn__BigFactsRun "?'Q='='Q9&5&QB&Q7&QAr1%43321%63791(Q2&K%211%<3;41pTB>1").
Proof. intros s0. vm_compute. reflexivity. Qed.
Lemma parse_a_state : ltac2:(TCodec.tc2 tcn__BigFactsRun "Q4'Q='<'='7'Q6%211&Q>&:'Q9&QB&Q7&QAr1%43321%736>1%911(4(Q1&Q?%117+R0%4221(Q0(Q3%23541%C1=%:3F21%;3G61%J3G=1'8%<1@(2%11=%O3431%Q1261pTBQ31").
Proof. intros s0. vm_compute. split; reflexivity. Qed.
Lemma a_val : ltac2:(TCodec.tc2 tcn__BigFactsRun "9'='B&E&Q:&K%211%411+QZclkS\Yile[iQ][llQfgaXdlE%83721").
Proof. reflexivity. Qed.
Lemma a_okN : ltac2:(TCodec.tc2 tcn__BigFactsRun ";'8'@u1r1%3221&Hr2&K%3221p051pQ::1").
Proof. intros N. intros. split. split. cbn [s_words a_sto]. constructor. unfold wordZ; rewrite M_val; lia. constructor. unfold wordZ; rewrite M_val; lia. constructor.
unfold size, capacity, a_sto, inlined_capacity; simpl. split. lia. auto.
unfold capacity, a_sto, inlined_capacity; simpl. rewrite round_up_eq. lia. Qed.
Lemma a_reduced : ltac2:(TCodec.tc2 tcn__BigFactsRun "3&I&K%211"). Proof. right. simpl. lia. Qed.
Lemma a_size : ltac2:(TCodec.tc2 tcn__BigFactsRun "7'='8&Q;&K%211u2%63521"). Proof. reflexivity. Qed.
Lemma parse_a_mspec : ltac2:(TCodec.tc2 tcn__BigFactsRun "F'B&QG+R0r1%3221&G'Q9&QB&Q7&QA%3221'=(Q2&K%211%439<1qT@:1u1r2%>5=9321p0@1p2E1").
Proof. intros B.
intros HB s0. unfold post. rewrite parse_a. split; auto. destruct (parse_a_state s0) as [E1 E2]. rewrite E1, E2.
exists [EAlloc (st_next s0) 64 SiteReserve; EFree (st_next s0) 64]. simpl. repeat split; auto; try lia.
constructor. simpl. lia. constructor. simpl. auto. constructor.
Qed.
Definition NW : nat := 266.
Lemma BB_NW : ltac2:(TCodec.tc2 tcn__BigFactsRun "7'='B&F&J%211+RT0%63521"). Proof. reflexivity. Qed.
Definition body_post (r : option exn * option sto * option sto * option sto) : Prop :=
let '(ex, ob, oc, od) := r in
match ob with Some b => okN NW b /\ reduced b /\ (size b <= 260)%nat | None => True end.
Ltac destroy_step := eapply mspec_bind' with (K1 := 0%nat); [apply destroy_mspec with (P := fun _ => True); auto | intros _ _ | lia].
Ltac emit_step L := eapply mspec_bind' with (K1 := 0%nat); [apply L with (P := fun _ => True); auto | intros _ _ | lia].
Lemma lor7_le : ltac2:(TCodec.tc2 tcn__BigFactsRun "A'B&QGzr1%3221&QF&QHr2+7%3221+1%6221+8%8261%=231p0;1pT:@1").
Proof. intros n. intros. pose proof (Z.add_lor_land n 7). pose proof (Z.land_nonneg n 7). lia. Qed.
Lemma str_alloc_bytes_le : ltac2:(TCodec.tc2 tcn__BigFactsRun "@'8'<&QGz&QEr1%211%5241&QF&QK%115+8%4221%;271%=271pT:?1").
Proof. intros n. unfold str_alloc_bytes. destruct (Nat.eqb_spec n 23). lia. pose proof (lor7_le (Z.of_nat n) ltac:(lia)). pose proof (Z.lor_nonneg (Z.of_nat n) 7). lia. Qed.
Theorem run_payload_large : ltac2:(TCodec.tc2 tcn__BigFactsRun "Q0'7'B%211'@uTl8&6r1%2261%5241'='Q6%;11&QDr2%211(4(Q0(1&QE%>2B6%211(Q4%63521(Q1%1274(9%11@%<3A31%=3B61%D3B?1p0F1pT>M1").
Proof. intros p.
intros Hp. unfold payload_events, run_payload, harness, harness_body.
destruct (Nat.ltb_spec sso_max (length p)). 2: unfold sso_max in *; lia.
destruct (Nat.ltb_spec (length p) 5000); try lia. reflexivity.
Qed.
