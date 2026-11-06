(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__DigitFam () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.DigitFam.DF."; "Stdlib.ZArith.BinInt.Z."], [["1andb"; "1app"; "1bool"; "1length"; "1list"; "1nat"; "1true"; "2and"; "2eq"; "2not"; "3sub"; "4le"; "4lt"; "5firstn"; "5nth"; "5skipn"]; ["6Z"; "7D20"; "7P19"; "7P20"; "7all_digits"; "7dval"; "7dval_acc"; "7leading_zeros"; "7nsig"; "7pfam"; "7pfam_cond"; "7sigd"; "8add"; "8le"; "8lt"; "8mul"]; ["8of_nat"; "8pow"; "8sub"; "0a"; "0acc"; "0b"; "0cs"; "0i"; "0k"; "0s"; "0u"; "0v"]]).
Module DF.
Definition TT : Z := 18446744073709551616.
Definition QT : Z := 1844674407370955161.
Fixpoint dval_acc (acc : Z) (cs : list Z) : Z :=
match cs with [] => acc | c :: t => dval_acc (acc * 10 + (c - 48)) t end.
Definition dval (cs : list Z) : Z := dval_acc 0 cs.
Fixpoint leading_zeros (b : list Z) : nat :=
match b with
| c :: r => if Z.eqb c 48 then S (leading_zeros r) else 0%nat
| [] => 0%nat
end.
Definition sigd (b : list Z) : list Z := skipn (leading_zeros b) b.
Definition nsig (b : list Z) : nat := length (sigd b).
Definition P19 (b : list Z) : Z := dval (firstn 19 (sigd b)).
Definition P20 (b : list Z) : Z := dval (firstn 20 (sigd b)).
Definition D20 (b : list Z) : Z := nth 19 (sigd b) 48.
Definition pfam_cond (f : nat) (b : list Z) : Prop :=
match f with
| 0%nat => (nsig b <= 19)%nat \/ (nsig b = 20%nat /\ P20 b < TT)
| 1%nat => (20 <= nsig b)%nat /\ QT + 1 <= P19 b
| 2%nat => (21 <= nsig b)%nat /\ P19 b = QT /\ 54 <= D20 b
| 3%nat => (21 <= nsig b)%nat /\ P20 b < TT
| 4%nat => nsig b = 20%nat /\ P19 b = QT /\ 54 <= D20 b
| _ => False
end.
Definition pfam (b : list Z) : nat :=
let n := nsig b in
if Nat.leb 39 (length b) then 0%nat
else if Nat.leb n 19 then 0%nat
else if Nat.eqb n 20 then
(if Z.ltb (P20 b) TT then 0%nat
else if Z.leb (QT + 1) (P19 b) then 1%nat
else 4%nat)
else
if Z.leb (QT + 1) (P19 b) then 1%nat
else if (Z.eqb (P19 b) QT && Z.leb 54 (D20 b))%bool then 2%nat
else 3%nat.
Definition all_digits (cs : list Z) : bool := forallb (fun c => Z.leb 48 c && Z.leb c 57)%bool cs.
Lemma dval_acc_app : ltac2:(TCodec.tc2 tcn__DigitFam "A'@'4%112'8&Fr3&1r2r1%33921%6251%7264%8214%:3=31pRH<1pRF=1pR8@1").
Proof. intros a u; revert a; induction u as [|c u IH]; intros a v; [reflexivity|]. cbn. apply IH. Qed.
Lemma dval_acc_bound : ltac2:(TCodec.tc2 tcn__DigitFam "Q7'@'4%112&Mzr2%3221'8'2&D%115(6%53421'7&Or4&Q1+:&Q0&3r3%22E1%411%7261%:291&F%12;6%H231&N&L+1%22@1%B219%5271%E271p0G1p0N1pR>Q31pR:Q61").
Proof.
intros acc cs; revert acc; induction cs as [|c t IH]; intros acc Hacc Hd; cbn [dval_acc length].
- cbn. lia.
- cbn in Hd. apply andb_prop in Hd as [Hc Ht]. apply andb_prop in Hc as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2.
specialize (IH (acc * 10 + (c - 48)) ltac:(lia) Ht). rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
pose proof (Z.pow_pos_nonneg 10 (Z.of_nat (length t))). nia.
Qed.
Lemma dval_bound : ltac2:(TCodec.tc2 tcn__DigitFam "M'4'@%211'8'2&Dr1%211(6%63521'7&Mz&Er2%211%5241&N&Q1+:&Q0&3%12E8%311%6251%82:1%@2:1p0B1pR>J1").
Proof. intros cs H. unfold dval. pose proof (dval_acc_bound 0 cs ltac:(lia) H). lia. Qed.
Lemma all_digits_app : ltac2:(TCodec.tc2 tcn__DigitFam "B'4'@%211'8'2&D&1r2r1%33821%511&0%715%815%3221%<3;51pRH>1pRF?1").
Proof. intros u v. unfold all_digits. rewrite forallb_app. reflexivity. Qed.
Lemma all_digits_firstn : ltac2:(TCodec.tc2 tcn__DigitFam "D'5'4'@%211'8'2&Dr1%211(6%63521&=r3r2%33<21%911%<3;17p071pRF?1pRBC1").
Proof.
intros k u H. rewrite <- (firstn_skipn k u) in H. rewrite all_digits_app in H. apply andb_prop in H as [H _]. exact H.
Qed.
Lemma all_digits_skipn : ltac2:(TCodec.tc2 tcn__DigitFam "D'5'4'@%211'8'2&Dr1%211(6%63521&?r3r2%33<21%911%<3;17p071pRF?1pRBC1").
Proof.
intros k u H. rewrite <- (firstn_skipn k u) in H. rewrite all_digits_app in H. apply andb_prop in H as [_ H]. exact H.
Qed.
Lemma leading_zeros_le : ltac2:(TCodec.tc2 tcn__DigitFam ";'4'@%211';&Gr1%211&3%1273%6231pR<81").
Proof. induction b as [|c r IH]; cbn; [lia|]. destruct (Z.eqb c 48); cbn; lia. Qed.
Lemma all_digits_sigd : ltac2:(TCodec.tc2 tcn__DigitFam "A'4'@%211'8'2&Dr1%211(6%63521&Kr2%211%811%;3:16p061pR<>1").
Proof. intros b H. unfold sigd. apply all_digits_skipn. exact H. Qed.
Lemma leading_zeros_spec : ltac2:(TCodec.tc2 tcn__DigitFam "O'4'@%211'7'5&<r1&Gr2%211%5241'8&>r3z%34>721+Q@%63@21p081pR@?1%=1>&3%12E@%B231&9%=4H@A;%?3I1:%311p051%J2:1pR<L1").
Proof.
induction b as [|c r IH]; cbn [leading_zeros length].
- split; [intros i Hi; lia | intros H; lia].
- destruct (Z.eqb_spec c 48) as [->|Hc].
+ destruct IH as [IH1 IH2]. split.
* intros [|i] Hi; cbn; [reflexivity | apply IH1; lia].
* intros H. cbn. apply IH2. lia.
+ split; [intros i Hi; lia | intros _; exact Hc].
Qed.
Lemma dval_prefix_le : ltac2:(TCodec.tc2 tcn__DigitFam "Q?'5'4'@%211'8'2&Dr1%211(6%63521';r3&3r2%22=1%5241'7&M&O&E&=r4%23E1;%411&Q1+:&Q0&:%@2KA%2218%411%7261%>291%>1F%A221&N&L+1%22?1%E218%5271%I271p0K1p0Q21pRDQ:1pRBQ>1").
Proof.
intros k s Hd Hk. unfold dval. rewrite <- (firstn_skipn k s) at 3. rewrite <- (firstn_skipn k s) at 5.
rewrite !dval_acc_app.
pose proof (dval_acc_bound (dval_acc 0 (firstn k s)) (skipn k s)) as B.
rewrite length_skipn in B.
assert (H0 : 0 <= dval_acc 0 (firstn k s)) by (pose proof (dval_bound (firstn k s) (all_digits_firstn k s Hd)) as X; unfold dval in X; lia).
specialize (B H0 (all_digits_skipn k s Hd)). lia.
Qed.
Lemma P20_split : ltac2:(TCodec.tc2 tcn__DigitFam "Q:'4'@%211'8'2&Dr1%211(6%63521';uD&Hr2%211%5241'7&Cr3%211&L&O&B%115+:%4221&Q2&A%11:+Q@%4221%;261%M3O=1&M%1256+QI%3281%E231%F261p0H1p0O1pR<Q71").
Proof.
intros b Hd Hn. unfold P20, P19, D20, nsig in *. pose proof (all_digits_sigd b Hd) as Hs. set (s := sigd b) in *.
assert (E : firstn 20 s = firstn 19 s ++ [nth 19 s 48]).
{ rewrite <- (firstn_skipn 19 (firstn 20 s)). rewrite firstn_firstn by lia. f_equal.
rewrite skipn_firstn_comm. replace (20 - 19)%nat with 1%nat by lia.
destruct (skipn 19 s) as [|x r] eqn:Hsk.
- exfalso. pose proof (f_equal (@length Z) Hsk) as X. rewrite length_skipn in X. cbn in X. lia.
- cbn. f_equal. change (nth 19 s 48) with (nth (19 + 0) s 48). rewrite <- nth_skipn, Hsk. reflexivity. }
split.
- unfold dval. rewrite E, dval_acc_app. cbn [dval_acc]. reflexivity.
- pose proof (all_digits_skipn 19 s Hs) as X. destruct (skipn 19 s) as [|x r] eqn:Hsk.
+ exfalso. pose proof (f_equal (@length Z) Hsk) as Y. rewrite length_skipn in Y. cbn in Y. lia.
+ cbn in X. apply andb_prop in X as [X _]. apply andb_prop in X as [X1 X2]. apply Z.leb_le in X1. apply Z.leb_le in X2.
change (nth 19 s 48) with (nth (19 + 0) s 48). rewrite <- nth_skipn, Hsk. cbn. lia.
Qed.
Lemma pfam_cond_sound : ltac2:(TCodec.tc2 tcn__DigitFam "H'4'@%211'8'2&Dr1%211(6%63521';&3r2%22<1uQ6%5221&J&Ir3%211%4212p061p0=1pR<E1").
Proof.
intros b Hd H38. pose proof (all_digits_sigd b Hd) as Hs. unfold pfam.
destruct (Nat.leb 39 (length b)) eqn:E39; [apply Nat.leb_le in E39; lia|].
set (n := nsig b).
destruct (Nat.leb n 19) eqn:E19.
{ apply Nat.leb_le in E19. cbn [pfam_cond]. left. exact E19. }
apply Nat.leb_gt in E19.
pose proof (P20_split b Hd ltac:(unfold n in E19; lia)) as [SP R20].
destruct (Nat.eqb n 20) eqn:E20.
- apply Nat.eqb_eq in E20.
destruct (Z.ltb (P20 b) TT) eqn:Ef.
+ apply Z.ltb_lt in Ef. cbn [pfam_cond]. right. split; [exact E20 | exact Ef].
+ apply Z.ltb_ge in Ef. destruct (Z.leb (QT + 1) (P19 b)) eqn:E1.
* apply Z.leb_le in E1. cbn [pfam_cond]. split; [unfold n in E20; lia | exact E1].
* apply Z.leb_gt in E1. cbn [pfam_cond]. unfold TT, QT in *.
split; [exact E20|]. split; lia.
- apply Nat.eqb_neq in E20. assert (N21 : (21 <= n)%nat) by lia.
destruct (Z.leb (QT + 1) (P19 b)) eqn:E1.
+ apply Z.leb_le in E1. cbn [pfam_cond]. split; [lia | exact E1].
+ apply Z.leb_gt in E1. destruct (Z.eqb (P19 b) QT && Z.leb 54 (D20 b))%bool eqn:E2.
* apply andb_prop in E2 as [Ea Eb]. apply Z.eqb_eq in Ea. apply Z.leb_le in Eb.
cbn [pfam_cond]. split; [lia|]. split; [exact Ea | exact Eb].
* cbn [pfam_cond]. split; [lia|]. unfold TT, QT in *.
destruct (Z.eqb (P19 b) 1844674407370955161) eqn:Ea.
-- apply Z.eqb_eq in Ea. cbn [andb] in E2. apply Z.leb_gt in E2. lia.
-- apply Z.eqb_neq in Ea. lia.
Qed.
Lemma pfam_range : ltac2:(TCodec.tc2 tcn__DigitFam ":'4'@%211';&Ir1%211u4%5221pR<71").
Proof.
intros b. unfold pfam.
repeat match goal with |- context [if ?c then _ else _] => destruct c end; lia.
Qed.
End DF.
