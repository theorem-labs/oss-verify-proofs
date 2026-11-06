(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import BigModel BigFactsBase BigFactsOps.
Import ListNotations.
Unset Lia Cache. Unset Nra Cache. Unset Nia Cache.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__BigFactsDiv () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Init.Peano."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.BigFactsBase."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.BigFactsDiv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.BigFactsOps."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.BigModel."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.BigModel.W."; "Stdlib.ZArith.BinInt.Z."], [["0A"; "0B"; "1O"; "1andb"; "1bool"; "1false"; "1fst"; "1length"; "1list"; "1nat"; "1orb"; "1pair"; "1prod"; "1snd"; "2and"; "2eq"]; ["2ex"; "3add"; "3sub"; "4le"; "5Z"; "0H"; "0N"; "6wordZ"; "6words_ok"; "7unnorm_ok"; "8reduced"; "9DDquotient"; "9DDquotient_f"; ":M"; ":add"; ":b2z"]; [":ltu"; ":sub"; ":wrap"; "9addback_loop"; "9ddq1_cond"; "9ddq1_loop"; "9ddq2_cond"; "9ddq2_loop"; "9no_unnorm"; "9set_neg"; "9slice"; "9splice"; "9sto"; "9subm_loop"; "9subtractmul"; "9words"]; [";add"; ";div"; ";eqb"; ";le"; ";leb"; ";lt"; ";ltb"; ";mul"; ";pow"; ";sub"; "0T"; "0a"; "0b"; "0bo"; "0carry"; "0d"]; ["0dHi"; "0dLo"; "0dLo1"; "0f"; "0g1"; "0g2"; "0h"; "0i"; "0l"; "0lo"; "0n"; "0q"; "0r"; "0s"; "0seg"; "0sh"]; ["0sl"; "0u"; "0v"; "0ws"; "0x"]]).
Lemma two_word_sub : ltac2:(TCodec.tc2 tcn__BigFactsDiv "QN'D&Gr4%211r3%411&QCzr5%3221&Q1r7%2214&O&Q0r8r1%3221%511'@'>'?&Q@&QGr;&Q2r9r2%6221%411%D261&M%9221%;21M&QI%<2;4r:%?221%?2<7%A21H%6231%B2::%C2J1%E231%G3Q<;1%Q72Q6<&QE%12>6%L231%M251qTHQB1%Q02QC1tSLQDQ21tU:QEQ91p0Q=1p0QB1p0QE1p0QF1pU2QJ1pU0QK1p4QL1p2QM1").
Proof. intros A B sh sl.
intros HA HB Hsl Hsh. cbv zeta.
rewrite (sub_borrow_test B sl HB Hsl).
pose proof (sub_borrow B sl HB Hsl) as EB. set (x := W.sub B sl) in *.
set (bo := W.b2z (W.ltu B sl)) in *. pose proof (b2z_range (W.ltu B sl)) as Rbo. fold bo in Rbo.
unfold W.sub. unfold W.wrap.
pose proof M_pos as MP.
set (u := (sh + bo) mod W.M). pose proof (Z.mod_pos_bound (sh + bo) W.M MP) as Ru. fold u in Ru.
pose proof (Z_div_mod_eq_full (sh + bo) W.M) as Du. fold u in Du.
set (a' := (A - u) mod W.M). pose proof (Z.mod_pos_bound (A - u) W.M MP) as Ra. fold a' in Ra.
pose proof (Z_div_mod_eq_full (A - u) W.M) as Da. fold a' in Da.
unfold wordZ in *. pose proof (sub_range B sl) as Rx. fold x in Rx. unfold wordZ in Rx.
exists ((sh + bo) / W.M - (A - u) / W.M).
set (qu := (sh + bo) / W.M) in *. set (qa := (A - u) / W.M) in *. set (M := W.M) in *.
assert (Ha': a' = A - u - M * qa) by lia. assert (Hu: u = sh + bo - M * qu) by lia.
split. rewrite EB, Ha', Hu. ring. nia.
Qed.
Lemma two_word_sub_exact : ltac2:(TCodec.tc2 tcn__BigFactsDiv "QI'D&Gr4%211r3%411&QCzr5%3221&Q@&QGr6&M%3221%5217r8%6214r7%9221%>251&Q1%126:&O&Q0r9r1%3221%511'?r;&Q2%F276%211%=241%H21Fr2%K221&QI%L29Jr:%O221%O2AM%Q121K%6231%@3Q=81tSLQ>B1tU:Q?I1p0L1p0Q81p0Q=1p0Q@1p0QA1pU2QE1pU0QF1p4QG1p2QH1").
Proof. intros A B sh sl.
intros HA HB Hsl Hsh Hle. destruct (two_word_sub A B sh sl HA HB Hsl Hsh) as (q & E & R). cbv zeta.
unfold wordZ in *. pose proof M_pos.
assert (q = 0) by nia. subst q. lia.
Qed.
Lemma lex_ge : ltac2:(TCodec.tc2 tcn__BigFactsDiv "Q4'D&Gr3%211r2%411'?'4&:&QFr4r6%3221&3&QB%1245&QDr5%22@1%6241%<281&Q@&QG&M%22>1%421G%42?3%621:%<231%G3F91p0I1p0L1pTBQ01pT>Q11p4Q21p2Q31").
Proof. intros A B h l. intros HB Hl. unfold wordZ in *. pose proof M_pos.
destruct (Z.ltb_spec h A); destruct (Z.eqb_spec A h); destruct (Z.leb_spec l B); destruct (Z.leb_spec (h * W.M + l) (A * W.M + B)); simpl; auto; try nia. Qed.
Lemma add_add_wrap : ltac2:(TCodec.tc2 tcn__BigFactsDiv "A'D'?&Nr3r2%3221r1%5221&Q2&Q@%1276%2215%411%<3=61pSJ>1pU6?1pU4@1").
Proof. intros u v b. unfold W.add, W.wrap. rewrite Zplus_mod_idemp_l. reflexivity. Qed.
Lemma add_wrap : ltac2:(TCodec.tc2 tcn__BigFactsDiv "='D'?&Nr2r1%3221&Q2&Q@%1254%311%93:51pSJ;1pU4<1").
Proof. intros u b. reflexivity. Qed.
Lemma sub_b2z_wrap : ltac2:(TCodec.tc2 tcn__BigFactsDiv "B'D'4'?&Q1r2&Or1%211%5241&Q2&Q@z%2215%411%;2:1%=3?71pSJ?1p2A1").
Proof. intros A b. unfold W.sub, W.wrap. f_equal. rewrite Z.add_0_l. rewrite Z.mod_small. reflexivity. rewrite M_val. destruct b; simpl; lia. Qed.
Lemma ddq1_loop_stop : ltac2:(TCodec.tc2 tcn__BigFactsDiv "O'9'D'?'4&Q4r5r4r2r1%544321(5%93821'<%12<<%221=&Q5r7r6r3%4632>=1<(;%14DD4@%249E1@%E3941p0=1pT6H1pT2I1pTHJ1p4K1p2L1pT8N1").
Proof. intros f A B q dHi dLo1. intros. destruct f; cbn [ddq1_loop]; auto. rewrite H. reflexivity. Qed.
Lemma ddq2_loop_stop : ltac2:(TCodec.tc2 tcn__BigFactsDiv "M'9'D'?'4&Q6r4r3r1%43321(5%83721'<%12;;%221<&Q7r6r5r2%4532=<1(;%14CC4?%249D1?%D3941p0=1pT0G1pTHH1p4I1p2J1pT8L1").
Proof. intros f A B q d. intros. destruct f; cbn [ddq2_loop]; auto. rewrite H. reflexivity. Qed.
Section DDQ.
Variable d : Z.
Hypothesis Hd : wordZ d.
Hypothesis Hd63 : 2 ^ 63 <= d.
Let dHi := W.shr d 32.
Let dLo := W.land d W.r_mask.
Let dLo1 := W.shl dLo 32.
Let H := W.half.
Lemma d_facts : ltac2:(TCodec.tc2 tcn__BigFactsDiv "QB'>'?'DvQO&Q@&QGvR0vE%3221vR1%6221%:3981&QC&QH+2+O%3221%521;&QE%12=<%D231z%:21=%52>@%H221vR2%E2AC%J3I21&M%H2G1%J215%J2LH%O3N21%L2JJ%Q13Q061+Q0%G2F1%Q43Q3N1&N+1%22Q21%Q52Q32%Q93Q821%Q;261%Q<2:1%Q=2=1%Q>2C1%Q?2G1%Q@2L1%QA2Q61").
Proof.
destruct (halves d Hd) as (E & R1 & R2). fold dHi dLo in E, R1, R2. fold dHi in R1. fold dLo in R2.
assert (HH: H = 2^32) by (unfold H; rewrite half_val; reflexivity).
assert (MM: W.M = H * H) by (unfold H; rewrite M_half; reflexivity).
assert (L1: dLo1 = dLo * H). { unfold dLo1. rewrite shl32. unfold H. rewrite Z.mod_small. reflexivity. fold H. lia. unfold wordZ. rewrite MM. nia. }
assert (R3: 2 ^ 31 <= dHi). { rewrite HH in *. nia. }
assert (DH: dHi * W.M + dLo1 = d * H). { rewrite L1, MM, E. nia. }
assert (AD: W.add dHi 1 = dHi + 1). { apply add_small. unfold wordZ; rewrite MM; nia. unfold wordZ; rewrite M_val; lia. rewrite MM; nia. }
repeat split; auto; lia.
Qed.
Lemma ddq1_cond_iff : ltac2:(TCodec.tc2 tcn__BigFactsDiv "J'D&Gr1%211'?'4&Q4r3r2vR0vR2%544321&QD&QGvQOvE%3221&Q@&M%62<1%321<%9251%B3A;1p0D1p4H1p2I1").
Proof. intros A B. intros HB. destruct d_facts as (E & R1 & R2 & L1 & DH & MM & HH & _).
unfold ddq1_cond. rewrite lex_ge; auto. rewrite DH. reflexivity. unfold wordZ. rewrite L1, MM. nia. Qed.
Lemma ddq1_body_exact A B q : wordZ A -> wordZ B -> d * H <= A * W.M + B ->
let '(A', B', q') := ddq1_body A B q dHi dLo1 in
A' * W.M + B' = A * W.M + B - d * H /\ wordZ A' /\ wordZ B' /\ q' = W.add q 1.
Proof.
intros HA HB Hge. destruct d_facts as (E & R1 & R2 & L1 & DH & MM & HH & _).
unfold ddq1_body. rewrite add_wrap.
assert (WL1: wordZ dLo1). { unfold wordZ. rewrite L1, MM. nia. }
pose proof (two_word_sub_exact A B dHi dLo1 HA HB WL1 ltac:(lia) ltac:(lia)) as T. cbv zeta in T.
rewrite DH in T. splits. exact T. apply sub_range. apply sub_range. reflexivity.
Qed.
Lemma ddq1_loop_spec : forall f A B q, wordZ A -> wordZ B -> 0 <= q ->
A * W.M + B < Z.of_nat f * (d * H) -> q + Z.of_nat f < W.M ->
let '(A', B', q') := ddq1_loop f A B q dHi dLo1 in
ddq1_cond A' B' dHi dLo1 = false /\ wordZ A' /\ wordZ B' /\
A' * W.M + B' = (A * W.M + B) mod (d * H) /\ q' = q + (A * W.M + B) / (d * H) /\
(forall g, ddq1_loop (f + g) A B q dHi dLo1 = (A', B', q')).
Proof.
destruct d_facts as (E & R1 & R2 & L1 & DH & MM & HH & _).
assert (DHpos: 0 < d * H). { apply Z.mul_pos_pos. lia. rewrite HH. lia. }
set (D := d * H) in *.
induction f as [|f IH]; intros A B q HA HB Hq Hlt Hqf.
- simpl Z.of_nat in Hlt. unfold wordZ in *. pose proof M_pos. exfalso. clear -HA HB Hlt H0. nia.
- assert (NN: 0 <= A * W.M + B). { pose proof M_pos. unfold wordZ in HA, HB. clear -HA HB H0. nia. }
rewrite Nat2Z.inj_succ, Z.mul_succ_l in Hlt. rewrite Nat2Z.inj_succ in Hqf.
assert (STEP: forall g, ddq1_loop (S f + g) A B q dHi dLo1 =
if ddq1_cond A B dHi dLo1 then let '(A1, B1, q1) := ddq1_body A B q dHi dLo1 in ddq1_loop (f + g) A1 B1 q1 dHi dLo1 else (A, B, q)).
{ intros g. reflexivity. }
cbn [ddq1_loop]. rewrite (ddq1_cond_iff A B HB) in STEP |- *. fold D in STEP |- *. destruct (Z.leb_spec D (A * W.M + B)).
+ pose proof (ddq1_body_exact A B q HA HB ltac:(lia)) as BE.
destruct (ddq1_body A B q dHi dLo1) as [[A1 B1] q1] eqn:EB. destruct BE as (E1 & WA1 & WB1 & Eq1). fold D in E1.
assert (Eq1': q1 = q + 1). { rewrite Eq1. apply add_small. unfold wordZ; pose proof M_pos; lia. unfold wordZ; rewrite M_val; lia. lia. }
assert (Hlt': A1 * W.M + B1 < Z.of_nat f * D) by lia.
specialize (IH A1 B1 q1 WA1 WB1 ltac:(lia) Hlt' ltac:(lia)).
destruct (ddq1_loop f A1 B1 q1 dHi dLo1) as [[A' B'] q']. destruct IH as (C & WA & WB & Em & Eq & G).
splits; auto.
* rewrite Em, E1. replace (A * W.M + B - D) with (A * W.M + B + (-1) * D) by lia. rewrite Z.mod_add by lia. reflexivity.
* rewrite Eq, E1, Eq1'. replace (A * W.M + B - D) with (A * W.M + B + (-1) * D) by lia. rewrite Z.div_add by lia. lia.
* intros g. rewrite STEP. apply G.
+ splits; auto.
all: try (rewrite ddq1_cond_iff; auto; fold D; destruct (Z.leb_spec D (A * W.M + B)); auto; lia).
all: try (rewrite Z.mod_small; auto; lia).
all: try (rewrite Z.div_small; lia).
all: try (intros g; apply ddq1_loop_stop; rewrite ddq1_cond_iff; auto; fold D; destruct (Z.leb_spec D (A * W.M + B)); auto; lia).
Qed.
Lemma ddq_step1_spec A B : wordZ A -> wordZ B ->
let '(A1, B1, qHi) := ddq_step1 A B d in
wordZ A1 /\ wordZ B1 /\ 0 <= qHi < 2 ^ 33 /\
exists c, 0 <= c <= 1 /\ A1 * W.M + B1 = A * W.M + B - qHi * (d * H) + c * (W.M * H)
/\ 0 <= A * W.M + B - qHi * (d * H) < W.M * 2 ^ 34
/\ (qHi * dLo < W.M -> c = 0) /\ qHi = A / (dHi + 1).
Proof.
intros HA HB. destruct d_facts as (E & R1 & R2 & L1 & DH & MM & HH & AD1).
unfold ddq_step1. fold dHi dLo. rewrite AD1.
assert (Hq: W.divu A (dHi + 1) = A / (dHi + 1)). { unfold W.divu. destruct (Z.eqb_spec (dHi + 1) 0); [lia|reflexivity]. }
rewrite Hq. set (qHi := A / (dHi + 1)).
assert (HqA: qHi * (dHi + 1) <= A). { unfold qHi. rewrite Z.mul_comm. apply Z.mul_div_le. lia. }
assert (HqA2: A < (dHi + 1) * (qHi + 1)). { unfold qHi. pose proof (Z.mul_succ_div_gt A (dHi + 1)). unfold Z.succ in H0. apply H0. lia. }
assert (Hq0: 0 <= qHi). { unfold qHi. apply Z.div_pos. unfold wordZ in HA; lia. lia. }
assert (Hq33: qHi < 2 ^ 33). { unfold wordZ in HA. rewrite MM, HH in HA. clear -HA HqA Hq0 R1 HH. rewrite HH in R1. nia. }
set (m := qHi * dLo). set (l := qHi * dHi).
assert (Hm: 0 <= m < 2 * W.M). { unfold m. rewrite MM, HH. clear -Hq0 Hq33 R2 HH. rewrite HH in R2. nia. }
assert (Hl: 0 <= l < 2 * W.M). { unfold l. rewrite MM, HH. clear -Hq0 Hq33 R1 HH. rewrite HH in R1. nia. }
pose proof M_pos as MP.
set (c := m / W.M). set (c2 := l / W.M).
assert (Hc: 0 <= c <= 1). { unfold c. split. apply Z.div_pos; lia. apply Z.lt_succ_r. apply Z.div_lt_upper_bound; lia. }
assert (Hc2: 0 <= c2 <= 1). { unfold c2. split. apply Z.div_pos; lia. apply Z.lt_succ_r. apply Z.div_lt_upper_bound; lia. }
assert (Emid: W.mul qHi dLo = m - c * W.M). { unfold W.mul, W.wrap. fold m. unfold c. rewrite (Z_div_mod_eq_full m W.M) at 1.
rewrite Z.add_comm, Z.mul_comm. rewrite Z.mod_add. rewrite Z.mod_mod. 2-3: lia. pose proof (Z_div_mod_eq_full m W.M). lia. }
assert (Eleft: W.mul qHi dHi = l - c2 * W.M). { unfold W.mul, W.wrap. fold l. unfold c2. pose proof (Z_div_mod_eq_full l W.M). lia. }
rewrite Emid, Eleft.
set (middle := m - c * W.M) in *. assert (Wmid: wordZ middle). { unfold wordZ, middle. pose proof (Z.mod_pos_bound m W.M MP). unfold c. pose proof (Z_div_mod_eq_full m W.M). lia. }
rewrite (shl32 middle Wmid). rewrite shr32. fold H.
set (sl := middle mod H * H). set (sh := middle / H + (l - c2 * W.M)).
assert (Hsl: wordZ sl). { unfold wordZ, sl. rewrite MM. pose proof (Z.mod_pos_bound middle H). rewrite HH in *. clear -H0. nia. }
assert (Hsh: 0 <= sh). { unfold sh. pose proof (Z.div_pos middle H). unfold wordZ in Wmid. rewrite HH in *. unfold c2. pose proof (Z.mul_div_le l W.M MP). lia. }
rewrite add_add_wrap. fold sh.
destruct (two_word_sub A B sh sl HA HB Hsl Hsh) as (q & EQ & RG). cbv zeta in EQ, RG.
set (A1 := W.sub A (W.wrap (sh + W.b2z (W.ltu B (W.sub B sl))))) in *. set (x := W.sub B sl) in *.
assert (Esum: sh * W.M + sl = m * H + l * W.M - c * (W.M * H) - c2 * (W.M * W.M)).
{ unfold sh, sl, middle. rewrite MM. pose proof (Z_div_mod_eq_full (m - c * W.M) H) as DM. rewrite MM in DM.
clear -DM HH. nia. }
assert (EdH: qHi * (d * H) = l * W.M + m * H). { unfold l, m. rewrite E, MM. clear. nia. }
assert (HT0: 0 <= A * W.M + B - qHi * (d * H)). { rewrite <- DH, L1, MM. unfold wordZ in HB. clear -HqA HB Hq0 R2 R1 HH. rewrite HH in *. nia. }
assert (HT1: A * W.M + B - qHi * (d * H) < W.M * (qHi + dHi + 1)). { rewrite <- DH, L1, MM. unfold wordZ in HB. rewrite MM in HB. clear -HqA2 HB Hq0 R2 R1 HH. rewrite HH in *. nia. }
assert (HT2: W.M * (qHi + dHi + 1) <= W.M * 2 ^ 34). { apply Z.mul_le_mono_nonneg_l. lia. rewrite HH in R1. clear -Hq33 R1. nia. }
assert (HMH: W.M * 2 ^ 34 + W.M * H <= W.M * W.M). { rewrite MM, HH. clear. nia. }
assert (EX: A1 * W.M + x = (A * W.M + B - qHi * (d * H)) + c * (W.M * H) + (q + c2) * (W.M * W.M)). { rewrite EQ, Esum, EdH. ring. }
set (X := A1 * W.M + x) in *. set (T := A * W.M + B - qHi * (d * H)) in *.
assert (HMH0: 0 <= W.M * H). { rewrite HH. clear -MP. nia. }
assert (Hq2: q + c2 = 0). { set (K := W.M * W.M) in *. set (MH := W.M * H) in *. clearbody X T K MH. clear -RG EX HT0 HT1 HT2 HMH HMH0 Hc Hc2 MP.
assert (0 <= T + c * MH < K) by nia. assert (Hk: q + c2 = 0 \/ 1 <= q + c2 \/ q + c2 <= -1) by lia.
destruct Hk as [Hk|[Hk|Hk]]; auto; exfalso; nia. }
rewrite Hq2, Z.mul_0_l, Z.add_0_r in EX.
splits.
- apply sub_range.
- apply sub_range.
- exact Hq0.
- exact Hq33.
- exists c. splits; auto; try lia. intros Hm2. unfold c. apply Z.div_small. lia.
Qed.
Lemma ddq2_cond_iff : ltac2:(TCodec.tc2 tcn__BigFactsDiv "G'D&Gr2%211'?'4&Q6r4r3vQO%43321&QD&Q@&QG&M%2281%4218%6281%>3=81p0@1p0A1p4E1p2F1").
Proof. intros A B. intros HA HB. unfold ddq2_cond. unfold wordZ in *. pose proof M_pos.
destruct (Z.eqb_spec A 0); destruct (Z.leb_spec d B); destruct (Z.leb_spec d (A * W.M + B)); simpl; auto; try lia; exfalso; nia. Qed.
Lemma ddq2_body_exact A B q : wordZ A -> wordZ B -> d <= A * W.M + B ->
let '(A', B', q') := ddq2_body A B q d in
A' * W.M + B' = A * W.M + B - d /\ wordZ A' /\ wordZ B' /\ q' = W.add q 1.
Proof.
intros HA HB Hge. unfold ddq2_body. rewrite sub_b2z_wrap.
pose proof (two_word_sub_exact A B 0 d HA HB Hd ltac:(lia) ltac:(lia)) as T. cbv zeta in T.
splits. lia. apply sub_range. apply sub_range. reflexivity.
Qed.
Lemma ddq2_loop_spec : forall f A B q, wordZ A -> wordZ B -> 0 <= q ->
A * W.M + B < Z.of_nat f * d -> q + Z.of_nat f < W.M ->
let '(A', B', q') := ddq2_loop f A B q d in
ddq2_cond A' B' d = false /\ wordZ A' /\ wordZ B' /\
A' * W.M + B' = (A * W.M + B) mod d /\ q' = q + (A * W.M + B) / d /\
(forall g, ddq2_loop (f + g) A B q d = (A', B', q')).
Proof.
assert (Dpos: 0 < d) by lia.
induction f as [|f IH]; intros A B q HA HB Hq Hlt Hqf.
- simpl Z.of_nat in Hlt. unfold wordZ in *. pose proof M_pos. exfalso. clear -HA HB Hlt H0. nia.
- assert (NN: 0 <= A * W.M + B). { pose proof M_pos. unfold wordZ in HA, HB. clear -HA HB H0. nia. }
rewrite Nat2Z.inj_succ, Z.mul_succ_l in Hlt. rewrite Nat2Z.inj_succ in Hqf.
assert (STEP: forall g, ddq2_loop (S f + g) A B q d =
if ddq2_cond A B d then let '(A1, B1, q1) := ddq2_body A B q d in ddq2_loop (f + g) A1 B1 q1 d else (A, B, q)).
{ intros g. reflexivity. }
cbn [ddq2_loop]. rewrite (ddq2_cond_iff A B HA HB) in STEP |- *. destruct (Z.leb_spec d (A * W.M + B)).
+ pose proof (ddq2_body_exact A B q HA HB ltac:(lia)) as BE.
destruct (ddq2_body A B q d) as [[A1 B1] q1] eqn:EB. destruct BE as (E1 & WA1 & WB1 & Eq1).
assert (Eq1': q1 = q + 1). { rewrite Eq1. apply add_small. unfold wordZ; pose proof M_pos; lia. unfold wordZ; rewrite M_val; lia. lia. }
assert (Hlt': A1 * W.M + B1 < Z.of_nat f * d) by lia.
specialize (IH A1 B1 q1 WA1 WB1 ltac:(lia) Hlt' ltac:(lia)).
destruct (ddq2_loop f A1 B1 q1 d) as [[A' B'] q']. destruct IH as (C & WA & WB & Em & Eq & G).
splits; auto.
* rewrite Em, E1. replace (A * W.M + B - d) with (A * W.M + B + (-1) * d) by lia. rewrite Z.mod_add by lia. reflexivity.
* rewrite Eq, E1, Eq1'. replace (A * W.M + B - d) with (A * W.M + B + (-1) * d) by lia. rewrite Z.div_add by lia. lia.
* intros g. rewrite STEP. apply G.
+ splits; auto.
all: try (rewrite ddq2_cond_iff; auto; destruct (Z.leb_spec d (A * W.M + B)); auto; lia).
all: try (rewrite Z.mod_small; auto; lia).
all: try (rewrite Z.div_small; lia).
all: try (intros g; apply ddq2_loop_stop; rewrite ddq2_cond_iff; auto; destruct (Z.leb_spec d (A * W.M + B)); auto; lia).
Qed.
Lemma ddq_step2_spec A2 B2 : wordZ A2 -> wordZ B2 -> A2 * W.M + B2 < d * H ->
let '(A4, B4, qLo) := ddq_step2 A2 B2 d in
wordZ A4 /\ wordZ B4 /\ 0 <= qLo < H /\
A4 * W.M + B4 = A2 * W.M + B2 - qLo * d /\ 0 <= A4 * W.M + B4 < 3 * d.
Proof.
intros HA HB HN. destruct d_facts as (E & R1 & R2 & L1 & DH & MM & HH & AD1). pose proof M_pos as MP.
unfold ddq_step2. fold dHi dLo. rewrite AD1.
assert (HA2: A2 < H). { unfold wordZ in HA, HB, Hd. rewrite MM in HA, HN. clear -HA HB HN Hd HH MP MM. rewrite MM in MP. nia. }
assert (Eshl: W.shl A2 32 = A2 * 2 ^ 32). { rewrite (shl32 A2 HA). fold H. rewrite Z.mod_small. rewrite HH; reflexivity. unfold wordZ in HA; lia. }
assert (Eshr: W.shr B2 32 = B2 / H) by (rewrite shr32; reflexivity).
assert (RB: 0 <= B2 / H < H). { unfold wordZ in HB. rewrite MM in HB. split. apply Z.div_pos; lia. apply Z.div_lt_upper_bound; lia. }
rewrite Eshl, Eshr. unfold W.lor. rewrite lor_high_low. 2: lia. 2: unfold wordZ in HA; lia. 2: rewrite <- HH; exact RB.
rewrite <- HH. set (t := A2 * H + B2 / H).
assert (Ht: t * H <= A2 * W.M + B2 < (t + 1) * H). { unfold t. rewrite MM. pose proof (Z_div_mod_eq_full B2 H). pose proof (Z.mod_pos_bound B2 H). clear -H0 H1 HH. rewrite HH in *. nia. }
assert (Htd: t < d). { clear -Ht HN HH. rewrite HH in *. nia. }
assert (Wt: wordZ t). { unfold wordZ. unfold wordZ in Hd. split. unfold t. clear -HA RB HA2 HH. destruct HA. rewrite HH in *. nia. lia. }
assert (Hq: W.divu t (dHi + 1) = t / (dHi + 1)). { unfold W.divu. destruct (Z.eqb_spec (dHi + 1) 0); [lia|reflexivity]. }
rewrite Hq. set (qLo := t / (dHi + 1)).
assert (HqA: qLo * (dHi + 1) <= t). { unfold qLo. rewrite Z.mul_comm. apply Z.mul_div_le. lia. }
assert (HqA2: t < (dHi + 1) * (qLo + 1)). { unfold qLo. pose proof (Z.mul_succ_div_gt t (dHi + 1)). unfold Z.succ in H0. apply H0. lia. }
assert (Hq0: 0 <= qLo). { unfold qLo. apply Z.div_pos. unfold wordZ in Wt; lia. lia. }
assert (HqH: qLo < H). { clear -HqA Htd E R1 R2 Hq0. nia. }
assert (Eright: W.mul qLo dLo = qLo * dLo). { apply mul_small; try lia; rewrite MM; clear -Hq0 HqH R2; nia. }
assert (Emid: W.mul qLo dHi = qLo * dHi). { apply mul_small; try lia; rewrite MM; clear -Hq0 HqH R1; nia. }
rewrite Eright, Emid.
assert (Wr: wordZ (qLo * dLo)). { unfold wordZ. rewrite MM. clear -Hq0 HqH R2. nia. }
assert (Wm: wordZ (qLo * dHi)). { unfold wordZ. rewrite MM. clear -Hq0 HqH R1. nia. }
assert (Hqd: qLo * d <= A2 * W.M + B2). { rewrite E. clear -HqA Ht Hq0 R2 R1 HH. rewrite HH in *. nia. }
rewrite (sub_b2z_wrap A2).
pose proof (two_word_sub_exact A2 B2 0 (qLo * dLo) HA HB Wr ltac:(lia)) as T1. cbv zeta in T1.
assert (P1: 0 * W.M + qLo * dLo <= A2 * W.M + B2). { assert (qLo * dLo <= qLo * d) by (rewrite E; clear -Hq0 R1 R2 HH; rewrite HH in *; nia). lia. }
specialize (T1 P1).
set (x := W.sub B2 (qLo * dLo)) in *. set (A3 := W.sub A2 (W.wrap (0 + W.b2z (W.ltu B2 x)))) in *.
assert (WA3: wordZ A3) by apply sub_range. assert (Wx: wordZ x) by apply sub_range.
rewrite (shl32 (qLo * dHi) Wm). rewrite shr32. fold H. rewrite add_wrap.
set (sl := (qLo * dHi) mod H * H). set (sh := qLo * dHi / H).
assert (Wsl: wordZ sl). { unfold wordZ, sl. rewrite MM. pose proof (Z.mod_pos_bound (qLo * dHi) H). clear -H0 HH. rewrite HH in *. nia. }
assert (Hsh: 0 <= sh). { unfold sh. apply Z.div_pos. clear -Hq0 R1; nia. lia. }
assert (Esum: sh * W.M + sl = qLo * dHi * H). { unfold sh, sl. rewrite MM. pose proof (Z_div_mod_eq_full (qLo * dHi) H). clear -H0 HH. rewrite HH in *. nia. }
assert (P2: sh * W.M + sl <= A3 * W.M + x). { rewrite Esum, T1. rewrite E in Hqd. clear -Hqd Hq0 R1 R2 HH. rewrite HH in *. nia. }
pose proof (two_word_sub_exact A3 x sh sl WA3 Wx Wsl Hsh P2) as T2. cbv zeta in T2.
rewrite T1, Esum in T2.
splits. apply sub_range. apply sub_range. exact Hq0. exact HqH.
- rewrite T2, E. ring.
- rewrite T2. lia.
- rewrite T2.
assert (S1: (t + 1) * H <= (dHi + 1) * (qLo + 1) * H). { apply Z.mul_le_mono_nonneg_r. rewrite HH; lia. lia. }
assert (S3: (dHi + 1) * (qLo + 1) * H - qLo * dHi * H = H * (qLo + dHi + 1)) by ring.
assert (S4: H * (qLo + dHi + 1) <= H * H + dHi * H). { clear -HqH R1 HH Hq0. rewrite HH in *. nia. }
assert (S5: H * H <= 2 * d). { rewrite HH. clear -Hd63. change (2 ^ 32 * 2 ^ 32) with (2 * 2 ^ 63). lia. }
assert (S6: dHi * H <= d). { rewrite E. lia. }
assert (S7: 0 <= qLo * dLo) by (clear -Hq0 R2; nia).
clear -Ht S1 S3 S4 S5 S6 S7 E. nia.
Qed.
Theorem DDquotient_loops A B : wordZ A -> wordZ B ->
let '(A1, B1, qHi) := ddq_step1 A B d in
let '(A2, B2, qHi') := ddq1_loop 10 A1 B1 qHi dHi dLo1 in
let '(A3, B3, qLo) := ddq_step2 A2 B2 d in
let '(A4, B4, qLo') := ddq2_loop 3 A3 B3 qLo d in
wordZ A1 /\ wordZ B1 /\ wordZ A2 /\ wordZ B2 /\ wordZ A3 /\ wordZ B3 /\ wordZ A4 /\ wordZ B4 /\
0 <= qHi < 2 ^ 33 /\ 0 <= qHi' < 2 ^ 34 /\ 0 <= qLo < H /\ 0 <= qLo' < H + 3 /\
A1 * W.M + B1 < 10 * (d * H) /\ A2 * W.M + B2 < d * H /\ A3 * W.M + B3 < 3 * d /\ A4 * W.M + B4 < d /\
ddq1_cond A2 B2 dHi dLo1 = false /\ ddq2_cond A4 B4 d = false /\
(forall g, ddq1_loop (10 + g) A1 B1 qHi dHi dLo1 = (A2, B2, qHi')) /\
(forall g, ddq2_loop (3 + g) A3 B3 qLo d = (A4, B4, qLo')).
Proof.
intros HA HB. destruct d_facts as (E & R1 & R2 & L1 & DH & MM & HH & AD1). pose proof M_pos as MP.
pose proof (ddq_step1_spec A B HA HB) as S1. destruct (ddq_step1 A B d) as [[A1 B1] qHi].
destruct S1 as (WA1 & WB1 & HqHi & c & Hc & EN1 & HT & Hc0 & EqHi).
assert (HN1: A1 * W.M + B1 < 10 * (d * H)).
{ rewrite EN1. assert (W.M * 2 ^ 34 + W.M * H <= 10 * (d * H)). { rewrite MM, HH. clear -Hd63. change (2^32 * 2^32) with (2 * 2^63). nia. } clear -H0 HT Hc MP HH. rewrite HH in *. nia. }
pose proof (ddq1_loop_spec 10 A1 B1 qHi WA1 WB1 ltac:(lia) ltac:(simpl Z.of_nat; lia) ltac:(simpl Z.of_nat; rewrite M_val; lia)) as L1s.
destruct (ddq1_loop 10 A1 B1 qHi dHi dLo1) as [[A2 B2] qHi']. destruct L1s as (C1 & WA2 & WB2 & EN2 & Eq1 & G1).
assert (HN2: 0 <= A2 * W.M + B2 < d * H). { rewrite EN2. apply Z.mod_pos_bound. clear -Hd63 HH. rewrite HH. nia. }
pose proof (ddq_step2_spec A2 B2 WA2 WB2 ltac:(lia)) as S2. destruct (ddq_step2 A2 B2 d) as [[A3 B3] qLo].
destruct S2 as (WA3 & WB3 & HqLo & EN3 & HN3).
pose proof (ddq2_loop_spec 3 A3 B3 qLo WA3 WB3 ltac:(lia) ltac:(simpl Z.of_nat; lia) ltac:(simpl Z.of_nat; rewrite M_val; rewrite HH in HqLo; lia)) as L2s.
destruct (ddq2_loop 3 A3 B3 qLo d) as [[A4 B4] qLo']. destruct L2s as (C2 & WA4 & WB4 & EN4 & Eq2 & G2).
assert (HN4: 0 <= A4 * W.M + B4 < d). { rewrite EN4. apply Z.mod_pos_bound. lia. }
assert (Hq1: 0 <= (A1 * W.M + B1) / (d * H) < 10).
{ split. apply Z.div_pos. clear -WA1 WB1 MP; unfold wordZ in *; nia. clear -Hd63 HH; rewrite HH; nia.
apply Z.div_lt_upper_bound. clear -Hd63 HH; rewrite HH; nia. lia. }
assert (Hq2: 0 <= (A3 * W.M + B3) / d < 3).
{ split. apply Z.div_pos; lia. apply Z.div_lt_upper_bound; lia. }
splits; auto; try lia.
Qed.
Theorem DDquotient_fuel : ltac2:(TCodec.tc2 tcn__BigFactsDiv "I'D&Gr2%211'9'?&L&Au:%2217u3r1%5221r6r5vQO%:574321%;597432%=3B21pT<?1pT:@1p0B1p0C1p4G1p2H1").
Proof. intros A B.
intros HA HB g1 g2. pose proof (DDquotient_loops A B HA HB) as L. unfold DDquotient_f. fold dHi dLo dLo1.
destruct (ddq_step1 A B d) as [[A1 B1] qHi].
destruct (ddq1_loop 10 A1 B1 qHi dHi dLo1) as [[A2 B2] qHi'] eqn:E1.
destruct (ddq_step2 A2 B2 d) as [[A3 B3] qLo] eqn:E2.
destruct (ddq2_loop 3 A3 B3 qLo d) as [[A4 B4] qLo'] eqn:E3.
destruct L as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G1 & G2).
rewrite G1, E2, G2. reflexivity.
Qed.
Corollary DDquotient_is_f10_3 : ltac2:(TCodec.tc2 tcn__BigFactsDiv "C'D&Gr2%211'?&Kr4r3vQO%43321&Lu:u3%3521765%:3>51p0<1p0=1p4A1p2B1").
Proof. intros A B. intros. unfold DDquotient, DDQ_FUEL1, DDQ_FUEL2. replace 16%nat with (10 + 6)%nat by reflexivity. replace 8%nat with (3 + 5)%nat by reflexivity. apply DDquotient_fuel; auto. Qed.
Theorem DDquotient_exact : ltac2:(TCodec.tc2 tcn__BigFactsDiv "I'D&Gr2%211&QEr4vQO%3221'?&Kr5%23165&QA&Q@&QG&M%2261%421<%621<%;3C81p0=1p0B1p0C1p4G1p2H1").
Proof. intros A B.
intros HA HB HAd. destruct d_facts as (E & R1 & R2 & L1 & DH & MM & HH & AD1). pose proof M_pos as MP.
rewrite DDquotient_is_f10_3 by auto. unfold DDquotient_f. fold dHi dLo dLo1.
pose proof (ddq_step1_spec A B HA HB) as S1. destruct (ddq_step1 A B d) as [[A1 B1] qHi].
destruct S1 as (WA1 & WB1 & HqHi & c & Hc & EN1 & HT & Hc0 & EqHi).
assert (HqA: qHi * (dHi + 1) <= A). { rewrite EqHi. rewrite Z.mul_comm. apply Z.mul_div_le. lia. }
assert (HqH: qHi < H). { clear -HqA HAd E R1 R2 HqHi. nia. }
assert (Hc00: c = 0). { apply Hc0. rewrite MM. clear -HqH HqHi R2. nia. }
subst c. rewrite Z.mul_0_l, Z.add_0_r in EN1.
set (N := A * W.M + B) in *.
assert (DHpos: 0 < d * H). { clear -Hd63 HH. rewrite HH. nia. }
assert (HN1: A1 * W.M + B1 < 10 * (d * H)).
{ rewrite EN1. assert (W.M * 2 ^ 34 <= 10 * (d * H)). { rewrite MM, HH. clear -Hd63. change (2^32 * 2^32) with (2 * 2^63). nia. } lia. }
pose proof (ddq1_loop_spec 10 A1 B1 qHi WA1 WB1 ltac:(lia)) as L1s.
destruct (ddq1_loop 10 A1 B1 qHi dHi dLo1) as [[A2 B2] qHi'].
specialize (L1s ltac:(simpl Z.of_nat; lia) ltac:(simpl Z.of_nat; rewrite M_val; lia)).
destruct L1s as (C1 & WA2 & WB2 & EN2 & Eq1 & _).
assert (Eq1': qHi' = N / (d * H)). { rewrite Eq1, EN1. replace (N - qHi * (d * H)) with (N + (- qHi) * (d * H)) by ring. rewrite Z.div_add by lia. lia. }
assert (EN2': A2 * W.M + B2 = N mod (d * H)). { rewrite EN2, EN1. replace (N - qHi * (d * H)) with (N + (- qHi) * (d * H)) by ring. rewrite Z.mod_add by lia. reflexivity. }
pose proof (Z.mod_pos_bound N (d * H) DHpos) as HN2. rewrite <- EN2' in HN2.
pose proof (ddq_step2_spec A2 B2 WA2 WB2 ltac:(lia)) as S2. destruct (ddq_step2 A2 B2 d) as [[A3 B3] qLo].
destruct S2 as (WA3 & WB3 & HqLo & EN3 & HN3).
pose proof (ddq2_loop_spec 3 A3 B3 qLo WA3 WB3 ltac:(lia) ltac:(simpl Z.of_nat; lia) ltac:(simpl Z.of_nat; rewrite M_val; rewrite HH in HqLo; lia)) as L2s.
destruct (ddq2_loop 3 A3 B3 qLo d) as [[A4 B4] qLo']. destruct L2s as (C2 & WA4 & WB4 & EN4 & Eq2 & G2).
assert (Eq2': qLo' = (N mod (d * H)) / d). { rewrite Eq2, EN3, EN2'. replace (N mod (d * H) - qLo * d) with (N mod (d * H) + (- qLo) * d) by ring. rewrite Z.div_add by lia. lia. }
assert (HN: 0 <= N < d * W.M). { subst N. unfold wordZ in HA, HB. clear -HA HB HAd MP. nia. }
assert (HqHi': 0 <= qHi' < H). { rewrite Eq1'. split. apply Z.div_pos; lia. apply Z.div_lt_upper_bound. lia. rewrite MM in HN. clear -HN. nia. }
rewrite EN2' in HN2.
assert (HqLo': 0 <= qLo' < H). { rewrite Eq2'. split. apply Z.div_pos; lia. apply Z.div_lt_upper_bound. lia. lia. }
assert (WqHi': wordZ qHi'). { unfold wordZ. rewrite MM. clear -HqHi' R1. nia. }
assert (Eshl: W.shl qHi' 32 = qHi' * H). { rewrite (shl32 qHi' WqHi'). fold H. rewrite Z.mod_small. reflexivity. lia. }
rewrite Eshl. rewrite add_small.
2:{ unfold wordZ; rewrite MM; clear -HqHi' R1; nia. } 2:{ unfold wordZ; rewrite MM; clear -HqLo' R1; nia. }
2:{ rewrite MM. clear -HqHi' HqLo'. nia. }
rewrite Eq1', Eq2'.
rewrite (Z_div_mod_eq_full N (d * H)) at 3.
replace (d * H * (N / (d * H)) + N mod (d * H)) with (N / (d * H) * H * d + N mod (d * H)) by ring.
rewrite Z.div_add_l by lia. reflexivity.
Qed.
End DDQ.
Lemma subm_loop_shape : ltac2:(TCodec.tc2 tcn__BigFactsDiv "Q@'9'D&Q?&Hr2%211'>&QCzr5%3221+1%5231%7231'<%12=>&Q=r8r7r6r4r3%66543=21'?&7&6r1%23IJ1%42K1%52LD%73N21%L14&=%13OQ07%K2J1%L22H%N221%O261%Q0281tTJHA1p0K1p0Q41pSJQ81pSHQ91pTHQ;1pSNQ<1pT@Q>1pT8Q?1").
Proof. intros f.
induction f as [|f IH]; intros i carry q a b Wa Hc; cbn [subm_loop].
- simpl. auto.
- destruct (DDproduct (nth_w b i) q) as [hi lo].
match goal with |- context [subm_loop f (S i) ?c q ?a' b] => specialize (IH (S i) c q a' b) end.
cbv zeta in IH |- *. destruct IH as (L & W1 & C).
+ apply upd_words_ok. apply upd_words_ok; auto. apply sub_range. apply sub_range.
+ apply b2z_range.
+ rewrite !upd_length in L. auto.
Qed.
Lemma addback_loop_shape : ltac2:(TCodec.tc2 tcn__BigFactsDiv "J'9'D&Q?&Hr2%211'>'?&7&Q3r6r5r4r3%554321:%72>1%82?3%:3A21%?14%=221p0?1pSJC1pSHD1pSNF1pT@H1pT8I1").
Proof. intros f.
induction f as [|f IH]; intros i carry a b Wa; cbn [addback_loop]. auto.
match goal with |- context [addback_loop f (S i) ?c ?a' b] => specialize (IH (S i) c a' b) end.
destruct IH as [L W1]. apply upd_words_ok; auto. apply add_range. rewrite upd_length in L. auto.
Qed.
Lemma subtractmul_shape : ltac2:(TCodec.tc2 tcn__BigFactsDiv "Q2&Q?'9'D&Hr4%211&Gr2%211'>'?&7&6&Q>r6r5r3%4432=1%63B@1%82A1%92B6%;3D21%C14&=%13HF7%C11%A241%B261p0D1p0H1pTHL1pTFN1pSJQ01pSHQ11").
Proof. intros a b n q.
intros Wa Wq. unfold subtractmul.
pose proof (subm_loop_shape n 0 0 q a b Wa ltac:(lia)) as S. destruct (subm_loop n 0 0 q a b) as [a1 carry]. cbv zeta in S. simpl in S.
destruct S as (L & W1 & C). destruct (Z.eqb_spec carry 0); simpl.
- repeat split; auto; unfold wordZ in *; lia.
- pose proof (addback_loop_shape n 0 0 a1 b W1) as [L2 W2]. split. rewrite upd_length, L2; auto. split.
apply upd_words_ok; auto. unfold wordZ; rewrite M_val; lia. apply sub_range.
Qed.
Lemma slice_length : ltac2:(TCodec.tc2 tcn__BigFactsDiv "B&Q?'9'C&7'D&Q:r3r2r1%43321%7261&B%9286%2216%<241pTF>1pTD?1pU8A1").
Proof. intros ws lo n. unfold slice. rewrite length_firstn, length_skipn. lia. Qed.
Lemma splice_length : ltac2:(TCodec.tc2 tcn__BigFactsDiv "I'8'D%211'9'C&7r1%2261&Br3%5291r2%4221%9261'?&Q;r4%23186%=2A1%>2B3%63A21p081pTND1pTDD1pU8F1").
Proof. intros ws lo seg. intros. unfold splice. rewrite !length_app, length_firstn, length_skipn. lia. Qed.
Lemma splice_words_ok : ltac2:(TCodec.tc2 tcn__BigFactsDiv "A&Q?'9&Hr3%211r2%411&Q;r5r4%33217%911p061p091pTN>1pTD>1pU8@1").
Proof. intros ws lo seg. intros. unfold splice. apply words_ok_app. apply words_ok_firstn; auto. apply words_ok_app; auto. apply words_ok_skipn; auto. Qed.
Lemma slice_words_ok : ltac2:(TCodec.tc2 tcn__BigFactsDiv ">&Q?'9&Hr3%211&Q:r4r2%33251%711p061pTF:1pTD;1pU8=1").
Proof. intros ws lo n. intros. unfold slice. apply words_ok_firstn. apply words_ok_skipn. auto. Qed.
Lemma divstep_shape k l d dws rws qws : words_ok rws -> words_ok qws ->
let (r1, q1) := divstep k l d dws rws qws in
length r1 = length rws /\ length q1 = length qws /\ words_ok r1 /\ words_ok q1.
Proof.
intros Wr Wq. unfold divstep.
pose proof (subtractmul_shape (slice rws (k - l - 1) (l + 2)) dws (l + 1) (DDquotient (nth_w rws k) (nth_w rws (k - 1)) d)
(slice_words_ok _ _ _ Wr) ltac:(unfold DDquotient, DDquotient_f; repeat (destruct (ddq_step1 _ _ _) as [[? ?] ?] || destruct (ddq1_loop _ _ _ _ _ _) as [[? ?] ?] || destruct (ddq_step2 _ _ _) as [[? ?] ?] || destruct (ddq2_loop _ _ _ _ _) as [[? ?] ?]); apply add_range)) as S.
destruct (subtractmul _ _ _ _) as [win q']. simpl in S. destruct S as (L & W1 & Wq').
repeat split. rewrite splice_length; auto. rewrite L. apply slice_length. apply upd_length. apply splice_words_ok; auto. apply upd_words_ok; auto.
Qed.
Lemma divloop_shape f : forall k l d dws rws qws, words_ok rws -> words_ok qws ->
let (r1, q1) := divloop f k l d dws rws qws in
length r1 = length rws /\ length q1 = length qws /\ words_ok r1 /\ words_ok q1.
Proof.
induction f as [|f IH]; intros k l d dws rws qws Wr Wq; cbn [divloop]. auto.
pose proof (divstep_shape k l d dws rws qws Wr Wq) as S. destruct (divstep k l d dws rws qws) as [r1 q1]. destruct S as (L1 & L2 & W1 & W2).
specialize (IH (k - 1)%nat l d dws r1 q1 W1 W2). destruct (divloop f (k - 1) l d dws r1 q1) as [r2 q2]. destruct IH as (L3 & L4 & W3 & W4).
repeat split; auto; congruence.
Qed.
Lemma halfdiv_loop_shape f : forall divisor dHi tws qws, words_ok qws -> wordZ dHi -> wordZ divisor -> words_ok tws ->
let (q1, r) := halfdiv_loop f divisor dHi tws qws in length q1 = length qws /\ words_ok q1 /\ wordZ r.
Proof.
induction f as [|i IH]; intros divisor dHi tws qws Wq Wd Wv Wt; cbn [halfdiv_loop]. auto.
match goal with |- context [halfdiv_loop i divisor ?dh tws ?qw] => specialize (IH divisor dh tws qw) end.
assert (WD1: wordZ (W.lor (W.shl dHi 32) (W.shr (nth_w tws i) 32))). { apply lor_range. apply shl_range. apply shr_range. apply words_ok_nth; auto. lia. }
assert (WD2: wordZ (W.lor (W.shl (W.remu (W.lor (W.shl dHi 32) (W.shr (nth_w tws i) 32)) divisor) 32) (W.land (nth_w tws i) W.r_mask))).
{ apply lor_range. apply shl_range. apply land_range. apply words_ok_nth; auto. unfold wordZ; rewrite r_mask_val, M_val; lia. }
destruct (halfdiv_loop _ _ _ _ _) as [q1 r]. destruct IH as (L & W1 & Wr).
- apply upd_words_ok; auto. apply lor_range. apply shl_range. apply divu_range; auto.
- apply remu_range; auto.
- auto. - auto.
- rewrite upd_length in L. auto.
Qed.
Lemma normalize_mspec N denom num : okN N denom -> okN N num -> reduced denom ->
(size denom + 2 <= N)%nat -> (size num + 2 <= N)%nat ->
mspec (normalize denom num)
(fun r => let '(d', n', x, sd) := r in
okN N d' /\ okN N n' /\ (size d' <= size denom + 2)%nat /\ (size n' <= size num + 2)%nat /\ 0 <= x <= 63)
6 (BB N).
Proof.
intros Hd Hn Hr HsD HsN. unfold normalize.
destruct (Nat.eqb_spec (size denom) 0).
- apply mspec_ret. splits; auto; lia.
- set (x := norm_count NORM_FUEL (nth_w (s_words denom) (size denom - 1)) 0).
assert (Hx: 0 <= x <= 63).
{ apply norm_count_64. apply words_ok_nth. apply (okN_words N); auto.
apply reduced_ws_top; auto. intro E. unfold size in n. rewrite E in n. simpl in n. lia. }
eapply mspec_bind' with (K1 := 2%nat). apply shl_bits_mspec; eauto. lia. lia. 2: lia.
intros d1 (Hd1 & _ & _ & Sd1 & _ & _).
eapply mspec_bind' with (K1 := 2%nat). apply shl_bits_mspec; eauto. lia. lia. 2: lia.
intros n1 (Hn1 & _ & _ & Sn1 & _ & _).
destruct ((0 <? size denom - 1)%nat && W.ltu (nth_w (s_words d1) (size denom - 1)) (nth_w (s_words d1) (size denom - 1 - 1))).
+ eapply mspec_bind' with (K1 := 1%nat). apply mul_word_mspec; eauto. unfold wordZ; rewrite max_word_val, M_val; lia. lia. 2: lia.
intros d2 (Hd2 & _ & _ & Sd2 & _ & _).
eapply mspec_bind' with (K1 := 1%nat). apply mul_word_mspec; eauto. unfold wordZ; rewrite max_word_val, M_val; lia. lia. 2: lia.
intros n2 (Hn2 & _ & _ & Sn2 & _ & _).
apply mspec_ret. splits; auto; lia.
+ apply mspec_ret. splits; auto; lia.
Qed.
Definition un_post N (rem : sto) (u : un_outcome) : Prop :=
match u with UnOk r => okN N r | UnAssert rc => okN N rc end.
Definition unnorm_ok N T Ku (unnorm : sto -> Z -> bool -> M un_outcome) : Prop :=
forall rem x sd, okN N rem -> (size rem <= T)%nat -> 0 <= x <= 63 -> mspec (unnorm rem x sd) (un_post N rem) Ku (BB N).
Definition div_post N (denom_ : sto) (o : div_outcome) : Prop :=
match o with
| DivOk q r => okN N q /\ okN N r
| DivZero => size denom_ = 0%nat
| DivAssert qc rc => okN N qc /\ okN N rc
end.
Lemma no_unnorm_ok : ltac2:(TCodec.tc2 tcn__BigFactsDiv "9'9&Ir2r1(2&Q8%544321pSF71pQ>81").
Proof. intros N T. intros rem x sd Hr Hs Hx. unfold no_unnorm. apply mspec_ret. simpl. auto. Qed.
Lemma okN_reduced_copy_neg : ltac2:(TCodec.tc2 tcn__BigFactsDiv "<'Q<'4&Jr2%211&Q9r3%2214%611p051pSJ91pTL;1"). Proof. intros s b. apply reduced_set_neg. Qed.
Definition sum_post N (r : sto + sto) : Prop := match r with inl q => okN N q | inr qc => okN N qc end.
Definition mod_post N (divisor : sto) (m : mod_outcome) : Prop :=
match m with ModOk x => okN N x | ModZero => size divisor = 0%nat | ModAssert xc => okN N xc end.
