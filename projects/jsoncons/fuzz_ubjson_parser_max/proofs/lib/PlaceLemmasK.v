(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AxSymExec3K AsanPlanCoreK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import AX2K. Import APCK.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PlaceLemmasK () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanCoreK.APCK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3K.AX2K."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PlaceLemmasK."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."], [["0A"; "1Some"; "1bool"; "1false"; "1fst"; "1list"; "1nat"; "1option"; "1pair"; "1prod"; "1snd"; "2and"; "2eq"; "2ex"; "2iff"; "2or"]; ["3Z"; "4am_base"; "4am_len"; "4amap"; "4atable"; "4first_run"; "4grant_vlo"; "4img_hi"; "4img_lo"; "4is_fog"; "4iv_coalesce"; "4iv_insert"; "4iv_sort"; "4lit_ivs"; "5ELit"; "5expr"]; ["5two64"; "6covered"; "6runs"; "7In"; "8add"; "8div"; "8le"; "8lt"; "8modulo"; "0a"; "0a'"; "0hi"; "0k"; "0l"; "0lo"; "0m"]; ["0ms"; "0n"; "0nZ"; "0nlo"; "0p"; "0q"; "0z"]]).
Definition covered (l : list (Z * Z)) (lo n : Z) : Prop :=
forall z, lo <= z < lo + n -> exists p, In p l /\ fst p <= z < fst p + snd p.
Lemma iv_insert_In : ltac2:(TCodec.tc2 tcn__PlaceLemmasK "F'9'@%2211'5%112&>&Q3r1&Kr3r2%3221%63:51'?'<%13=86%:3>96%4221%=261pS<A1pRL@1pS:C1").
Proof.
intros p l. induction l as [|r l IH]; intros q; cbn [iv_insert].
- cbn. split; [intros [H|[]]; left; symmetry; exact H | intros [H|[]]; left; symmetry; exact H].
- destruct (Z.leb (fst p) (fst r)).
+ cbn. split; [intros [H|H]; [left; symmetry; exact H | right; exact H] | intros [H|H]; [left; symmetry; exact H | right; exact H]].
+ cbn. rewrite IH. split.
* intros [H|[H|H]]; [right; left; exact H | left; exact H | right; right; exact H].
* intros [H|[H|H]]; [right; left; exact H | left; exact H | right; right; exact H].
Qed.
Lemma iv_sort_In : ltac2:(TCodec.tc2 tcn__PlaceLemmasK "@'5'9'@%2211%411&>&Q3r1&Lr2%211%53841%63953%8221pS<;1pRL;1").
Proof.
induction l as [|p l IH]; intros q; cbn [iv_sort]; [tauto|]. rewrite iv_insert_In, IH. cbn.
split; (intros [H|H]; [left; symmetry; exact H | right; exact H]).
Qed.
Lemma iv_coalesce_covered : forall l t, In t (iv_coalesce l) ->
let '(lo, n, k) := t in covered l lo n.
Proof.
induction l as [|[a n] r IH]; intros t Ht; [destruct Ht|].
cbn [iv_coalesce] in Ht.
destruct (iv_coalesce r) as [|[[b m] k] r'] eqn:Hc.
- destruct Ht as [<-|[]]. intros z Hz. exists (a, n). split; [left; reflexivity | cbn; lia].
- destruct (Z.eqb (a + n) b && Z.ltb 0 n && Z.ltb 0 m)%bool eqn:Hb.
+ apply andb_prop in Hb as [Hb Hm]. apply andb_prop in Hb as [Hb Hn]. apply Z.eqb_eq in Hb. apply Z.ltb_lt in Hn. apply Z.ltb_lt in Hm.
destruct Ht as [<-|Ht].
* intros z Hz. destruct (Z_lt_le_dec z (a + n)) as [Hlt|Hge].
-- exists (a, n). split; [left; reflexivity | cbn; lia].
-- pose proof (IH (b, m, k) (or_introl eq_refl)) as C. cbn in C.
destruct (C z ltac:(lia)) as (p & Hp & Hpz). exists p. split; [right; exact Hp | exact Hpz].
* pose proof (IH t (or_intror Ht)) as C. destruct t as [[lo n0] k0]. intros z Hz.
destruct (C z Hz) as (p & Hp & Hpz). exists p. split; [right; exact Hp | exact Hpz].
+ destruct Ht as [<-|Ht].
* intros z Hz. exists (a, n). split; [left; reflexivity | cbn; lia].
* pose proof (IH t Ht) as C. destruct t as [[lo n0] k0]. intros z Hz.
destruct (C z Hz) as (p & Hp & Hpz). exists p. split; [right; exact Hp | exact Hpz].
Qed.
Lemma lit_ivs_In : ltac2:(TCodec.tc2 tcn__PlaceLemmasK "QI'5'C%211'@&Q3'9%1233(8r2r1%347721&Mr3%211%:3841';&Q6z%2216&Q7%123<&Q4%12:>&Q0%5221%:251%;281'=r5%I3LD1'<'2&I%11H(3%53421'O&A%11M(Nr4%211%<3641&B%11Q3%61Q1%@3:21%Q0251%Q12=1%Q22D1qS0QA1%H2QB1%Q52J1p0Q71pS4QC1pRDQD1pS2QF1").
Proof.
induction ms as [|m ms IH]; intros a n H; [destruct H|]. cbn [lit_ivs] in H.
assert (REST : In (a, n) (lit_ivs ms) -> (0 <= a /\ 0 < n /\ a + n < two64)
/\ exists m0, In m0 (m :: ms) /\ is_fog m0 = false /\ am_base m0 = ELit a /\ am_len m0 = ELit n).
{ intros H'. destruct (IH a n H') as (B & m' & Hm' & X). split; [exact B|]. exists m'. split; [right; exact Hm' | exact X]. }
destruct (is_fog m) eqn:Hf; [exact (REST H)|].
destruct (am_base m) eqn:Hb; try exact (REST H).
destruct (am_len m) eqn:Hl; try exact (REST H).
match type of H with In _ (if ?c then _ else _) => destruct c eqn:Hc end; [|exact (REST H)].
destruct H as [H|H]; [|exact (REST H)].
injection H as <- <-.
apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [H1 H2].
apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.ltb_lt in H3.
split; [lia|]. exists m. split; [left; reflexivity|]. auto.
Qed.
Lemma iv_coalesce_pos : ltac2:(TCodec.tc2 tcn__PlaceLemmasK "Q1'5'9'@%2211%411&Q3r1r2%33521&Q7z&:%13::5%4231p061pS:<1'6%@2>1(8r3%24BB1=%34B51?&Jr5%211%D3841%A2@7p021pRJ<1pS4K1pRNL1p0@1pRLL1").
Proof.
induction l as [|[a n] r IH]; intros Hpos lo n0 k Ht; [destruct Ht|].
cbn [iv_coalesce] in Ht.
assert (Hn : 0 < n) by (exact (Hpos (a, n) (or_introl eq_refl))).
assert (Hr : forall p, In p r -> 0 < snd p) by (intros p Hp; apply Hpos; right; exact Hp).
destruct (iv_coalesce r) as [|[[b m] k'] r'] eqn:Hc.
- destruct Ht as [Ht|[]]. injection Ht as <- <- <-. exact Hn.
- destruct (Z.eqb (a + n) b && Z.ltb 0 n && Z.ltb 0 m)%bool eqn:Hb.
+ apply andb_prop in Hb as [Hb Hm]. apply Z.ltb_lt in Hm.
destruct Ht as [Ht|Ht]; [injection Ht as <- <- <-; lia|]. eapply IH; [exact Hr | right; exact Ht].
+ destruct Ht as [Ht|Ht]; [injection Ht as <- <- <-; exact Hn|]. eapply IH; [exact Hr | exact Ht].
Qed.
Lemma run_apart : ltac2:(TCodec.tc2 tcn__PlaceLemmasK "QB'5'9'@%2211%411&Q1r5r4r3%43321&Q7zr2%3221%4238&Q3r1r9%33?21'?&Q6&Q4r7r6%3221&4%13HH>%7231&:%13KKA%9241%;219%=251p0?1pS:O1%>2<Mr8%A221%A22@%C21@%E231p071p0L1p0N1p0Q31pS6Q;1pRDQ<1pS4Q=1pRNQ>1pRLQ=1").
Proof.
intros l lo n a nZ Hcov HnZ Hn Hap.
destruct (Z_lt_le_dec a (lo + n)) as [H1|H1]; [|right; lia].
destruct (Z_lt_le_dec lo (a + nZ)) as [H2|H2]; [|left; lia].
exfalso.
set (z := Z.max a lo).
destruct (Hcov z ltac:(unfold z; lia)) as (p & Hp & Hz).
destruct (Hap p Hp); unfold z in Hz; lia.
Qed.
Definition runs (ms : list amap) : list (Z * Z * nat) := iv_coalesce (iv_sort (lit_ivs ms)).
Lemma runs_covered : ltac2:(TCodec.tc2 tcn__PlaceLemmasK "QB'5'C%211'@'6&Q3'9%1244%2214(8r3r2%349921r1%547:21&Q2r4%211%=3:41';&Q6r5%2219&Q7&Q4%1249%32=1%8251'=%D4JJB@&Mr9%211%L3J41%>2GB%;2HF%=2D1%B231%C251qS0Q41%<2Q51qRDQ61%>2Q71p0@1pS>Q91p0K1pRJQ:1pS4Q<1pRNQ=1pS2Q?1").
Proof.
intros ms lo n k H z Hz. pose proof (iv_coalesce_covered (iv_sort (lit_ivs ms)) (lo, n, k) H) as C. cbn in C.
destruct (C z Hz) as ([a m] & Hin & Haz). apply (proj1 (iv_sort_In _ _)) in Hin. exists a, m. split; [exact Hin | exact Haz].
Qed.
Lemma runs_pos : ltac2:(TCodec.tc2 tcn__PlaceLemmasK "K'5'C%211'@'6&Q3'9%1244%2214(8r3r2%349921r1%547:21&Q2r4%211%=3:41&Q7z%221;p041pRJC1pS4E1pRNF1pS2H1").
Proof.
intros ms lo n k H. eapply (iv_coalesce_pos (iv_sort (lit_ivs ms))); [|exact H].
intros [a m] Hp. apply (proj1 (iv_sort_In _ _)) in Hp. cbn. exact (proj1 (proj2 (proj1 (lit_ivs_In ms a m Hp)))).
Qed.
Lemma iv_coalesce_bounds : ltac2:(TCodec.tc2 tcn__PlaceLemmasK "QB'5'9'@%2211%411&Q3r1r2%33521';&Q6z&4%13;;6%4231&Q7&:%13??:%3271&Q4%1273&Q0%<221%>251%?2:1p0A1pS:G1'6%K2I1(8r3%24MM1H%34M51J&Jr5%211%O3841r4%L2K1%H2L9%E23:%O21D%Q1231%Q2251p081pRJB1pS4Q<1pRNQ=1p0F1pRLQ=1").
Proof.
induction l as [|[a n] r IH]; intros Hb lo n0 k Ht; [destruct Ht|].
cbn [iv_coalesce] in Ht.
pose proof (Hb (a, n) (or_introl eq_refl)) as Ha. cbn in Ha.
assert (Hr : forall p, In p r -> 0 <= fst p /\ 0 < snd p /\ fst p + snd p <= two64) by (intros p Hp; apply Hb; right; exact Hp).
destruct (iv_coalesce r) as [|[[b m] k'] r'] eqn:Hc.
- destruct Ht as [Ht|[]]. injection Ht as <- <- <-. lia.
- destruct (Z.eqb (a + n) b && Z.ltb 0 n && Z.ltb 0 m)%bool eqn:Hbm.
+ apply andb_prop in Hbm as [Hbm Hm]. apply andb_prop in Hbm as [Hbm Hn]. apply Z.eqb_eq in Hbm.
pose proof (IH Hr b m k' (or_introl eq_refl)) as Bm.
destruct Ht as [Ht|Ht]; [injection Ht as <- <- <-; lia|]. eapply IH; [exact Hr | right; exact Ht].
+ destruct Ht as [Ht|Ht]; [injection Ht as <- <- <-; lia|]. eapply IH; [exact Hr | exact Ht].
Qed.
Lemma runs_bounds : ltac2:(TCodec.tc2 tcn__PlaceLemmasK "Q4'5'C%211'@'6&Q3'9%1244%2214(8r3r2%349921r1%547:21&Q2r4%211%=3:41';&Q6z%2216&Q7%123>&Q4%12:@&Q0%8221%:251%;281p0=1pRJL1pS4N1pRNO1pS2Q11").
Proof.
intros ms lo n k H. eapply (iv_coalesce_bounds (iv_sort (lit_ivs ms))); [|exact H].
intros [a m] Hp. apply (proj1 (iv_sort_In _ _)) in Hp. cbn. pose proof (proj1 (lit_ivs_In ms a m Hp)). lia.
Qed.
Lemma runs_apart : ltac2:(TCodec.tc2 tcn__PlaceLemmasK "QH'5'C%211'@'6&Q3'9%1244%2214(8r5r4%349921r3%547:21&Q2r6%211%=3:41&Q7zr2%3221r1%?4EE31&Mr:%211%G3E41'?&Q6&Q4r7%221A%421E%42F>%6214%8231p0:1pS0Q41pRFQ51%:2ONr8%=221%=22<%?21Q3%A231p071p0J1p0O1pS6Q?1pRDQ@1pRJQ@1pS4QB1pRNQC1pS2QE1").
Proof.
intros ms lo n k a nZ H HnZ Hap.
pose proof (iv_coalesce_covered (iv_sort (lit_ivs ms)) (lo, n, k) H) as C. cbn in C.
eapply (run_apart (iv_sort (lit_ivs ms)) lo n a nZ C HnZ (runs_pos ms lo n k H)).
intros [a' m] Hp. apply (proj1 (iv_sort_In _ _)) in Hp. cbn. exact (Hap a' m Hp).
Qed.
Lemma fold_vlo_bound : forall (ts : list (Z * Z * nat)) (acc a nZ nlo : Z),
0 < nZ -> nlo <= nZ -> 4096 <= a -> a mod 4096 = 0 ->
acc <= a / 4096 ->
(forall lo n k, In (lo, n, k) ts -> a + nZ <= lo \/ lo + n <= a) ->
fold_left (fun acc (t : Z * Z * nat) => let '(lo, n, _) := t in
if Z.ltb (lo - 4096) nlo then Z.max acc ((lo + n) / 4096) else acc) ts acc
<= a / 4096.
Proof.
induction ts as [|[[lo n] k] ts IH]; intros acc a nZ nlo HnZ Hnlo Ha Hal Hacc Hap; cbn [fold_left]; [exact Hacc|].
apply (IH _ a nZ nlo HnZ Hnlo Ha Hal).
- destruct (Z.ltb (lo - 4096) nlo) eqn:Hlt; [|exact Hacc]. apply Z.ltb_lt in Hlt.
apply Z.max_lub; [exact Hacc|].
destruct (Hap lo n k (or_introl eq_refl)) as [H|H]; [exfalso; lia|].
apply Z.div_le_mono; lia.
- intros lo' n' k' Hin. apply (Hap lo' n' k'). right. exact Hin.
Qed.
Lemma grant_vlo_sound : ltac2:(TCodec.tc2 tcn__PlaceLemmasK "R?'D'5'C%211'@&Q7zr2%3221&Q6r3%2241+TP0r5%5221'<&Q8r6%2216%43?1='?&Q4r7%2216&Hr9%211%B241&G%114%E218%;241r:%511%B21F%D3O1M'6&Q3'9%12Q3Q3%2214(8%14Q6Q6Q0Q3r1%345821&Q2r=%211%;3841r<%M241r4%Q;221%Q022Q;%Q=218%Q3231p081pRJE1pS4QF1pRNQG1&Fr;r8%33>21&Q5%12Q1QE%QI231p081p0Q11p0Q61p0QC1p0QI1p0QM1p0R11pS8R61pS6R71pRDR81pS2R:1p2R>1").
Proof.
intros A ms a nZ nlo HnZ Hnlo Ha Hal Hhull Hih Hruns. unfold grant_vlo. fold (runs ms).
apply (fold_vlo_bound (runs ms) _ a nZ nlo HnZ Hnlo Ha Hal); [|exact Hruns].
destruct (Z.ltb (img_lo A - 4096) nlo) eqn:Hlt.
- apply Z.ltb_lt in Hlt. destruct Hhull as [H|H]; [exfalso; lia|].
apply Z.div_le_mono; lia.
- apply Z.div_le_lower_bound; lia.
Qed.
Lemma first_run_In : ltac2:(TCodec.tc2 tcn__PlaceLemmasK "Q<'5'C%211'@'<'7'9%1244%311&Er3%211(1(8r2r1%34==21%52:1%>3:71'='6';r4&Q4r5%221;%F3G41&Q3%F2E8%@4JJ5?%A4G:1?&Q2r6%211%73641%>291qRJ@1%B2A1qS4Q31%D2Q41p0F1pRHQ61pRNQ71pS2Q91").
Proof.
intros ms lo hi H. unfold first_run in H. fold (runs ms) in H.
destruct (runs ms) as [|[[lo' n] k] r] eqn:Hr; [discriminate|]. injection H as <- <-.
exists n, k. split; [reflexivity | left; reflexivity].
Qed.
