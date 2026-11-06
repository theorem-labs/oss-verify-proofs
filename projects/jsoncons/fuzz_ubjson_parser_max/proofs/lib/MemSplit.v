(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec SeqExec StepTac StoreOk StreamSim.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__MemSplit () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.StackLayout."; "LinuxProcessSemantics.LinuxProcessSem.State."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.MemSplit."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StreamSim."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1Some"; "1bool"; "1length"; "1list"; "1nat"; "1option"; "1true"; "2and"; "2eq"; "2or"; "3nth"; "3repeat"; "4Z"; "0D"; "0J"]; ["0J'"; "0J1"; "0J2"; "0J3"; "5PhdrInfo"; "5Segment"; "6store_ok"; "7EntryDraw"; "8stack_max_size"; "9wbytes"; ":agree_above"; ":cmem"; ":in_win"; ":wfJ"; ":win_lo"; ";rdn"]; [";wrap_mem"; "<wseg_ok"; "=add"; "=le"; "=lt"; "=of_nat"; "=pow"; "=sub"; "=to_nat"; "0a"; "0av"; "0b"; "0bs"; "0bs1"; "0bs2"; "0ev"]; ["0hw"; "0lo"; "0lo'"; "0m"; "0mem0"; "0n"; "0ph"; "0rdraw"; "0segs"; "0sp0"; ">Z_to_bv"; ">bv"; ">bv_unsigned"; "0uid"; "0x"]]).
Lemma wbytes_inside : ltac2:(TCodec.tc2 tcn__MemSplit "QL'4'QKy8%211%411yR0%511'6%115p031&Q3&Q2&QLr2%2291&Q5&3r4%22?1%411%9261&Q6+2+R0%3221%?251'8r3%@2G1%C21?&Q4r5%@2M1%B11%G261%52E1%:271'9&Ir6%249G1=(1&;&Q8&Q7%Q12Q8L%22B1%411&QJz%22Q@1%94Q@4<1%;2QA1%@3Q==1p0B1p0N1pSNQB1pRDQC1pS8QA1pRJQG1").
Proof.
induction bs as [|b rest IH]; intros m a x Hnw Hx; [cbn in Hx; lia|].
cbn [wbytes length] in *.
destruct (Z.eq_dec (bv_unsigned x) (bv_unsigned a)) as [Heq|Hne].
- assert (x = a) by (apply bv_eq; exact Heq). subst x.
rewrite Z.sub_diag. cbn [Z.to_nat nth].
destruct rest as [|b' rest'].
+ cbn [wbytes]. rewrite bv_eqb_refl. reflexivity.
+ cbn [length] in Hnw. rewrite wbytes_below.
* rewrite bv_eqb_refl. reflexivity.
* rewrite u_add1 by lia. cbn [length]. lia.
* rewrite u_add1 by lia. lia.
- assert (Hu1 : bv_unsigned (a + 1) = bv_unsigned a + 1)
by (apply u_add1; lia).
rewrite (IH _ (a + 1)%bv) by (rewrite Hu1; lia).
rewrite Hu1.
replace (Z.to_nat (bv_unsigned x - bv_unsigned a))
with (S (Z.to_nat (bv_unsigned x - (bv_unsigned a + 1)))) by lia.
reflexivity.
Qed.
Lemma wbytes_outside : ltac2:(TCodec.tc2 tcn__MemSplit "QA'4'QKy8%211%411yR0%511'6%115p031&Q3&Q2&QLr2%2291&Q5&3r4%22?1%411%9261&Q6+2+R0%3221%?251':&Q4r3%A2H1%32@1r5%@2M1%B11%G251%I21E%:261'9&Ir6%249G1<%:1=%53Q221p071p0C1pSNQ71pRDQ81pS8Q61pRJQ<1").
Proof.
intros bs m a x Hnw [Hlt|Hge].
- apply wbytes_below; assumption.
- apply wbytes_above; assumption.
Qed.
Lemma wbytes_select : forall (P : word -> bool) (f g : word -> option byte) (a : word) bs,
bv_unsigned a + Z.of_nat (length bs) <= 2^64 ->
(forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat (length bs) ->
P x = true) ->
wbytes (fun x => if P x then f x else g x) a bs
= (fun x => if P x then wbytes f a bs x else g x).
Proof.
intros P f g a bs Hnw HP. apply functional_extensionality. intro x.
destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a)) as [Hlt|Hge].
- rewrite !wbytes_outside by lia. reflexivity.
- destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a + Z.of_nat (length bs))) as [Hin|Hout].
+ rewrite !wbytes_inside by lia. rewrite (HP x) by lia. reflexivity.
+ rewrite !wbytes_outside by lia. reflexivity.
Qed.
Lemma wbytes_select_r : forall (P : word -> bool) (f g : word -> option byte) (a : word) bs,
bv_unsigned a + Z.of_nat (length bs) <= 2^64 ->
(forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat (length bs) ->
P x = false) ->
wbytes (fun x => if P x then f x else g x) a bs
= (fun x => if P x then f x else wbytes g a bs x).
Proof.
intros P f g a bs Hnw HP. apply functional_extensionality. intro x.
destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a)) as [Hlt|Hge].
- rewrite !wbytes_outside by lia. reflexivity.
- destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a + Z.of_nat (length bs))) as [Hin|Hout].
+ rewrite !wbytes_inside by lia. rewrite (HP x) by lia. reflexivity.
+ rewrite !wbytes_outside by lia. reflexivity.
Qed.
Lemma wbytes_shadow : ltac2:(TCodec.tc2 tcn__MemSplit "Q='QKyR0%211'6y8%511%311p051'4%114'9'5&3r2%2291r1%42;1%73631&Q3&Q2&QLr4%22E1&Q5%11:%6231&Q6+2+R0%3221%<251&Ir6r5%3321=r3%53231%63542%L3O21p091p0G1pRNQ01pRLQ11pRDQ91pS8Q51").
Proof.
intros m a bs1 bs2 Hlen Hnw. apply functional_extensionality. intro x.
destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a)) as [Hlt|Hge].
- rewrite !wbytes_outside by lia. reflexivity.
- destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a + Z.of_nat (length bs2))) as [Hin|Hout].
+ rewrite !wbytes_inside by lia. reflexivity.
+ rewrite !wbytes_outside by lia. reflexivity.
Qed.
Lemma rdn_const : ltac2:(TCodec.tc2 tcn__MemSplit "QN'4'E%211'QKyR0%211'6y8%511%311pSN51'5&Q3&Q2&QLr3%22<1&Q5r2%211%7241&Q6+2+R0%3221%=251'8r5%>2H1r1%@2J1%C231&Q4r4%A11%F271%4261%;261'9r7%11F(1%12Q29%53Q231p071pSNQ81%Q>1Q6%Q911&Or6%24;1GA&<%13Q<Q5C%<271%@3741p0:1p0O1pRHQA1pS<Q?1pRDQF1pS8QB1pSBQK1").
Proof.
intros segs m a n; revert a; induction n as [|n IH]; intros a b Hnw Hall; [reflexivity|].
cbn [rdn repeat]. rewrite (Hall a) by lia.
destruct n as [|n'].
- reflexivity.
- assert (Hu1 : bv_unsigned (a + 1) = bv_unsigned a + 1) by (apply u_add1; lia).
rewrite (IH (a + 1)%bv b) by (rewrite Hu1; first [lia | intros x Hx; apply Hall; lia]).
reflexivity.
Qed.
Definition win_lo (sp0 : word) : Z := bv_unsigned sp0 - stack_max_size.
Definition in_win (sp0 : word) (x : word) : Prop :=
win_lo sp0 <= bv_unsigned x < bv_unsigned sp0.
Definition cmem (sp0 : word) (mem0 J D : word -> option byte) : word -> option byte :=
fun a => if (bv_unsigned sp0 <=? bv_unsigned a) then mem0 a
else if (win_lo sp0 <=? bv_unsigned a) then J a else D a.
Definition wfJ (sp0 : word) (J : word -> option byte) : Prop :=
forall x : word, in_win sp0 x -> J x <> None.
Lemma wfJ_const : ltac2:(TCodec.tc2 tcn__MemSplit "='QKyR0%211y8%411&Mr2(1%1242q071%5241pRH71pSD:1").
Proof. intros sp0 b x _. discriminate. Qed.
Lemma wfJ_wbytes : ltac2:(TCodec.tc2 tcn__MemSplit "H'QKyR0%211'6y8%511%311p051'4%114&Mr4r3%3221r5&Ir2%23651%8241p061pRJ;1pRDC1pQ0?1pSDE1").
Proof. intros sp0 J a bs H x Hx. apply wbytes_grows. apply H. exact Hx. Qed.
Definition agree_above (lo : Z) (J J' : word -> option byte) : Prop :=
forall x : word, lo <= bv_unsigned x -> J' x = J x.
Lemma agree_above_refl : ltac2:(TCodec.tc2 tcn__MemSplit "?'='QKyR0%211'6y8%511%311p051&Jr2r1%33211pQ051pS4>1").
Proof. intros lo J x _. reflexivity. Qed.
Lemma agree_above_trans : ltac2:(TCodec.tc2 tcn__MemSplit "H'='QKyR0%211'6y8%511%311p051&Jr4r3r2%43321r5%63143r6%83136p031p061pQ8<1pQ6=1pQ4>1pS4G1").
Proof. intros lo J1 J2 J3 H12 H23 x Hx. rewrite (H23 x Hx). apply H12. exact Hx. Qed.
Lemma agree_above_mono : ltac2:(TCodec.tc2 tcn__MemSplit "H'='QKyR0%211'6y8%511%311p051&Q3r4r3%3221&Jr5r2%33251%43376p021p071pQ2<1pQ0=1pS6F1pS4G1").
Proof. intros lo lo' J J' Hle H x Hx. apply H. lia. Qed.
Lemma agree_above_wbytes : ltac2:(TCodec.tc2 tcn__MemSplit "Q3'='QKyR0%211'6y8%511%311p051'4%114&Q3&Q2&QLr2%22=1&Q5&3r1%22=1%411%9261r4%<221&Jr5&Ir3%2361>%53471p071pRJE1pRDM1pQ0I1pS4Q21").
Proof.
intros lo J a bs Hle x Hx. apply wbytes_above. lia.
Qed.
Lemma rdn_agree_above : ltac2:(TCodec.tc2 tcn__MemSplit "QC'4'E%211'='QKyR0%211'6y8%511%311p051'5&Jr5r4r3%43321&Q3r6&QL%12@5%4231&Q2%42C9&Q5%11:%4231&Q6+2+R0%3221%>251'9%Q21I%L11&Or9%241CHGr7%4431JI%83631p0:1p0E1p0K1pS<Q11pRDQ81pQ2Q41pQ0Q51pS4Q>1pSBQ@1").
Proof.
intros segs lo J J' a n H Hlo Hnw. apply rdn_ext; [exact Hnw|].
intros x Hx. apply H. lia.
Qed.
Section CMem.
Variable sp0 : word.
Variable mem0 : word -> option byte.
Let csel := cmem sp0 mem0.
Lemma stack_max_size_pos : ltac2:(TCodec.tc2 tcn__MemSplit "4&Q4z&H%3221").
Proof. rewrite stack_max_size_val. lia. Qed.
Lemma wbytes_cmem_win : ltac2:(TCodec.tc2 tcn__MemSplit "Q>'QKyR0%211'6y8%511%311p051'4%114&Q3&NvQI%211&QLr2%22?1%7241&Q2r3%62C1&Q5&3%12B8%311%7251%<2I>%A221'9&I&KvQDr6r5%44F321r4%7321A%8352B%84J715%;3Q031p0=1p0H1pRJQ11pRDQ91pNQ51pQ0Q61").
Proof.
intros J D a bs Hlo Hhi. unfold cmem.
pose proof (u64_range sp0) as Hsp.
rewrite (wbytes_select_r (fun x => bv_unsigned sp0 <=? bv_unsigned x) mem0
(fun x => if win_lo sp0 <=? bv_unsigned x then J x else D x) a bs)
by (first [lia | intros x Hx; apply Z.leb_gt; lia]).
apply functional_extensionality. intro x.
destruct (bv_unsigned sp0 <=? bv_unsigned x); [reflexivity|].
rewrite (wbytes_select (fun x => win_lo sp0 <=? bv_unsigned x) J D a bs)
by (first [lia | intros y Hy; apply Z.leb_le; lia]).
reflexivity.
Qed.
Lemma wbytes_cmem_data : ltac2:(TCodec.tc2 tcn__MemSplit "Q:'QKyR0%211'6y8%511%311p051'4%114&Q3&Q2&QLr2%22=1&Q5&3r1%22=1%411%9261&NvQI%211%>241'9&I&KvQDr5r4%449321r3%7321D%8342E%84=761%;3M31p0=1pRJM1pRDQ51pNQ11pQ0Q21").
Proof.
intros J D a bs Hhi. unfold cmem.
pose proof (u64_range sp0) as Hsp. pose proof stack_max_size_pos.
unfold win_lo in *.
rewrite (wbytes_select_r (fun x => bv_unsigned sp0 <=? bv_unsigned x) mem0
(fun x => if bv_unsigned sp0 - stack_max_size <=? bv_unsigned x then J x else D x) a bs)
by (first [lia | intros x Hx; apply Z.leb_gt; lia]).
apply functional_extensionality. intro x.
destruct (bv_unsigned sp0 <=? bv_unsigned x); [reflexivity|].
rewrite (wbytes_select_r (fun x => bv_unsigned sp0 - stack_max_size <=? bv_unsigned x) J D a bs)
by (first [lia | intros y Hy; apply Z.leb_gt; lia]).
reflexivity.
Qed.
Lemma rdn_cmem_above : ltac2:(TCodec.tc2 tcn__MemSplit "QC'4'E%211'QKyR0%211'6y8%511%311p051'5&Q3&QLvQI%22;1r2%42=1%6231&Q2r3%82A1&Q5%117%5231&Q6+2+R0%3221%A251'9%O1G%J11&Or7&KvQDr6r5%44I321r4%84721E%94862F%=3;21p0?1p0K1pS<Q31pRDQ:1pNQ61pQ0Q71pSBQ@1").
Proof.
intros segs J D a n Hlo Hnw. apply rdn_ext; [exact Hnw|].
intros x Hx. unfold cmem. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity.
Qed.
Lemma rdn_cmem_win : ltac2:(TCodec.tc2 tcn__MemSplit "QA'4'E%211'QKyR0%211'6y8%511%311p051'5&Q3&NvQI%211&QLr2%22>1%7241&Q2r3%62B1&Q5%117%5231%:2F<%?221'9%M1E%H11&Or7&KvQDr6r5%44G321r4%84721B%94852C%=3;21p0?1p0H1pS<Q11pRDQ81pNQ41pQ0Q51pSBQ>1").
Proof.
intros segs J D a n Hlo Hhi. pose proof (u64_range sp0).
apply rdn_ext; [lia|].
intros x Hx. unfold cmem.
rewrite (proj2 (Z.leb_gt _ _)) by lia.
rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity.
Qed.
Lemma rdn_cmem_data : ltac2:(TCodec.tc2 tcn__MemSplit "Q='4'E%211'QKyR0%211'6y8%511%311p051'5&Q3&Q2&QLr2%22<1&Q5r1%211%7241&NvQI%211%<241'9%J1B%E11&Or6&KvQDr5r4%44<321r3%84721E%94842F%=3;21p0?1pS<M1pRDQ41pNQ01pQ0Q11pSBQ:1").
Proof.
intros segs J D a n Hhi. pose proof (u64_range sp0). pose proof stack_max_size_pos.
unfold win_lo in *.
apply rdn_ext; [lia|].
intros x Hx. unfold cmem, win_lo.
rewrite (proj2 (Z.leb_gt _ _)) by lia.
rewrite (proj2 (Z.leb_gt _ _)) by lia. reflexivity.
Qed.
Lemma cmem_at_above : ltac2:(TCodec.tc2 tcn__MemSplit "L'QKyR0%211'6y8%511%311p051&Q3&QLvQI%22:1r1%42<1%6231'9&KvQDr4r3r2%55;4321%512%83A21p0:1pSNG1pNC1pQ0D1").
Proof. intros. unfold cmem. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity. Qed.
Lemma cmem_at_win : ltac2:(TCodec.tc2 tcn__MemSplit "I'QKyR0%211'6y8%511%311p051&LvQIr1%3221'9&KvQDr4r3r2%5594321%412%83>21p0:1pSND1pN@1pQ0A1").
Proof.
intros J D x [Hlo Hhi]. unfold cmem.
rewrite (proj2 (Z.leb_gt _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity.
Qed.
Lemma cmem_at_data : ltac2:(TCodec.tc2 tcn__MemSplit "M'QKyR0%211'6y8%511%311p051&Q4&QLr1%22:1&NvQI%211%7241'9&KvQDr4r3r2%5594321%312%83B21p0:1pSNH1pND1pQ0E1").
Proof.
intros J D x Hx. pose proof stack_max_size_pos. unfold cmem, win_lo in *.
rewrite (proj2 (Z.leb_gt _ _)) by lia. rewrite (proj2 (Z.leb_gt _ _)) by lia. reflexivity.
Qed.
Lemma store_ok_cmem_win : ltac2:(TCodec.tc2 tcn__MemSplit "QC'4'E%211'QKyR0%211'6y8%511%311p051'5&MvQIr4%3221&Q3&N%115&QLr3%22A1%6241&Q2%52D:&Q5%116%4231%92H?%=221'9'2&Fr8&KvQDr7r6%44I321r5%84721J(7%<3;21p0>1p0F1p0N1pS<Q31pRDQ:1pNQ61pQ0Q71pSBQ@1").
Proof.
intros segs J D a n HJ Hlo Hhi. pose proof (u64_range sp0).
apply store_ok_of_all; [lia|].
intros x Hx. unfold wview.
rewrite cmem_at_win by (unfold in_win; lia).
destruct (J x) as [b|] eqn:E; [discriminate|].
exfalso. apply (HJ x); [unfold in_win; lia | exact E].
Qed.
Lemma store_ok_cmem_data : ltac2:(TCodec.tc2 tcn__MemSplit "Q5'4'E%211'QKyR0%211'6y8%511%311p051'5'9'2&Q1r5r2r1%43321(7%83721&Fr6&KvQIvQDr4%4432<1r3%84721=%B3A1;p0;1pS<E1pRDL1pNH1pQ0I1pSBQ21").
Proof. intros. apply store_ok_wseg. assumption. Qed.
End CMem.
Lemma cmem_init : ltac2:(TCodec.tc2 tcn__MemSplit "Q:'D'QKyR0%211'4y8%511%311%411'G'9'6%116p0:1&Q0r7r6r5r4r3r2r1%877654321&K(1&QJz%22F1%42F1q0J1(0%11Iq0M1%:4A;41%H3E<1pS@J1pS2Q11pSLQ21pS0N1pRFO1pSDQ51pS>Q91").
Proof.
intros ph sp0 av ev uid hw rdraw. apply functional_extensionality. intro x.
unfold cmem.
destruct (bv_unsigned sp0 <=? bv_unsigned x) eqn:E1; [reflexivity|].
apply Z.leb_gt in E1.
unfold wrap_mem, win_lo.
assert (Hst : stack_to_mem sp0 (entry_stack_image ph sp0 av ev uid hw rdraw) x = None).
{ unfold stack_to_mem. rewrite (proj2 (Z.leb_gt _ _)) by lia. reflexivity. }
rewrite Hst. rewrite (proj2 (Z.ltb_lt _ _) E1), andb_true_r. reflexivity.
Qed.
