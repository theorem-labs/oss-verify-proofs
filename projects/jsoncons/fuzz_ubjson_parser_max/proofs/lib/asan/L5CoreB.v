(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceA
LibIface BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5LazyA L5DefsA L5CoreA L5CoreSpecsA L5StepA.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__asan_L5CoreB () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.IcptIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5DefsA.L5A."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.LibIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.L5CoreA.L5CA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.L5CoreB.L5CB.SCFG_1."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.bitvector.definitions."], [["0A"; "0C"; "1app"; "1bool"; "1cons"; "1false"; "1list"; "1nat"; "1option"; "1pair"; "1prod"; "2and"; "2eq"; "2iff"; "2not"; "3map"]; ["4Z"; "0FF"; "0FF'"; "0H"; "0HI"; "0IL"; "0L"; "0LB"; "0LB'"; "0LK"; "0LK'"; "5Model"; "0M"; "0M'"; "6mrestrict"; "7credit"]; ["8S"; "8aacc"; "8aclient"; "8acredit_ok"; "8adebit"; "8ahid"; "8ar_sptop"; "8asan_layout"; "8asan_statics_cells"; "8ff_addr"; "8ff_class"; "8ff_count"; "8ff_room"; "8fframe"; "8ri_inv"; "8shadow_blk"]; ["8shadow_zero"; "8vml"; "8vml_of"; "9icl_globals"; "9icpt_layout"; ":as0_layout"; ":avis"; ";credit_le"; "<aobj"; "<ffr"; "=as0_layout2"; "=asrc"; "=ffrk"; ">In"; ">incl"; "?add"]; ["?le"; "?lt"; "?modulo"; "?mul"; "?sub"; "0V"; "0a"; "0ar"; "0b"; "0c"; "0c'"; "0cr"; "0d"; "0d'"; "0f"; "0g"]; ["0i"; "0k"; "0l"; "0m"; "0m'"; "0model"; "0n"; "0n'"; "0p"; "0p'"; "0scr"; "0so"; "0sp"; "@NoDup"; "AZ_to_bv"; "Abv"]; ["0u"; "0x"]]).
Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Module L5CB.
Import L5A. Import L5CA. Import L5CSA. Import L5SA.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Definition ffrk (k : Z) (FF LK : list fframe) (d : Z) : Prop := Z.of_nat (ff_count k (FF ++ LK)) + d <= ff_cap k.
Lemma ffrk_1 : ltac2:(TCodec.tc2 tcn__asan_L5CoreB "A'6&Q=%211'@&=&QL+1r3r2r1%544321&QI%13543%9231pTJ;1pQD=1pQ4>1"). Proof. intros FF LK d. reflexivity. Qed.
Lemma ffrk_room : ltac2:(TCodec.tc2 tcn__asan_L5CoreB "G'@'6&Q=%211&QLr4r3r2r1%544321&R0+2%2215&Q<r6r5%3321;p051p091pTJC1pQDA1pQ4B1pU4F1"). Proof. intros k FF LK d. unfold ffrk, ff_room. lia. Qed.
Lemma ffrk_le : ltac2:(TCodec.tc2 tcn__asan_L5CoreB "F'@'6&Q=%211&QLr5r4r3r2%544321&R0%1234r7r6%:42197p041p071pTLA1pTJB1pQD@1pQ4A1pU4E1"). Proof. intros k FF LK d d'. unfold ffrk. lia. Qed.
Lemma ff_count_cons_other : ltac2:(TCodec.tc2 tcn__asan_L5CoreB "H'@&Q='6%112&>'<&Q:r2%211r3%53:21%711'7&Q;r4(4%13?79%4231%524;%>3721p091pU6B1pTNE1pU4G1").
Proof. intros k f l.
intros N. unfold ff_count. rewrite list_basics.list.filter_cons. destruct (decide _) as [E|E]; [|reflexivity].
exfalso. apply N. apply Z.eqb_eq. destruct (ff_class f =? k); [reflexivity | exact (False_ind _ (E))].
Qed.
Lemma ffrk_push : ltac2:(TCodec.tc2 tcn__asan_L5CoreB "Q;'@'6&Q=%211&QLr7r6r5r2%544321&QN%13945'RM&?&Q9&2(4r8%23@;1%43A1=%74BD61%92E1&R0&QOr4+1%3221%521Dr;r:%>3LI1%K431>Hp051p0<1p0G1p0J1pTLQ41pTJQ51pTNQ41pQFQ41pQDQ51pQ4Q61pU4Q:1").
Proof. intros k FF LK LK' f d d'.
unfold ffrk. intros R I ND Hd. rewrite ff_count_app in R. change ((f :: FF) ++ LK') with (f :: (FF ++ LK')).
pose proof (ff_count_cons k f (FF ++ LK')) as C1. rewrite ff_count_app in C1.
pose proof (ff_count_incl k LK' LK I (nodup_of_map_app_r (f :: FF) LK' ND)) as C2. lia.
Qed.
Lemma ffrk_push_other : ltac2:(TCodec.tc2 tcn__asan_L5CoreB "Q:'@'6&Q=%211&>'<&Q:r2%211r6%53:21%711&QLr7r5%342618&QN%13?38'RM&?&Q9&2(4r8%23F:1%43G1@%74HJ61%92K1r:r9%83LE1%C431BAp051p0@1p0C1p0H1pTJQ41pTNQ31pQFQ31pQDQ41pQ4Q51pU4Q91").
Proof. intros k FF LK LK' f d.
unfold ffrk. intros N R I ND. rewrite ff_count_app in R. change ((f :: FF) ++ LK') with (f :: (FF ++ LK')).
rewrite (ff_count_cons_other k f _ N), ff_count_app.
pose proof (ff_count_incl k LK' LK I (nodup_of_map_app_r (f :: FF) LK' ND)) as C2. lia.
Qed.
Lemma ffrk_shrink : ltac2:(TCodec.tc2 tcn__asan_L5CoreB "O'@'6&Q=%211&QLr5r4r3r1%544321&QN%13945'RM&?&Q9&2r6%23?1;%54@B41%72C1r8r7%B421A@p041p0=1p0@1pTJJ1pQFH1pQDI1pQ4J1pU4N1").
Proof. intros k FF LK LK' d.
unfold ffrk. intros R I ND. rewrite ff_count_app in *. pose proof (ff_count_incl k LK' LK I (nodup_of_map_app_r FF LK' ND)) as C2. lia.
Qed.
Lemma ffrk_pop : ltac2:(TCodec.tc2 tcn__asan_L5CoreB "E'@'6&Q=%211&QLr5(4r2r4%33721r3r1%847321r6%:41967p031pTJ@1pTN?1pQD?1pQ4@1pU4D1").
Proof. intros k FF LK f d. unfold ffrk. change ((f :: FF) ++ LK) with (f :: (FF ++ LK)). intros H. unfold ff_count in *. rewrite list_basics.list.filter_cons in H. destruct (decide _); cbn [length] in H; lia. Qed.
Record as0_layout2 (L : asan_layout) : Prop := ALY2 {
aly2_static_lo : forall a, hl_rt_static L a -> 0x134000 <= a;
aly2_cost : 0 <= hl_k_per_malloc L /\ 0 <= hl_b_lin L /\ 0 <= hl_b_overhead L
}.
Lemma as0_layout2_of : ltac2:(TCodec.tc2 tcn__asan_L5CoreB "<'Q7'Q8'QEr2r1%3221'QJr3%211p041p491pQ>;1").
Proof. intros L C. intros LY. split. exact (L5A.aly_static_lo L C LY). exact (L5A.aly_cost L C LY). Qed.
Lemma credit_le_refl : ltac2:(TCodec.tc2 tcn__asan_L5CoreB "5&O&QGr1%2211pTD41"). Proof. intros c. unfold credit_le. lia. Qed.
Lemma credit_le_trans : ltac2:(TCodec.tc2 tcn__asan_L5CoreB "<&O&QGr3r2%3221r5%5214p031p041pTD91pTB:1pT>;1"). Proof. intros a b c. unfold credit_le. lia. Qed.
Lemma adebit_le : ltac2:(TCodec.tc2 tcn__asan_L5CoreB "E'Q7&O'@'QJr3%211&R0zr2%3221&QG&Q4r5r4%3321:%5212p071p0<1pU>@1pTDB1pQ>D1").
Proof. intros L c n. intros [_ (K & B & O)] Hn. unfold credit_le, adebit. cbn [fst snd]. nia. Qed.
Lemma adebit_mono : ltac2:(TCodec.tc2 tcn__asan_L5CoreB "B'Q7&O'@&QGr3r2%3221&Q4r5r4%33215%43376%9221p071pU><1pTF>1pTD?1pQ>A1").
Proof. intros L c c' n. unfold credit_le, adebit. cbn [fst snd]. lia. Qed.
Lemma adebit_le_amount : ltac2:(TCodec.tc2 tcn__asan_L5CoreB "G'Q7&O'@'QJr4%211&R0r2r3%3221&QG&Q4r6r5%3321:%43327%6221p081p0=1pU@A1pU>B1pTDD1pQ>F1").
Proof. intros L c n n'. intros [_ (K & B & O)] Hn. unfold credit_le, adebit. cbn [fst snd]. nia. Qed.
Lemma acredit_ok_le : ltac2:(TCodec.tc2 tcn__asan_L5CoreB "F'Q7&O'@'QJr4%211&Q3r5r3%33251&R0%1237r7r6%8321:p041p071p0<1pU@@1pU>A1pTDC1pQ>E1").
Proof. intros L c n n'. intros [_ (K & B & O)] [H1 H2] Hn. unfold acredit_ok. split. exact H1. nia. Qed.
Lemma acredit_ok_mono : ltac2:(TCodec.tc2 tcn__asan_L5CoreB "B'Q7&O'@&Q3r4r3r1%43321&QG%1254r6%83176p031p061pU><1pTF>1pTD?1pQ>A1").
Proof. intros L c c' n. unfold acredit_ok, credit_le. lia. Qed.
Definition asrc (IL : icpt_layout) (LB : list (Z * Z)) (FF : list fframe) (M : word -> option byte) (p m : Z) : Prop :=
m = 0
\/ (exists b n, In (b, n) LB /\ b <= p /\ p + m <= b + n)
\/ (exists g n, In (g, n) (icl_globals IL) /\ g <= p /\ p + m <= g + n)
\/ (exists so, aobj FF so 24 /\ so <= p /\ p + m <= so + 24 /\ shadow_zero M so 3).
Lemma asrc_sub : ltac2:(TCodec.tc2 tcn__asan_L5CoreB "QA'QD'6':'@%2211%411&Q=%611'ROyR0%211'8y8%511%311p051&QKr8r7r6r5r4r3%76654321&R0%1253&QO%1265%2298%5221z%721:r<r;r:r9%D64321A@p061p091p0>1p0A1pU:Q61pUDQ71pU8Q81pUBQ91pQJN1pQ4Q71pQ@Q:1pQ<Q@1").
Proof. intros IL LB FF M p m p' m'.
intros [E|[(b & n & I & H1 & H2)|[(g & n & I & H1 & H2)|(so & AO & H1 & H2 & SZ)]]] Hp Hm Hm0.
- left. lia.
- right; left. exists b, n. split. exact I. lia.
- right; right; left. exists g, n. split. exact I. lia.
- right; right; right. exists so. split. exact AO. split. lia. split. lia. exact SZ.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma aacc_of_blk : ltac2:(TCodec.tc2 tcn__asan_L5CoreB "Q;'ROyR0%211'8y8%511%311p051'@&Q?r5r4r3%43321'<&R2+8%2271z%53;21&R0r6%2241r7%421>&QO%125@r8%3215%9231&Q1r:%2319;p041p0:1p0=1p0A1p0H1pU8N1pUBO1pU>Q01pV2Q11pQJQ31").
Proof. intros M u n p m.
intros [SZ SP] U8 U0 H1 H2 a Ha. unfold shadow_zero, byte_at in SZ, SP |- *.
assert (E : S a = S u + (a / 8 - u / 8)) by (unfold S; lia).
destruct (Z_lt_le_dec (a / 8 - u / 8) (n / 8)) as [LT|GE].
- left. rewrite E. apply SZ. lia.
- right. exists (n mod 8). assert (NZ : n mod 8 <> 0) by lia. assert (G : a / 8 - u / 8 = n / 8) by lia.
split. rewrite E, G. apply SP. exact NZ. lia.
Qed.
Lemma aacc_of_zero : ltac2:(TCodec.tc2 tcn__asan_L5CoreB "Q='ROyR0%211'8y8%511%311p051'@&Q@r5r4r3%43321'<&R2+8%2271z%53;21&R0r6%2241r7%421>&QO%125@r8&R3%12=6%5231%;251&Q1r:%231;=p041p0<1p0?1p0C1p0J1pU8Q01pUBQ11pU0Q21pV2Q31pQJQ51").
Proof. intros M u g p m.
intros SZ U8 U0 H1 H2 a Ha. left. unfold shadow_zero, byte_at in SZ |- *.
replace (S a) with (S u + (a / 8 - u / 8)) by (unfold S; lia). apply SZ. lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma aacc_sub : ltac2:(TCodec.tc2 tcn__asan_L5CoreB "O'ROyR0%211'8y8%511%311p051'@&Q1r5r4r3%43321&R0%1253&QO%1265r6%3219%6231r8%=31<;p031p091p0<1pU:B1pUDC1pU8D1pUBE1pQJG1").
Proof. intros M p m p' m'. intros H Hp Hm a Ha. apply H. lia. Qed.
Section WithIface.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : as0_layout L C.
Hypothesis LY2 : as0_layout2 L.
Hypothesis ILY : as0_icpt_layout IL.
Hypothesis HIok : asan_iface_ok L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Lemma img_client : ltac2:(TCodec.tc2 tcn__asan_L5CoreB "O'6':'@%2211%411&Q=%611';&R0+RPP0r1%3221&R1+QV`P0%2241%8241&Q2vFvR7r6r5r4r3r2%877654321p0:1pT>H1pUFI1pUJJ1pQ4G1pQ@J1").
Proof. intros LB FF sp scr a.
intros Ha. right; right; left. rewrite (aly_img_lo L C LY), (aly_img_hi L C LY). split. lia.
intros X. pose proof (aly2_static_lo L LY2 a X). lia.
Qed.
Lemma globals_facts : ltac2:(TCodec.tc2 tcn__asan_L5CoreB "Q3'@&QM':%1233(9r2r1%347721&QCvE%211%:3841';&R0+RPP0r3%3221&QO%123=+QV`P0%7221'<&R2+8%2291z%53J21&R1%123G%A231%B2:1%C2?1p0E1pU>Q11pU0Q21").
Proof.
rewrite (aicl_globals IL ILY). intros g n Hin. cbn [In] in Hin.
repeat (destruct Hin as [E|Hin]; [injection E as <- <-; repeat split; first [reflexivity | lia] |]). destruct Hin.
Qed.
Lemma asrc_aacc : ltac2:(TCodec.tc2 tcn__asan_L5CoreB "Q='6':'@%2211%411&Q=%611&O'ROyR0%211'8y8%511%311p051&QA&Q>vDr9r8r7r6r5r4r3%9887654321&QKvEr:r2%4632<861&Q1%13;98p031p091pU8Q21pUBQ31pT<F1pQJH1p2Q41pTHQ21pQDQ41pQ4Q51pQ@Q81").
Proof. intros LB FF LK cr A M V p m.
intros HH [E|[(b & n & I & H1 & H2)|[(g & n & I & H1 & H2)|(so & AO & H1 & H2 & SZ)]]].
- intros a Ha. lia.
- pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _). pose proof (WB _ I) as ((B0 & _ & B2 & _) & _ & BSH & _). cbn [fst snd] in *.
apply (aacc_of_blk M b n p m BSH). clear - B2. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. lia. exact H1. exact H2.
- Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
pose proof (aic_globals _ _ _ _ _ ICok _ _ _ _ _ _ _ HH) as G. rewrite Forall_forall in G. pose proof (G _ I) as [GSH _]. cbn [fst snd] in GSH.
pose proof (globals_facts g n I) as (G0 & _ & G8 & _).
apply (aacc_of_blk M g n p m GSH G8). lia. exact H1. exact H2.
- destruct AO as (f & Hf & O1 & O2 & O8). pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & WF & FSAPP & _).
pose proof (WF f Hf) as (Y1 & _). unfold app_mem in FSAPP.
apply (aacc_of_zero M so 3 p m SZ O8). lia. exact H1. lia.
Qed.
Lemma asrc_client : ltac2:(TCodec.tc2 tcn__asan_L5CoreB "QA'6':'@%2211%411&Q=%611'ROyR0%211'8y8%511%311p051&QKvEr8r7r6r3r2%76654321';&R0z%2215&R1%1278%6231&Q2vFvR7r:r9&QOr5%221A%877654DC1p0:1p0B1pU2Q71pU8Q81pUBQ91pUFQ:1pUJQ;1pQJQ01pQ4Q91pQ@Q<1").
Proof. intros LB FF M sp scr p m i.
intros [E|[(b & n & I & H1 & H2)|[(g & n & I & H1 & H2)|(so & AO & H1 & H2 & SZ)]]] Hi.
- lia.
- apply (block_client L ar LB FF sp scr b n). exact I. lia.
- pose proof (globals_facts g n I) as (G0 & G1 & _). apply img_client. lia.
- apply (obj_client L ar LB FF sp scr so 24). exact AO. lia.
Qed.
Lemma asrc_vis : ltac2:(TCodec.tc2 tcn__asan_L5CoreB "QA'6':'@%2211%411&Q=%611&O'ROyR0%211'8y8%511%311p051'K&Q>vDr9r8r7r6r5r4&QBr3%211%;8:9876541&QKvEr:r2%4632>:71&QF&Q5%12?=%331=;p051p0;1pU8Q61pUBQ71pU<J1pQJL1p2Q81pTHQ61pQDQ81pQ4Q91pQ@Q<1").
Proof. intros LB FF LK cr A M model p m.
intros HH SRC. pose proof (vis_pack L ar C HI LY HIok LB FF LK cr A M model HH) as (_ & _ & VIMG & _ & VBLK & _).
destruct SRC as [E|[(b & n & I & H1 & H2)|[(g & n & I & H1 & H2)|(so & AO & H1 & H2 & SZ)]]].
- intros i Hi. lia.
- apply (VBLK b n p m I H1 H2).
- pose proof (globals_facts g n I) as (G0 & G1 & _). apply VIMG. lia. lia.
- pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr A M model so 24 0 0 HH AO ltac:(lia) ltac:(reflexivity)) as (_ & _ & _ & OVIS & _).
eapply avis_sub. exact OVIS. exact H1. exact H2.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma asrc_shadow_vis : ltac2:(TCodec.tc2 tcn__asan_L5CoreB "R1'6':'@%2211%411&Q=%611&O'ROyR0%211'8y8%511%311p051'K&Q>vDr:r9r8r7r6r5&QBr4%211%;8:9876541&QKvEr;r3%4632>:71';&R0%12<4&R1&QO%12?=%3281%7251'<'3&Q5&RN&Q0%11E%32Q71%53MK1(5%93821p0;1p0D1p0J1pT>QE1pU8QF1pUBQG1pU<Q:1pQJQ<1p2QH1pTHQF1pQDQH1pQ4QI1pQ@QL1").
Proof. intros LB FF LK cr A M model p m a.
intros HH SRC Ha. pose proof (vis_pack L ar C HI LY HIok LB FF LK cr A M model HH) as (_ & _ & _ & _ & _ & VBSH & _).
destruct SRC as [E|[(b & n & I & H1 & H2)|[(g & n & I & H1 & H2)|(so & AO & H1 & H2 & SZ)]]].
- lia.
- replace (S a) with (S a + 0) by lia. apply (VBSH b n (S a) 1 I). 2: lia. intros i Hi. unfold in_shadow_of, S.
pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _). pose proof (WB _ I) as ((B0 & _ & B2 & _) & _). cbn [fst snd] in *. lia.
- pose proof (aic_globals _ _ _ _ _ ICok _ _ _ _ _ _ _ HH) as G. rewrite Forall_forall in G. pose proof (G _ I) as [_ GAL]. cbn [fst snd] in GAL.
pose proof (globals_facts g n I) as (G0 & _ & G8 & _).
replace (S a) with (S a + 0) by lia. apply (avis_of_shadow_allowed A model g n (S a) 1 GAL). 2: lia. intros i Hi. unfold in_shadow_of, S. lia.
- pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr A M model so 24 0 0 HH AO ltac:(lia) ltac:(reflexivity)) as ((_ & _ & _ & O8 & _) & _ & _ & _ & OVSH & _).
change (24 / 8) with 3 in OVSH. replace (S a) with (so / 8 + SB + (a / 8 - so / 8)) by (unfold S; lia). apply OVSH. lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma asrc_range : ltac2:(TCodec.tc2 tcn__asan_L5CoreB "QM'6':'@%2211%411&Q=%611&O'ROyR0%211'8y8%511%311p051&QA&Q>vDr9r8r7r6r5r4r3%9887654321&QKvEr:r2%4632<861&R1z%2219';&R0+TP0%221?&QO%12A@&R4&Q6vR7%211+XPPP0%5221%;271%=2:1p0?1p0C1p0I1pU8QB1pUBQC1pT<Q61pQJQ81p2QD1pTHQB1pQDQD1pQ4QE1pQ@QH1").
Proof. intros LB FF LK cr A M V p m.
intros HH SRC Hm. pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _ & _ & SB1 & _ & TOP & _).
destruct SRC as [E|[(b & n & I & H1 & H2)|[(g & n & I & H1 & H2)|(so & AO & H1 & H2 & SZ)]]].
- lia.
- pose proof (WB _ I) as ((B0 & _ & _ & _ & B4 & _) & _). cbn [fst snd] in *. lia.
- pose proof (globals_facts g n I) as (G0 & G1 & _). rewrite (aly_img_lo L C LY), (aly_img_hi L C LY) in FSIMG. unfold app_mem, FS_BYTES in *.
assert (0x691000 <= ahl_ceil ar). { destruct FSIMG as [X|X]; lia. } lia.
- destruct AO as (f & Hf & O1 & O2 & _). pose proof (WF f Hf) as (Y1 & Y2 & _). unfold app_mem, FS_BYTES in *. rewrite (aly_img_lo L C LY), (aly_img_hi L C LY) in FSIMG.
assert (HB : 0 < ff_bytes (ff_class f)). { pose proof (WF f Hf) as (_ & _ & _ & Y4 & _). destruct Y4 as [E|[E|[E|[]]]]; rewrite <- E; reflexivity. }
lia.
Qed.
Lemma aacc_vis : ltac2:(TCodec.tc2 tcn__asan_L5CoreB "Q?'ROyR0%211'3pV421'8y8%711%311p071'@&Q1r3r2r1%43321';&R0r4%2215&R1&QO%124:%3291%8251'<r7&RN&Q0%11@%32M1%511(5%83N21p0:1pT>I1&Nr6r5%3221%M31FLp061p0K1pU8Q11pUBQ21pQJQ41pQ8Q:1").
Proof. intros H M p m.
intros ACC V a Ha. unfold byte_at in *. rewrite (mrestrict_visible H M _ (V a Ha)). exact (ACC a Ha).
Qed.
Lemma asrc_keep : ltac2:(TCodec.tc2 tcn__asan_L5CoreB "QG'6':'@%2211%411&Q=%611'ROyR0%211'8y8%511%311p051&QKvEr8r6r4r2r1%76654321&QNr9%23F18r7%43F:1&QHr:+H%332:1&Q@+3%23:>1r3%43<13p031p071pUHQ51r;r5%K6J2B@H1p041p0A1p0D1p0H1pU8Q=1pUBQ>1pQLQ31pQJQ41pQ6Q=1pQ4Q>1pQBQA1pQ@QB1").
Proof. intros LB LB' FF FF' M M' p m.
intros [E|[(b & n & I & H1 & H2)|[(g & n & I & H1 & H2)|(so & AO & H1 & H2 & SZ)]]] IB IF KEEP.
- left. exact E.
- right; left. exists b, n. split. apply IB. exact I. lia.
- right; right; left. exists g, n. split. exact I. lia.
- right; right; right. exists so. split. { destruct AO as (f & Hf & X). exists f. split. apply IF. exact Hf. exact X. }
split. exact H1. split. exact H2. apply KEEP. exact AO. exact SZ.
Qed.
End WithIface.
End SCFG_1.
End L5CB.
