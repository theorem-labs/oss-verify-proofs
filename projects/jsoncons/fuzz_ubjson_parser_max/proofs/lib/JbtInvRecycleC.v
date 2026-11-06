(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatSim StoreOk As0Tables ArtMem JbtPoison JbtInitCache JbtPopulate1 ArtRuns JbtCls JbtFp JbtClsRep JbtSecAllocPost JbtFxQ
JbtRecycle2C JbtRecycle3L JbtRecycle4P JbtRecycle4S JbtRecycle5A JbtRecycle5I JbtRecycle5T JbtInvRecycleA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JbtInvRecycleC () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtCls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtFp."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtInvRecycleA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtInvRecycleC.Where."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtPoison."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtRecycle3L."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtRecycle5A."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtRecycle5I."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtRecycle5T."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."], [["1cons"; "1fst"; "1length"; "1list"; "1nil"; "1pair"; "1prod"; "1snd"; "2and"; "2ex"; "2not"; "2or"; "3Z"; "0G"; "4cl_cache"; "4cl_free"]; ["5art_out"; "6art_rg_ok"; "7art_fp_where"; "8SB"; "9art_lcd_fp"; ":RES"; ":art_rel"; ":art_rg"; ":rg_bl"; ":rg_cls"; ";art_rel_fp"; ";art_rel_pre"; "<art_rels_fp"; "<art_rels_pre"; "=In"; ">add"]; [">div"; ">le"; ">lt"; ">mul"; ">of_nat"; ">pow"; ">sub"; "0W"; "0b"; "0b1"; "0bl"; "0bl'"; "0bl0"; "0c"; "0e"; "0es"]; ["0es'"; "0m"; "0mb"; "0ms"; "0n"; "0nf"; "0p"; "0parr"; "0ris"; "0sp1"; "0spb"; "0t"; "0x"; "0z"]]).
Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma art_not_out_in : ltac2:(TCodec.tc2 tcn__JbtInvRecycleC "Q2'3'6'<%2211%411&:&@r2r1%3221%511'9'8&Nr4%23<71&Q1&1%13@@:r3%4221&Q2&O&7%13FF@%3271%5271%?271%@2=1qS>J1%C2K1p0E1pSJN1pR@M1").
Proof.
induction W as [|p r IH]; intros x N; cbn [art_out] in N; [exfalso; apply N; exact I|].
destruct (Z_le_dec (fst p) x) as [H1|H1]; [destruct (Z_lt_dec x (fst p + snd p)) as [H2|H2]|].
- exists p. split; [left; reflexivity|lia].
- destruct (IH x) as (q & Hq & Rq); [intros O; apply N; split; [lia|exact O]|]. exists q. split; [right; exact Hq|exact Rq].
- destruct (IH x) as (q & Hq & Rq); [intros O; apply N; split; [lia|exact O]|]. exists q. split; [right; exact Hq|exact Rq].
Qed.
Definition art_rel_shw (spb : Z) (e : art_rel) : Z * Z :=
match e with
| REP c w d _ n => (SB + (spb + c * 2 ^ 32 + 16 * w + d + 16) / 8, (n + 7) / 8 * 8 / 8)
| RES mb ms _ _ _ => (SB + mb / 8, ms / 8)
| REB _ => (0, 0)
end.
Lemma art_out_intro : ltac2:(TCodec.tc2 tcn__JbtInvRecycleC "O'3'6'<%2211%411&Nr1r3%33521&:'8&Q1&1r2%23<<1%4218&Q2&O&7%13AA6%3261%52>1%<271%>11p0@1pS>F1&@%12D>p031pSJK1pR@J1").
Proof. induction W as [|p r IH]; intros x H; cbn [art_out]; [exact I|]. split; [apply H; left; reflexivity|apply IH; intros q Hq; apply H; right; exact Hq]. Qed.
Section SE.
Local Abbreviation SEC_T_art_shw_in_zone := (forall spb qs e x, spb = 65536 * qs ->
match e with
| REP c w d _ n => 0 <= d /\ d mod 16 = 0 /\ d + 16 + (n + 7) / 8 * 8 <= AsanTab.class_size c /\ AsanTab.class_size c mod 16 = 0 /\ 0 <= n
| _ => True end ->
fst (art_rel_shw spb e) <= x < fst (art_rel_shw spb e) + snd (art_rel_shw spb e) ->
SB + fst (art_rel_zone spb e) / 8 <= x < SB + (fst (art_rel_zone spb e) + snd (art_rel_zone spb e)) / 8) (only parsing).
Variable spb : ltac:(sec_ty2 constr:(SEC_T_art_shw_in_zone) 0%nat 0%nat).
Variable qs : ltac:(sec_ty2 constr:(SEC_T_art_shw_in_zone) 1%nat 0%nat).
Lemma art_shw_in_zone : ltac:(sec_stmt2 constr:(SEC_T_art_shw_in_zone) 2%nat 0%nat).
Proof.
intros e x Espb GE Hx.
destruct e as [c w d b1 n|mb ms m b1 n|wb]; cbn [art_rel_shw art_rel_zone fst snd] in *.
- destruct GE as (Hd & Hd16 & Hdsz & Hsz16 & Hn).
pose proof (Z.div_mod d 16 ltac:(lia)) as Dd. rewrite Hd16 in Dd. pose proof (Z.div_mod (AsanTab.class_size c) 16 ltac:(lia)) as Ds. rewrite Hsz16 in Ds.
set (r := (n + 7) / 8) in *.
assert (E1 : (spb + c * 2 ^ 32 + 16 * w + d + 16) / 8 = 8192 * qs + c * 2 ^ 29 + 2 * w + 2 * (d / 16) + 2).
{ rewrite Espb. replace (65536 * qs + c * 2 ^ 32 + 16 * w + d + 16) with ((8192 * qs + c * 2 ^ 29 + 2 * w + 2 * (d / 16) + 2) * 8) by lia. apply Z_div_mult. lia. }
assert (E2 : (spb + c * 2 ^ 32 + 16 * w) / 8 = 8192 * qs + c * 2 ^ 29 + 2 * w).
{ rewrite Espb. replace (65536 * qs + c * 2 ^ 32 + 16 * w) with ((8192 * qs + c * 2 ^ 29 + 2 * w) * 8) by lia. apply Z_div_mult. lia. }
assert (E3 : (spb + c * 2 ^ 32 + 16 * w + AsanTab.class_size c) / 8 = 8192 * qs + c * 2 ^ 29 + 2 * w + 2 * (AsanTab.class_size c / 16)).
{ rewrite Espb. replace (65536 * qs + c * 2 ^ 32 + 16 * w + AsanTab.class_size c) with ((8192 * qs + c * 2 ^ 29 + 2 * w + 2 * (AsanTab.class_size c / 16)) * 8) by lia. apply Z_div_mult. lia. }
assert (E4 : r * 8 / 8 = r) by (apply Z_div_mult; lia).
rewrite E1, E4 in Hx. rewrite E2, E3. assert (0 <= r) by (apply Z.div_pos; lia). lia.
- assert (mb / 8 + ms / 8 <= (mb + ms) / 8).
{ pose proof (Z.div_mod mb 8 ltac:(lia)). pose proof (Z.mod_pos_bound mb 8 ltac:(lia)). pose proof (Z.div_mod ms 8 ltac:(lia)). pose proof (Z.mod_pos_bound ms 8 ltac:(lia)).
apply Z.div_le_lower_bound; lia. }
lia.
- lia.
Qed.
End SE.
Section Where.
Variables (t spb ris parr : Z).
Definition art_fp_where (sp1 : Z) (bl : list (Z * Z)) (es : list art_rel) (x : Z) : Prop :=
(sp1 - 320 <= x < sp1) \/ (0x139418 + 56 <= x < 0x1396a8) \/ (t + 208 <= x < t + 2904) \/ (ris <= x < ris + 4096)
\/ (exists c, 1 <= c <= 30 /\ spb + c * 2 ^ 32 + 3758096384 <= x < spb + c * 2 ^ 32 + 2 ^ 32)
\/ (exists e, In e es /\ (fst (art_rel_zone spb e) <= x < fst (art_rel_zone spb e) + snd (art_rel_zone spb e)
\/ fst (art_rel_shw spb e) <= x < fst (art_rel_shw spb e) + snd (art_rel_shw spb e)))
\/ (parr <= x < parr + 2 ^ 23) \/ (exists b, In b bl /\ fst b + 24 <= x < fst b + 32).
#[using="Type"] Lemma art_fp_where_mono : ltac2:(TCodec.tc2 tcn__JbtInvRecycleC "Q5'<'3'6%1233%311'F%511&Nr1r6%33721r2%53913p031pRB;1r5%93;81%:3<62p021pRN>1&Br8r7r3%443291r9r4%7425<1p041p0:1p0@1pSJO1pS2J1pS0K1pRHN1pRFO1pSDQ41").
Proof.
intros sp1 bl bl' es es' x Hb He [H|[H|[H|[H|[H|[(e & Hin & H)|[H|(b & Hin & H)]]]]]]]; unfold art_fp_where; auto 10.
- do 5 right. left. exists e. split; [apply He; exact Hin|exact H].
- do 7 right. exists b. split; [apply Hb; exact Hin|exact H].
Qed.
#[using="Type"] Lemma art_lcd_fp_where : ltac2:(TCodec.tc2 tcn__JbtInvRecycleC "RG'<'6%1222'8&Q1+1r4%3221+N%5231%7231z%8216&O&Q3+4r5%3221+Q0%6221&Q5+2+M%3221%D251&N&Dr8vQK+V@%A221vQJvQHr7r6%96854321%;3Q2N1&1%13Q6Q6F%Q3215&Q2&7%13Q:Q:J%N251%42:1%Q:261';&Q6r:+Z0%3221%Q?21B%<2C4%QB221%QB2HE+RjH%Q;2L1%A2H1%QG241%QG2KJ+TP0%Q@2M1%F2M1%QL241r9%Q=2Q<Q?%QD221%QF2Q41+S`PPPP0%QH221%R221Q5%QJ246%Q02Q71%R6231%L2;1%M2A1%N2G1p0Q01p0Q:1p0QG1p0R41p0R71pS>R@1pSJRC1pS<RD1pRLRE1pSDRF1").
Proof.
intros sp1 c nf x p Hc Hnf Hb Hin Hx. unfold art_lcd_fp in Hin. cbn [In] in Hin.
destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [fst snd] in Hx; lia.
Qed.
Section SE.
Local Abbreviation SEC_T_art_rel_fp_where := (ltac2:(TCodec.tc2 tcn__JbtInvRecycleC "RF'<'G'F'6%1244&Kr4r3%3221'8&Q1+1r1%3221+N%5231%7231&O&Q3+4&Q4&2&?&Ir7r2%3221%511%72L1%911%<2;1+Q0%?221&Q5+2+M%3221%K251p0F1pRLQ71&Hr6%211%F2Q71%H11+D%=2<1%Q5231&N&JvQKvQJvQHvQGr8%6754321O>%83QDQB1&1r5%23QKQK1%QB21C&Q2&7%13QOQO5%Q?251%42H1%QI261&Br:r9%N11(0(4%11R7%33R8D1%84751QCp0:1p0E1p0O1p0Q81p0R81pS>R=1pSJRB1pRNRA1pLRC1pSDRE1")) (only parsing).
Variable sp1 : ltac:(sec_ty2 constr:(SEC_T_art_rel_fp_where) 0%nat 0%nat).
Variable G : ltac:(sec_ty2 constr:(SEC_T_art_rel_fp_where) 1%nat 0%nat).
Lemma art_rel_fp_where : ltac:(sec_stmt2 constr:(SEC_T_art_rel_fp_where) 2%nat 0%nat).
Proof using Type sp1 G.
intros e x p PRE NF LEN Hin Hx.
unfold art_fp_where.
destruct e as [c w d b1 n|mb ms m b1 n|wb]; cbn [art_rel_fp art_rel_pre] in *.
- destruct PRE as (Hc & (Hw0 & _) & _ & Hd & Hd16 & Hdsz & _ & Hn).
assert (Hr0 : 0 <= (n + 7) / 8 * 8) by (assert (0 <= (n + 7) / 8) by (apply Z.div_pos; lia); lia).
unfold art_cbr_prim_fp in Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
+ cbn [In] in Hin. destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd] in Hx.
* left. lia.
* do 5 right. left. exists (REP c w d b1 n). split; [left; reflexivity|]. left. cbn [art_rel_zone fst snd]. lia.
* do 5 right. left. exists (REP c w d b1 n). split; [left; reflexivity|]. left. cbn [art_rel_zone fst snd]. lia.
* do 5 right. left. exists (REP c w d b1 n). split; [left; reflexivity|]. right. cbn [art_rel_shw fst snd]. exact Hx.
* right; right; left. lia.
+ destruct (art_lcd_fp_where sp1 c (Z.of_nat (length (cl_free (rg_cls G c)))) x p Hc ltac:(lia) (NF c Hc) Hin Hx) as [H|[H|[H|H]]]; [left; exact H|right; right; left; exact H|right; right; right; left; exact H|].
do 4 right. left. exists c. split; [exact Hc|exact H].
- destruct PRE as (Hbl & Lo & Hi & _).
assert (NEl : rg_bl G <> []) by (intros E; rewrite E in Hbl; destruct Hbl).
assert (Hlast : In (nth (length (rg_bl G) - 1) (rg_bl G) (0, 0)) (rg_bl G)) by (apply nth_In; destruct (rg_bl G); [contradiction|cbn [length]; lia]).
assert (Hidx : (art_bl_idx mb (rg_bl G) < length (rg_bl G))%nat).
{ clear - Hbl. induction (rg_bl G) as [|b r IH]; [destruct Hbl|]. cbn [art_bl_idx length]. destruct (Z.eqb_spec (fst b) mb) as [E|NE]; [lia|].
destruct Hbl as [Eb|Hb]; [exfalso; apply NE; rewrite Eb; reflexivity|]. specialize (IH Hb). lia. }
unfold art_cbr_sec_fp, art_secd_fp in Hin. cbn [In app] in Hin.
destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]; cbn [fst snd] in Hx.
+ left. lia.
+ right; right; left. lia.
+ left. lia.
+ right; left. lia.
+ right; left. lia.
+ do 6 right. left. lia.
+ do 7 right. exists (nth (length (rg_bl G) - 1) (rg_bl G) (0, 0)). split; [exact Hlast|lia].
+ right; right; left. lia.
+ do 5 right. left. exists (RES mb ms m b1 n). split; [left; reflexivity|]. right. cbn [art_rel_shw fst snd]. exact Hx.
+ do 5 right. left. exists (RES mb ms m b1 n). split; [left; reflexivity|]. left. cbn [art_rel_zone fst snd]. exact Hx.
- destruct (art_lcd_fp_where sp1 24 (Z.of_nat (length (cl_free (rg_cls G 24)))) x p ltac:(lia) ltac:(lia) (NF 24 ltac:(lia)) Hin Hx) as [H|[H|[H|H]]]; [left; exact H|right; right; left; exact H|right; right; right; left; exact H|].
do 4 right. left. exists 24. split; [lia|exact H].
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_rels_fp_where := (ltac2:(TCodec.tc2 tcn__JbtInvRecycleC "S2'<'3'6%1233%311'F%511'G&Mr3r4%3221&A%113'8&Q1+1r1%3221+N%5231%7231&O&Q4&2&>&Ir7r2%3221%511%72O1%911&?%115%;2Q31%=11%?251r8%?2Q21%A11%C241&Q5+2+J%3221%O251p0J1pRLQ@1&Hr6%211%L2QA1%N11+D%=2<1%Q9231&N%91D%23QHQ:1r;%43QJQ11p031pRBQL1&LvQKvQJvQHvQGr9%675432:Q01%>3R4E1&1%13R9R9Q>%QK21Q4&Q2&7%13R=R=QB%QH251%42Q91%R2261&Br=r<%3421H?p051p0?1p0H1p0Q01p0Q91p0R=1p0R@1pS>RI1pSJRM1pLRG1pS0RI1pRJRL1pSDS11")) (only parsing).
Variable sp1 : ltac:(sec_ty2 constr:(SEC_T_art_rels_fp_where) 0%nat 0%nat).
Variable bl0 : ltac:(sec_ty2 constr:(SEC_T_art_rels_fp_where) 1%nat 0%nat).
Lemma art_rels_fp_where : ltac:(sec_stmt2 constr:(SEC_T_art_rels_fp_where) 2%nat 0%nat).
Proof using Type sp1 bl0.
intros es.
induction es as [|e r IH]; intros G x p PRE OK CNT LEN SUB Hin Hx; cbn [art_rels_fp] in Hin; [destruct Hin|].
destruct PRE as (Pe & Pr). apply in_app_or in Hin. destruct Hin as [Hin|Hin].
- apply (art_fp_where_mono sp1 (rg_bl G) bl0 [e] (e :: r) x SUB); [intros e' [<-|[]]; left; reflexivity|].
apply (art_rel_fp_where sp1 G e x p Pe); [|exact LEN|exact Hin|exact Hx].
intros c Hc. specialize (CNT c Hc). cbn [length] in CNT. lia.
- apply (art_fp_where_mono sp1 bl0 bl0 r (e :: r) x (fun b H => H)); [intros e' He'; right; exact He'|].
apply (IH (art_rel_step e G) x p Pr (art_rg_ok_step e G OK Pe)); [| | |exact Hin|exact Hx].
+ intros c Hc. specialize (CNT c Hc). cbn [length] in CNT. destruct OK as (CK & _).
destruct e as [c0 w0 d0 b10 n0|mb0 ms0 m0 b10 n0|wb0]; cbn [art_rel_step rg_cls art_rel_pre] in *.
* destruct Pe as (Hc0 & _). destruct (Z.eq_dec c c0) as [->|NE]; [rewrite art_cls_upd_same|rewrite art_cls_upd_other by exact NE; lia].
pose proof (art_cls_dealloc_total c0 w0 (rg_cls G c0) (CK c0 Hc0) ltac:(lia)). lia.
* lia.
* destruct (Z.eq_dec c 24) as [->|NE]; [rewrite art_cls_upd_same|rewrite art_cls_upd_other by exact NE; lia].
pose proof (art_cls_dealloc_total 24 wb0 (rg_cls G 24) (CK 24 ltac:(lia)) ltac:(lia)). lia.
+ destruct e as [c0 w0 d0 b10 n0|mb0 ms0 m0 b10 n0|wb0]; cbn [art_rel_step rg_bl]; try exact LEN. rewrite art_swap_remove_length. lia.
+ intros b Hb. apply SUB. destruct e as [c0 w0 d0 b10 n0|mb0 ms0 m0 b10 n0|wb0]; cbn [art_rel_step rg_bl] in Hb; try exact Hb. exact (art_swap_remove_in _ _ _ _ _ Hb).
Qed.
End SE.
End Where.
Lemma art_in_not_out : ltac2:(TCodec.tc2 tcn__JbtInvRecycleC "O'3'6'<%2211%411&Nr2r3%33521'8&Q1&1%13::5%3217&Q2&O&7%13??:%3261%52=1%;271&:&@r5%221A%411p061p0C1pSLJ1pS>J1pR@J1").
Proof. induction W as [|q r IH]; intros p z Hp Hz O; [destruct Hp|]. cbn [art_out] in O. destruct O as (O1 & O2). destruct Hp as [->|Hp]; [exact (O1 Hz)|exact (IH p z Hp Hz O2)]. Qed.
Lemma art_rels_fp_sec_in : ltac2:(TCodec.tc2 tcn__JbtInvRecycleC "QE'<'3'F%211'G&N(Er5r4r3r2r1%6554321r7%93<21'8'6%12AA(5r6%24DD1=&Lr=r<r;r:r9r8%7765432?1%H3<91&O&C&Q0+8%22?1%5241%42M3%C4Q5Q521%Q13E1:%H2:1p0J1pS:Q91pRDQ:1pS4Q;1pS8Q<1pS6Q=1pLQ:1pS0Q<1pSDQ@1pS@QA1pSBQB1pSFQC1pSHQD1").
Proof.
intros t spb ris parr sp1 es. induction es as [|e r IH]; intros G mb ms m b1 n Hin; [destruct Hin|]. cbn [art_rels_fp].
destruct Hin as [->|Hin]; [|destruct (IH (art_rel_step e G) mb ms m b1 n Hin) as (X1 & X2); split; apply in_or_app; right; assumption].
cbn [art_rel_fp]. unfold art_cbr_sec_fp, art_secd_fp. split; apply in_or_app; left; cbn [In app]; tauto.
Qed.
