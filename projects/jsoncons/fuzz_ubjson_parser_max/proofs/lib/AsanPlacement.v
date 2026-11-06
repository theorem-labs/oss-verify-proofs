(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Monad Specs.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AsanCeil PlacementSearch.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__AsanPlacement () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanCeil."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlacement.FPX_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlacement.FPX_1.Gap."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1app"; "1bool"; "1cons"; "1false"; "1length"; "1list"; "1nat"; "1nil"; "1pair"; "1prod"; "1snd"; "1true"; "2and"; "2eq"; "2ex"; "2or"]; ["3le"; "3lt"; "4Forall"; "5Z"; "0K"; "0L"; "6VmMaps"; "6iv_overlap"; "6mmap_base_min"; "6page_size"; "6region_free"; "6vm_maps"; "6vm_mmap_base"; "6vm_reserved"; "0N"; "7alloc_ceiling"]; ["7bottomup_floor"; "7hint_placement_ok_b"; "7placement_ok_b"; "9gap_at"; "9scan_inv"; "8gap_weight"; "8gw_sizes"; "8kHighMemBeg"; "8ledger_split"; "8live_at"; ":In"; ":filter"; ":incl"; ";add"; ";div"; ";le"]; [";lt"; ";min"; ";modulo"; ";mul"; ";of_nat"; ";pow"; ";sub"; "0Y"; "0Y'"; "0a"; "0b"; "0c"; "0c'"; "0f"; "0g"; "0h"]; ["0k"; "0l"; "0l'"; "0l1"; "0l2"; "0lo"; "0maps"; "0n"; "0nZ"; "0p"; "0s"; "<Z_to_bv"; "<bv"; "<bv_unsigned"; "0tot"; "0x"]; ["0z"]]).
Section FPX_1. Context {fx : PropExec.FPState}.
Lemma fg_u64_lit : ltac2:(TCodec.tc2 tcn__AsanPlacement "G'C'<&Q?zr1%3221&Q@&QE+2+R0%3221%5271%;271'=&R=yR0&R;r2%2231%5241%73D13p091pU2F1").
Proof.
intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
unfold bv_modulus. exact Hz.
Qed.
Lemma fg_alloc_ceiling_val : ltac2:(TCodec.tc2 tcn__AsanPlacement "5'='C&O+SoomohPPP0%43321").
Proof. reflexivity. Qed.
Lemma fg_u64_range : ltac2:(TCodec.tc2 tcn__AsanPlacement "B'R<yR0%211'<&Q?z&R=r1%2271%5241&Q@&QE+2+R0%3221%5271%=271pU0?1").
Proof. intro x. exact (bv_unsigned_in_range _ x). Qed.
Lemma page_multiple_eq : ltac2:(TCodec.tc2 tcn__AsanPlacement "A'C'=&QBr1&I%3221z%63721r2&QC&Q>+TP0%2241%4212%=3>61p081pU2@1").
Proof.
intros z Hz. unfold page_size in Hz.
pose proof (Z.div_mod z 4096 ltac:(lia)). lia.
Qed.
Lemma fg_region_free_false : ltac2:(TCodec.tc2 tcn__AsanPlacement "Q6'5'9'R<yR0%211%4211%611'='1&Jr3r2r1%43321(3%83721'>'<&Q:(8%14@@98r6%43A21&Gr5r4%3421?>(;%E3D21%<271qTFJ1%?2K1qSFL1%A2M1p0C1pT@O1pT<Q01pT>O1").
Proof.
induction maps as [|[b s] r IH]; intros lo n H; [discriminate|].
cbn in H. apply andb_false_iff in H as [H|H].
- apply negb_false_iff in H. exists b, s. split; [now left|exact H].
- destruct (IH lo n H) as (b' & s' & Hin & Hov).
exists b', s'. split; [now right|exact Hov].
Qed.
Fixpoint gap_weight (nZ : Z) (l : list (word * word)) : Z :=
match l with
| [] => 0
| (_, s) :: r => bv_unsigned s + nZ + 4095 + gap_weight nZ r
end.
Lemma gap_weight_app : ltac2:(TCodec.tc2 tcn__AsanPlacement "H'C'5'9'R<yR0%211%4211%611'=&Q5r3&0r2r1%33821%6251&Q=%8275%9285%3221%<3D51pT:>1pT8?1pTBG1").
Proof. induction l1 as [|[b s] l1 IH]; intros l2; cbn; [reflexivity|rewrite IH; lia]. Qed.
Lemma gap_weight_nonneg : ltac2:(TCodec.tc2 tcn__AsanPlacement "C'C'5'9'R<yR0%211%4211%611&Q?zr2%3221&Q5r3%2214%7261p051pT4:1pTBB1").
Proof.
induction l as [|[b s] l IH]; intros HnZ; cbn; [lia|].
pose proof (bv_unsigned_in_range 64 s). specialize (IH HnZ). lia.
Qed.
Definition live_at (c : Z) (p : word * word) : bool :=
c <? bv_unsigned (fst p) + bv_unsigned (snd p).
Lemma gap_weight_filter_le : ltac2:(TCodec.tc2 tcn__AsanPlacement "J'C'9'R<yR0%211%4211'1p021'5%114&Q?zr3%3221&Q5r4&Q;r2%23=61%5241%6253%;221p091pT4>1pSLA1pTBI1").
Proof.
induction l as [|[b s] l IH]; intros HnZ; cbn; [lia|].
pose proof (bv_unsigned_in_range 64 s). specialize (IH HnZ).
destruct (f (b, s)); cbn; lia.
Qed.
Lemma live_weight_step : ltac2:(TCodec.tc2 tcn__AsanPlacement "R6'C'5'9'R<yR0%211%4211%611&Q?zr6%3221r5r4%6221&Q:(8r3%24==51r7%53>21'='1&Q9%84CC<;%2261(;%63521%<4GGB@%62:1(3%:3921'<&Q=&Q5r;&Q;r8%?11r:%43Q221%7261&R=%12Q7Q1%;219+SoO%=221%>261r9%J11%>3Q<1;%A2@1%Q<251&A&4%12QA?%22QB6%4221%J261p0L1p0Q11p0Q91p0Q@1p0QD1pTFQK1pSFQL1pSJR21pSHR31pT4QM1pTBR51").
Proof.
intros nZ l c c' b s HnZ Hcc'.
induction l as [|[b0 s0] l IH]; intros Hin Hlive Hdead; [contradiction|].
assert (Hmono : forall p, live_at c' p = true -> live_at c p = true).
{ intros [x y] H. unfold live_at in *. cbn in *. apply Z.ltb_lt in H. apply Z.ltb_lt. lia. }
assert (Hle : gap_weight nZ (List.filter (live_at c') l) <= gap_weight nZ (List.filter (live_at c) l)
/\ (length (List.filter (live_at c') l) <= length (List.filter (live_at c) l))%nat).
{ clear IH Hin. induction l as [|[x y] l IHl]; cbn; [split; [lia|constructor]|].
pose proof (bv_unsigned_in_range 64 y).
destruct (live_at c' (x, y)) eqn:E'.
- rewrite (Hmono _ E'). cbn. destruct IHl; split; [lia|]. apply le_n_S. assumption.
- destruct (live_at c (x, y)); cbn; destruct IHl; split; try lia. }
destruct Hin as [Heq|Hin].
- injection Heq as -> ->. cbn. rewrite Hlive, Hdead. cbn.
destruct Hle as [Hw Hl]. split; [lia|]. apply Nat.lt_succ_r in Hl. exact Hl.
- destruct (IH Hin Hlive Hdead) as [Hw Hl]. cbn.
pose proof (bv_unsigned_in_range 64 s0).
destruct (live_at c' (b0, s0)) eqn:E'.
+ rewrite (Hmono _ E'). cbn. split; [lia|]. apply Nat.succ_lt_mono in Hl. exact Hl.
+ destruct (live_at c (b0, s0)); cbn; split; lia.
Qed.
Section Gap.
Variable L : list (word * word).
Variable nZ : Z.
Hypothesis HnZ : 0 <= nZ.
Definition scan_inv (c : Z) : Prop :=
c mod page_size = 0 /\ bottomup_floor <= c
/\ c + nZ + gap_weight nZ (List.filter (live_at c) L) <= alloc_ceiling.
Definition gap_at (c : Z) : Prop :=
c mod page_size = 0 /\ bottomup_floor <= c /\ c + nZ <= alloc_ceiling
/\ region_free L (Z_to_bv 64 c) (Z_to_bv 64 nZ) = true.
Lemma scan_ok_or_step : ltac2:(TCodec.tc2 tcn__AsanPlacement "Q2'C&Q4r1%211'?&Q3r2%211'>'<&A&4'9'R<yR0%211%4211&Q;&Q9%11AvE%43521%;261r3%611%83915%?2:1%A251%C2I1qSJM1%F2N1%K2H1p0M1pSHQ11").
Proof.
intros c (Hal & Hfl & Hw).
pose proof fg_alloc_ceiling_val as Hcv. pose proof bottomup_floor_val as Hfv.
pose proof (gap_weight_nonneg nZ (List.filter (live_at c) L) HnZ) as Hw0.
assert (Hc64 : 0 <= c < 2 ^ 64) by lia.
assert (Hcu : bv_unsigned (Z_to_bv 64 c) = c) by (apply fg_u64_lit; lia).
assert (Hnu : bv_unsigned (Z_to_bv 64 nZ) = nZ) by (apply fg_u64_lit; lia).
destruct (region_free L (Z_to_bv 64 c) (Z_to_bv 64 nZ)) eqn:Hfree.
- left. split; [exact Hal|]. split; [exact Hfl|]. split; [lia | exact Hfree].
- right.
destruct (fg_region_free_false _ _ _ Hfree) as (b & s & Hin & Hov).
unfold iv_overlap in Hov. rewrite Hcu, Hnu in Hov.
apply andb_true_iff in Hov as [H1 H2]. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2.
set (B := bv_unsigned b) in *. set (S := bv_unsigned s) in *.
set (c' := page_round_up_Z (B + S)).
pose proof (page_round_up_Z_ge (B + S)) as Hge.
assert (Hle : c' <= B + S + 4095).
{ unfold c', page_round_up_Z, page_size.
pose proof (Z.mul_div_le (B + S + 4096 - 1) 4096 ltac:(lia)). lia. }
assert (Hlive : live_at c (b, s) = true) by (unfold live_at; cbn; apply Z.ltb_lt; lia).
assert (Hdead : live_at c' (b, s) = false) by (unfold live_at; cbn; apply Z.ltb_ge; lia).
destruct (live_weight_step nZ L c c' b s HnZ ltac:(lia) Hin Hlive Hdead) as [Hws Hlen].
exists c'. split; [|exact Hlen].
split; [apply page_round_up_Z_aligned|].
split; lia.
Qed.
Lemma scan : ltac2:(TCodec.tc2 tcn__AsanPlacement "M'6'C'@&4'9'R<yR0%211%4211&Q;&Q9r1%211vE%53621%<271r2%?221&Q4%113'>&Q3%11;qSNF1%42G1p061p091pSHJ1pT2L1").
Proof.
induction k as [|k IH]; intros c Hk Hinv.
- destruct (scan_ok_or_step c Hinv) as [Hok|(c' & _ & Hlt)]; [|lia].
exists c. exact Hok.
- destruct (scan_ok_or_step c Hinv) as [Hok|(c' & Hinv' & Hlt)].
+ exists c. exact Hok.
+ apply (IH c'); [lia|exact Hinv'].
Qed.
Theorem free_gap_of_slack : ltac2:(TCodec.tc2 tcn__AsanPlacement "Q7&Q?&Q=&Q0vR8%3221&Q5vE%2241%7241&O%:221'>'C'<'=&QBr1&I%3221z%63821%E2C5%E26C%G21>'1&J&R;yR0%221<%322J%53H21(;%B3821%D2:1%E2=1%F2?1qSNH1%J2I1p0L1").
Proof.
intros Hslack.
assert (Hinv : scan_inv bottomup_floor).
{ split; [rewrite bottomup_floor_val; reflexivity|]. split; [lia|].
pose proof (gap_weight_filter_le nZ (live_at bottomup_floor) L HnZ). lia. }
exact (scan _ bottomup_floor (le_n _) Hinv).
Qed.
End Gap.
Lemma gap_weight_bound : ltac2:(TCodec.tc2 tcn__AsanPlacement "Q:'C'5'9'R<yR0%211%4211%611&Q?zr3%3221'B&R=&:r1%23;;1%42=1r4%;221qTD>1r2%:3@21&Q5r5%221?&QC&QD&4%12GC%311&Q=%12>8+SoO%3221%9251%L2;1p0?1p0K1pT4Q01pQNQ81pTBQ91").
Proof.
intros nZ N l HnZ H. induction H as [|[b s] l Hs _ IH]; cbn -[Z.of_nat]; [lia|].
cbn in Hs. rewrite Nat2Z.inj_succ. lia.
Qed.
Fixpoint gw_sizes (l : list (word * word)) : Z :=
match l with [] => 0 | iv :: r => bv_unsigned (snd iv) + gw_sizes r end.
Lemma gap_weight_sizes : ltac2:(TCodec.tc2 tcn__AsanPlacement "L'C'5'9'R<yR0%211%4211%611'=&Q5r2r1%3221&Q=&Q6%114&QC&QD&4%12=8%311+SoO%92<1%7231%;291%A3I=1pT4C1pTBK1").
Proof.
intros nZ l. induction l as [|[b s] l IH]; cbn -[Z.of_nat Z.mul Z.add]; [reflexivity|].
rewrite IH, Nat2Z.inj_succ. lia.
Qed.
Theorem free_gap_of_totals : ltac2:(TCodec.tc2 tcn__AsanPlacement "RA'F'C&Q?zr2%3221&Q6&0'9'R<yR0%211%4211&Mr4%211&K%113%;3631%=11%B21@&Q=&Q0%2219r3%4221&QC&QD&4r5%A11%?12%I3D21%52E1%711+SoO%?2F1%;231%A2=1&O%Q6221'>'<'=&QBr1&I%3221%53Q?1Q=%Q?2K4r6%N261%QB21='1&Jr7%Q;11%Q912%QC3Q>21&R;%12QB?%22QC;%83421(;%E3;21&Q1%72QHQO%241<FA%I3?15%K251%L2B1%M2F1%N2H1qSNR81%Q12R91p0Q31p0QH1p0R81pTNR=1pTBR>1pT0R@1").
Proof.
intros h nZ tot HnZ Htot Hband.
destruct (free_gap_of_slack (vm_reserved h ++ vm_maps h) nZ HnZ) as (g & Hal & Hfl & Hc & Hfree).
{ rewrite gap_weight_sizes. lia. }
exists g. split; [exact Hal|]. split; [exact Hfl|]. split; [exact Hc|]. split; [exact Hfree|].
apply hint_placement_ok_b_of_floor. exact Hfl.
Qed.
Definition ledger_split (l : list (word * word)) (K Y : Z) : Prop :=
forall b s, In (b, s) l -> bv_unsigned b + bv_unsigned s <= K \/ Y <= bv_unsigned b.
Lemma ledger_split_nil : ltac2:(TCodec.tc2 tcn__AsanPlacement ">'C&Q8(7'9'R<yR0%211%4211%611r2r1%:3321pS@<1pQ:=1").
Proof. intros K Y b s []. Qed.
Lemma ledger_split_mono : ltac2:(TCodec.tc2 tcn__AsanPlacement "H'5'9'R<yR0%211%4211%611'C&Q8r4r3r2%43321&Q?%1234r6r5%93217p041p071pSB=1pS@>1pQ:?1pT4A1").
Proof. intros l K Y Y' H HY b s Hin. destruct (H b s Hin); [left|right]; lia. Qed.
Lemma ledger_split_cons : ltac2:(TCodec.tc2 tcn__AsanPlacement "Q6'5'9'R<yR0%211%4211%611'C&Q8r5r4r3%43321'?&Q?&Q=&R=%12>6r2%32@1%5231%721<%82<5%:221(2(8%14FF@?r7%43G21r6%F321Ep081p0D1pTFM1pSFN1pS@L1pQ:M1pT4O1").
Proof.
intros l K Y b s H Hbs b' s' [Heq|Hin]; [injection Heq as <- <-; exact Hbs|].
exact (H b' s' Hin).
Qed.
Lemma ledger_split_app : ltac2:(TCodec.tc2 tcn__AsanPlacement "J'5'9'R<yR0%211%4211%611'C&Q8r4r2r1%43321r3%63514&0r6r5%33=21%;31:6p061p091pS@?1pQ:@1pT:B1pT8C1").
Proof.
intros l1 l2 K Y H1 H2 b s Hin. apply in_app_iff in Hin as [Hin|Hin]; eauto.
Qed.
Lemma ledger_split_app_inv : ltac2:(TCodec.tc2 tcn__AsanPlacement "J'5'9'R<yR0%211%4211%611'C&Q8&0r4r3%33721r2r1%73321'<r5%:3175%;3986%4221p061pS@?1pQ:@1pT:B1pT8C1").
Proof.
intros l1 l2 K Y H. split; intros b s Hin; apply H; apply in_app_iff; auto.
Qed.
Lemma ledger_split_incl : ltac2:(TCodec.tc2 tcn__AsanPlacement "H'5'9'R<yR0%211%4211%611'C&Q8r4r2r1%43321&Q<r5%23:61r3%93381p031p071pS@=1pQ:>1pT6@1pT4A1").
Proof. intros l l' K Y H Hincl b s Hin. apply H. apply Hincl. exact Hin. Qed.
Lemma ledger_split_filter : ltac2:(TCodec.tc2 tcn__AsanPlacement "I'9'R<yR0%211%4211'1p021'5%114'C&Q8r3r2r1%43321&Q;r5r4%33>21%93187p061pS@<1pQ:=1pT4?1pSLB1").
Proof.
intros f l K Y H. apply (ledger_split_incl l); [exact H|].
intros x Hx. apply filter_In in Hx. tauto.
Qed.
Lemma ledger_split_window_free : ltac2:(TCodec.tc2 tcn__AsanPlacement "QE'5'9'R<yR0%211%4211%611'C&Q?zr3%3221&Q@r2%2251&Q=r5&QC+2%2219%5241r4%>221&QE+R0%2271%>2:1&Q8r8r7r6%43321'='1&Jr9&R;&QF%1298%32Q41%42Q5:%73621(;%;3:21p0=1p0C1p0H1p0Q11p0Q51pTBQ:1pS@Q;1pQ:Q<1pT4Q>1").
Proof.
intros l K Y nZ HK HnZ HY HY64 Hsplit.
apply region_free_intro. intros b s Hin.
unfold iv_overlap. rewrite !fg_u64_lit by lia.
pose proof (bv_unsigned_in_range 64 s).
destruct (Hsplit b s Hin) as [Hlow|Hhigh].
- apply andb_false_iff. left. apply Z.ltb_ge. lia.
- apply andb_false_iff. right. apply Z.ltb_ge. lia.
Qed.
Theorem null_hint_grant_above : ltac2:(TCodec.tc2 tcn__AsanPlacement "R?'F'R<yR0%211'C&Q@zr3%3221'=&QBr4&I%3221%53:18&R=r6%22?1%8216%:3?1=&Q?r5&Lr9%211%:2G1%6251r7%82F1&Q=r8&QC+2%221:%5241%?218&Q8&0'9%12Q4Q4&Mr<%211&K%113%83631%:31G@'1&Q2r=%Q32Q@9r;%43321(;%Q=3721'?&Q0%Q:2QG8%Q6221&QFr:%N2MD%3221%QJ216%9261p0;1p0D1p0Q01p0Q81p0Q;1p0QH1p0QD1p0QJ1p0R11pS@R61pQ:R71pTBR81pSDR:1pT0R>1").
Proof.
intros h a nZ K Y HnZ HnAl HaAl HYal HYB HK HY Hsplit Hpl.
pose proof (fg_u64_range a) as Ha.
pose proof (fg_u64_range (vm_mmap_base h)) as HB.
assert (HY64 : Y < 2 ^ 64) by (clear - HB HYB; lia).
assert (HgAl : (Y - nZ) mod page_size = 0).
{ rewrite Zminus_mod, HYal, HnAl. reflexivity. }
pose proof (ledger_split_window_free _ K Y nZ HK HnZ HY HY64 Hsplit) as Hfree.
apply (placement_ok_b_iff h (bv_unsigned a) nZ (proj1 Ha) HnZ HaAl HnAl) in Hpl.
clear HnAl HaAl HYal.
destruct Hpl as [Hfl|Hnhf]; [left; exact Hfl|right].
destruct (Z.lt_ge_cases (Y - 2 * nZ) (bv_unsigned a)) as [Hlt|Hge]; [exact Hlt|exfalso].
assert (H1 : bv_unsigned a + nZ <= Y - nZ) by (clear - Hge; lia).
assert (H2 : Y - nZ + nZ <= bv_unsigned (vm_mmap_base h)) by (clear - HYB; lia).
pose proof (Hnhf (Y - nZ) HgAl H1 H2) as Hno.
rewrite Hfree in Hno. discriminate.
Qed.
Theorem null_hint_grant_step : ltac2:(TCodec.tc2 tcn__AsanPlacement "S@'F'R<yR0%211'C&Q@zr3%3221'=&QBr4&I%3221%53:18&R=r7%22?1%8216%:3?1=&Q?r5&Lr:%211%:2G1%6251%72E;r8&Q0%I221&Q=r9&QC+2%221<%5241%A219&Q8&0'9%12Q6Q6&Mr>%211&K%113%83631%:31I@'1&Q2r?%Q52QB9r<%43321(;%Q?3721&QAr;%Q<2QI8%3221'<r=r@%QA2QN1%QL231'?r1%Q@2Q71&QF%Q52Q4K%22B1%Q921QL%QE216%8261%QG28F%R229R0%R43R91R7rA%QI11%R12R>1%QM2>1%Q814(2(8%14RBRBFQ2%Q918%43Q>21%QA3Q?61%QC31KF%M291%N2>1%O2A1%Q02C1%Q12M1tSBRKQ31p0Q81p0QA1p0QM1p0R51p0R91p0R;1p0RH1p0RD1p0RJ1p0S11pS@S61pQ:S71pTBS81pT@S:1pSDS;1pT0S?1").
Proof.
intros h a n nZ K Y HnZ HnAl HaAl HYal HYB HK HKfl HY Hsplit Hpl Y'.
pose proof (null_hint_grant_above h a nZ K Y HnZ HnAl HaAl HYal HYB HK HY Hsplit Hpl) as Habove.
pose proof bottomup_floor_val as Hfv.
pose proof (page_multiple_eq _ HaAl) as E1.
pose proof (page_multiple_eq _ HYal) as E2.
pose proof (page_multiple_eq _ HnAl) as E3.
clear HnAl HaAl HYal Hpl. unfold page_size.
set (qa := bv_unsigned a / 4096) in *. set (qy := Y / 4096) in *. set (qn := nZ / 4096) in *.
clearbody qa qy qn.
assert (Hqn : 1 <= qn) by lia.
assert (Hpage : bottomup_floor <= bv_unsigned a \/ Y - 2 * nZ + 4096 <= bv_unsigned a).
{ destruct Habove as [Hfl|Hlt]; [left; exact Hfl|right]. lia. }
split; [|split; [|split; [|split; [|split]]]].
- destruct Habove; lia.
- subst Y'.
destruct (Z.le_gt_cases Y (bv_unsigned a));
[rewrite Z.min_l by lia; right; lia | rewrite Z.min_r by lia; destruct Hpage; [left|right]; lia].
- lia.
- subst Y'. destruct (Z.le_gt_cases Y (bv_unsigned a)); [rewrite Z.min_l by lia | rewrite Z.min_r by lia];
[rewrite E2 | rewrite E1]; apply Z_mod_mult.
- lia.
- apply ledger_split_app_inv in Hsplit as [Hr Hm].
apply ledger_split_app; [eapply ledger_split_mono; [exact Hr|lia]|].
apply ledger_split_cons; [eapply ledger_split_mono; [exact Hm|lia]|].
right. lia.
Qed.
Definition kHighMemBeg : Z := 0x10007fff8000.
Lemma kHighMemBeg_below_mmap_base_min : ltac2:(TCodec.tc2 tcn__AsanPlacement "='<'='C&Q=&Q7+UXcZe[lP0%3221&H%73621&Q@&Q0%2241%<241").
Proof. unfold kHighMemBeg, mmap_base_min. rewrite bottomup_floor_val. split; reflexivity. Qed.
Corollary kHighMemBeg_le : ltac2:(TCodec.tc2 tcn__AsanPlacement "R7'F'R<yR0%211'C&Q@zr2%3221'=&QBr3&I%3221%53:18&R=r5%22?1%8216%:3?1=r4%;219%=3B1@&Q?&Lr8%211%<2I1%52<1&Q=&Q7&QC+2r7%3221%6251r6%>221&Q8&0'9%12Q6Q6&Mr:%211&K%113%83631%:31B?'1&Q2r;%Q52QB9r9%43321(;%Q?3721%Q:2QG6%QE2L1p031p0<1p0H1p0Q21p0Q91p0Q=1p0QC1p0QJ1pS@QO1pTBR01pSDR21pT0R61").
Proof.
intros h a nZ Y HnZ HnAl HaAl HYal HYB HY Hsplit Hpl.
assert (HK : 0 <= kHighMemBeg) by (unfold kHighMemBeg; clear; lia).
destruct (null_hint_grant_above h a nZ kHighMemBeg Y HnZ HnAl HaAl HYal HYB HK HY Hsplit Hpl)
as [Hfl|Hlt]; clear HnAl HaAl HYal Hpl; [|lia].
rewrite bottomup_floor_val in Hfl. unfold kHighMemBeg. lia.
Qed.
End FPX_1.
