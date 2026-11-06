(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit
PmLayout PmModel PmModelFacts PmStatics PmStep.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmKeep () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Core.L5C."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmKeep.PMKP.Keep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayout."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStatics.PMST."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStep.PMK."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "0B"; "1bool"; "1fst"; "1list"; "1option"; "1pair"; "1prod"; "1snd"; "2and"; "2eq"; "2or"; "3Z"; "0L"; "0LB"; "0M"]; ["0M'"; "4hl_img_hi"; "4hl_img_lo"; "4hl_sptop"; "5agree_on"; "5kept"; "5stk"; "6img_clear"; "6outside"; "6range"; "7cstatic"; "8pa_atexit"; "8pa_canary"; "8pa_errcat_guard"; "8pa_loc_foot"; "8pa_locale_lock"]; ["8pa_need_locks"; "8pa_rw_lo"; "8pa_syscat_guard"; "9base_ok"; "9dep"; "9err_ok"; "9loc_ok"; "9ls_ok"; "9st"; "9sys_ok"; ":ek"; ";In"; "<add"; "<le"; "<lt"; "<pow"]; ["<sub"; "0W"; "0a"; "0b"; "0g"; "0hi"; "0i"; "0iv"; "0lo"; "0n"; "0scr"; "0segs"; "0sp"; "=Z_to_bv"; "=bv"]]).
Module PMKP.
Ltac outW := repeat (apply L5C.outside_cons; [unfold L5.in_rng; cbn [fst snd]; lia|]); apply L5C.outside_nil.
Section Keep.
Context {SCFG_P : ScfgP}.
Variable segs : list Segment.
Variable A : pm_addrs.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis KL : PMK.klayout segs L.
Definition cstatic (a : Z) : Prop := hl_img_lo L <= a < hl_img_hi L /\ ~ hl_alloc_static L a /\ ~ in_errno L a.
Lemma kept_cstatic : ltac2:(TCodec.tc2 tcn__PmKeep "L'4'7'<%2211%411&I%611&Jr1%211&Hr3r2%3221&Ev=r7r6r5r4%66543219p081p0=1pS6E1pS4B1pSFG1pSJH1pNG1").
Proof. intros LB sp scr W a.
intros (I & S & E) OW. pose proof (PMK.kl_img segs L KL) as KI. split; [lia|]. split; [right; right; split; assumption|]. split; assumption.
Qed.
Lemma kept_stack : ltac2:(TCodec.tc2 tcn__PmKeep "QE'4'7'<%2211%411'QNyR0%211'5y8%511%311p051&I%>11&F&Cv=%211r5r4r3%744321&Q=z%2215'9r6%5217&Q>&Q?+2+R0%3221%52=1%9271&H%12BA&Er:r8r7%46I321?Gp061p091p0D1p0H1pS6Q=1pS4Q21pSFQ?1pSJQ@1pQ0Q71pNQ@1").
Proof. intros LB M sp scr W a.
intros ST Hs Ha OW. pose proof (PMK.kl_img segs L KL) as KI. pose proof (PMK.kl_errno segs L KL) as KE.
apply (L5C.kept_stack_stk L LB M sp scr W a ST Hs Ha); [lia| exact OW].
Qed.
Lemma kept_block : ltac2:(TCodec.tc2 tcn__PmKeep "R9'4'7'<%2211%411&I%611&Q;(6r3r2%349921r7%63:21'9&Q=r4%2217&Q>&Q<%124;%32;1%8251zr5%:221r6%8213&Q@&Cv=%211+XPPP0%5221%C271';%A2H:&B%118%H231&A%11;%K21N%8241&Q?+2+Q?%3221%Q12A1&Hr:%221Q7&Er>r=r<r;r8%66L54321p081p0<1p0B1p0L1p0Q61p0Q:1p0QD1pS6R01pSDR11p4R21pS4QO1pSFR41pSJR51pNR41").
Proof. intros LB sp scr W B n a.
intros Hin Ha HB Hc Hh Hs OW. pose proof (PMK.kl_errno segs L KL) as KE.
apply (L5C.kept_block L LB sp scr W B n a Hin Ha HB); [lia| lia| exact OW].
Qed.
Lemma ek_agree : ltac2:(TCodec.tc2 tcn__PmKeep "QE'4'7'<%2211%411&I%611'QNyR0%211'5y8%511%311p051&Q:v=r8r7r6r5r4r3%877654321'9&Q=r1%2261&Q>&Q<%1298%3251%8251&Er;r:r9r2%56F432E1p071pS>Q61&D%14GFEDp031p0E1pSDQ;1pS6Q<1pQ2Q11pQ0Q21pS4Q;1pSFQ@1pSJQA1pNQ@1").
Proof. intros LB sp scr W M M' a n. intros E K i Hi. apply E. apply K. exact Hi. Qed.
Lemma ek_agree_stack : ltac2:(TCodec.tc2 tcn__PmKeep "R6'4'7'<%2211%411&I%611'QNyR0%211'5y8%511%311p051&Q:v=r8r7r6r5r4r3%877654321&F&C%11:%3417:9&Q=z%221=r:%421<&Q<%12?>&Q?+2+R0%3221%;251'9r1%>2I1&Q>%;2KJ%2241%6241&Hr<r2%3221p051pS>QB1&Dr9%24H1Q6Q5p041p0B1p0J1p0M1p0Q11p0Q61pSDQL1pS6QM1pQ2QB1pQ0QC1pS4QL1pSFR11pSJR21pNR11").
Proof. intros LB sp scr W M M' a n. intros E ST Hs Ha Hn OW. apply (ek_agree LB sp scr W M M' a n E). intros i Hi. apply (kept_stack LB M sp scr W i ST Hs); [lia| apply OW; exact Hi]. Qed.
Lemma ek_agree_static : ltac2:(TCodec.tc2 tcn__PmKeep "QE'4'7'<%2211%411&I%611'QNyR0%211'5y8%511%311p051&Q:v=r8r7r6r5r4r3%877654321'9&Q=r1%2261&Q>&Q<%1298%3251%8251&Jr2%211&H%12D3%>231p071pS>Q61&D%14GFEDp031p0E1pSDQ;1pS6Q<1pQ2Q11pQ0Q21pS4Q;1pSFQ@1pSJQA1pNQ@1").
Proof. intros LB sp scr W M M' a n. intros E C. apply (ek_agree LB sp scr W M M' a n E). intros i Hi. destruct (C i Hi). apply kept_cstatic; assumption. Qed.
Lemma clear_agree : ltac2:(TCodec.tc2 tcn__PmKeep "K'QNyR0%211'5y8%511%311p051'<&Dr4r3r2&Q@r1%2213%746541&Gr5%23187%332:9p021p061pS<?1pSB@1pQ2B1pQ0C1").
Proof. intros M M' lo hi. intros AG C i Hi. rewrite AG by lia. apply C. exact Hi. Qed.
Record sfoot : Prop := SFOOT {
sf_wf : PMST.addrs_wf A;
sf_ro : forall a, 65536 <= a < pa_rw_lo A -> cstatic a;
sf_foot : forall iv a, In iv (pm_foot A) -> fst iv <= a < snd iv -> cstatic a;
sf_canary : forall a, pa_canary A <= a < pa_canary A + 8 -> cstatic a;
sf_initc : forall iv a, In iv (pm_initc A) -> fst iv <= a < snd iv -> cstatic a
}.
Hypothesis SF : sfoot.
Section Along.
Variables (LB : list (Z * Z)) (sp scr : Z) (W : list L5.range) (M M' : word -> option byte).
Hypothesis E : PMK.ek L LB sp scr W M M'.
Lemma dep_agree : ltac2:(TCodec.tc2 tcn__PmKeep "Q:'<&Q4v0r1%3221&HvQAr2%3221p051pS6:1'9&Q=z%221;&Q>&Q?+2+R0%3221%52A1%:271%E2D?':'5'QNy8%211%411v@&QMyR0r3%3221%511v?%113%>3931p0@1p0B1pS6Q81p0O1").
Proof.
intros OW a Ha D. apply E. apply kept_cstatic; [|apply OW; exact D].
destruct D as [(iv & Hin & Hr)|[Hc|(iv & Hin & Hr)]]; [apply (sf_foot SF iv a Hin Hr)| apply (sf_canary SF a Hc)| apply (sf_initc SF iv a Hin Hr)].
Qed.
Lemma ls_ok_keep : ltac2:(TCodec.tc2 tcn__PmKeep "Q3'Q8'<&Q4v0r1%3221&HvQAr2%3221p051pS6:1'9&Q=+RPP0%221;&Q>&Q1%11?%32?1%8251p01<pS6E1&Q7vQKr3v?%443H21r4v@%746K21p041p0:1p0F1pS:Q21").
Proof. intros g.
intros OD OR H. apply (PMST.ls_ok_frame segs A (sf_wf SF) M M'); [exact (dep_agree OD)| |exact H].
intros a Ha Hn. rewrite E; [exact Hn|]. apply kept_cstatic; [apply (sf_ro SF); exact Ha| apply OR; exact Ha].
Qed.
Lemma base_ok_keep : ltac2:(TCodec.tc2 tcn__PmKeep "QI'<'9&Q=+RPP0r1%3221&Q>&Q1v0%211%4261%:261&HvQAr2%3221p051pS6A1&L%11;%B21@&Q<+8%2241%B2D1%H251p01;pS6K1&Q0%11E%L21J+1%;231%K2M1%Q1241p01DpS6Q41&O%11N%Q521Q3+4%D231%Q42Q61%Q:241p01MpS6Q=1&Q3vQKv?%332Q91v@%534Q;1p031p081p0B1p0L1p0Q71").
Proof.
intros O1 O2 O3 O4 (RO0 & (can & Hcan & CAN) & NL & LL).
pose proof (PMST.aw_canary A (sf_wf SF)) as Hc. pose proof (PMST.aw_nl A (sf_wf SF)) as Hn. pose proof (PMST.aw_ll A (sf_wf SF)) as Hl. pose proof (PMST.aw_rw A (sf_wf SF)) as Hr.
split; [|split; [|split]].
- apply (clear_agree M M' 65536 (pa_rw_lo A)); [|exact RO0]. apply (ek_agree_static LB sp scr W M M' _ _ E). intros i Hi. split; [apply (sf_ro SF); lia| apply O1; lia].
- exists can. split; [exact Hcan|]. apply (L5C.u64_at_agree segs M M'); [|lia|lia|exact CAN].
apply (ek_agree_static LB sp scr W M M' _ _ E). intros i Hi. split; [apply (sf_canary SF); lia| apply O2; lia].
- apply (clear_agree M M' _ _); [|exact NL]. apply (ek_agree_static LB sp scr W M M' _ _ E). intros i Hi. split; [|apply O3; lia].
apply (sf_initc SF (pa_need_locks A, pa_need_locks A + 1)); [cbn; auto|cbn; lia].
- apply (clear_agree M M' _ _); [|exact LL]. apply (ek_agree_static LB sp scr W M M' _ _ E). intros i Hi. split; [|apply O4; lia].
apply (sf_initc SF (pa_locale_lock A, pa_locale_lock A + 4)); [cbn; auto|cbn; lia].
Qed.
Lemma agree_st : ltac2:(TCodec.tc2 tcn__PmKeep "K'<'9&Q=r3r1%3221&Q>&Q<r2%2261%4261%:261&J%115&HvQA%2218%@241p071pS>C1&Dv?v@%3421D?p051pSDI1pS6J1").
Proof. intros a n. apply (ek_agree_static LB sp scr W M M' a n E). Qed.
Lemma loc_ok_keep : ltac2:(TCodec.tc2 tcn__PmKeep "Q5'2'7'<%2211&Q;r2&Nv0%211%53641'9&Q=&3r3%23<<1%421:&Q>&8%13@@5%32>1%:251&HvQA%221:p041p0@1pS6H1pS@H1&Q6vQKv?%342H1Jv@%544J1Dp031p081pS8Q41").
Proof. intros b.
intros OW H. pose proof (PMST.aw_gloc A (sf_wf SF)) as Hg. unfold PMST.loc_ok in *. destruct b.
- destruct H as (G & P). destruct (PMST.aw_gloc_in A (sf_wf SF)) as (iv & Hin & Hlo & Hhi).
assert (CS : forall i, pa_glocale A + 32 <= i < pa_glocale A + 41 -> cstatic i /\ L5.outside W i).
{ intros i Hi. split; [apply (sf_foot SF iv); [|lia]| apply (OW iv); [exact Hin| lia]].
unfold pm_foot. cbn [app]. right. right. apply in_or_app. left. exact Hin. }
split.
+ apply (L5C.u8_at_agree segs M M'); [|lia|lia|exact G]. apply agree_st. intros i Hi. apply CS. lia.
+ apply (L5C.u64_at_agree segs M M'); [|lia|lia|exact P]. apply agree_st. intros i Hi. apply CS. lia.
- intros iv Hin. apply (clear_agree M M' (fst iv) (snd iv)); [|apply H; exact Hin]. apply agree_st. intros i Hi.
split; [apply (sf_foot SF iv); [|lia]| apply (OW iv); [exact Hin| lia]].
unfold pm_foot. cbn [app]. right. right. apply in_or_app. left. exact Hin.
Qed.
Lemma sys_ok_keep : ltac2:(TCodec.tc2 tcn__PmKeep "O'2'<'9&Q=&Q2v0%211r1%5221&Q>&Q<+2%2261%4261%<261&HvQAr2%3221p051pS6C1&Q9vQKv?%342C17v@r3%645F21p041p091pS8N1").
Proof. intros b.
intros OW H. pose proof (PMST.aw_sysg A (sf_wf SF)) as Hg. unfold PMST.sys_ok in *.
assert (CS : forall i, pa_syscat_guard A <= i < pa_syscat_guard A + 2 -> cstatic i /\ L5.outside W i).
{ intros i Hi. split; [|apply OW; exact Hi]. apply (sf_foot SF (pa_syscat_guard A, pa_syscat_guard A + 2)); [|cbn; lia]. unfold pm_foot. cbn. auto. }
destruct b.
- apply (L5C.u8_at_agree segs M M'); [|lia|lia|exact H]. apply agree_st. intros i Hi. apply CS. lia.
- apply (clear_agree M M' _ _); [|exact H]. apply agree_st. intros i Hi. apply CS. lia.
Qed.
Lemma err_ok_keep : ltac2:(TCodec.tc2 tcn__PmKeep "Q:'2'<'9&Q=&Mv0%211r1%5221&Q>&Q<+2%2261%4261%<261&HvQAr2%3221p051pS6C1&K%11A%D21@+a0%?231%A2C1%I241p01:pS6L1&Q5vQKv?r3%443M21v@r4%746Q021p041p0:1p0D1pS8Q91").
Proof. intros b.
intros OG OA (G & AT). pose proof (PMST.aw_errg A (sf_wf SF)) as Hg. pose proof (PMST.aw_atexit A (sf_wf SF)) as Ha.
assert (CG : forall i, pa_errcat_guard A <= i < pa_errcat_guard A + 2 -> cstatic i /\ L5.outside W i).
{ intros i Hi. split; [|apply OG; exact Hi]. apply (sf_foot SF (pa_errcat_guard A, pa_errcat_guard A + 2)); [|cbn; lia]. unfold pm_foot. cbn. auto. }
assert (CA : forall i, pa_atexit A <= i < pa_atexit A + 544 -> cstatic i /\ L5.outside W i).
{ intros i Hi. split; [|apply OA; exact Hi]. apply (sf_foot SF (pa_atexit A, pa_atexit A + 544)); [|cbn; lia].
unfold pm_foot. cbn [app]. right. right. apply in_or_app. right. cbn. auto. }
split.
- destruct b.
+ apply (L5C.u8_at_agree segs M M'); [|lia|lia|exact G]. apply agree_st. intros i Hi. apply CG. lia.
+ apply (clear_agree M M' _ _); [|exact G]. apply agree_st. intros i Hi. apply CG. lia.
- apply (PMST.atexit_agree segs A (sf_wf SF) M M'); [|exact AT]. intros i Hi. apply (agree_st (pa_atexit A) 544); [exact CA| lia].
Qed.
End Along.
End Keep.
End PMKP.
