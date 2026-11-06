(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit
PmLayout PmModel PmModelFacts PmStatics PmSpecs PmStep PmKeep.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmFrame () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Core.L5C."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmFrame.PMFR.Kit."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecs.PMSP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStep.PMK."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "0B"; "1cons"; "1fst"; "1list"; "1nil"; "1option"; "1pair"; "1prod"; "1snd"; "2and"; "2eq"; "2not"; "3Z"; "0HI"; "0HIok"]; ["0L"; "0LB"; "0LB1"; "0LB2"; "0LBc"; "0LBf"; "4Model"; "4VmMaps"; "0M"; "0M'"; "0M1"; "0P"; "5credit"; "5heap_iface_ok"; "5hi_heap"; "5hl_sptop"]; ["5model_but_vm"; "6agree_on"; "6stk"; "8defined"; "8outside"; "8range"; "8u32_at"; "8u64_at"; "8u8_at"; "7SCFG"; "9brange"; ":CHUNK"; ":iosb_at"; ":iss_at"; ":nullis_at"; ":parser_at"]; [":parser_own"; ":pst"; ":sr_qc"; ":src_fields_at"; ":srcst"; ":strm"; ":vs_own"; ":vstr"; ":vstr_at"; ";T3"; ";T4"; ";ec_at"; ";model_ok"; ";visitor_at"; "<ek"; "<inW"]; ["0SCFG_P"; "=In"; "=incl"; ">add"; ">le"; ">lt"; ">pow"; ">sub"; "0VM"; "0W"; "0W'"; "0a"; "0b"; "0c"; "0cr"; "0i"]; ["0isp"; "0m"; "0model"; "0model'"; "0n"; "0o"; "0ois"; "0op"; "0os"; "0rdb"; "0s"; "0sbp"; "0scr"; "0segs"; "0sm"; "0sp"]; ["0sp'"; "0src"; "0st"; "?Z_to_bv"; "?bv"; "0str"; "0v"; "0vp"; "0vp'"; "0x"]]).
Module PMFR.
Lemma outside_of_not_inW : ltac2:(TCodec.tc2 tcn__PmFrame "@'4&Q5%211'=&<&QOr2r1%3221%511&Q4r3%2216p041pTH;1pTD=1").
Proof. intros W a. intros N r Hin Hr. apply N. exists r. split; assumption. Qed.
Lemma inW_nil : ltac2:(TCodec.tc2 tcn__PmFrame ":'=&<&QO(5&Q5%211r1%5221%711pTH91").
Proof. intros a. intros (r & [] & _). Qed.
Lemma inW_inv1 : ltac2:(TCodec.tc2 tcn__PmFrame "K'=&QO(2'8%1244(7r3r2%348821(5%116%93731r1%<221':&R4r4%221:&R5&R3%124>%32>1%8251p0:1pTHH1pU:I1pTJJ1").
Proof. intros b n a. intros (r & [<-|[]] & Hr). exact Hr. Qed.
Section Kit.
Context {SCFG_P : ScfgP}.
Variable segs : list Segment.
Variable A : pm_addrs.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis KL : PMK.klayout segs L.
Abbreviation T3 := PMSP.T3.
Abbreviation T4 := PMSP.T4.
Definition brange (LBc : list (Z * Z)) : Prop :=
forall B m, In (B, m) LBc -> 4096 <= B /\ (B + m <= hl_img_lo L \/ hl_img_hi L <= B) /\ B + m <= hl_ceil L.
Lemma brange_of_heap : ltac2:(TCodec.tc2 tcn__PmFrame "Q9'Mv@&Q9vR0%211v>%63521'4'8'=%2211%411&L'S4yR0%211'6y8%511%311p051'G&Nr5r3r2r1%55F4321&R2r6%23D71&Q:%113p031p071pTB>1pQB@1pTNI1pQ:K1pQ<L1pQ0Q21").
Proof. intros HIok LBf LBc cr M VM.
intros HH INC B m Hin. pose proof (proj1 (hio_wf L SCFG HI HIok LBf cr M VM HH) (B, m) (INC _ Hin)) as ((Q0 & Q1 & Q2 & Q3 & Q4) & _).
cbn [fst snd] in *. split; [exact Q0|]. split; [exact Q1| exact Q4].
Qed.
Lemma brange_incl : ltac2:(TCodec.tc2 tcn__PmFrame "B'4'8'=%2211%411&Q:r1%211&R2r3r2%33821r4%811p031p081pQ8<1pQ6=1").
Proof. intros LB1 LB2. intros BR INC B m Hin. apply BR. apply INC. exact Hin. Qed.
Section Along.
Variables (LBc : list (Z * Z)) (sp' scr' : Z) (W' : list L5.range) (M M' : word -> option byte).
Hypothesis E : PMK.ek L LBc sp' scr' W' M M'.
Hypothesis STKc : L5C.stk (hl_sptop L) M sp' scr'.
Hypothesis SCR0 : 0 <= scr'.
Hypothesis BR : brange LBc.
Hypothesis WHI : forall a, PMK.inW W' a -> sp' <= a \/ hl_img_lo L <= a < hl_img_hi L.
Lemma ag_hi : ltac2:(TCodec.tc2 tcn__PmFrame "Q6'=&R4vS0r2%3221&R3r3%2214&R6+2+R0%3221%;251':r5r1%?221&R5r4%>251%3251%8251&<&QOvR:%221F%411p061pU0L1&Q1vHvI%3421B>p051p0F1p0O1pU:Q41pTHQ51").
Proof. intros a n.
intros H1 H2 N. apply (PMKP.ek_agree_stack segs L KL LBc sp' scr' W' M M' a n E STKc SCR0 H1 H2). intros i Hi. apply outside_of_not_inW. apply N. exact Hi.
Qed.
Lemma ag_block : ltac2:(TCodec.tc2 tcn__PmFrame "B'=&R1'8%1233(7r2r1%347721vD%83621&Q1vHvIr3%443219p061pU4@1p4A1").
Proof. intros B m.
intros Hin. destruct (BR B m Hin) as (Q0 & Q1 & Q4).
pose proof STKc as (_ & SLO & SHI & STOP & _).
apply (PMKP.ek_agree L LBc sp' scr' W' M M' B m E). intros i Hi.
apply (PMKP.kept_block segs L KL LBc sp' scr' W' B m i Hin Hi); [lia| exact Q4| exact Q1| lia|].
apply outside_of_not_inW. intros I. destruct (WHI i I) as [X|X]; lia.
Qed.
Lemma u64_keep : ltac2:(TCodec.tc2 tcn__PmFrame "Q;'=&R4vS0r2%3221&R3r3+8%3221&R6+2+R0%3221%<251':r5r1%@221&R5%>24<%2241%7241&<&QOvR:%221F%411p061pU0L1&Q7vRMvHr4%4432B1vIr6%74621Ep041p0:1p0J1p0Q41pV>Q91pTHQ:1").
Proof. intros a v. intros H1 H2 N. pose proof STKc as (_ & SLO & _ & STOP & _). apply (L5C.u64_at_agree segs M M'); [apply ag_hi; assumption|lia|lia]. Qed.
Lemma u32_keep : ltac2:(TCodec.tc2 tcn__PmFrame "Q;'=&R4vS0r2%3221&R3r3+4%3221&R6+2+R0%3221%<251':r5r1%@221&R5%>24<%2241%7241&<&QOvR:%221F%411p061pU0L1&Q6vRMvHr4%4432B1vIr6%74621Ep041p0:1p0J1p0Q41pV>Q91pTHQ:1").
Proof. intros a v. intros H1 H2 N. pose proof STKc as (_ & SLO & _ & STOP & _). apply (PMF.u32_at_agree segs M M'); [apply ag_hi; assumption|lia|lia]. Qed.
Lemma u8_keep : ltac2:(TCodec.tc2 tcn__PmFrame "Q;'=&R4vS0r2%3221&R3r3+1%3221&R6+2+R0%3221%<251':r5r1%@221&R5%>24<%2241%7241&<&QOvR:%221F%411p061pU0L1&Q8vRMvHr4%4432B1vIr6%74621Ep041p0:1p0J1p0Q41pV>Q91pTHQ:1").
Proof. intros a v. intros H1 H2 N. pose proof STKc as (_ & SLO & _ & STOP & _). apply (L5C.u8_at_agree segs M M'); [apply ag_hi; assumption|lia|lia]. Qed.
Lemma defined_keep : ltac2:(TCodec.tc2 tcn__PmFrame "Q9'=&R4vS0r2%3221&R3r3%2214&R6+2+R0%3221%;251':r5r1%?221&R5r4%>251%3251%8251&<&QOvR:%221F%411p061pU0L1&Q3vH%231A=vIr6%5321Dp041p081p0I1p0Q21pU:Q71pTHQ81").
Proof. intros a n. intros H1 H2 N. apply (L5C.defined_agree M M' a n). apply ag_hi; assumption. Qed.
Lemma vstr_keep : ltac2:(TCodec.tc2 tcn__PmFrame "QF'='QG&R4vS0r2%3221&R3r3+H%3221&R6+2+R0%3221%<251':r5r1%@221&R5%>24<%2241%7241&<&QOvR:%221F%411p061pU0M1&R2'8%12Q0Q0&QFr4%211vD%73521&QHvRM&QIvHr6%554321KvIr7%8576214p041p0;1p0D1p0Q41p0Q>1pUFQC1pU<QE1").
Proof. intros o s.
intros H1 H2 N INC VS. pose proof STKc as (_ & SLO & _ & STOP & _).
apply (PMF.vstr_at_agree segs M M' o s); [lia|lia| apply ag_hi; assumption| |exact VS].
intros c n p ->. apply ag_block. apply INC. cbn. auto.
Qed.
Lemma iss_keep : ltac2:(TCodec.tc2 tcn__PmFrame "QJ'='QG'QE&R4vS0r3%3221&R3r4+X@%3221&R6+2+R0%3221%<251':r6r1%@221&R5%>24<%2241%7241&<&QOvR:r2%3221%511p071pU0O1&R2'8%12Q2Q2&QFr5%211vD%73521&Q=vRMv0&QIvHr7%6754321M:vIr8%97876214Q0p041p0<1p0E1p0Q61p0Q@1pUNQE1pV<QG1pU>QI1").
Proof. intros ois str sm.
intros H1 H2 N INC VS. pose proof STKc as (_ & SLO & _ & STOP & _).
apply (PMF.iss_at_agree segs A M M' ois str sm); [lia|lia| apply ag_hi; assumption| |exact VS].
intros c n p ->. apply ag_block. apply INC. cbn. auto.
Qed.
Lemma parser_keep : ltac2:(TCodec.tc2 tcn__PmFrame "QJ'='QA&R4vS0r3%3221&R3r4+\0%3221&R6+2+R0%3221%<251':r6r1%@221&R5%>24<%2241%7241&<&QOvR:r2%3221%511p071pU0N1&R2'8%12Q1Q1&Q@%11LvD%63421&Q?vRMv0&QI&QJvHr7r5%88765432N1vIr8%;8:987215Q1p041p0>1p0F1p0Q71p0QA1pUFQF1pU>QH1pU@QI1").
Proof. intros op ois s.
intros H1 H2 N INC PA. pose proof STKc as (_ & SLO & SHI & STOP & _).
assert (Bq : In (PM.sr_qc (PM.p_src s), PM.CHUNK) LBc) by (apply INC; unfold PM.parser_own, PM.src_own; cbn; auto).
assert (Bv : In (PM.p_b s, 32 * 2 ^ PM.p_k s) LBc) by (apply INC; unfold PM.parser_own, PM.src_own, PM.vec_own; cbn; auto).
destruct (BR _ _ Bq) as (Q0 & Q1 & Q4). destruct (BR _ _ Bv) as (V0 & V1 & V4).
apply (PMF.parser_at_agree segs A M M' op ois s); [lia|lia| apply ag_hi; assumption|lia|lia| apply ag_block; exact Bq|lia|lia| apply ag_block; exact Bv| |exact PA].
intros c n p Et. apply ag_block. apply INC. unfold PM.parser_own. apply in_or_app. right. apply in_or_app. right. rewrite Et. cbn. auto.
Qed.
Lemma nullis_keep : ltac2:(TCodec.tc2 tcn__PmFrame "Q:'=&R4vS0r1%3221&R3r2+W8%3221&R6+2+R0%3221%<251':r4%?21=&R5%=23;%22@1%6241&<&QOvR:%221B%411p061pU0K1&Q>vRMv0&QIvH%554321BvIr5%8576521p041p0;1p0J1p0Q41pU<Q91").
Proof. intros o. intros H1 H2 N. pose proof STKc as (_ & SLO & _ & STOP & _). apply (PMF.nullis_at_agree segs A M M' o); [lia|lia| apply ag_hi; assumption]. Qed.
Lemma src_keep : ltac2:(TCodec.tc2 tcn__PmFrame "QN'='QD&R4vS0r4%3221&R3r5+Y8%3221&R6+2+R0%3221%<251':r7+W@%<221r1%B221&R5%@26>%2241%9241&<&QOvR:r2%3221%511p071pU0Q01&R1'8%12Q3Q3(7&QB%11Q2&Q;%44Q8Q821vD%93721&QCvRM&QIvHr8r6%675432Q11Q:vIr9%9787215Q44p041p0<1p0G1p0Q:1p0QD1pV4QI1pUHQK1pU2QL1pUBQM1").
Proof. intros os isp sbp src.
intros H1 H2 N Bq. pose proof STKc as (_ & SLO & SHI & STOP & _). destruct (BR _ _ Bq) as (Q0 & Q1 & Q4).
apply (PMF.src_fields_at_agree segs M M' os isp sbp src); [lia|lia|lia|lia| apply ag_hi; [lia|lia|intros i Hi; apply N; lia]| apply ag_block; exact Bq].
Qed.
Lemma ec_keep : ltac2:(TCodec.tc2 tcn__PmFrame "Q='=&R4vS0r3%3221&R3r4+@%3221&R6+2+R0%3221%<251':r6r1%@221&R5%>24<%2241%7241&<&QOvR:r2%3221%511p071pU0M1&QKvRMvHr5%4532C1LvIr7%75621F4p041p0:1p0K1p0Q51pTLQ:1pV>Q;1pU<Q<1").
Proof. intros o v c.
intros H1 H2 N (E0 & E8 & ED). split; [|split].
- apply u32_keep; [lia|lia| intros i Hi; apply N; lia| exact E0].
- apply u64_keep; [lia|lia| intros i Hi; apply N; lia| exact E8].
- apply defined_keep; [lia|lia| exact N| exact ED].
Qed.
Lemma visitor_keep : ltac2:(TCodec.tc2 tcn__PmFrame "Q9'=&R4vS0r1%3221&R3r2+8%3221&R6+2+R0%3221%<251':r4%?21=&R5%=23;%22@1%6241&<&QOvR:%221B%411p061pU0K1&QMvRMv0vH%44321AvIr5%746521p041p0:1p0I1p0Q31pU<Q81").
Proof. intros o. unfold PMSP.visitor_at. apply u64_keep. Qed.
End Along.
Lemma ek_of_piece : ltac2:(TCodec.tc2 tcn__PmFrame "RI'4'8'=%2211%411'S4yR0%211'6y8%511%311pVD51!p0<1':&R4zr1%3221&R5&R6+2+R0%3221%5271%;271&<r3r2%211%411';r5&S3%12M7%311r6%113%73L31p091p0?1pTHQ81&Q2&Ov@%211r4%5421;?&R1r9%23Q@Q11&R3&3%13QDQDI&9%13QFQFK%5231&R7+XPPP0%22>1%Q=241p0;1pTJQL1%O1Q>r:%821@%QC21Q6%Q@2Q73%QF221p061pTHR51&QNr8(5&Q5%211r7%67Q1=L521Q9p081p0A1p0Q11p0Q81pQHR51pQFR81pQBR91pUJRD1pV0RE1pQ4RD1").
Proof. intros LB sp scr M M1 P. intros FRZ STK LBhi PF. apply (PMK.ek_piece_in segs L KL LB sp scr [] M M1 P FRZ STK LBhi). intros a Pa. left. apply PF. exact Pa. Qed.
Lemma brange_hi : ltac2:(TCodec.tc2 tcn__PmFrame "N'4'8'=%2211%411&Q:r1%211&R1r3%23741&R4&R3&3r2%23==1&9%13??3%6231&R7&Ov@%211+XPPP0%5221%>271p0@1pTJH1p0E1pQ4I1").
Proof. intros LB. intros BR (B & m) Hin. destruct (BR B m Hin) as (_ & _ & Q). exact Q. Qed.
Lemma iosb_revptr : ltac2:(TCodec.tc2 tcn__PmFrame "QH'S4yR0%211'6y8%511%311p051'=&R4zr5%3221&R3r6+TH%3221&R6+2+R0%3221%<251&Q1r9r8r7+8%>221+T@%746521&Q7vRM%24198B&Q3r:%231<D&Q<v0&QIr<%4893216A?Jr;%68;5431CBAp031p091p0=1p0A1p0J1p0Q41pV6Q91pUDQ:1pVBQ;1pV@Q<1pU<Q=1pQDQ?1pQBQ@1").
Proof. intros M M' o vp vp' rdb st.
intros Ho Ho' AG V D' (H0 & H32 & H36 & H40 & H48 & Z & D & _ & ST).
assert (S : forall a' n', o + 8 <= a' -> a' + n' <= o + 152 -> L5C.agree_on M M' a' n') by (intros a' n' X Y; apply (L5C.agree_on_sub M M' (o + 8) 144 a' n' AG); lia).
split; [exact V|].
split; [apply (PMF.u32_at_agree segs M M'); [apply S; lia|lia|lia|exact H32]|].
split; [apply (PMF.u32_at_agree segs M M'); [apply S; lia|lia|lia|exact H36]|].
split; [apply (L5C.u64_at_agree segs M M'); [apply S; lia|lia|lia|exact H40]|].
split; [apply (L5C.u64_at_agree segs M M'); [apply S; lia|lia|lia|exact H48]|].
split; [apply (PMF.zeros_at_agree M M'); [apply S; lia|exact Z]|].
split; [exact D'|]. split; [exact I| exact ST].
Qed.
Lemma model_ok_but_vm : ltac2:(TCodec.tc2 tcn__PmFrame "<'F&QLr2%211&Q0r3%2214%612p021p061pU8:1pU6;1").
Proof. intros model model'.
intros (H1 & H2 & H3) MB. unfold PMSP.model_ok. rewrite (L5C.halted_but_vm _ _ MB), (L5C.lazy_but_vm _ _ MB), (L5C.materialized_but_vm _ _ MB). auto.
Qed.
End Kit.
End PMFR.
