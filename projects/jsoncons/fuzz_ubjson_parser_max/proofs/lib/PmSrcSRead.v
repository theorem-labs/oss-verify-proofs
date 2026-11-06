(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit PmLayout PmLayoutS PmModel PmModelFacts PmStatics PmSpecs PmSpecsS PmStep PmKeep PmKitS PmFrame PmParSpecs PmParSpecsS PmParKit PmSrcSMemmove PmSrcSReadP.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmSrcSRead () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Core.L5C."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5CoreKit.L5K."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmFrame.PMFR."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmParSpecsS.PMPSS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecs.PMSP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStep.PMK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.bitvector.definitions."], [["1None"; "1cons"; "1fst"; "1list"; "1nat"; "1nil"; "1option"; "1prod"; "2and"; "2eq"; "2not"; "2or"; "3map"; "4Z"; "0HI"; "0K"]; ["0L"; "0LB"; "5Model"; "5m_halted"; "5m_vm_lazy"; "5m_vmmaps"; "6bvmap"; "0M"; "0M1"; "0M3"; "0R"; "0R1"; "0R3"; "7msteps"; "8credit"; "8hi_heap"]; ["8hl_sptop"; "9stk"; ":CS"; "<defined"; "<ra_ok"; "<range"; ";SCFG"; "=brange"; ">fill_buffer_spec"; ">src_read_spec"; ">xsgetn_spec"; "?cfg"; "@cwr"; "@ek"; "@inW"; "AFPState"]; ["Agetr"; "Amkst"; "Aseg_rom"; "BTSet"; "Csrealizes"; "Dmem_grows"; "Eloaded_segments"; "0SCFG_P"; "FIn"; "Gadd"; "Gle"; "Glt"; "Gof_nat"; "Gpow"; "Gsub"; "0W"]; ["0a"; "0b"; "0c"; "0cr"; "0dst"; "0fb"; "0fx"; "0fx1"; "0i"; "0l"; "0m"; "0model"; "0n"; "0n1"; "0n2"; "0pc"]; ["0pc1"; "0ra"; "0sp"; "0src"; "HNoDup"; "IZ_to_bv"; "Ibv"; "0x"; "0y"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc. Local Ltac lia := L5FastLia.plia.
Module PMSRD.
Import PMS.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKS.klayout_S L LY.
Let SF := PMKS.sfoot_S L LY.
Lemma rd_cpy : ltac2:(TCodec.tc2 tcn__PmSrcSRead "VI'3'7'=%2211%411&N'Q?&Fy5'RFyR0%211%5241'6y8%611%311p061'B&QC&Ov>r;r:r7&Er6%211%8576541'9%A1C&C%118(0%11G%63531%Q32II%Q511&Dr8%211(5%116%>3631&QJ+SoonPPPPP0&Q0v@%211%5241&Q@r<&RE&QLu:%211%42Q@1%7261%62Q@C%N3Q@21r=u;%911%;2QG1%>241%Q43QF17r>u<%?11%A2QM1%D241%Q:3QL1=r?u1%E11%G2R31%J241%Q@3R21C&Q4r9%211+1%Q621QLz%Q821B&QK&QI%12?K&QM+2+QO%3221%7251%QA2:Er@%921G%;215';rB%=215rA%QI221%@228%QK215%7231&Q3rFrC%33218rG%5313<'8r1%R5271rD%M291%O241%6241&Q<rNr2%33R:21p051pT2SI1&QErK%221>%RC2Q<?+R0%Q92Q81%Q=2B1%D241&:%RI28=rI%QA2:1%QC2@1%J241%611r5r3%RI2T31%311rO%113%SD3T131p081p0@1pT2TB1rJrH%Q>3;21'4&QH&Q2%233Q;1%S71Q4%S92TE1%S<2T61rQ1%S>213%T43TF31p071pTB;1rQ3rQ2%T=1Q?%TC5TB32L1'QD&QF&Q6vQG%211&Q;%1659TFITDO%74631QHp091p0>1p0K1p0O1p0QF1pQDU41pQJU:1rL+eT[0%<6@2QL1Q4QC%B4A>1Q4p051p0R11p0R?1p0RB1p0RG1p0S01p0S41p0S61p0S?1p0SB1p0SE1p0SI1p0T01p0T71p0T>1p0TI1p0U01p0U91p0UA1pU4V<1pTJV=1pU8V>1pT:V?1pQ0UO1pTHV11pQ@V31pQFV91pT>V@1pT8VB1pQ4VD1").
Proof. intros LB cr fx R M model K dst src n ra.
intros HH Mh Ml TOP H10 H11 H12 H1 RA Hn Hd Hdn Hs Hsn AP DD DS CW KONT.
destruct (PMCPS.memcpy_run fx R M dst src n ra H10 H11 H12 H1 RA Hn Hd Hdn Hs Hsn AP
ltac:(apply (L5C.writable_of_defined RSEGS); [exact DD| lia| lia]) DS) as (R3 & M3 & MS & MG & FRZ & D3 & KS & _).
apply (PMK.spiece RSEGS L HI KL HIok LB cr M model fx fx R 0xa9160 R3 ra M3 (fun a => dst <= a < dst + n) K HH Mh Ml TOP MS MG FRZ CW
(fun a => PMK.rng_dec a dst (dst + n))).
intros HH3. apply KONT; assumption.
Qed.
Lemma nodup3 : ltac2:(TCodec.tc2 tcn__PmSrcSRead "Q7'7'=%2211'3%112'RD&<&2%1277(1r4r3r2r1%53<21%63=41%73>61%;4?@91%=2A1'8&:'9r5%@3FF1%A3GG>%43H21%611%D3JJ@%73K51%911%93M63%;11%=231%>271p0@1pTDO1pT6Q21pT4Q31pT2Q41").
Proof. intros a b c l.
intros ND. cbn [map] in ND. inversion ND as [|x l1 NI1 ND1]. subst. inversion ND1 as [|y l2 NI2 ND2]. subst.
split; [|split]; intros E.
- apply NI1. rewrite E. constructor.
- apply NI1. rewrite E. constructor. constructor.
- apply NI2. rewrite E. constructor.
Qed.
Lemma apart_pt : ltac2:(TCodec.tc2 tcn__PmSrcSRead "Q7'=&QJ+1r3%3221r2%5241'8r7r1%9221&QK&QIr6%2261%4261%9261&:%A25=r5%8271%:2@1%?241%611p081pT2I1';%J2=8r4%A2:1%M21F%5241p071p0K1p0N1pTFQ31pUBQ41pTJQ51pU@Q61").
Proof. intros x n y m.
intros Hn Hm H. destruct (Z_lt_le_dec x y) as [L1|L1].
- left. destruct (Z_le_gt_dec (x + n) y) as [X|X]; [exact X|]. exfalso. apply (H y); lia.
- right. destruct (Z_le_gt_dec (y + m) x) as [X|X]; [exact X|]. exfalso. apply (H x); lia.
Qed.
Lemma defined_app : ltac2:(TCodec.tc2 tcn__PmSrcSRead "O'RFyR0%211'6y8%511%311p051'=&QJzr2%3221&Q3r5r4r3%43321r6&QI%1265%83315r7%:3153p031p081p0>1pTNC1pTLD1pT2E1pQ@G1").
Proof. intros M a n1 n2.
intros H0 D1 D2 i Hi. destruct (Z_lt_le_dec i n1) as [X|X]; [apply D1; lia|].
replace (a + i) with (a + n1 + (i - n1)) by lia. apply D2. lia.
Qed.
Lemma rd_step : ltac2:(TCodec.tc2 tcn__PmSrcSRead "U2'3'7'=%2211%411&N'Q?&Fy5'RFyR0%211%5241'6y8%611%311p061'B&QC&Ov>r>r=r6&Er4%211%8576541'9%A1C&Cr5%211(0%11H%73631%Q42JJ%Q611&D%11@(5%115%>3531&QJ+SoonPPPPP0&Q0v@%211%5241&QN+XPPP0%2241+Q@%42N1%;231r7%=21Q1&QI+[8%2241%A21='M&QF&QArCrA&REr?%22QK1&QB%118%85763QA1rBr@%82R1QEr<%=543216%@3?61&QE%12QJQI'8zr1%Q8221&QK&QM+2+R0%3221%5271%:271&:%Q;2R6Q8r2%QC221%Q623Q;%<231%A231%711+Q8%Q;2R>1+H%Q=221+X0%Q?221r3%QO221%QB238%H231%M231%C11%Q=2S6RF%Q811%QA12%RF3S321p051p0B1p0K1pTBSE1rHrG%S11S4%S75S632QG1'QD&Q6vQG%211&Q;rFrD%36R421QJQIQO%84R551S>p0:1rE%76R8>1R6R5R3%<4R991SBp041p0C1p0QK1p0QN1p0R@1p0RE1p0RH1p0RO1p0S61p0S>1p0SG1pT<TB1pU6TC1pQ0T31pTHT51pQBT71pQ@T81pU2TH1pU0TI1pQHT@1pQFTA1pT@TH1pT>TI1pT8TK1pQ4TM1").
Proof. intros LB cr fx fx1 R R1 pc pc1 M M1 model K sp fb.
intros HH Mh Ml TOP H1 H1' H2 MS MG FRZ KONT.
apply (PMK.spiece RSEGS L HI KL HIok LB cr M model fx fx1 R pc R1 pc1 M1
(fun a => (sp - 48 <= a < sp - 48 + 48) \/ (fb + 40 + 24 + 256 <= a < fb + 40 + 24 + 256 + 40)) K HH Mh Ml TOP MS MG).
- intros a Ha N. apply FRZ; [exact Ha| |]; intros X; apply N; [left|right]; exact X.
- intros a Pa. unfold PMK.cwr. left. lia.
- intros a. apply PMK.or_dec; apply PMK.rng_dec.
- exact KONT.
Qed.
Lemma rd_ek : ltac2:(TCodec.tc2 tcn__PmSrcSRead "S2'3'7'=%2211%411&Q5%611'RFyR0%211'6y8%511%311pU@51'8&QJzr1%3221&QK&QM+2+R0%3221%5271%;271&:&QNr7+Q@%3221r2%A221&QI%1245%@241%F241%;11+Q8%62;1+H%8221+X0%:221r3%N221%=238%L231%Q2231%G11'9r5&REr4%22Q?1%411r6%113%83Q>31p0:1p0G1p0Q41pTBQM1&Q1&Q0v@%211+dP0%542H<1&Q7r8%2261+Z0%Q8231%QK21QI+[8%Q;261%QJ2QL1%R0241&Q>%12:QAp031pT2RA1&Q=r:r9%37E21CQJNQ3p051p0A1p0E1p0L1pQBR>1pQ@R?1pT0RH1pT<RM1pU6RN1pQ4RM1").
Proof. intros LB sp fb W M M1.
intros FRZ STK BR INF.
apply (PMK.ek_piece_in RSEGS L KL LB sp 20480 W M M1
(fun a => (sp - 48 <= a < sp - 48 + 48) \/ (fb + 40 + 24 + 256 <= a < fb + 40 + 24 + 256 + 40)) ltac:(intros a Ha N; apply FRZ; [exact Ha| |]; intros X; apply N; [left|right]; exact X)
STK (PMFR.brange_hi L LB BR)).
intros a [Pa|Pa]; [left; lia| right; apply INF; lia].
Qed.
Lemma rd_ek_cpy : ltac2:(TCodec.tc2 tcn__PmSrcSRead "RB'3'7'=%2211%411&Q5%611'RFyR0%211'6y8%511%311pU@51'8&QJzr1%3221&QK&QM+2+R0%3221%5271%;271&:r7r2%>221&QIr6%2251%>251%D251%911'9r4&REr3%22Q11%411r5%113%83Q031p0:1p0E1pT2Q>1&Q1&Q0v@%211+dP0%542>J1&Q7r9%2261%Q:22Q8r8%M241%Q92Q;1%Q?241&Q>%125Q3p031pT2R01&Q=r;r:%37C21AQ:Q6Kp051p0?1p0C1p0J1pQBQM1pQ@QN1pT0R71pTJR<1pT:R=1pU6R>1pQ4R=1").
Proof. intros LB sp dst n W M M1.
intros FRZ STK BR INF.
apply (PMK.ek_piece_in RSEGS L KL LB sp 20480 W M M1 (fun a => dst <= a < dst + n) FRZ STK (PMFR.brange_hi L LB BR)).
intros a Pa. right. apply INF. exact Pa.
Qed.
Local Ltac tr64 M0 AG := lazymatch goal with |- L5.u64_at ?sg ?M2 ?a ?v =>
let X := fresh "X" in assert (X : L5.u64_at sg M0 a v) by PMK.gmem;
apply (L5C.u64_at_agree sg M0 M2 a v); [apply AG; lia | lia | lia | exact X] end.
Theorem src_read_ok : ltac2:(TCodec.tc2 tcn__PmSrcSRead ";&Q8vQGv@v>%43321&Q:%13543&Q9%13765p031p061").
Proof.
intros FB XS. unfold PMPSS.src_read_spec, PMPS.src_read_spec, PMPS.src_spec.
intros fx R M model K LBX cr sp r fb s str sm Wextra HH MOK K0 ENT FOK A10 ARGS WX PA IA BASE INCS KONT.
destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & STK). destruct FOK as (F1 & F2 & F3). cbn [pa_frame AD PmLayoutS.ADDR_S] in F2.
pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & SDEF). pose proof RAok as (Hr1 & Hr2).
destruct ARGS as (p & k & A11 & A12 & Hk & DST). destruct WX as (p' & k' & A11' & A12' & Hp' & Hk' & ->).
rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10.
rewrite L5K.rl11 in A11, A11'. rewrite L5K.rl12 in A12, A12'.
unfold PMPS.read_dst, PMSP.o_tb, PMSP.o_src, PMSP.o_p, PMSP.o_is in *. cbn [pa_off_p pa_off_is AD PmLayoutS.ADDR_S] in *.
change (PMSP.pm_scr 4) with 20480 in *. unfold PM.CHUNK in *.
assert (SC0 : 0 <= 20480) by lia.
set (LB := PM.parser_own s ++ LBX) in *.
assert (BR : PMFR.brange L LB) by (apply (PMFR.brange_of_heap L HI HIok LB LB cr M _ HH); apply incl_refl).
assert (NDL : NoDup (map fst LB)) by exact (PMPK.heap_nodup L HI HIok LB cr M _ HH).
pose proof (L5C.stk_writable RSEGS _ M sp 20480 STK) as WR.
destruct s as [mo dn dp src tb tg vb vk stk]. destruct src as [qc de rem]. destruct sm as [g eg st].
cbn [PM.p_src PM.p_tb PM.sr_qc PM.sr_de PM.sr_rem PM.sm_g PM.sm_eg PM.sm_st] in *.
assert (QIN : In (qc, 16384) LB) by (unfold LB, PM.parser_own, PM.src_own; cbn; left; reflexivity).
assert (VIN : In (vb, 32 * 2 ^ vk) LB) by (unfold LB, PM.parser_own, PM.vec_own; cbn; right; left; reflexivity).
assert (SINC : incl (PM.vs_own str) LB) by (unfold LB; apply incl_appr; exact INCS).
destruct (BR qc 16384 QIN) as (Q0 & Q1 & Q4). unfold hl_ceil in Q4.
destruct (BR _ _ VIN) as (V0 & V1 & V4). unfold hl_ceil in V4.
pose proof PA as (_ & PDEF & _ & _ & _ & _ & _ & _ & _ & PSRC & _ & _ & _ & PTB & _).
destruct PSRC as (S240 & S248 & S256 & S264 & S272 & S280 & S288 & G1 & G2 & G3 & _ & DCH & _).
cbn [PM.p_src PM.p_tb PM.sr_qc PM.sr_de PM.sr_rem] in *. unfold PM.CHUNK in *.
set (s0 := PM.PST mo dn dp (PM.SRC qc de rem) tb tg vb vk stk) in *.
assert (PINC : incl (PM.parser_own s0) LB) by (unfold LB; apply incl_appl; apply incl_refl).
assert (AL36 : (fb + 40 + 24) mod 8 = 0) by (replace (fb + 40 + 24) with (fb + 8 * 8) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
assert (AL37 : (fb + 440) mod 8 = 0) by (replace (fb + 440) with (fb + 8 * 55) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
assert (WF : L5.writable RSEGS M (fb + 40 + 24 + 256) 40).
{ apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M (fb + 40) 384); [exact PDEF|lia|lia]|lia|lia]. }
set (WS := PMSP.W_srcf AD fb ++ [(qc, 16384)]).
assert (WSE : PMSP.W_src AD fb (PM.SRC qc de rem) = WS) by reflexivity. rewrite WSE in KONT. clear WSE.
assert (WCs : forall a, PMK.inW WS a -> (fb + 320 <= a < fb + 360) \/ (fb + 480 <= a < fb + 488) \/ (fb + 592 <= a < fb + 596) \/ (qc <= a < qc + 16384)).
{ intros a (r0 & Hin & Hr). unfold WS, PMSP.W_srcf, PMSP.o_src, PMSP.o_p, PMSP.o_is in Hin. cbn [pa_off_p pa_off_is AD PmLayoutS.ADDR_S app] in Hin.
unfold L5.in_rng in Hr. destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hr; lia. }
pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 1))) as B1. pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 8))) as B8.
pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 9))) as B9. pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 18))) as B18.
pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 19))) as B19.
change (bv_modulus 64) with (2 ^ 64) in *.
assert (REMB : 0 <= rem <= 16384) by lia.
assert (DEB : qc <= de <= qc + 16384) by lia.
pose proof (PMPK.iss_size_lt RSEGS AD M (fb + 440) str _ IA) as SZ. cbn [PM.sm_g PM.sm_eg] in SZ.
pose proof IA as (I0 & IDEF & _ & I16 & _ & _ & I40 & _ & _ & _ & _ & _ & IIOS & _ & IE2).
destruct IIOS as (_ & J32 & J36 & J40 & _ & _ & JD & _ & JST).
cbn [PM.sm_g PM.sm_eg PM.sm_st pa_vp_iss pa_vp_strbuf pa_vp_iss_ios AD PmLayoutS.ADDR_S] in *.
assert (DF : 0 <= p /\ p + k <= 2 ^ 47 /\ L5.defined M p k /\ (forall a, p <= a < p + k -> PMK.cwr L LB a)
/\ (forall a, p <= a < p + k -> ~ (sp - 20480 <= a < sp) /\ ~ (fb + 40 <= a < fb + 377) /\ ~ (fb + 400 <= a < fb + 752)
/\ ~ (qc <= a < qc + 16384) /\ ~ (vb <= a < vb + 32 * 2 ^ vk) /\ (forall c1 n1 q1, str = PM.VLong c1 n1 q1 -> ~ (q1 <= a < q1 + c1))
/\ (forall c0 n0 q0, tb = PM.VLong c0 n0 q0 -> ~ (fb + 376 <= a < fb + 400)))
/\ (k = 16384 -> exists c0 n0 q0, tb = PM.VLong c0 n0 q0 /\ q0 <= p /\ p + k <= q0 + c0)
/\ ((sp <= p /\ p + k <= fb + 400) \/ (exists c0 n0 q0, tb = PM.VLong c0 n0 q0 /\ q0 <= p /\ p + k <= q0 + c0))
/\ (forall a, p <= a < p + k -> ~ (hl_img_lo L <= a < hl_img_hi L))).
{ pose proof (PMK.kl_img RSEGS L KL) as KI. rewrite (ly_img_lo L LY), (ly_img_hi L LY) in KI |- *.
destruct DST as [(D1 & D2 & D3 & D4)|[((n0 & ->) & D1 & D2)|(c0 & n0 & q0 & -> & D1 & D2)]].
- split; [lia|]. split; [lia|]. split; [exact D4|]. split.
{ intros a Ha. apply (PMK.cwr_stack L LB M sp 20480 a STK). lia. }
split; [|split; [intros E; exfalso; lia| split; [left; lia| intros a Ha; unfold hl_ceil in *; lia]]].
intros a Ha. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
split; [|intros c0 n0 q0 _; lia].
intros c1 n1 q1 ->. assert (SIN : In (q1, c1) LB) by (apply SINC; left; reflexivity).
destruct (BR _ _ SIN) as (_ & _ & Z4). unfold hl_ceil in Z4. lia.
- destruct PTB as (TD & _ & _ & _).
split; [lia|]. split; [lia|]. split; [apply (L5.defined_sub M (fb + 40 + 336) 24); [exact TD|lia|lia]|]. split.
{ intros a Ha. apply (PMK.cwr_stack L LB M sp 20480 a STK). lia. }
split; [|split; [intros E; exfalso; lia| split; [left; lia| intros a Ha; unfold hl_ceil in *; lia]]].
intros a Ha. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
split; [|intros c0 n1 q0 E; discriminate E].
intros c1 n1 q1 ->. assert (SIN : In (q1, c1) LB) by (apply SINC; left; reflexivity).
destruct (BR _ _ SIN) as (_ & _ & Z4). unfold hl_ceil in Z4. lia.
- assert (TIN : In (q0, c0) LB) by (unfold LB, PM.parser_own, PM.vs_own; cbn; right; right; left; reflexivity).
destruct (BR _ _ TIN) as (T0 & T1 & T4). unfold hl_ceil in T4.
pose proof PTB as (_ & _ & _ & _ & _ & _ & _ & _ & TBD & _).
assert (ND3 : NoDup (map fst ((qc, 16384) :: (vb, 32 * 2 ^ vk) :: (q0, c0) :: LBX))) by exact NDL.
destruct (nodup3 _ _ _ _ ND3) as (N1 & N2 & N3). cbn [fst] in N1, N2, N3.
destruct (PMPK.blocks_apart_heap L HI HIok LB cr M _ q0 c0 qc 16384 HH TIN QIN ltac:(intros E; apply N2; symmetry; exact E)) as [AQ|AQ];
destruct (PMPK.blocks_apart_heap L HI HIok LB cr M _ q0 c0 vb (32 * 2 ^ vk) HH TIN VIN ltac:(intros E; apply N3; symmetry; exact E)) as [AV|AV].
all: split; [lia|]; split; [lia|]; split; [apply (L5.defined_sub M q0 c0); [exact TBD|lia|lia]|]; split;
[intros a Ha; apply (PMK.cwr_block L LB q0 c0 a TIN); lia|].
all: split; [|split; [intros _; exists c0, n0, q0; split; [reflexivity| lia]| split; [right; exists c0, n0, q0; split; [reflexivity| lia]|]]];
[| intros a Ha; rewrite (ly_img_lo L LY), (ly_img_hi L LY) in T1; clear - Ha D1 D2 T1 T0; lia].
all: intros a Ha; split; [clear - Ha D2 T4 SLO; unfold hl_ceil in *; lia|]; split; [clear - Ha D2 T4 SLO F1; unfold hl_ceil in *; lia|];
split; [clear - Ha D2 T4 SLO F1; unfold hl_ceil in *; lia|]; split; [clear - Ha D1 D2 AQ; lia|]; split; [clear - Ha D1 D2 AV; lia|];
split; [|intros c2 n2 q2 _; clear - Ha D2 T4 SLO F1; unfold hl_ceil in *; lia].
all: intros c1 n1 q1 ->; assert (SIN : In (q1, c1) LBX) by (apply INCS; left; reflexivity).
all: assert (NE : q0 <> q1) by (apply (PMPK.fst_neq_app (PM.parser_own s0) LBX q0 c0 q1 c1); [exact NDL| unfold s0, PM.parser_own, PM.vs_own; cbn; right; right; left; reflexivity| exact SIN]).
all: destruct (PMPK.blocks_apart_heap L HI HIok LB cr M _ q0 c0 q1 c1 HH TIN (SINC _ (or_introl eq_refl)) NE) as [AS|AS]; clear - Ha D1 D2 AS; lia. }
destruct DF as (DP0 & DP1 & DD & DCW & DX & D16K & DWH & DXI).
assert (QI : forall a, qc <= a < qc + 16384 -> ~ (65536 <= a < 954368)).
{ rewrite (ly_img_lo L LY), (ly_img_hi L LY) in Q1. intros a Ha. clear - Ha Q1. lia. }
clear DST Q1 V1.
assert (NDF : forall i, (sp - 20480 <= i < sp) \/ (fb + 40 <= i < fb + 377) \/ (fb + 400 <= i < fb + 752) \/ (qc <= i < qc + 16384) -> ~ (p <= i < p + k)).
{ intros i H Hd. destruct (DX i Hd) as (Y1 & Y2 & Y3 & Y4 & _). clear - H Y1 Y2 Y3 Y4. lia. }
assert (NDR : forall a n, (sp - 20480 <= a /\ a + n <= sp) \/ (fb + 40 <= a /\ a + n <= fb + 377) \/ (fb + 400 <= a /\ a + n <= fb + 752) ->
forall i, a <= i < a + n -> ~ (p <= i < p + k)).
{ intros a n H i Hi. apply NDF. clear - H Hi. lia. }
assert (pk : p' = p /\ k' = k).
{ rewrite A11 in A11'. rewrite A12 in A12'. apply (f_equal bv_unsigned) in A11', A12'. rewrite !L5.unsigned_lit in A11', A12' by lia. split; congruence. }
destruct pk as (-> & ->). clear A11' A12'.
set (WA := WS ++ [(p, k)]).
assert (WCA : forall a, PMK.inW WA a -> (fb + 320 <= a < fb + 360) \/ (fb + 480 <= a < fb + 488) \/ (fb + 592 <= a < fb + 596) \/ (qc <= a < qc + 16384) \/ (p <= a < p + k)).
{ intros a I. unfold WA in I. destruct I as (r0 & Hin & Hr). apply in_app_or in Hin. destruct Hin as [Hin|Hin].
- assert (X : PMK.inW WS a) by (exists r0; split; assumption). apply WCs in X. lia.
- destruct Hin as [<-|[]]. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. lia. }
assert (INWf : forall a, fb + 320 <= a < fb + 360 -> PMK.inW WA a).
{ intros a Ha. unfold WA, WS, PMSP.W_srcf, PMSP.o_src, PMSP.o_p, PMSP.o_is. cbn [pa_off_p pa_off_is AD PmLayoutS.ADDR_S app]. apply PMK.inW_here. lia. }
assert (INWd : forall a, p <= a < p + k -> PMK.inW WA a).
{ intros a Ha. unfold WA. apply PMK.inW_app_r. apply PMK.inW_here. exact Ha. }
assert (INWg : forall a, fb + 480 <= a < fb + 488 -> PMK.inW WA a).
{ intros a Ha. unfold WA, WS, PMSP.W_srcf, PMSP.o_src, PMSP.o_p, PMSP.o_is. cbn [pa_off_p pa_off_is AD PmLayoutS.ADDR_S app]. apply PMK.inW_next. apply PMK.inW_here. lia. }
assert (INWs : forall a, fb + 592 <= a < fb + 596 -> PMK.inW WA a).
{ intros a Ha. unfold WA, WS, PMSP.W_srcf, PMSP.o_src, PMSP.o_p, PMSP.o_is. cbn [pa_off_p pa_off_is AD PmLayoutS.ADDR_S app]. do 2 apply PMK.inW_next. apply PMK.inW_here. lia. }
unfold PMSP.cfg. cbn [pa_src_read AD PmLayoutS.ADDR_S].
assert (AVQ : vb + 32 * 2 ^ vk <= qc \/ qc + 16384 <= vb).
{ assert (NE : qc <> vb).
{ apply (PMPK.fst_neq_app [(qc, 16384)] (PM.vec_own vb vk ++ PM.vs_own tb ++ LBX) qc 16384 vb (32 * 2 ^ vk)); [exact NDL| left; reflexivity| left; reflexivity]. }
destruct (PMPK.blocks_apart_heap L HI HIok LB cr M _ vb (32 * 2 ^ vk) qc 16384 HH VIN QIN ltac:(intros E; apply NE; symmetry; exact E)) as [X|X]; lia. }
assert (FIN : forall (fx3 : FPState) (R3 : bvmap 5 word) (M3 : word -> option byte) (de' rem' g' st' d : Z),
getr R3 (PMK.reg 1) = getr R (PMK.reg 1) ->
(forall x, In x PMK.cs_all -> getr R3 (PMK.reg x) = getr R (PMK.reg x)) ->
getr R3 (PMK.reg 10) = Z_to_bv 64 d ->
L5.u64_at RSEGS M3 (fb + 40 + 24 + 264) qc -> L5.u64_at RSEGS M3 (fb + 40 + 24 + 272) 16384 ->
L5.u64_at RSEGS M3 (fb + 40 + 24 + 280) de' -> L5.u64_at RSEGS M3 (fb + 40 + 24 + 288) rem' ->
qc <= de' -> 0 <= rem' -> de' + rem' <= qc + 16384 ->
L5.u64_at RSEGS M3 (fb + 440 + 40) g' -> L5.u32_at RSEGS M3 (fb + 440 + 152) st' ->
g <= g' <= eg -> (st' = 0 \/ st' = 2) -> (st = 2 -> st' = 2) ->
0 <= d <= k -> (rem + (eg - g)) - (rem' + (eg - g')) = d ->
(1 <= rem -> 1 <= d) -> (d = 0 -> rem' = 0 /\ st' = 2) ->
PMK.ek L LB sp 20480 WA M M3 -> PMK.dk L LB sp 20480 M M3 -> L5C.stk (hl_sptop L) M3 sp 20480 ->
hi_heap HI LB cr M3 (m_vmmaps model) ->
srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx3 R3 0x369ac M3 model) K).
{ intros fx3 R3 M3 de' rem' g' st' d E1 E2 E10 C264 C272 C280 C288 Q1' Q2' Q3' CG CS Hg Hst Hst2 Hd Hcons HR1 HR0 EK DK STK3 HH3.
unfold PMSP.cfg.
eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| |].
{ apply (PMK.ret_to RSEGS fx3 R3 M3 0x369ac (ltac:(oW' 0x369ac%Z)) r (ltac:(oF' 0x369ac%Z)) eq_refl (ltac:(oD' 0x369ac%Z))); [rewrite E1; exact Rra| lia| exact Hr2]. }
assert (HPf : L5C.hpres L LB sp 20480 WA M M3).
{ apply (PMK.hpres_of L LB sp 20480 WA M M3 EK); [destruct STK3 as (_ & _ & _ & _ & D3); exact D3| exact DK]. }
assert (AGH : forall a n, sp <= a -> a + n <= 2 ^ 64 -> (forall i, a <= i < a + n -> ~ PMK.inW WA i) -> L5C.agree_on M M3 a n).
{ intros a n H1 H2 N. apply (PMPK.ag_hi RSEGS L KL LB sp 20480 WA M M3 EK STK SC0 a n H1 H2 N). }
assert (DKH : forall a n, sp <= a -> a + n <= 2 ^ 64 -> PMPK.dkr M M3 a n).
{ intros a n H1 H2. apply (PMPK.dkr_hpres_hi RSEGS L KL LB sp 20480 WA M M3 a n HPf STK SC0 H1 H2). }
assert (DKB : forall B m, In (B, m) LB -> PMPK.dkr M M3 B m).
{ intros B m Hin. apply (PMPK.dkr_hpres_blk RSEGS L KL LB sp 20480 WA M M3 B m HPf Hin BR). lia. }
assert (NWR : forall a n, (fb + 40 <= a /\ a + n <= fb + 320) \/ (fb + 360 <= a /\ a + n <= fb + 377) \/ (fb + 400 <= a /\ a + n <= fb + 480)
\/ (fb + 488 <= a /\ a + n <= fb + 592) \/ (fb + 596 <= a /\ a + n <= fb + 752)
\/ ((exists c0 n0 q0, tb = PM.VLong c0 n0 q0) /\ fb + 376 <= a /\ a + n <= fb + 400) ->
forall i, a <= i < a + n -> ~ PMK.inW WA i).
{ intros a n H i Hi I. apply WCA in I.
destruct I as [I|[I|[I|[I|I]]]]; [clear - Hi I H Q4 SLO F1 STOP; unfold hl_ceil in *; lia ..|].
destruct (DX i I) as (_ & Y2 & Y3 & _ & _ & _ & Y7).
destruct H as [H|[H|[H|[H|[H|((c0 & n0 & q0 & E) & H)]]]]]; [clear - Hi H Y2 Y3; lia ..|].
assert (Y7' := Y7 c0 n0 q0 E). clear - Hi H Y7'. lia. }
assert (DD3 : L5.defined M3 p k).
{ destruct DWH as [(W1 & W2)|(c0 & n0 & q0 & E & W1 & W2)].
- apply (PMPK.defined_dkr M M3 p k (DKH p k ltac:(lia) ltac:(lia)) DD).
- assert (TIN : In (q0, c0) LB) by (unfold LB, s0, PM.parser_own, PM.vs_own; rewrite E; cbn; right; right; left; reflexivity).
apply (PMPK.defined_dkr M M3 p k); [apply (PMPK.dkr_sub M M3 q0 c0 p k (DKB q0 c0 TIN)); lia| exact DD]. }
apply (KONT fx3 R3 M3 (PM.SRC qc de' rem') (PM.STRM g' eg st')).
+ apply PMK.preserved_by_index. exact E2.
+ apply (PMPK.parser_src_tb_upd RSEGS AD M M3 (fb + 40) (fb + 440) s0 de' rem' PA); cbn [s0 PM.p_src PM.p_b PM.p_k PM.p_tb PM.sr_qc]; unfold PM.CHUNK.
* lia.
* lia.
* apply AGH; [lia|lia|]. apply NWR; lia.
* apply AGH; [lia|lia|]. apply NWR; lia.
* apply AGH; [lia|lia|]. apply NWR; lia.
* apply DKH; lia.
* apply DKH; lia.
* destruct tb as [n0|c0 n0 q0].
-- apply (PMPK.vstr_short_keep RSEGS M M3 (fb + 40 + 336) n0); [lia|lia| |apply DKH; lia| exact PTB].
apply AGH; [lia|lia|]. apply NWR; lia.
-- apply (PMPK.vstr_at_keep RSEGS M M3 (fb + 40 + 336) (PM.VLong c0 n0 q0)); [lia|lia| | |exact PTB].
++ apply AGH; [lia|lia|]. apply NWR. right. right. right. right. right. split; [exists c0, n0, q0; reflexivity| lia].
++ intros c1 n1 q1 E. injection E as <- <- <-. apply DKB. unfold LB, PM.parser_own, PM.vs_own. cbn. right. right. left. reflexivity.
* apply DKB. exact QIN.
* clear - V0. lia.
* clear - V4 STOP. unfold hl_ceil in *. lia.
* apply (PMPK.ag_blk RSEGS L KL LB sp 20480 WA M M3 EK STK BR vb (32 * 2 ^ vk) VIN).
intros i Hi I. apply WCA in I. destruct I as [I|[I|[I|[I|I]]]]; [clear - Hi I V4 SLO F1; unfold hl_ceil in *; lia ..| clear - Hi I AVQ; lia |].
destruct (DX i I) as (_ & _ & _ & _ & Y5 & _). clear - Hi Y5. lia.
* replace (fb + 40 + 288) with (fb + 40 + 24 + 264) by lia. exact C264.
* replace (fb + 40 + 296) with (fb + 40 + 24 + 272) by lia. exact C272.
* replace (fb + 40 + 304) with (fb + 40 + 24 + 280) by lia. exact C280.
* replace (fb + 40 + 312) with (fb + 40 + 24 + 288) by lia. exact C288.
* exact Q1'.
* exact Q2'.
* exact Q3'.
+ apply (PMPK.iss_upd RSEGS AD M M3 (fb + 440) str (PM.STRM g eg st) g' st' IA); cbn [PM.sm_g PM.sm_eg PM.sm_st].
* lia.
* lia.
* apply AGH; [lia|lia|]. apply NWR; lia.
* apply AGH; [lia|lia|]. apply NWR; lia.
* apply AGH; [lia|lia|]. apply NWR; lia.
* apply DKH; lia.
* apply DKH; lia.
* intros c1 n1 q1 ->. apply DKB. apply SINC. left. reflexivity.
* exact CG.
* exact CS.
* lia.
* exact Hst.
+ unfold PMSP.src_step, PM.unread. cbn [PM.sr_qc PM.sr_rem PM.sm_eg PM.sm_g PM.sm_st]. split; [reflexivity|]. split; [reflexivity|].
split; [lia|]. split; [exact Hst2| lia].
+ unfold PMPS.read_res, PMSP.consumed, PM.unread. cbn [PM.sr_rem PM.sm_eg PM.sm_g PM.sm_st]. exists p, k, d.
rewrite L5K.rl11, L5K.rl12, L5K.rl10. split; [exact A11|]. split; [exact A12|]. split; [lia|]. split; [unfold PM.CHUNK; lia|].
split; [exact E10|]. split; [exact Hd|].
split; [exact Hcons|]. split; [apply (L5.defined_sub M3 p k); [exact DD3|lia|lia]|]. split; [exact HR1| exact HR0].
+ exact HPf.
+ exact HH3. }
assert (CPART : forall (fx2 : FPState) (R2 : bvmap 5 word) (M2 : word -> option byte) (len1 c g2 st2 : Z),
getr R2 (PMK.reg 10) = Z_to_bv 64 c -> getr R2 (PMK.reg 2) = Z_to_bv 64 (sp - 48) -> getr R2 (PMK.reg 8) = Z_to_bv 64 (fb + 40 + 24) ->
getr R2 (PMK.reg 9) = Z_to_bv 64 len1 -> getr R2 (PMK.reg 18) = Z_to_bv 64 p -> getr R2 (PMK.reg 19) = Z_to_bv 64 (k - len1) ->
(forall x, In x [3; 4; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R2 (PMK.reg x) = getr R (PMK.reg x)) ->
L5.u64_at RSEGS M2 (sp - 8) (bv_unsigned (getr R (PMK.reg 1))) -> L5.u64_at RSEGS M2 (sp - 16) (bv_unsigned (getr R (PMK.reg 8))) ->
L5.u64_at RSEGS M2 (sp - 24) (bv_unsigned (getr R (PMK.reg 9))) -> L5.u64_at RSEGS M2 (sp - 32) (bv_unsigned (getr R (PMK.reg 18))) ->
L5.u64_at RSEGS M2 (sp - 40) (bv_unsigned (getr R (PMK.reg 19))) ->
L5.u64_at RSEGS M2 (fb + 40 + 24 + 264) qc -> L5.u64_at RSEGS M2 (fb + 40 + 24 + 272) 16384 ->
L5.u64_at RSEGS M2 (fb + 40 + 24 + 280) qc -> L5.u64_at RSEGS M2 (fb + 40 + 24 + 288) 0 -> L5.defined M2 (fb + 40 + 24 + 256) 40 ->
L5.defined M2 qc 16384 ->
L5.u64_at RSEGS M2 (fb + 440 + 40) g2 -> L5.u32_at RSEGS M2 (fb + 440 + 152) st2 ->
len1 = rem -> len1 < k -> k - len1 <= 16383 -> 0 <= c <= 16384 -> g2 = g + c -> g2 <= eg -> (st2 = 0 \/ st2 = 2) -> (st = 2 -> st2 = 2) -> (c = 0 -> st2 = 2) ->
L5.defined M2 p k ->
PMK.ek L LB sp 20480 WA M M2 -> PMK.dk L LB sp 20480 M M2 -> L5C.stk (hl_sptop L) M2 sp 20480 ->
hi_heap HI LB cr M2 (m_vmmaps model) ->
srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx2 R2 0x368c8 M2 model) K).
{ intros fx2 R2 M2 len1 c g2 st2 Y10 Y2 Y8 Y9 Y18 Y19 KS2 C8 C16 C24 C32 C40 D264 D272 D280 D288 D256 DQ CG CS Hl1 Hl1k Hl1k' Hc Hg2 Hg2e Hst2 Hst22 Hc0 DP2 EK2 DK2 STK2 HH2.
pose proof (L5C.stk_writable RSEGS _ M2 sp 20480 STK2) as WR2.
assert (WF2 : L5.writable RSEGS M2 (fb + 40 + 24 + 256) 40) by (apply (L5C.writable_of_defined RSEGS); [exact D256|lia|lia]).
assert (DE8 : L5.defined M2 (fb + 40 + 24 + 256) 8) by (apply (L5.defined_sub M2 _ 40 _ 8 D256); lia).
destruct (Z.eq_dec c 0) as [E0|N0].
-
subst c.
cfeed P (PMSRDP.srC0_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 34%nat => qc | 36%nat => fb + 40 + 24 | 37%nat => p | 38%nat => k - len1 | 39%nat => len1
| 40%nat => bv_unsigned (getr R (PMK.reg 1)) | 41%nat => bv_unsigned (getr R (PMK.reg 8)) | 42%nat => bv_unsigned (getr R (PMK.reg 9))
| 43%nat => bv_unsigned (getr R (PMK.reg 18)) | 44%nat => bv_unsigned (getr R (PMK.reg 19)) | _ => 0 end)) ltac:(first [PMK.sc | unfold PMSRDP.aligned; first [exact A16 | exact AL36] ]).
PMK.pvz_hg ltac:(idtac; destruct P as (fx3 & R3 & M3 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG3 & _ & FRZ3 & MS3 & KS3 & T1 & T2 & T8 & T9 & T10 & T18 & T19 & E288 & E264 & E272 & E280 & _)); PMK.pvz_clrT.
rewrite PMPK.word_id in T1, T8, T9, T18, T19.
apply (rd_step LB cr fx2 fx3 R2 R3 0x368c8 0x369ac M2 M3 model K sp fb HH2 Mh Ml ltac:(lia) ltac:(unfold hl_ceil; lia) ltac:(lia) ltac:(lia) MS3 MG3 FRZ3).
intros HH3.
apply (FIN fx3 R3 M3 qc 0 g2 st2 len1).
+ exact T1.
+ intros x Hx. cbn in Hx. repeat (destruct Hx as [<-|Hx]; [first [ rewrite T2; symmetry; exact Rsp | PMK.rk ] |]). destruct Hx.
+ exact T10.
+ exact E264.
+ exact E272.
+ exact E280.
+ exact E288.
+ lia.
+ lia.
+ lia.
+ apply (L5C.u64_at_agree RSEGS M2 M3); [intros i Hi; apply FRZ3; lia|lia|lia| exact CG].
+ apply (PMF.u32_at_agree RSEGS M2 M3); [intros i Hi; apply FRZ3; lia|lia|lia| exact CS].
+ lia.
+ exact Hst2.
+ exact Hst22.
+ lia.
+ lia.
+ lia.
+ intros _. split; [reflexivity| apply Hc0; reflexivity].
+ apply (PMK.ek_trans L LB sp 20480 WA M M2 M3 EK2). apply (rd_ek LB sp fb WA M2 M3 FRZ3 STK2 BR INWf).
+ apply (PMK.dk_trans L LB sp 20480 M M2 M3 DK2). apply (PMK.dk_grows L LB sp 20480 M2 M3 MG3).
+ apply (PMK.stk_grows L M2 M3 sp 20480 MG3 STK2).
+ exact HH3.
-
set (len2 := Z.min c (k - len1)).
assert (HEADC : exists fx3 R3 M3, msteps RSEGS (@mkst fx2 R2 (Z_to_bv 64 0x368c8) M2 (seg_rom RSEGS)) (@mkst fx3 R3 (Z_to_bv 64 0xa9160) M3 (seg_rom RSEGS))
/\ mem_grows M2 M3
/\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 48 <= i < sp - 48 + 48) -> ~ (fb + 40 + 24 + 256 <= i < fb + 40 + 24 + 256 + 40) -> M3 (Z_to_bv 64 i) = M2 (Z_to_bv 64 i))
/\ (forall x, In x [2; 3; 4; 8; 9; 18; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R3 (PMK.reg x) = getr R2 (PMK.reg x))
/\ getr R3 (PMK.reg 1) = Z_to_bv 64 223464 /\ getr R3 (PMK.reg 10) = Z_to_bv 64 (p + len1) /\ getr R3 (PMK.reg 11) = Z_to_bv 64 qc
/\ getr R3 (PMK.reg 12) = Z_to_bv 64 len2 /\ getr R3 (PMK.reg 19) = Z_to_bv 64 len2
/\ L5.u64_at RSEGS M3 (fb + 40 + 24 + 288) c /\ L5.u64_at RSEGS M3 (fb + 40 + 24 + 264) qc /\ L5.u64_at RSEGS M3 (fb + 40 + 24 + 272) 16384
/\ L5.u64_at RSEGS M3 (fb + 40 + 24 + 280) qc
/\ L5.u64_at RSEGS M3 (sp - 8) (bv_unsigned (getr R (PMK.reg 1))) /\ L5.u64_at RSEGS M3 (sp - 16) (bv_unsigned (getr R (PMK.reg 8)))
/\ L5.u64_at RSEGS M3 (sp - 24) (bv_unsigned (getr R (PMK.reg 9))) /\ L5.u64_at RSEGS M3 (sp - 32) (bv_unsigned (getr R (PMK.reg 18)))
/\ L5.u64_at RSEGS M3 (sp - 40) (bv_unsigned (getr R (PMK.reg 19)))).
{ destruct (Z_lt_le_dec (k - len1) c) as [CLT|CGE].
- assert (len2 = k - len1) as -> by (clear - CLT; unfold len2; lia).
cfeed P (PMSRDP.srClt_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 33%nat => c | 34%nat => qc | 36%nat => fb + 40 + 24 | 37%nat => p | 38%nat => k - len1 | 39%nat => len1
| 40%nat => bv_unsigned (getr R (PMK.reg 1)) | 41%nat => bv_unsigned (getr R (PMK.reg 8)) | 42%nat => bv_unsigned (getr R (PMK.reg 9))
| 43%nat => bv_unsigned (getr R (PMK.reg 18)) | 44%nat => bv_unsigned (getr R (PMK.reg 19)) | _ => 0 end)) ltac:(first [PMK.sc | unfold PMSRDP.aligned; first [exact A16 | exact AL36] ]).
PMK.pvz_hg ltac:(idtac; destruct P as (fx3 & R3 & M3 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG3 & _ & FRZ3 & MS3 & KS3 & T1 & T10 & T11 & T12 & E288 & E264 & E272 & E280 & _ & S8 & S16 & S24 & S32 & S40)); PMK.pvz_clrT.
exists fx3, R3, M3. split; [exact MS3|]. split; [exact MG3|]. split; [exact FRZ3|].
split. { intros x Hx. apply KS3. revert x Hx. apply (PMPK.sub_in PMSRDP.KS_srClt). vm_compute. reflexivity. }
split; [exact T1|]. split; [exact T10|]. split; [exact T11|]. split; [exact T12|].
split; [rewrite (KS3 19%nat) by PMK.inl; exact Y19|].
split; [exact E288|]. split; [exact E264|]. split; [exact E272|]. split; [exact E280|].
split; [exact S8|]. split; [exact S16|]. split; [exact S24|]. split; [exact S32| exact S40].
- assert (len2 = c) as -> by (clear - CGE; unfold len2; lia).
cfeed P (PMSRDP.srCge_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 33%nat => c | 34%nat => qc | 36%nat => fb + 40 + 24 | 37%nat => p | 38%nat => k - len1 | 39%nat => len1
| 40%nat => bv_unsigned (getr R (PMK.reg 1)) | 41%nat => bv_unsigned (getr R (PMK.reg 8)) | 42%nat => bv_unsigned (getr R (PMK.reg 9))
| 43%nat => bv_unsigned (getr R (PMK.reg 18)) | 44%nat => bv_unsigned (getr R (PMK.reg 19)) | _ => 0 end)) ltac:(first [PMK.sc | unfold PMSRDP.aligned; first [exact A16 | exact AL36] ]).
PMK.pvz_hg ltac:(idtac; destruct P as (fx3 & R3 & M3 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG3 & _ & FRZ3 & MS3 & KS3 & T1 & T10 & T11 & T12 & T19 & E288 & E264 & E272 & E280 & _ & S8 & S16 & S24 & S32 & S40)); PMK.pvz_clrT.
exists fx3, R3, M3. split; [exact MS3|]. split; [exact MG3|]. split; [exact FRZ3|].
split. { intros x Hx. apply KS3. revert x Hx. apply (PMPK.sub_in PMSRDP.KS_srCge). vm_compute. reflexivity. }
split; [exact T1|]. split; [exact T10|]. split; [exact T11|]. split; [exact T12|]. split; [exact T19|].
split; [exact E288|]. split; [exact E264|]. split; [exact E272|]. split; [exact E280|].
split; [exact S8|]. split; [exact S16|]. split; [exact S24|]. split; [exact S32| exact S40]. }
destruct HEADC as (fx3 & R3 & M3 & MS3 & MG3 & FRZ3 & KS3 & T1 & T10 & T11 & T12 & T19 & E288 & E264 & E272 & E280 & S8 & S16 & S24 & S32 & S40).
assert (L2R : 1 <= len2 <= 16383 /\ len2 <= c /\ len2 <= k - len1 /\ (len2 = k - len1 \/ len2 = c)) by (clear - N0 Hc Hl1k Hl1k'; unfold len2; lia).
destruct L2R as (L2a & L2b & L2c & L2d).
apply (rd_step LB cr fx2 fx3 R2 R3 0x368c8 0xa9160 M2 M3 model K sp fb HH2 Mh Ml ltac:(lia) ltac:(unfold hl_ceil; lia) ltac:(lia) ltac:(lia) MS3 MG3 FRZ3).
intros HH3.
assert (STK3 : L5C.stk (hl_sptop L) M3 sp 20480) by (apply (PMK.stk_grows L M2 M3 sp 20480 MG3 STK2)).
apply (rd_cpy LB cr fx3 R3 M3 model K (p + len1) qc len2 223464 HH3 Mh Ml ltac:(lia) T10 T11 T12 T1 ltac:(split; [lia| reflexivity])).
{ lia. } { lia. } { lia. } { lia. } { lia. }
{ destruct (apart_pt (p + len1) len2 qc 16384 ltac:(lia) ltac:(lia)) as [X|X]; [| left; exact X| right; lia].
intros a Ha. destruct (DX a ltac:(lia)) as (_ & _ & _ & Y4 & _). exact Y4. }
{ apply (L5.defined_grows M2 M3 _ _ MG3). apply (L5.defined_sub M2 p k); [exact DP2|lia|lia]. }
{ apply (L5.defined_grows M2 M3 _ _ MG3). apply (L5.defined_sub M2 qc 16384); [exact DQ|lia|lia]. }
{ intros a Ha. apply DCW. lia. }
intros R4 M4 MG4 FRZ4 _ KS4 HH4.
assert (AG4 : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (forall i, a <= i < a + n -> ~ (p <= i < p + k)) -> L5C.agree_on M3 M4 a n).
{ intros a n H1 H2 N i Hi. apply FRZ4; [lia|]. intros X. apply (N i Hi). clear - X L2a L2c Hl1k DP0 Hl1 REMB. lia. }
assert (ND : forall a n, (sp - 20480 <= a /\ a + n <= sp) \/ (fb + 40 <= a /\ a + n <= fb + 377) \/ (fb + 400 <= a /\ a + n <= fb + 752) ->
forall i, a <= i < a + n -> ~ (p <= i < p + k)).
{ intros a n H i Hi. apply NDF. clear - H Hi. lia. }
assert (S8' : L5.u64_at RSEGS M4 (sp - 8) (bv_unsigned (getr R (PMK.reg 1)))) by (apply (L5C.u64_at_agree RSEGS M3 M4); [apply AG4; [lia|lia| apply ND; lia]|lia|lia| exact S8]).
assert (S16' : L5.u64_at RSEGS M4 (sp - 16) (bv_unsigned (getr R (PMK.reg 8)))) by (apply (L5C.u64_at_agree RSEGS M3 M4); [apply AG4; [lia|lia| apply ND; lia]|lia|lia| exact S16]).
assert (S24' : L5.u64_at RSEGS M4 (sp - 24) (bv_unsigned (getr R (PMK.reg 9)))) by (apply (L5C.u64_at_agree RSEGS M3 M4); [apply AG4; [lia|lia| apply ND; lia]|lia|lia| exact S24]).
assert (S32' : L5.u64_at RSEGS M4 (sp - 32) (bv_unsigned (getr R (PMK.reg 18)))) by (apply (L5C.u64_at_agree RSEGS M3 M4); [apply AG4; [lia|lia| apply ND; lia]|lia|lia| exact S32]).
assert (S40' : L5.u64_at RSEGS M4 (sp - 40) (bv_unsigned (getr R (PMK.reg 19)))) by (apply (L5C.u64_at_agree RSEGS M3 M4); [apply AG4; [lia|lia| apply ND; lia]|lia|lia| exact S40]).
assert (E288' : L5.u64_at RSEGS M4 (fb + 40 + 24 + 288) c) by (apply (L5C.u64_at_agree RSEGS M3 M4); [apply AG4; [lia|lia| apply ND; lia]|lia|lia| exact E288]).
assert (E264' : L5.u64_at RSEGS M4 (fb + 40 + 24 + 264) qc) by (apply (L5C.u64_at_agree RSEGS M3 M4); [apply AG4; [lia|lia| apply ND; lia]|lia|lia| exact E264]).
assert (E272' : L5.u64_at RSEGS M4 (fb + 40 + 24 + 272) 16384) by (apply (L5C.u64_at_agree RSEGS M3 M4); [apply AG4; [lia|lia| apply ND; lia]|lia|lia| exact E272]).
assert (E280' : L5.u64_at RSEGS M4 (fb + 40 + 24 + 280) qc) by (apply (L5C.u64_at_agree RSEGS M3 M4); [apply AG4; [lia|lia| apply ND; lia]|lia|lia| exact E280]).
assert (WR4 : L5.writable RSEGS M4 (sp - 20480) 20480).
{ apply (L5.writable_grows RSEGS M3 M4 _ _ MG4). apply (L5.writable_grows RSEGS M2 M3 _ _ MG3). exact WR2. }
assert (WF4 : L5.writable RSEGS M4 (fb + 40 + 24 + 256) 40).
{ apply (L5.writable_grows RSEGS M3 M4 _ _ MG4). apply (L5.writable_grows RSEGS M2 M3 _ _ MG3). exact WF2. }
assert (DE84 : L5.defined M4 (fb + 40 + 24 + 256) 8).
{ apply (L5.defined_grows M3 M4 _ _ MG4). apply (L5.defined_grows M2 M3 _ _ MG3). exact DE8. }
cfeed P (PMSRDP.srD_conc fx3 R4 M4 (fun j => match j with 2%nat => sp | 33%nat => c | 34%nat => qc | 35%nat => qc | 36%nat => fb + 40 + 24 | 37%nat => p
| 38%nat => len2 | 39%nat => len1
| 40%nat => bv_unsigned (getr R (PMK.reg 1)) | 41%nat => bv_unsigned (getr R (PMK.reg 8)) | 42%nat => bv_unsigned (getr R (PMK.reg 9))
| 43%nat => bv_unsigned (getr R (PMK.reg 18)) | 44%nat => bv_unsigned (getr R (PMK.reg 19)) | _ => 0 end)) ltac:(first [PMK.sc | unfold PMSRDP.aligned; first [exact A16 | exact AL36] ]).
PMK.pvz_hg ltac:(idtac; destruct P as (fx5 & R5 & M5 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG5 & _ & FRZ5 & MS5 & KS5 & U1 & U2 & U8 & U9 & U10 & U11 & U18 & U19 & F288 & F280 & F264 & F272 & _)); PMK.pvz_clrT.
rewrite PMPK.word_id in U1, U8, U9, U18, U19.
apply (rd_step LB cr fx3 fx5 R4 R5 0x368e8 0x369ac M4 M5 model K sp fb HH4 Mh Ml ltac:(lia) ltac:(unfold hl_ceil; lia) ltac:(lia) ltac:(lia) MS5 MG5 FRZ5).
intros HH5.
assert (STK4 : L5C.stk (hl_sptop L) M4 sp 20480) by (apply (PMK.stk_grows L M3 M4 sp 20480 MG4 STK3)).
assert (AG25 : forall a n, (fb + 400 <= a /\ a + n <= fb + 752) -> L5C.agree_on M2 M5 a n).
{ intros a n H. apply (L5C.agree_on_trans M2 M3 M5); [intros i Hi; apply FRZ3; lia|].
apply (L5C.agree_on_trans M3 M4 M5); [apply AG4; [lia|lia| apply ND; lia]|]. intros i Hi; apply FRZ5; lia. }
apply (FIN fx5 R5 M5 (qc + len2) (c - len2) g2 st2 (len2 + len1)).
+ exact U1.
+ intros x Hx. cbn in Hx. repeat (destruct Hx as [<-|Hx]; [first [ rewrite U2; symmetry; exact Rsp | PMK.rk ] |]). destruct Hx.
+ exact U10.
+ exact F264.
+ exact F272.
+ exact F280.
+ exact F288.
+ lia.
+ lia.
+ lia.
+ apply (L5C.u64_at_agree RSEGS M2 M5); [apply AG25; lia|lia|lia| exact CG].
+ apply (PMF.u32_at_agree RSEGS M2 M5); [apply AG25; lia|lia|lia| exact CS].
+ lia.
+ exact Hst2.
+ exact Hst22.
+ lia.
+ destruct L2d as [X|X]; rewrite X; lia.
+ lia.
+ intros X. exfalso. lia.
+ apply (PMK.ek_trans L LB sp 20480 WA M M2 M5 EK2). apply (PMK.ek_trans L LB sp 20480 WA M2 M3 M5); [apply (rd_ek LB sp fb WA M2 M3 FRZ3 STK2 BR INWf)|].
apply (PMK.ek_trans L LB sp 20480 WA M3 M4 M5); [apply (rd_ek_cpy LB sp (p + len1) len2 WA M3 M4 FRZ4 STK3 BR); intros a Ha; apply INWd; lia|].
apply (rd_ek LB sp fb WA M4 M5 FRZ5 STK4 BR INWf).
+ apply (PMK.dk_trans L LB sp 20480 M M2 M5 DK2). apply (PMK.dk_grows L LB sp 20480 M2 M5).
apply (mem_grows_trans M2 M3 M5 MG3). apply (mem_grows_trans M3 M4 M5 MG4 MG5).
+ apply (PMK.stk_grows L M4 M5 sp 20480 MG5 STK4).
+ exact HH5. }
assert (FILLC : forall (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (len1 : Z),
getr R1 (PMK.reg 1) = Z_to_bv 64 223432 -> getr R1 (PMK.reg 2) = Z_to_bv 64 (sp - 48) -> getr R1 (PMK.reg 8) = Z_to_bv 64 (fb + 40 + 24) ->
getr R1 (PMK.reg 9) = Z_to_bv 64 len1 -> getr R1 (PMK.reg 10) = Z_to_bv 64 (fb + 40 + 24) -> getr R1 (PMK.reg 11) = Z_to_bv 64 qc ->
getr R1 (PMK.reg 12) = Z_to_bv 64 16384 -> getr R1 (PMK.reg 18) = Z_to_bv 64 p -> getr R1 (PMK.reg 19) = Z_to_bv 64 (k - len1) ->
(forall x, In x [3; 4; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R1 (PMK.reg x) = getr R (PMK.reg x)) ->
L5.u64_at RSEGS M1 (sp - 8) (bv_unsigned (getr R (PMK.reg 1))) -> L5.u64_at RSEGS M1 (sp - 16) (bv_unsigned (getr R (PMK.reg 8))) ->
L5.u64_at RSEGS M1 (sp - 24) (bv_unsigned (getr R (PMK.reg 9))) -> L5.u64_at RSEGS M1 (sp - 32) (bv_unsigned (getr R (PMK.reg 18))) ->
L5.u64_at RSEGS M1 (sp - 40) (bv_unsigned (getr R (PMK.reg 19))) ->
L5.u64_at RSEGS M1 (fb + 40 + 24 + 264) qc -> L5.u64_at RSEGS M1 (fb + 40 + 24 + 272) 16384 ->
L5.u64_at RSEGS M1 (fb + 40 + 24 + 280) qc -> L5.u64_at RSEGS M1 (fb + 40 + 24 + 288) 0 ->
len1 = rem -> len1 < k -> k - len1 <= 16383 ->
(forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 48 <= i < sp) -> ~ (fb + 320 <= i < fb + 360) -> ~ (p <= i < p + k) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
mem_grows M M1 ->
hi_heap HI LB cr M1 (m_vmmaps model) ->
srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x36a08 M1 model) K).
{ intros fx1 R1 M1 len1 X1 X2 X8 X9 X10 X11 X12 X18 X19 KS1 C8 C16 C24 C32 C40 C264 C272 C280 C288 Hl1 Hl1k Hl1k' FRZ1 MG1 HH1.
assert (AG1 : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (a + n <= sp - 48 \/ sp <= a) -> (a + n <= fb + 320 \/ fb + 360 <= a) ->
(forall i, a <= i < a + n -> ~ (p <= i < p + k)) -> L5C.agree_on M M1 a n).
{ intros a n H1 H2 H3 H4 N i Hi. apply FRZ1; [clear - H1 H2 Hi; lia| clear - H3 Hi; lia| clear - H4 Hi; lia| apply (N i Hi)]. }
assert (ND : forall a n, (sp - 20480 <= a /\ a + n <= sp) \/ (fb + 40 <= a /\ a + n <= fb + 377) \/ (fb + 400 <= a /\ a + n <= fb + 752) ->
forall i, a <= i < a + n -> ~ (p <= i < p + k)).
{ intros a n H i Hi. apply NDF. clear - H Hi. lia. }
assert (STK1 : L5C.stk (hl_sptop L) M1 sp 20480) by (apply (PMK.stk_grows L M M1 sp 20480 MG1 STK)).
assert (EK1 : PMK.ek L LB sp 20480 WA M M1).
{ apply (PMK.ek_piece_in RSEGS L KL LB sp 20480 WA M M1 (fun a => (sp - 48 <= a < sp) \/ (fb + 320 <= a < fb + 360) \/ (p <= a < p + k))
ltac:(intros a Ha N; apply FRZ1; [exact Ha| | |]; intros X; apply N; [left|right; left|right; right]; exact X) STK (PMFR.brange_hi L LB BR)).
intros a [Pa|[Pa|Pa]]; [left; lia| right; apply INWf; lia| right; apply INWd; lia]. }
set (s1 := PMPS.with_src s0 (PM.SRC qc qc 0)).
assert (PA1 : PM.parser_at RSEGS AD PMSP.T3 PMSP.T4 M1 (fb + 40) (fb + 440) s1).
{ apply (PMPK.parser_src_tb_upd RSEGS AD M M1 (fb + 40) (fb + 440) s0 qc 0 PA); cbn [s0 PM.p_src PM.p_b PM.p_k PM.p_tb PM.sr_qc]; unfold PM.CHUNK.
- lia.
- lia.
- apply AG1; [lia|lia|lia|lia| apply ND; lia].
- apply AG1; [lia|lia|lia|lia| apply ND; lia].
- apply AG1; [lia|lia|lia|lia| apply ND; lia].
- apply PMPK.dkr_grows. exact MG1.
- apply PMPK.dkr_grows. exact MG1.
- destruct tb as [n0|c0 n0 q0].
+ apply (PMPK.vstr_short_keep RSEGS M M1 (fb + 40 + 336) n0); [lia|lia| |apply PMPK.dkr_grows; exact MG1| exact PTB].
apply AG1; [lia|lia|lia|lia| apply ND; lia].
+ apply (PMPK.vstr_at_keep RSEGS M M1 (fb + 40 + 336) (PM.VLong c0 n0 q0)); [lia|lia| | |exact PTB].
* apply AG1; [lia|lia|lia|lia|]. intros i Hi Hd. destruct (DX i Hd) as (_ & _ & _ & _ & _ & _ & Y7). apply (Y7 c0 n0 q0 eq_refl). lia.
* intros c1 n1 q1 _. apply PMPK.dkr_grows. exact MG1.
- apply PMPK.dkr_grows. exact MG1.
- lia.
- clear - V4 STOP. unfold hl_ceil in *. lia.
- intros i Hi. apply FRZ1; [clear - Hi V0 V4 STOP; unfold hl_ceil in *; lia| clear - Hi V4 SLO; unfold hl_ceil in *; lia| clear - Hi V4 SLO F1; unfold hl_ceil in *; lia|].
intros Hd. destruct (DX i Hd) as (_ & _ & _ & _ & Y5 & _). lia.
- replace (fb + 40 + 288) with (fb + 40 + 24 + 264) by lia. exact C264.
- replace (fb + 40 + 296) with (fb + 40 + 24 + 272) by lia. exact C272.
- replace (fb + 40 + 304) with (fb + 40 + 24 + 280) by lia. exact C280.
- replace (fb + 40 + 312) with (fb + 40 + 24 + 288) by lia. exact C288.
- lia.
- lia.
- lia. }
assert (IA1 : PM.iss_at RSEGS AD PMSP.T3 M1 (fb + 440) str (PM.STRM g eg st)).
{ apply (PMPK.iss_upd RSEGS AD M M1 (fb + 440) str (PM.STRM g eg st) g st IA); cbn [PM.sm_g PM.sm_eg PM.sm_st].
- lia.
- lia.
- apply AG1; [lia|lia|lia|lia| apply ND; lia].
- apply AG1; [lia|lia|lia|lia| apply ND; lia].
- apply AG1; [lia|lia|lia|lia| apply ND; lia].
- apply PMPK.dkr_grows. exact MG1.
- apply PMPK.dkr_grows. exact MG1.
- intros c1 n1 q1 _. apply PMPK.dkr_grows. exact MG1.
- apply (L5C.u64_at_agree RSEGS M M1); [apply AG1; [lia|lia|lia|lia| apply ND; lia]|lia|lia| exact I40].
- apply (PMF.u32_at_agree RSEGS M M1); [apply AG1; [lia|lia|lia|lia| apply ND; lia]|lia|lia| replace (fb + 440 + 152) with (fb + 440 + 120 + 32) by lia; exact J32].
- lia.
- exact JST. }
assert (BASE1 : PMST.base_ok RSEGS AD M1).
{ apply (PMKP.base_ok_keep RSEGS AD L KL SF LB sp 20480 WA M M1 EK1); [| | | | exact BASE].
all: intros a Ha; apply PMFR.outside_of_not_inW; intros I; apply WCA in I; pose proof (DXI a) as Y;
cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock AD PmLayoutS.ADDR_S] in Ha.
all: destruct I as [I|[I|[I|[I|I]]]].
all: first [ clear - I Ha SLO F1 STOP; lia | apply (QI a I); clear - Ha; lia | apply (Y I); rewrite (ly_img_lo L LY), (ly_img_hi L LY); clear - Ha; lia ]. }
assert (STKc : L5C.stk (hl_sptop L) M1 (sp - 48) 18432).
{ apply (PMK.stk_call L M1 sp 20480 (sp - 48) 18432 STK1); [lia|lia|lia|]. replace (sp - 48) with (sp + (-3) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
unfold PMPSS.fill_buffer_spec, PMPS.fill_buffer_spec, PMPS.src_spec in FB. cbn [pa_fill_buffer AD PmLayoutS.ADDR_S] in FB.
apply (FB fx1 R1 M1 model K LBX cr (sp - 48) 223432 fb s1 str (PM.STRM g eg st) [] HH1 MOK K0).
{ unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact X1|]. split; [split; [lia| reflexivity]|]. split; [exact X2|].
split; [rewrite (KS1 3%nat) by PMK.inl; exact Rgp|]. split; [rewrite (KS1 4%nat) by PMK.inl; exact Rtp|]. exact STKc. }
{ unfold PMSP.frame_ok. cbn [pa_frame AD PmLayoutS.ADDR_S]. split; [lia|]. split; [lia| exact F3]. }
{ rewrite L5K.rl10. unfold PMSP.o_src, PMSP.o_p. cbn [pa_off_p AD PmLayoutS.ADDR_S]. exact X10. }
{ unfold PMPS.fill_args. rewrite L5K.rl11, L5K.rl12. split; [exact X11| exact X12]. }
{ unfold PMSP.no_W. reflexivity. }
{ unfold PMSP.o_p, PMSP.o_is. cbn [pa_off_p pa_off_is AD PmLayoutS.ADDR_S]. exact PA1. }
{ unfold PMSP.o_is. cbn [pa_off_is AD PmLayoutS.ADDR_S]. exact IA1. }
{ exact BASE1. } { exact INCS. }
intros fx2 R2 M2 src2 sm2 RP2 PA2 IA2 STEP2 RES2 HP2 HH2.
unfold PMPS.fill_res in RES2. destruct RES2 as (-> & c & Y10 & CR & GG2 & RS0 & RS2).
unfold PMSP.o_p, PMSP.o_is in PA2, IA2. cbn [pa_off_p pa_off_is AD PmLayoutS.ADDR_S] in PA2, IA2.
change (PMSP.pm_scr 3) with 18432 in HP2. rewrite app_nil_r in HP2.
rewrite L5K.rl10 in Y10. unfold PM.CHUNK in CR, RS0.
destruct sm2 as [g2 eg2 st2]. cbn [PM.sm_g PM.sm_eg PM.sm_st] in GG2, RS0, RS2.
assert (EKc : PMK.ek L LB (sp - 48) 18432 WS M1 M2) by (apply (PMK.ek_of_hpres L); exact HP2).
assert (SCc : 0 <= 18432) by lia.
assert (STK2 : L5C.stk (hl_sptop L) M2 sp 20480) by (apply (PMK.stk_after RSEGS L KL LB M1 M2 sp 20480 (sp - 48) 18432 WS STK1 HP2); lia).
assert (HI2 : forall a n, sp - 48 <= a -> a + n <= fb + 320 -> L5C.agree_on M1 M2 a n).
{ intros a n H1 H2. apply (PMPK.ag_hi RSEGS L KL LB (sp - 48) 18432 WS M1 M2 EKc STKc SCc a n H1); [lia|]. intros i Hi I. apply WCs in I.
clear - Hi I H1 H2 Q4 SLO; unfold hl_ceil in *; lia. }
pose proof PA2 as (_ & PDEF2 & _ & _ & _ & _ & _ & _ & _ & PSRC2 & _).
destruct PSRC2 as (_ & _ & T256 & T264 & T272 & T280 & T288 & _ & _ & _ & _ & DCH2 & _).
cbn [PMPS.with_src s1 s0 PM.p_src PM.sr_qc PM.sr_de PM.sr_rem] in T264, T280, T288, DCH2. unfold PM.CHUNK in *.
pose proof IA2 as (_ & _ & _ & _ & _ & _ & K40 & _ & _ & _ & _ & _ & KIOS & _ & KE2).
destruct KIOS as (_ & L32 & _ & _ & _ & _ & _ & _ & LST). cbn [PM.sm_g PM.sm_eg PM.sm_st] in K40, L32, LST, KE2.
unfold PMSP.src_step in STEP2. cbn [s1 s0 PMPS.with_src PM.p_src PM.sr_qc PM.sm_eg PM.sm_g PM.sm_st] in STEP2. destruct STEP2 as (_ & E2 & _ & S2 & _).
subst eg2.
apply (CPART fx2 R2 M2 len1 c g2 st2).
- exact Y10.
- rewrite (PMK.cs_of_preserved R1 R2 2%nat RP2) by PMK.inl. exact X2.
- rewrite (PMK.cs_of_preserved R1 R2 8%nat RP2) by PMK.inl. exact X8.
- rewrite (PMK.cs_of_preserved R1 R2 9%nat RP2) by PMK.inl. exact X9.
- rewrite (PMK.cs_of_preserved R1 R2 18%nat RP2) by PMK.inl. exact X18.
- rewrite (PMK.cs_of_preserved R1 R2 19%nat RP2) by PMK.inl. exact X19.
- intros x Hx. rewrite (PMK.cs_of_preserved R1 R2 x RP2) by (revert x Hx; apply (PMPK.sub_in PMK.cs_all); vm_compute; reflexivity). apply KS1. exact Hx.
- apply (L5C.u64_at_agree RSEGS M1 M2); [apply HI2; lia|lia|lia| exact C8].
- apply (L5C.u64_at_agree RSEGS M1 M2); [apply HI2; lia|lia|lia| exact C16].
- apply (L5C.u64_at_agree RSEGS M1 M2); [apply HI2; lia|lia|lia| exact C24].
- apply (L5C.u64_at_agree RSEGS M1 M2); [apply HI2; lia|lia|lia| exact C32].
- apply (L5C.u64_at_agree RSEGS M1 M2); [apply HI2; lia|lia|lia| exact C40].
- exact T264.
- exact T272.
- exact T280.
- exact T288.
- apply (L5.defined_sub M2 (fb + 40) 384); [exact PDEF2|lia|lia].
- exact DCH2.
- exact K40.
- replace (fb + 440 + 152) with (fb + 440 + 120 + 32) by lia. exact L32.
- exact Hl1.
- exact Hl1k.
- exact Hl1k'.
- exact CR.
- exact GG2.
- lia.
- exact LST.
- exact S2.
- intros C0. subst c. destruct JST as [J0|J2]; [destruct (RS0 J0) as (_ & ->); reflexivity| destruct (RS2 J2) as (_ & ->); reflexivity].
- destruct DWH as [(W1 & W2)|(c0 & n0 & q0 & E & W1 & W2)].
+ apply (PMPK.defined_dkr M1 M2 p k); [apply (PMPK.dkr_hpres_hi RSEGS L KL LB (sp - 48) 18432 WS M1 M2 p k HP2 STKc SCc); lia|].
exact (L5.defined_grows M M1 p k MG1 DD).
+ assert (TIN : In (q0, c0) LB) by (unfold LB, s0, PM.parser_own, PM.vs_own; rewrite E; cbn; right; right; left; reflexivity).
apply (PMPK.defined_dkr M1 M2 p k); [apply (PMPK.dkr_sub M1 M2 q0 c0 p k); [apply (PMPK.dkr_hpres_blk RSEGS L KL LB (sp - 48) 18432 WS M1 M2 q0 c0 HP2 TIN BR); lia|lia|lia]|].
exact (L5.defined_grows M M1 p k MG1 DD).
- apply (PMK.ek_trans L LB sp 20480 WA M M1 M2 EK1).
apply (PMK.ek_callee_in' RSEGS L KL LB LB sp 20480 (sp - 48) 18432 WA WS M1 M2 HP2 (incl_refl _)); [lia|lia|unfold hl_ceil; lia|lia| exact (PMFR.brange_hi L LB BR)|].
intros a I. right. unfold WA. apply PMK.inW_app_l. exact I.
- apply (PMK.dk_trans L LB sp 20480 M M1 M2); [apply (PMK.dk_grows L LB sp 20480 M M1 MG1)|].
apply (PMK.dk_callee L LB LB sp 20480 (sp - 48) 18432 WS M1 M2 HP2 (incl_refl _)); lia.
- exact STK2.
- exact HH2. }
pose proof BASE as (IMG & _). cbn [pa_rw_lo AD PmLayoutS.ADDR_S] in IMG.
destruct (Z_le_gt_dec 1 rem) as [REM1|REM0].
-
set (len1 := Z.min k rem).
assert (L1R : 1 <= len1 <= rem /\ len1 <= k /\ (len1 = k \/ len1 = rem)) by (clear - REM1 Hk; unfold len1; lia).
destruct L1R as (L1a & L1b & L1c).
assert (HEAD : exists fx1 R1 M1, msteps RSEGS (@mkst fx R (Z_to_bv 64 0x36830) M (seg_rom RSEGS)) (@mkst fx1 R1 (Z_to_bv 64 0xa9160) M1 (seg_rom RSEGS))
/\ mem_grows M M1
/\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 48 <= i < sp - 48 + 48) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i))
/\ (forall x, In x [3; 4; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R1 (PMK.reg x) = getr R (PMK.reg x))
/\ getr R1 (PMK.reg 1) = Z_to_bv 64 223352 /\ getr R1 (PMK.reg 2) = Z_to_bv 64 (sp - 48) /\ getr R1 (PMK.reg 8) = Z_to_bv 64 (fb + 40 + 24)
/\ getr R1 (PMK.reg 9) = Z_to_bv 64 len1 /\ getr R1 (PMK.reg 10) = Z_to_bv 64 p /\ getr R1 (PMK.reg 11) = Z_to_bv 64 de
/\ getr R1 (PMK.reg 12) = Z_to_bv 64 len1 /\ getr R1 (PMK.reg 18) = Z_to_bv 64 p /\ getr R1 (PMK.reg 19) = Z_to_bv 64 k
/\ L5.u64_at RSEGS M1 (sp - 40) (bv_unsigned (getr R (PMK.reg 19))) /\ L5.u64_at RSEGS M1 (sp - 32) (bv_unsigned (getr R (PMK.reg 18)))
/\ L5.u64_at RSEGS M1 (sp - 24) (bv_unsigned (getr R (PMK.reg 9))) /\ L5.u64_at RSEGS M1 (sp - 16) (bv_unsigned (getr R (PMK.reg 8)))
/\ L5.u64_at RSEGS M1 (sp - 8) (bv_unsigned (getr R (PMK.reg 1)))).
{ destruct (Z_lt_le_dec k rem) as [KLT|KGE].
- assert (len1 = k) as -> by (clear - KLT; unfold len1; lia).
cfeed P (PMSRDP.srAlt_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => rem | 34%nat => qc | 35%nat => de | 36%nat => fb + 40 + 24
| 37%nat => p | 38%nat => k | _ => 0 end)) ltac:(first [PMK.sc | unfold PMSRDP.aligned; first [exact A16 | exact AL36] ]).
PMK.pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG1 & _ & FRZ1 & MS1 & KS1 & X1 & X2 & X8 & X9 & X10 & X11 & X18 & X19 & C40 & C32 & C24 & C16 & C8)); PMK.pvz_clrT.
exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|]. split; [exact FRZ1|].
split. { intros x Hx. apply KS1. revert x Hx. apply (PMPK.sub_in PMSRDP.KS_srAlt). vm_compute. reflexivity. }
do 6 (split; [assumption|]). split; [rewrite (KS1 12%nat) by PMK.inl; exact A12|]. do 6 (split; [assumption|]). assumption.
- assert (len1 = rem) as -> by (clear - KGE; unfold len1; lia).
cfeed P (PMSRDP.srAge_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => rem | 34%nat => qc | 35%nat => de | 36%nat => fb + 40 + 24
| 37%nat => p | 38%nat => k | _ => 0 end)) ltac:(first [PMK.sc | unfold PMSRDP.aligned; first [exact A16 | exact AL36] ]).
PMK.pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG1 & _ & FRZ1 & MS1 & KS1 & X1 & X2 & X8 & X9 & X10 & X11 & X12 & X18 & X19 & C40 & C32 & C24 & C16 & C8)); PMK.pvz_clrT.
exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|]. split; [exact FRZ1|].
split. { intros x Hx. apply KS1. revert x Hx. apply (PMPK.sub_in PMSRDP.KS_srAge). vm_compute. reflexivity. }
do 13 (split; [assumption|]). assumption. }
destruct HEAD as (fx1 & R1 & M1 & MS1 & MG1 & FRZ1 & KS1 & X1 & X2 & X8 & X9 & X10 & X11 & X12 & X18 & X19 & C40 & C32 & C24 & C16 & C8).
apply (rd_step LB cr fx fx1 R R1 0x36830 0xa9160 M M1 model K sp fb HH Mh Ml ltac:(lia) ltac:(unfold hl_ceil; lia) ltac:(lia) ltac:(lia) MS1 MG1
(fun i Hi N1 _ => FRZ1 i Hi N1)).
intros HH1.
assert (STK1 : L5C.stk (hl_sptop L) M1 sp 20480) by (apply (PMK.stk_grows L M M1 sp 20480 MG1 STK)).
apply (rd_cpy LB cr fx1 R1 M1 model K p de len1 223352 HH1 Mh Ml ltac:(lia) X10 X11 X12 X1 ltac:(split; [lia| reflexivity])).
{ lia. } { lia. } { lia. } { lia. } { lia. }
{ destruct (apart_pt p len1 de len1 ltac:(lia) ltac:(lia)) as [X|X]; [| left; exact X| right; exact X].
intros a Ha Hd. destruct (DX a ltac:(lia)) as (_ & _ & _ & Y4 & _). apply Y4. lia. }
{ apply (L5.defined_grows M M1 _ _ MG1). apply (L5.defined_sub M p k); [exact DD|lia|lia]. }
{ apply (L5.defined_grows M M1 _ _ MG1). apply (L5.defined_sub M qc 16384); [exact DCH|lia|lia]. }
{ intros a Ha. apply DCW. lia. }
intros R2 M2 MG2 FRZ2 _ KS2 HH2.
assert (STK2 : L5C.stk (hl_sptop L) M2 sp 20480) by (apply (PMK.stk_grows L M1 M2 sp 20480 MG2 STK1)).
assert (AG12 : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (forall i, a <= i < a + n -> ~ (p <= i < p + k)) -> L5C.agree_on M1 M2 a n).
{ intros a n H1 H2 N i Hi. apply FRZ2; [lia|]. intros X. apply (N i Hi). clear - X L1a L1b DP0. lia. }
assert (AG02 : forall a n, sp <= a -> a + n <= 2 ^ 64 -> (forall i, a <= i < a + n -> ~ (p <= i < p + k)) -> L5C.agree_on M M2 a n).
{ intros a n H1 H2 N. apply (L5C.agree_on_trans M M1 M2); [intros i Hi; apply FRZ1; lia| apply AG12; [lia|lia|exact N]]. }
assert (C8' : L5.u64_at RSEGS M2 (sp - 8) (bv_unsigned (getr R (PMK.reg 1)))) by (apply (L5C.u64_at_agree RSEGS M1 M2); [apply AG12; [lia|lia| apply NDR; lia]|lia|lia| exact C8]).
assert (C16' : L5.u64_at RSEGS M2 (sp - 16) (bv_unsigned (getr R (PMK.reg 8)))) by (apply (L5C.u64_at_agree RSEGS M1 M2); [apply AG12; [lia|lia| apply NDR; lia]|lia|lia| exact C16]).
assert (C24' : L5.u64_at RSEGS M2 (sp - 24) (bv_unsigned (getr R (PMK.reg 9)))) by (apply (L5C.u64_at_agree RSEGS M1 M2); [apply AG12; [lia|lia| apply NDR; lia]|lia|lia| exact C24]).
assert (C32' : L5.u64_at RSEGS M2 (sp - 32) (bv_unsigned (getr R (PMK.reg 18)))) by (apply (L5C.u64_at_agree RSEGS M1 M2); [apply AG12; [lia|lia| apply NDR; lia]|lia|lia| exact C32]).
assert (C40' : L5.u64_at RSEGS M2 (sp - 40) (bv_unsigned (getr R (PMK.reg 19)))) by (apply (L5C.u64_at_agree RSEGS M1 M2); [apply AG12; [lia|lia| apply NDR; lia]|lia|lia| exact C40]).
assert (F264 : L5.u64_at RSEGS M2 (fb + 40 + 24 + 264) qc) by (apply (L5C.u64_at_agree RSEGS M M2); [apply AG02; [lia|lia| apply NDR; lia]|lia|lia| exact S264]).
assert (F272 : L5.u64_at RSEGS M2 (fb + 40 + 24 + 272) 16384) by (apply (L5C.u64_at_agree RSEGS M M2); [apply AG02; [lia|lia| apply NDR; lia]|lia|lia| exact S272]).
assert (F280 : L5.u64_at RSEGS M2 (fb + 40 + 24 + 280) de) by (apply (L5C.u64_at_agree RSEGS M M2); [apply AG02; [lia|lia| apply NDR; lia]|lia|lia| exact S280]).
assert (F288 : L5.u64_at RSEGS M2 (fb + 40 + 24 + 288) rem) by (apply (L5C.u64_at_agree RSEGS M M2); [apply AG02; [lia|lia| apply NDR; lia]|lia|lia| exact S288]).
assert (F256 : L5.defined M2 (fb + 40 + 24 + 256) 8).
{ apply (L5.defined_grows M M2); [apply (mem_grows_trans M M1 M2 MG1 MG2)|]. apply (L5.defined_sub M (fb + 40) 384); [exact PDEF|lia|lia]. }
assert (WF2 : L5.writable RSEGS M2 (fb + 40 + 24 + 256) 40).
{ apply (L5.writable_grows RSEGS M M2); [apply (mem_grows_trans M M1 M2 MG1 MG2)| exact WF]. }
assert (WR2 : L5.writable RSEGS M2 (sp - 20480) 20480).
{ apply (L5.writable_grows RSEGS M M2); [apply (mem_grows_trans M M1 M2 MG1 MG2)| exact WR]. }
assert (EK01 : PMK.ek L LB sp 20480 WA M M1) by (apply (rd_ek LB sp fb WA M M1 (fun i Hi N1 _ => FRZ1 i Hi N1) STK BR INWf)).
assert (EK12 : PMK.ek L LB sp 20480 WA M1 M2) by (apply (rd_ek_cpy LB sp p len1 WA M1 M2 FRZ2 STK1 BR); intros a Ha; apply INWd; lia).
destruct (Z.eq_dec len1 k) as [EK|NK].
+
rewrite <- EK in X19.
cfeed P (PMSRDP.srBeq_conc fx1 R2 M2 (fun j => match j with 2%nat => sp | 33%nat => rem | 34%nat => qc | 35%nat => de | 36%nat => fb + 40 + 24
| 37%nat => p | 39%nat => len1
| 40%nat => bv_unsigned (getr R (PMK.reg 1)) | 41%nat => bv_unsigned (getr R (PMK.reg 8)) | 42%nat => bv_unsigned (getr R (PMK.reg 9))
| 43%nat => bv_unsigned (getr R (PMK.reg 18)) | 44%nat => bv_unsigned (getr R (PMK.reg 19)) | _ => 0 end)) ltac:(first [PMK.sc | unfold PMSRDP.aligned; first [exact A16 | exact AL36] ]).
PMK.pvz_hg ltac:(idtac; destruct P as (fx3 & R3 & M3 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG3 & _ & FRZ3 & MS3 & KS3 & T1 & T2 & T8 & T9 & T10 & T11 & T18 & T19 & E288 & E280 & E264 & E272 & _)); PMK.pvz_clrT.
rewrite PMPK.word_id in T1, T8, T9, T18, T19.
apply (rd_step LB cr fx1 fx3 R2 R3 0x36878 0x369ac M2 M3 model K sp fb HH2 Mh Ml ltac:(lia) ltac:(unfold hl_ceil; lia) ltac:(lia) ltac:(lia) MS3 MG3 FRZ3).
intros HH3.
assert (AG03 : forall a n, (fb + 400 <= a /\ a + n <= fb + 752) -> L5C.agree_on M M3 a n).
{ intros a n H. apply (L5C.agree_on_trans M M2 M3); [apply AG02; [lia|lia| apply NDR; lia]|]. intros i Hi; apply FRZ3; lia. }
apply (FIN fx3 R3 M3 (de + len1) (rem - len1) g st len1).
* exact T1.
* intros x Hx. cbn in Hx. repeat (destruct Hx as [<-|Hx]; [first [ rewrite T2; symmetry; exact Rsp | PMK.rk ] |]). destruct Hx.
* exact T10.
* exact E264.
* exact E272.
* exact E280.
* exact E288.
* lia.
* lia.
* lia.
* apply (L5C.u64_at_agree RSEGS M M3); [apply AG03; lia|lia|lia| exact I40].
* apply (PMF.u32_at_agree RSEGS M M3); [apply AG03; lia|lia|lia| replace (fb + 440 + 152) with (fb + 440 + 120 + 32) by lia; exact J32].
* lia.
* exact JST.
* intros E; exact E.
* lia.
* lia.
* lia.
* intros X. exfalso. lia.
* apply (PMK.ek_trans L LB sp 20480 WA M M1 M3 EK01). apply (PMK.ek_trans L LB sp 20480 WA M1 M2 M3 EK12).
apply (rd_ek LB sp fb WA M2 M3 FRZ3 STK2 BR INWf).
* apply (PMK.dk_grows L LB sp 20480 M M3). apply (mem_grows_trans M M1 M3 MG1). apply (mem_grows_trans M1 M2 M3 MG2 MG3).
* apply (PMK.stk_grows L M2 M3 sp 20480 MG3 STK2).
* exact HH3.
+
assert (EL : len1 = rem) by (destruct L1c as [X|X]; [exfalso; apply NK; exact X| exact X]).
rewrite EL in X9.
cfeed P (PMSRDP.srBne_conc fx1 R2 M2 (fun j => match j with 2%nat => sp | 34%nat => qc | 35%nat => de | 36%nat => fb + 40 + 24
| 37%nat => p | 38%nat => k | 39%nat => rem
| 40%nat => bv_unsigned (getr R (PMK.reg 1)) | 41%nat => bv_unsigned (getr R (PMK.reg 8)) | 42%nat => bv_unsigned (getr R (PMK.reg 9))
| 43%nat => bv_unsigned (getr R (PMK.reg 18)) | 44%nat => bv_unsigned (getr R (PMK.reg 19)) | _ => 0 end)) ltac:(first [PMK.sc | unfold PMSRDP.aligned; first [exact A16 | exact AL36] ]).
PMK.pvz_hg ltac:(idtac; destruct P as (fx3 & R3 & M3 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG3 & _ & FRZ3 & MS3 & KS3 & T1 & T10 & T11 & T12 & T19 & E280 & E288 & E264 & E272 & S8 & S16 & S24 & S32 & S40)); PMK.pvz_clrT.
apply (rd_step LB cr fx1 fx3 R2 R3 0x36878 0x36a08 M2 M3 model K sp fb HH2 Mh Ml ltac:(lia) ltac:(unfold hl_ceil; lia) ltac:(lia) ltac:(lia) MS3 MG3 FRZ3).
intros HH3.
apply (FILLC fx3 R3 M3 rem T1); try (PMK.rk; fail); try assumption.
all: lazymatch goal with
| |- forall x, In x _ -> _ => intros x Hx; cbn in Hx; repeat (destruct Hx as [<-|Hx]; [PMK.rk|]); destruct Hx
| |- forall i, 0 <= i < 2 ^ 64 -> _ =>
intros i Hi N1 N2 N3; rewrite FRZ3 by (first [exact Hi | intros X; apply N1; lia | intros X; apply N2; lia]);
rewrite FRZ2 by (first [exact Hi | intros X; apply N3; lia]); apply FRZ1; [exact Hi| intros X; apply N1; lia]
| |- mem_grows _ _ => apply (mem_grows_trans M M1 M3 MG1); apply (mem_grows_trans M1 M2 M3 MG2 MG3)
| _ => lia
end.
-
assert (rem = 0) by lia. subst rem.
destruct (Z.eq_dec k 16384) as [K16|K16].
+
subst k.
destruct JST as [ST0|ST2].
*
subst st.
destruct (D16K eq_refl) as (c0 & n0 & q0 & ETB & W1 & W2).
assert (TIN : In (q0, c0) LB) by (unfold LB, s0, PM.parser_own, PM.vs_own; rewrite ETB; cbn; right; right; left; reflexivity).
cfeed P (PMSRDP.srA0d_conc fx R M (fun j => match j with 2%nat => sp | 34%nat => qc | 35%nat => de | 36%nat => fb + 40 + 24 | 37%nat => p
| 45%nat => fb + 440 | _ => 0 end)) ltac:(first [PMK.sc | unfold PMSRDP.aligned; first [exact A16 | exact AL36 | exact AL37]
| replace (fb + 440 + 152) with (fb + 440 + 120 + 32) by lia; assumption ]).
PMK.pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG1 & _ & FRZ1 & MS1 & KS1 & X1 & X2 & X8 & X9 & X10 & _ & X18 & X19 & C40 & C32 & C24 & C16 & C8)); PMK.pvz_clrT.
apply (rd_step LB cr fx fx1 R R1 0x36830 0x5b254 M M1 model K sp fb HH Mh Ml ltac:(lia) ltac:(unfold hl_ceil; lia) ltac:(lia) ltac:(lia) MS1 MG1
(fun i Hi N1 _ => FRZ1 i Hi N1)).
intros HH1.
assert (STK1 : L5C.stk (hl_sptop L) M1 sp 20480) by (apply (PMK.stk_grows L M M1 sp 20480 MG1 STK)).
assert (EK1 : PMK.ek L LB sp 20480 [] M M1).
{ apply (PMFR.ek_of_piece RSEGS L KL LB sp 20480 M M1 (fun a => sp - 48 <= a < sp - 48 + 48)
ltac:(intros a Ha N; apply FRZ1; [exact Ha| exact N]) STK (PMFR.brange_hi L LB BR)). intros a Pa. lia. }
assert (WHI0 : forall a, PMK.inW [] a -> sp <= a \/ hl_img_lo L <= a < hl_img_hi L) by (intros a I; destruct (PMFR.inW_nil a I)).
assert (IA1 : PM.iss_at RSEGS AD PMSP.T3 M1 (fb + 440) str (PM.STRM g eg 0)).
{ apply (PMFR.iss_keep RSEGS AD L KL LB sp 20480 [] M M1 EK1 STK SC0 BR WHI0); [lia|lia| intros i _; apply PMFR.inW_nil| exact SINC| exact IA]. }
assert (BASE1 : PMST.base_ok RSEGS AD M1).
{ apply (PMKP.base_ok_keep RSEGS AD L KL SF LB sp 20480 [] M M1 EK1); first [exact BASE | intros a _; apply L5C.outside_nil]. }
assert (STKc : L5C.stk (hl_sptop L) M1 (sp - 48) 16384).
{ apply (PMK.stk_call L M1 sp 20480 (sp - 48) 16384 STK1); [lia|lia|lia|]. replace (sp - 48) with (sp + (-3) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
assert (APG : p + 16384 <= g \/ eg <= p).
{ pose proof (PMPK.iss_unread_where RSEGS AD M (fb + 440) str _ IA) as [(Y1 & Y2)|(c1 & n1 & q1 & -> & Y1 & Y2)]; cbn [PM.sm_g PM.sm_eg] in *.
- left. destruct (BR _ _ TIN) as (_ & _ & Z4). unfold hl_ceil in Z4. lia.
- pose proof IA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & VS & _). destruct VS as (_ & _ & _ & _ & _ & _ & HC1 & _).
destruct (apart_pt p 16384 q1 c1 ltac:(lia) ltac:(lia)) as [X|X]; [| left; lia| right; lia].
intros a Ha. destruct (DX a Ha) as (_ & _ & _ & _ & _ & Y6 & _). exact (Y6 c1 n1 q1 eq_refl). }
unfold PMPSS.xsgetn_spec, PMPS.xsgetn_spec in XS. cbn [pa_xsgetn AD PmLayoutS.ADDR_S] in XS.
apply (XS fx1 R1 M1 model K LB cr (sp - 48) 223560 (fb + 440) p str (PM.STRM g eg 0) HH1 MOK K0).
{ unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact X1|]. split; [split; [lia| reflexivity]|]. split; [exact X2|].
split; [rewrite (KS1 3%nat) by PMK.inl; exact Rgp|]. split; [rewrite (KS1 4%nat) by PMK.inl; exact Rtp|]. exact STKc. }
{ rewrite L5K.rl10. exact X10. }
{ rewrite L5K.rl11. rewrite (KS1 11%nat) by PMK.inl. exact A11. }
{ rewrite L5K.rl12. rewrite (KS1 12%nat) by PMK.inl. exact A12. }
{ lia. } { lia. } { exact AL37. } { exact IA1. } { exact BASE1. } { exact SINC. }
{ exists q0, c0. split; [exact TIN| unfold PM.CHUNK; lia]. }
{ unfold PM.CHUNK. cbn [PM.sm_g PM.sm_eg]. exact APG. }
cbn [PM.sm_g PM.sm_eg PM.sm_st]. unfold PM.CHUNK.
intros fx2 R2 M2 c RP2 Y10 CEQ IA2 DD2 HP2 HH2.
rewrite L5K.rl10 in Y10. change (PMSP.pm_scr 2) with 16384 in HP2.
assert (CR : 0 <= c <= 16384) by (clear - CEQ SZ; Lia.lia).
set (Wx := [(fb + 440 + 40, 8); (p, 16384)] : list L5.range).
assert (WCx : forall a, PMK.inW Wx a -> (fb + 480 <= a < fb + 488) \/ (p <= a < p + 16384)).
{ intros a (r0 & Hin & Hr). unfold Wx in Hin. unfold L5.in_rng in Hr. destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; lia. }
assert (EKc : PMK.ek L LB (sp - 48) 16384 Wx M1 M2) by (apply (PMK.ek_of_hpres L); exact HP2).
assert (SCc : 0 <= 16384) by lia.
assert (STK2 : L5C.stk (hl_sptop L) M2 sp 20480) by (apply (PMK.stk_after RSEGS L KL LB M1 M2 sp 20480 (sp - 48) 16384 Wx STK1 HP2); lia).
pose proof (L5C.stk_writable RSEGS _ M2 sp 20480 STK2) as WR2.
assert (HI2 : forall a n, sp - 48 <= a -> a + n <= 2 ^ 64 -> (a + n <= fb + 480 \/ fb + 488 <= a) -> L5C.agree_on M1 M2 a n).
{ intros a n H1 H2 H3. apply (PMPK.ag_hi RSEGS L KL LB (sp - 48) 16384 Wx M1 M2 EKc STKc SCc a n H1 H2). intros i Hi I. apply WCx in I.
destruct I as [I|I]; [clear - Hi I H3; lia|]. destruct (BR _ _ TIN) as (_ & _ & Z4). clear - Hi I H1 W1 W2 Z4 SLO. unfold hl_ceil in *. lia. }
assert (BASE2 : PMST.base_ok RSEGS AD M2).
{ apply (PMKP.base_ok_keep RSEGS AD L KL SF LB (sp - 48) 16384 Wx M1 M2 EKc); [| | | | exact BASE1].
all: intros a Ha; apply PMFR.outside_of_not_inW; intros I; apply WCx in I; pose proof (DXI a) as Y;
cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock AD PmLayoutS.ADDR_S] in Ha.
all: destruct I as [I|I]; [clear - I Ha SLO F1 STOP; lia| apply (Y I); rewrite (ly_img_lo L LY), (ly_img_hi L LY); clear - Ha; lia]. }
pose proof BASE2 as (IMG2 & _). cbn [pa_rw_lo AD PmLayoutS.ADDR_S] in IMG2.
pose proof IA2 as (K0' & _ & _ & K16 & _ & _ & K40 & _ & _ & _ & _ & _ & KIOS & _ & KE2).
destruct KIOS as (_ & L32 & L36 & L40 & _ & _ & LD & _ & _).
cbn [PM.sm_g PM.sm_eg PM.sm_st pa_vp_iss pa_vp_strbuf pa_vp_iss_ios AD PmLayoutS.ADDR_S] in *.
assert (R2_2 : getr R2 (PMK.reg 2) = Z_to_bv 64 (sp - 48)) by (rewrite (PMK.cs_of_preserved R1 R2 2%nat RP2) by PMK.inl; exact X2).
assert (R2_8 : getr R2 (PMK.reg 8) = Z_to_bv 64 (fb + 40 + 24)) by (rewrite (PMK.cs_of_preserved R1 R2 8%nat RP2) by PMK.inl; exact X8).
assert (R2_9 : getr R2 (PMK.reg 9) = Z_to_bv 64 0) by (rewrite (PMK.cs_of_preserved R1 R2 9%nat RP2) by PMK.inl; exact X9).
assert (R2_18 : getr R2 (PMK.reg 18) = Z_to_bv 64 p) by (rewrite (PMK.cs_of_preserved R1 R2 18%nat RP2) by PMK.inl; exact X18).
assert (R2_19 : getr R2 (PMK.reg 19) = Z_to_bv 64 16384) by (rewrite (PMK.cs_of_preserved R1 R2 19%nat RP2) by PMK.inl; exact X19).
assert (AG02 : forall a n, sp <= a -> a + n <= 2 ^ 64 -> (a + n <= fb + 480 \/ fb + 488 <= a) -> L5C.agree_on M M2 a n).
{ intros a n H1 H2 H3. apply (L5C.agree_on_trans M M1 M2); [intros i Hi; apply FRZ1; lia| apply HI2; lia]. }
assert (C8' : L5.u64_at RSEGS M2 (sp - 8) (bv_unsigned (getr R (PMK.reg 1)))) by (apply (L5C.u64_at_agree RSEGS M1 M2); [apply HI2; lia|lia|lia| exact C8]).
assert (C16' : L5.u64_at RSEGS M2 (sp - 16) (bv_unsigned (getr R (PMK.reg 8)))) by (apply (L5C.u64_at_agree RSEGS M1 M2); [apply HI2; lia|lia|lia| exact C16]).
assert (C24' : L5.u64_at RSEGS M2 (sp - 24) (bv_unsigned (getr R (PMK.reg 9)))) by (apply (L5C.u64_at_agree RSEGS M1 M2); [apply HI2; lia|lia|lia| exact C24]).
assert (C32' : L5.u64_at RSEGS M2 (sp - 32) (bv_unsigned (getr R (PMK.reg 18)))) by (apply (L5C.u64_at_agree RSEGS M1 M2); [apply HI2; lia|lia|lia| exact C32]).
assert (C40' : L5.u64_at RSEGS M2 (sp - 40) (bv_unsigned (getr R (PMK.reg 19)))) by (apply (L5C.u64_at_agree RSEGS M1 M2); [apply HI2; lia|lia|lia| exact C40]).
assert (F264 : L5.u64_at RSEGS M2 (fb + 40 + 24 + 264) qc) by (apply (L5C.u64_at_agree RSEGS M M2); [apply AG02; lia|lia|lia| exact S264]).
assert (F272 : L5.u64_at RSEGS M2 (fb + 40 + 24 + 272) 16384) by (apply (L5C.u64_at_agree RSEGS M M2); [apply AG02; lia|lia|lia| exact S272]).
assert (F280 : L5.u64_at RSEGS M2 (fb + 40 + 24 + 280) de) by (apply (L5C.u64_at_agree RSEGS M M2); [apply AG02; lia|lia|lia| exact S280]).
assert (F288 : L5.u64_at RSEGS M2 (fb + 40 + 24 + 288) 0) by (apply (L5C.u64_at_agree RSEGS M M2); [apply AG02; lia|lia|lia| exact S288]).
assert (F240 : L5.u64_at RSEGS M2 (fb + 40 + 24 + 240) (fb + 440)) by (apply (L5C.u64_at_agree RSEGS M M2); [apply AG02; lia|lia|lia| exact S240]).
assert (F248 : L5.u64_at RSEGS M2 (fb + 40 + 24 + 248) (fb + 440 + 16)) by (apply (L5C.u64_at_agree RSEGS M M2); [apply AG02; lia|lia|lia| exact S248]).
assert (F256 : L5.defined M2 (fb + 40 + 24 + 256) 8).
{ apply (L5C.defined_agree M M2); [apply AG02; lia|]. apply (L5.defined_sub M (fb + 40) 384); [exact PDEF|lia|lia]. }
assert (WF2 : L5.writable RSEGS M2 (fb + 40 + 24 + 256) 40).
{ apply (L5C.writable_of_defined RSEGS); [|lia|lia]. apply (L5C.defined_agree M M2); [apply AG02; lia|]. apply (L5.defined_sub M (fb + 40) 384); [exact PDEF|lia|lia]. }
assert (EK2 : PMK.ek L LB sp 20480 WA M1 M2).
{ apply (PMK.ek_callee_in' RSEGS L KL LB LB sp 20480 (sp - 48) 16384 WA Wx M1 M2 HP2 (incl_refl _)); [lia|lia|unfold hl_ceil; lia|lia| exact (PMFR.brange_hi L LB BR)|].
intros a I. right. apply WCx in I. destruct I as [I|I]; [apply INWg; lia| apply INWd; lia]. }
assert (EK01 : PMK.ek L LB sp 20480 WA M M1).
{ apply (PMK.ek_weaken L LB LB sp 20480 sp 20480 WA [] M M1 EK1); [apply incl_refl| intros x Hx; exact Hx|]. intros a _. apply L5C.outside_nil. }
destruct (Z.eq_dec c 16384) as [E16|N16].
--
revert E16 Y10 CEQ CR DD2. intros -> Y10 CEQ CR DD2.
cfeed P (PMSRDP.srE1_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 34%nat => qc | 35%nat => de | 36%nat => fb + 40 + 24 | 37%nat => p
| 40%nat => bv_unsigned (getr R (PMK.reg 1)) | 41%nat => bv_unsigned (getr R (PMK.reg 8)) | 42%nat => bv_unsigned (getr R (PMK.reg 9))
| 43%nat => bv_unsigned (getr R (PMK.reg 18)) | 44%nat => bv_unsigned (getr R (PMK.reg 19)) | 45%nat => fb + 440 | _ => 0 end)) ltac:(first [PMK.sc | unfold PMSRDP.aligned; first [exact A16 | exact AL36 | exact AL37]
| replace (fb + 440 + 152) with (fb + 440 + 120 + 32) by lia; assumption
| replace (fb + 440 + 156) with (fb + 440 + 120 + 36) by lia; assumption
| replace (fb + 440 + 160) with (fb + 440 + 120 + 40) by lia; assumption ]).
PMK.pvz_hg ltac:(idtac; destruct P as (fx3 & R3 & M3 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG3 & _ & FRZ3 & MS3 & KS3 & T1 & T2 & T8 & T9 & T18 & T19 & E264 & E272 & E280 & E288 & _)); PMK.pvz_clrT.
rewrite PMPK.word_id in T1, T8, T9, T18, T19.
apply (rd_step LB cr fx2 fx3 R2 R3 0x36948 0x369ac M2 M3 model K sp fb HH2 Mh Ml ltac:(lia) ltac:(unfold hl_ceil; lia) ltac:(lia) ltac:(lia) MS3 MG3 FRZ3).
intros HH3.
apply (FIN fx3 R3 M3 de 0 (g + 16384) 0 16384).
++ exact T1.
++ intros x Hx. cbn in Hx. repeat (destruct Hx as [<-|Hx]; [first [ rewrite T2; symmetry; exact Rsp | PMK.rk ] |]). destruct Hx.
++ rewrite (KS3 10%nat) by PMK.inl. exact Y10.
++ exact E264.
++ exact E272.
++ exact E280.
++ exact E288.
++ lia.
++ lia.
++ lia.
++ apply (L5C.u64_at_agree RSEGS M2 M3); [intros i Hi; apply FRZ3; lia|lia|lia| exact K40].
++ apply (PMF.u32_at_agree RSEGS M2 M3); [intros i Hi; apply FRZ3; lia|lia|lia| replace (fb + 440 + 152) with (fb + 440 + 120 + 32) by lia; exact L32].
++ clear - CEQ SZ. Lia.lia.
++ left. reflexivity.
++ intros E; discriminate E.
++ lia.
++ lia.
++ lia.
++ intros X. exfalso. lia.
++ apply (PMK.ek_trans L LB sp 20480 WA M M1 M3 EK01). apply (PMK.ek_trans L LB sp 20480 WA M1 M2 M3 EK2).
apply (rd_ek LB sp fb WA M2 M3 FRZ3 STK2 BR INWf).
++ apply (PMK.dk_trans L LB sp 20480 M M1 M3); [apply (PMK.dk_grows L LB sp 20480 M M1 MG1)|].
apply (PMK.dk_trans L LB sp 20480 M1 M2 M3); [|apply (PMK.dk_grows L LB sp 20480 M2 M3 MG3)].
apply (PMK.dk_callee L LB LB sp 20480 (sp - 48) 16384 Wx M1 M2 HP2 (incl_refl _)); lia.
++ apply (PMK.stk_grows L M2 M3 sp 20480 MG3 STK2).
++ exact HH3.
--
cfeed P (PMSRDP.srE2_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 33%nat => c | 34%nat => qc | 35%nat => de | 36%nat => fb + 40 + 24 | 37%nat => p
| 40%nat => bv_unsigned (getr R (PMK.reg 1)) | 41%nat => bv_unsigned (getr R (PMK.reg 8)) | 42%nat => bv_unsigned (getr R (PMK.reg 9))
| 43%nat => bv_unsigned (getr R (PMK.reg 18)) | 44%nat => bv_unsigned (getr R (PMK.reg 19)) | 45%nat => fb + 440 | _ => 0 end)) ltac:(first [PMK.sc | unfold PMSRDP.aligned; first [exact A16 | exact AL36 | exact AL37]
| replace (fb + 440 + 152) with (fb + 440 + 120 + 32) by lia; assumption
| replace (fb + 440 + 156) with (fb + 440 + 120 + 36) by lia; assumption
| replace (fb + 440 + 160) with (fb + 440 + 120 + 40) by lia; assumption
| apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M2 (fb + 440 + 120) 152); [exact LD|lia|lia]|lia|lia] ]).
PMK.pvz_hg ltac:(idtac; destruct P as (fx3 & R3 & M3 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG3 & _ & FRZ3 & MS3 & KS3 & T1 & T2 & T8 & T9 & _ & _ & _ & T18 & T19 & E152 & E264 & E272 & E280 & E288 & _)); PMK.pvz_clrT.
rewrite PMPK.word_id in T1, T8, T9, T18, T19.
set (P3 := fun a => (sp - 48 <= a < sp - 48 + 48) \/ (fb + 40 + 24 + 256 <= a < fb + 40 + 24 + 256 + 40) \/ (fb + 440 + 152 <= a < fb + 440 + 152 + 4)).
assert (FRZ3' : forall a, 0 <= a < 2 ^ 64 -> ~ P3 a -> M3 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)).
{ intros a Ha N. apply FRZ3; [exact Ha| | |]; intros X; apply N; unfold P3; [left| right; left| right; right]; exact X. }
apply (PMK.spiece RSEGS L HI KL HIok LB cr M2 model fx2 fx3 R2 0x36948 R3 0x369ac M3 P3 K HH2 Mh Ml ltac:(lia) MS3 MG3 FRZ3').
{ intros a Pa. apply (PMK.cwr_stack L LB M sp 20480 a STK). unfold P3 in Pa. lia. }
{ intros a. apply PMK.or_dec; [apply PMK.rng_dec| apply PMK.or_dec; apply PMK.rng_dec]. }
intros HH3.
apply (FIN fx3 R3 M3 de 0 (g + c) 2 c).
++ exact T1.
++ intros x Hx. cbn in Hx. repeat (destruct Hx as [<-|Hx]; [first [ rewrite T2; symmetry; exact Rsp | PMK.rk ] |]). destruct Hx.
++ rewrite (KS3 10%nat) by PMK.inl. exact Y10.
++ exact E264.
++ exact E272.
++ exact E280.
++ exact E288.
++ lia.
++ lia.
++ lia.
++ apply (L5C.u64_at_agree RSEGS M2 M3); [intros i Hi; apply FRZ3; lia|lia|lia| exact K40].
++ exact E152.
++ clear - CEQ SZ. Lia.lia.
++ right. reflexivity.
++ intros _. reflexivity.
++ lia.
++ lia.
++ lia.
++ intros _. split; reflexivity.
++ apply (PMK.ek_trans L LB sp 20480 WA M M1 M3 EK01). apply (PMK.ek_trans L LB sp 20480 WA M1 M2 M3 EK2).
apply (PMK.ek_piece_in RSEGS L KL LB sp 20480 WA M2 M3 P3 FRZ3' STK2 (PMFR.brange_hi L LB BR)).
intros a [Pa|[Pa|Pa]]; [left; lia| right; apply INWf; lia| right; apply INWs; lia].
++ apply (PMK.dk_trans L LB sp 20480 M M1 M3); [apply (PMK.dk_grows L LB sp 20480 M M1 MG1)|].
apply (PMK.dk_trans L LB sp 20480 M1 M2 M3); [|apply (PMK.dk_grows L LB sp 20480 M2 M3 MG3)].
apply (PMK.dk_callee L LB LB sp 20480 (sp - 48) 16384 Wx M1 M2 HP2 (incl_refl _)); lia.
++ apply (PMK.stk_grows L M2 M3 sp 20480 MG3 STK2).
++ exact HH3.
*
subst st.
cfeed P (PMSRDP.srA0e_conc fx R M (fun j => match j with 2%nat => sp | 34%nat => qc | 35%nat => de | 36%nat => fb + 40 + 24 | 37%nat => p
| 45%nat => fb + 440 | _ => 0 end)) ltac:(first [PMK.sc | unfold PMSRDP.aligned; first [exact A16 | exact AL36 | exact AL37]
| replace (fb + 440 + 152) with (fb + 440 + 120 + 32) by lia; assumption ]).
PMK.pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG1 & _ & FRZ1 & MS1 & KS1 & X10 & X11 & C288 & C40 & C32 & C24 & C16 & C8 & C264 & C272 & C280 & _)); PMK.pvz_clrT.
apply (rd_step LB cr fx fx1 R R1 0x36830 0x369ac M M1 model K sp fb HH Mh Ml ltac:(lia) ltac:(unfold hl_ceil; lia) ltac:(lia) ltac:(lia) MS1 MG1 FRZ1).
intros HH1.
apply (FIN fx1 R1 M1 de 0 g 2 0).
-- rewrite (KS1 1%nat) by PMK.inl. reflexivity.
-- intros x Hx. apply KS1. revert x Hx. apply (PMPK.sub_in PMSRDP.KS_srA0e). vm_compute. reflexivity.
-- exact X10.
-- exact C264.
-- exact C272.
-- exact C280.
-- exact C288.
-- lia.
-- lia.
-- lia.
-- apply (L5C.u64_at_agree RSEGS M M1); [intros i Hi; apply FRZ1; lia|lia|lia| exact I40].
-- apply (PMF.u32_at_agree RSEGS M M1); [intros i Hi; apply FRZ1; lia|lia|lia| replace (fb + 440 + 152) with (fb + 440 + 120 + 32) by lia; exact J32].
-- lia.
-- right. reflexivity.
-- intros E; exact E.
-- lia.
-- lia.
-- lia.
-- intros _. split; reflexivity.
-- apply (rd_ek LB sp fb WA M M1 FRZ1 STK BR INWf).
-- apply (PMK.dk_grows L LB sp 20480 M M1 MG1).
-- apply (PMK.stk_grows L M M1 sp 20480 MG1 STK).
-- exact HH1.
+
cfeed P (PMSRDP.srA0f_conc fx R M (fun j => match j with 2%nat => sp | 34%nat => qc | 35%nat => de | 36%nat => fb + 40 + 24 | 37%nat => p | 38%nat => k | _ => 0 end)) ltac:(first [PMK.sc | unfold PMSRDP.aligned; first [exact A16 | exact AL36] ]).
PMK.pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG1 & _ & FRZ1 & MS1 & KS1 & X1 & X2 & X8 & X9 & X11 & X12 & X18 & X19 & C280 & C40 & C32 & C24 & C16 & C8 & C264 & C272 & C288 & _)); PMK.pvz_clrT.
apply (rd_step LB cr fx fx1 R R1 0x36830 0x36a08 M M1 model K sp fb HH Mh Ml ltac:(lia) ltac:(unfold hl_ceil; lia) ltac:(lia) ltac:(lia) MS1 MG1 FRZ1).
intros HH1.
apply (FILLC fx1 R1 M1 0 X1 X2 X8 X9); try assumption.
all: lazymatch goal with
| |- getr _ (PMK.reg 10) = _ => rewrite (KS1 10%nat) by PMK.inl; exact A10
| |- getr _ (PMK.reg 19) = _ => rewrite Z.sub_0_r; exact X19
| |- forall x, In x _ -> _ => intros x Hx; apply KS1; revert x Hx; apply (PMPK.sub_in PMSRDP.KS_srA0f); vm_compute; reflexivity
| |- forall i, 0 <= i < 2 ^ 64 -> _ => intros i Hi N1 N2 N3; apply FRZ1; [exact Hi| intros X; apply N1; lia| intros X; apply N2; lia]
| _ => lia
end.
Qed.
End WithHeap.
End PMSRD.
