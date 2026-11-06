(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceAB0 LibIface
AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsAB0 L5CoreAB0 L5CoreSpecsAB0 L5StepARB0 L5CoreBRB0 L5ADetailHRB0
PmLayout PmLayoutA PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceAJx PmSpecsA PmSpecsAX PmSpecsAb PmSpecsBX PmBPushQ
PmModelFactsA PmStepAB0 PmStep PmParStep PmParKit PmBSrcKit PmBParKit PmBReset1 PmBUarK PmBUar PmBUarKS PmBBaK PmBBaK2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmBBaK3 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBBaK.PMBBK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBBaK3.PMBBK3."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBBaK3.PMBBK3.WithHeap.Call.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBPushQ.PMBPQ."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModelFactsA.PMFA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsAX.PMSAX."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A0"; "0Ac"; "0Aw"; "0Aw'"; "0Aw0"; "0BX"; "1app"; "1bool"; "1cons"; "1false"; "1length"; "1list"; "1nil"; "1option"; "1prod"; "2and"]; ["2eq"; "2not"; "3Z"; "0F"; "0FF"; "0FF1"; "0HI"; "0K"; "0L"; "0LBX"; "0LK"; "0LK'"; "0LK0"; "0LKc"; "4Model"; "5bvmap"]; ["0M"; "0M'"; "0M0"; "0Mc"; "0Q"; "0R"; "0R'"; "0R0"; "6mrestrict"; "7credit"; "7regs_preserved"; "8aacc"; "8acredit_ok"; "8adebit"; "8ahid"; "8fframe"]; ["8ri_inv"; "8vml"; ":defined"; ":ra_ok"; ":u64_at"; "9SCFG"; ";FF'"; ";binv'"; ";bst"; ";bst0"; ";op"; ";ov"; "=bstp"; "<push_st"; ">pushq_spec_at"; "?ADDR_B"]; ["@CHUNK"; "@MAX_DEPTH"; "@VLong"; "@mode_bottom"; "@mode_counted"; "@p_b"; "@p_k"; "@p_src"; "@p_stk"; "@p_tb"; "@p_tg"; "@parser_at"; "@pot_parser"; "@ps_idx"; "@ps_mode"; "@pst"]; ["@pstate"; "@pstate_ok"; "@sr_qc"; "@srcst"; "@stack_shape"; "@strm"; "@tb_ok"; "@unread"; "@vec_at"; "@vec_own"; "@vs_cap"; "@vstr"; "AagA"; "Aagsh"; "BHV"; "BaccA"]; ["BannA"; "Bcfg"; "Bcredit_keep"; "Bcredit_le"; "BscA"; "Cpush_out"; "DFPState"; "Dgetr"; "Esrealizes"; "Floaded_segments"; "0S"; "0SCFG_P"; "0SPEC"; "Gadd"; "Gle"; "Glt"]; ["Gmul"; "Gof_nat"; "Gpow"; "Gsub"; "0V"; "0X"; "0a"; "0a'"; "0ar"; "0b'"; "0c"; "0c0"; "0cat"; "0cells"; "0cr"; "0cr'"]; ["0cr0"; "0crc"; "0e"; "0e0"; "0fb"; "0fx"; "0fx'"; "0k"; "0k'"; "0l"; "0model'"; "0model0"; "0modelc"; "0n"; "0ois"; "0op"]; ["0p"; "0pc"; "0s"; "0s'"; "0s0"; "0sm"; "0sm0"; "HZ_to_bv"; "Hbv"; "0stk"; "0str"; "0typed"; "0x"; "0y"]]).
Local Ltac lia := L5FastLia.plia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PMBBK3.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation AD := PMB.AD.
Definition push_st (s : PM.pst) (b k : Z) (c : PM.pstate) : PM.pst :=
PM.PST (PM.p_more s) (PM.p_done s) (PM.p_depth s) (PM.p_src s) (PM.p_tb s) (PM.p_tg s) b k (PM.p_stk s ++ [c]).
Lemma aacc_sub : ltac2:(TCodec.tc2 tcn__PmBBaK3 "O'THyR0%211'=y8%511%311p051'B&Q;r5r4r3%43321&S>%1253&S=%1265r6%3219%6231r8%=31<;p031p091p0<1pXBB1pW@C1pX@D1pW>E1pR2G1").
Proof. intros M a k a' k'. intros AC H1 H2 x Hx. apply AC. lia. Qed.
Lemma parser_push_updA : ltac2:(TCodec.tc2 tcn__PmBBaK3 "SA'THyR0%211'=y8%511%311p051'B'R?'R@&R;&S9&QO&RO&S0r8r6r5r4%9887654321&S>zr7%3221&S=+\0%22;1&SB+2+R0%3221%;251&RLr;r:r9+[8%544321&RMr<%24176?&QB%1339A&RHr=%E269&6&R8%11>(8(<%11Q:%33Q;N1%73Q<51%;8Q;Q9Q8:9CQ71&RB&R7%11H%311%Q72Q61%41E%611&R0%Q7221%Q<21Q2rAr@%;1G%=11%Q544317'@'RK&R9%118(R2r3r2r1%43321%93861rFrE%QB4216R0p041pY2R=1pXLR>1pWHR?1rB&QMr?r>%3421Q?QD%RB8RAR@R?R>5KJ1p071p0I1p0O1p0Q51p0Q;1p0QH1p0QK1p0QO1p0R61p0R?1p0RD1pWFRO1pXBS21pWDS31pY6S31pXNS51pY0S61pR4S81pR2S91").
Proof. intros M M' op ois s b' k' c.
intros (H0 & D & C24 & H8 & H9 & H12 & H16 & H20 & NI & SRC & H320 & H328 & C320 & TB & VEC & B1 & B2 & B3) Ho Ho' AG SH D' VEC' Hq Hq' AGQ AGT.
pose proof AG as [AGd _].
unfold push_st, PM.parser_at. cbn [PM.p_more PM.p_done PM.p_depth PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk].
assert (AG4 : forall a n, op <= a -> a + n <= op + 360 -> PMFA.agA M M' a n).
{ intros a n X1 X2. split; [eapply (L5C.agree_on_sub M M'); [exact AGd|lia|lia]| intros x Hx; apply SH; lia]. }
split; [apply (L5C.u64_at_agree RSEGS M M'); [apply (AG4 op 8); lia| lia| lia| exact H0]|].
split; [exact D'|].
split; [apply (PMFA.accA_agree M M' op 24); [intros x Hx; apply SH; lia| exact C24]|].
split; [apply (L5C.u8_at_agree RSEGS M M'); [apply (AG4 (op + 8) 1); lia|lia|lia|exact H8]|].
split; [apply (L5C.u8_at_agree RSEGS M M'); [apply (AG4 (op + 9) 1); lia|lia|lia|exact H9]|].
split; [apply (PMF.u32_at_agree RSEGS M M'); [apply (AG4 (op + 12) 4); lia|lia|lia|exact H12]|].
split; [apply (L5C.u8_at_agree RSEGS M M'); [apply (AG4 (op + 16) 1); lia|lia|lia|exact H16]|].
split; [apply (PMF.u32_at_agree RSEGS M M'); [apply (AG4 (op + 20) 4); lia|lia|lia|exact H20]|].
split; [apply (PMFA.nullis_at_agreeA RSEGS PMB.AD M M' (op + 32)); [lia|lia| apply AG4; lia| exact NI]|].
split; [apply (PMFA.src_fields_at_agreeA RSEGS M M' (op + 24)); [lia|lia|exact Hq|exact Hq'| apply AG4; lia| exact AGQ| exact SRC]|].
split; [apply (PMF.u32_at_agree RSEGS M M'); [apply (AG4 (op + 320) 4); lia|lia|lia|exact H320]|].
split; [apply (L5C.u64_at_agree RSEGS M M'); [apply (AG4 (op + 328) 8); lia|lia|lia|exact H328]|].
split; [apply (PMFA.accA_agree M M' (op + 320) 64); [intros x Hx; apply SH; lia| exact C320]|].
split; [apply (PMFA.vstr_at_agreeA RSEGS M M' (op + 336)); [lia|lia| apply AG4; lia| exact AGT| exact TB]|].
split; [exact VEC'|].
split; [exact B1|]. split; [exact B2| exact B3].
Qed.
Lemma stack_shape_push : ltac2:(TCodec.tc2 tcn__PmBBaK3 "Q6';'R@%211&RDr2%211&S>&SA&:r3%2291%411&R1%7221&RA%116&A&R3&R>r4%211%411%611&6r6(8r5(<%11K%43L31%73M61%L11p0:1p0B1p0E1p0N1pWFQ31pYDQ31").
Proof. intros stk c.
intros (H1 & H2 & H3 & H4 & H5) HL Hc Hm. unfold PM.stack_shape. rewrite length_app. cbn [length].
split; [lia|]. split; [rewrite Nat2Z.inj_add; cbn; unfold PM.MAX_DEPTH in *; lia|].
split; [rewrite app_nth1 by lia; exact H3|].
split.
- intros i Hi. destruct (Nat.lt_ge_cases i (length stk)) as [Lt|Ge].
+ rewrite app_nth1 by exact Lt. apply H4. lia.
+ assert (E : i = length stk) by lia. subst i. rewrite app_nth2 by lia. rewrite Nat.sub_diag. exact Hm.
- intros i Hi. destruct (Nat.lt_ge_cases i (length stk)) as [Lt|Ge].
+ rewrite app_nth1 by exact Lt. apply H5. exact Lt.
+ assert (E : i = length stk) by lia. subst i. rewrite app_nth2 by lia. rewrite Nat.sub_diag. exact Hc.
Qed.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMB.ly_as0 L C LY.
Lemma ri_swap12 : ltac2:(TCodec.tc2 tcn__PmBBaK3 "Q>'>'B%2211';%112&Q?%311&Q9'THyR0%211'=y8%511%311p051&QA&Q@vF(8r9r8r7%43E21%53F41r6r5r4r3r2r1%>8=7654321r:%>3O1<%?3Q0>1%B8A1=:9876p051pW:E1pR2G1p6Q31pWNQ11pQFQ31pQ<Q41pXDQ71pYLQ:1pYJQ;1").
Proof. intros x y l FF1 LK cr Aw M V. exact (PMBRS1.ri_swap12 L ar C HI HIok x y l FF1 LK cr Aw M V). Qed.
Lemma stk_credit : ltac2:(TCodec.tc2 tcn__PmBBaK3 "RJ'R?&Q9&RF&R9r2%211&R:%113%6231&S>&RJr3%911%311&SB+2+K%3221%9251'?z&R6r4%211%?241+:%A231%8231&S3&S4vH&R<&RNvSH%2241r5%5221%8271%:21@&Q<&S@+Q0&S=r6%G11+1%4221%Q12Q01%8271%:3C>1'@'Br1%Q011r7%Q211%>21;%73641'RKr8%QI11%;33QH1%QH1QCr9%QJ11%?3>31&S2&Q=r:%Q@11%L21I%QI2QH1%Q02O1%63Q;:1%Q;2Q86%Q>2Q=1%Q=2Q:QF%Q@2Q?1%<4?531p0>1p0C1p0H1pY8RB1%R02Q21p0Q>1p0QJ1p0R41p0R?1pX4RG1pY6RI1").
Proof. intros s crc.
intros (Tg & Tc & _) Cap Hk (CR1 & CR2). pose proof (PMB.ly_cost L C LY) as (K8 & B3 & BO).
assert (P : 2 ^ (PM.p_k s + 1 + 1) = 2 * 2 ^ (PM.p_k s + 1)) by (rewrite Z.pow_add_r by lia; lia).
assert (P11 : 2 ^ (PM.p_k s + 1) <= 2048) by (change 2048 with (2 ^ 11); apply Z.pow_le_mono_r; lia).
assert (P0 : 1 <= 2 ^ (PM.p_k s + 1)) by (apply (Zpow_facts.Zpower_le_monotone 2 0 (PM.p_k s + 1)); lia).
unfold PMSPA.scA, PM.pot_parser, PM.credit_add, PM.pot_stack, PM.pot_text, PMSPA.HV, LibIfaceAJ.heap_view in *.
cbn [fst snd HeapIface.hl_k_per_malloc HeapIface.hl_b_overhead] in *. rewrite K8, B3, BO in *.
split.
- unfold acredit_ok. rewrite K8, B3, BO. split; lia.
- intros s' Ek Et Eg. unfold PMSPA.credit_keep, adebit. rewrite K8, B3, BO. cbn [fst snd]. rewrite Ek, Et, Eg, P. split; lia.
Qed.
Section Call.
Variables (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet) (LBX : list (Z * Z)) (FF LK0 : list fframe) (Aw0 : list (Z * Z)) (cr0 : credit).
Variables (S r fb cat : Z) (s0 : PM.pst) (str : PM.vstr) (sm0 : PM.strm) (e0 : bool).
Hypothesis HH0 : ri_inv HI (PM.parser_own s0 ++ LBX) FF LK0 cr0 Aw0 M0 (vml_of model0).
Hypothesis AM0 : L5CA.amodel_ok Aw0 model0.
Hypothesis K0 : K [].
Hypothesis ENT : PMSPA.entryA AD L ar R0 M0 S r 7.
Hypothesis FRM : PMSPA.ffroomA 7 FF LK0.
Hypothesis FRS : PMSPA.ffrsA FF S.
Hypothesis FOK : PMSPA.frame_okA FF fb.
Hypothesis SP32 : S mod 32 = 0.
Hypothesis ARGS : PMSPA.args3 AD R0 fb s0.
Hypothesis RPRE : PMSPA.run_pre RSEGS AD PMB.AAD M0 fb s0 str sm0 e0.
Hypothesis INCS : incl (PM.vs_own str) LBX.
Hypothesis INV : PM.inv s0.
Hypothesis EC0 : PMSPA.ec_at RSEGS M0 (PMSPA.o_ec AD fb) 0 cat.
Hypothesis UNR : PM.unread (PM.p_src s0) sm0 < 2 ^ 26.
Hypothesis CRED : PMSPA.credit_le (PMSPA.scA L (PM.pot_parser (PMSPA.HV L ar) s0)) cr0.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (s' : PM.pst) (sm' : PM.strm) (e' : bool) (cr' : credit),
regs_preserved R0 R' ->
PMSPA.run_post RSEGS AD PMB.AAD (fun _ => PMSPA.prog_value) R' M' fb s0 s' str sm0 sm' e0 e' cat ->
L5CA.ahpres L ar LBX FF S (PMSPA.pm_scr 7) (PMSPA.W_run AD fb) M0 M' ->
PMSPA.credit_keep cr0 cr' (PMSPA.scA L (PM.pot_parser (PMSPA.HV L ar) s0)) (PMSPA.scA L (PM.pot_parser (PMSPA.HV L ar) s')) ->
model_rt model0 model' -> incl LK' LK0 -> incl Aw0 Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (PM.parser_own s' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx' R' r M' model') K.
Hypothesis PEEK : PMB.peek_spec L ar HI.
Hypothesis IGN : PMB.ignore_spec L ar HI.
Hypothesis SRD : PMB.src_read_spec L ar HI.
Hypothesis GLS : PMB.get_length_spec L ar HI.
Hypothesis MKE : PMB.make_ec_spec L ar HI.
Hypothesis CMI : PMBX.cone_mi_spec L ar HI.
Hypothesis SMI : PMBX.slow_mi_spec L ar HI.
Hypothesis CMS : PMBX.cone_ms_spec L ar HI.
Hypothesis SMS : PMBX.slow_ms_spec L ar HI.
Hypothesis CMSU : PMBX.cone_msu_spec L ar HI.
Hypothesis SMSU : PMBX.slow_msu_spec L ar HI.
Local Abbreviation SCR := PMBBK.SCR.
Local Abbreviation BARR := PMBBK.BARR.
Local Abbreviation op := (PMBBK.op fb).
Local Abbreviation ois := (PMBBK.ois fb).
Local Abbreviation ov := (PMBBK.ov fb).
Local Abbreviation oec := (PMBBK.oec fb).
Local Abbreviation WR := (PMBBK.WR fb).
Local Abbreviation U := (PMBBK.U R0).
Local Abbreviation ocell := (PMBBK.ocell S).
Local Abbreviation own := (PMBBK.own R0 S).
Local Abbreviation own_agree := (PMBBK.own_agree R0 S).
Local Abbreviation sd := (PMBBK.sd s0).
Local Abbreviation sdl := (PMBBK.sdl s0).
Local Abbreviation spush := (PMBBK.spush s0).
Local Abbreviation frame_geo := (PMBBK.frame_geo fb).
Section Frame.
Variables (F fl : Z) (LK2 : list fframe) (M2 : word -> option byte) (model2 : Model).
Hypothesis G : PMBUK.gctx L ar HI LBX FF LK0 Aw0 S SCR (S - 160) (S - 104) S ocell own F fl 0 LK2 M2 model2 cr0 (PM.parser_own s0).
Local Abbreviation FF' := (PMBBK.FF' FF S F).
Local Abbreviation binv' := (PMBBK.binv' L ar HI R0 M0 model0 LBX FF LK0 Aw0 S fb F).
Local Abbreviation hdr := (PMBBK.hdr S F).
Local Abbreviation fsh := (PMBBK.fsh F).
Local Abbreviation bst := (PMBBK.bst L ar HI R0 M0 model0 LBX FF LK0 Aw0 cr0 S fb cat s0 str sm0 e0 F).
Local Abbreviation bste := (PMBBK.bste L ar HI R0 M0 model0 LBX FF LK0 Aw0 cr0 S fb s0 str sm0 F).
Local Abbreviation vfacts := (PMBBK.vfacts R0 S fb F fl).
Local Abbreviation vpack := (PMBBK.vpack L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE CMI SMI CMS SMS CMSU SMSU F fl LK2 M2 model2 G).
Local Abbreviation centry := (PMBBK.centry L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE CMI SMI CMS SMS CMSU SMSU F fl LK2 M2 model2 G).
Local Abbreviation own_with_src := PMBBK.own_with_src.
Local Abbreviation call_src := (PMBBK.call_src L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE CMI SMI CMS SMS CMSU SMSU F fl LK2 M2 model2 G).
Local Abbreviation call_mkec := (PMBBK.call_mkec L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE CMI SMI CMS SMS CMSU SMSU F fl LK2 M2 model2 G).
Local Abbreviation fsh_nc := (PMBBK2.fsh_nc L ar C HI HIok R0 LBX FF LK0 Aw0 cr0 S s0 F fl LK2 M2 model2 G).
Local Abbreviation fsh_agree := (PMBBK2.fsh_agree S F).
Local Abbreviation step_piece := (PMBBK2.step_piece L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE CMI SMI CMS SMS CMSU SMSU F fl LK2 M2 model2 G).
Local Abbreviation wr_rng := (PMBBK2.wr_rng fb).
Local Abbreviation bsterr := (PMBBK2.bsterr L ar HI R0 M0 model0 LBX FF LK0 Aw0 cr0 S fb s0 str sm0 F).
Local Abbreviation call_gl := (PMBBK2.call_gl L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE CMI SMI CMS SMS CMSU SMSU F fl LK2 M2 model2 G).
Abbreviation pot := (fun (s : PM.pst) => PMSPA.scA L (PM.pot_parser (PMSPA.HV L ar) s)).
Definition bstp (typed : bool) (s : PM.pst) (sm : PM.strm) (e : bool) (Mc : word -> option byte) (modelc : Model) (LKc : list fframe) (crc : credit) (Ac : list (Z * Z)) : Prop :=
binv' (PM.parser_own s) Mc modelc LKc crc Ac
/\ PMSPA.run_pre RSEGS AD PMB.AAD Mc fb s str sm e /\ PMSPA.ec_at RSEGS Mc oec 0 cat
/\ hdr Mc /\ fsh typed Mc
/\ PMSPA.src_step (PM.p_src s0) (PM.p_src s) sm0 sm /\ (e0 = true -> e = true)
/\ PM.inv s /\ PMSPA.prog_value s0 s sm0 sm
/\ PMSPA.credit_le (pot s) crc /\ PMSPA.credit_keep cr0 crc (pot s0) (pot s) /\ L5.u64_at RSEGS Mc (S - 136) ov.
Lemma call_push : ltac2:(TCodec.tc2 tcn__PmBBaK3 "XE'B';'R@%211'>%1255%511!p021p061p0:1p0;1&Oy5'THyR0%211%5241p0?;p0C1p031&Q?%E11'=y8%;11%311p0;1p0JEp0<1p031p0O1p0Q01p0;1&QNvS;&S9&QOvHvSHvFr4r3r2r1%;::987654321'7'R?'RE'S6'N&Q9&QHvQ7vQ2vT;vIvDvLv4vT0vS:vT4vSLvTDvTJvTFvT3vCr=r<r;r:r7r6r5%HLQ6Q5Q4GFEDCBA@?>=<;:987654321Q3Q2'@&S7r9&TG&SAu1%211%42R71%7261%62R7Q<%:3R721&QC%11Q@u2%:11%<2R?1%?2F1&SC+U0%22Q31%A2RB1%E3RB51u3%C11%E2RH1%H2Q01%I2QB2%K3RH21u4%I11%K2RN1%N2Q71%O2QH2%Q13RN21r>u:%Q011%Q22S51%Q5241&S=&QJ%11QH+[8%4221%Q92S:1%Q=3S:71rF&QF%13R4R0QIr?r8%563Q08A21rI&R5rD%211&R6%113&R8%115&RI%1264%:47531&RA%11R5&R=%11R8z%R43TA21&A&R3&R>%11R?%311%511&R4%51RD%211&S?&RG&R7%11MrH%4221%41S1%621S0%8231p0:1&S>&:%Q01S7%22U61%RH11&R1%6221&Q:rN%221S5rQ7%Q>1T6%Q:1T7%33QC21%Q<1T:&6rQ4%Q?11(8(<%11UG%33UHQI1%73UI51%S?3UI91&S5(9rQ5%QN11%QL12%QK13%QJ232%R21SI%R01SJrM%::U197654321TN&QL%19JSO:DT1SJR:SNT0'RC%Q>1T2%Q?1M%T03321'?%Q:2S?U3%QE2U4TC%3221%T22V3U7%S411%E12%T83UK21p051pW>VG1'S8&QE%11UG&S1rO%26UIROS>1THTGvG%74UK521p091p0D1p0I1p0L1p0Q81p0QC1p0QH1pX0UD1pY8UI1p8W31pQHVD1pXFUI1pR4VA1pR>VL1pX>UM1rGrQ1rE%G6V>RC32SG1%K4V?I1Ep061p0R:1p0RB1p0S01p0S71p0S<1p0S?1p0SK1p0T21p0T?1p0TF1p0TM1p0U71p0U:1p0UF1pWFX11pW<X41p4WO1pX4VC1pQLWA1pXJVF1pR8W>1pR<WI1pX<VJ1pX6VN1pY<VM1pY6VO1pYHW11pVJW31pWLW@1p2WN1pR:X81pY4XD1").
Proof using All. intros pc Q A0 cells SPEC typed s sm e fx R Mc modelc LKc crc Ac X c.
intros BS A1 RAX A2 A3 A4 A10 CELLS HQ Hc Hidx Hm Hcnt HL NEXT.
pose proof BS as (BI & RP & EC & HD & FSH & STEP0 & E0 & SD & CRL & CRK & VSL).
pose proof BI as (HHc & AMc & MRTc & IAc & ILKc & ASTKc & EKc & DKc & OWNc & SHDc).
pose proof RP as (PA & IA & VIS & VREF & BASE & ERR & TBOK).
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHc) as (WB & WF & FSAPP & FSCEIL & _ & _ & _ & _ & _ & STOP & _ & NDF & _).
pose proof G as G'. destruct G' as [Hk SPTg SLOg SHIg SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
pose proof frame_geo as (Eop & Eois & Eov & Eoec & Eos).
pose proof FOK as ((rs & Hfb) & Fal).
pose proof ENT as (_ & _ & _ & _ & _ & ASTK0 & _). pose proof ASTK0 as (A16 & SLO & SHI & SPT & SDEF & SUP).
unfold SCR in *. change (PMSPA.pm_scr 7) with 26624 in *.
assert (HfbF : In (fb, 4, rs) FF') by (right; exact Hfb).
destruct (WF _ HfbF) as (Ff1 & Ff2 & _). cbn [ff_addr ff_class fst snd] in Ff1, Ff2. change (ff_bytes 4) with 1024 in Ff2.
unfold app_mem, FS_BYTES in FSAPP, FSCEIL, Ff1, Ff2, FS2. change (ff_bytes 0) with 64 in *.
assert (FAP : F + 64 <= fb \/ fb + 1024 <= F).
{ destruct (WF (F, 0, S - 160 + 32) (or_introl eq_refl)) as (_ & _ & _ & _ & _ & APF). cbn [ff_addr ff_class fst snd] in APF. change (ff_bytes 0) with 64 in APF.
assert (Iin : In (fb, 4, rs) (ff_remove F FF' ++ LKc)).
{ apply in_or_app. left. unfold PMBBK.FF'. cbn [ff_remove ff_addr]. rewrite Z.eqb_refl. exact Hfb. }
destruct (APF _ Iin) as [X0|X0]; cbn [ff_addr ff_class fst snd] in X0; change (ff_bytes 4) with 1024 in X0; [left| right]; lia. }
assert (AOF : forall a n, fb + 32 <= a -> a + n <= fb + 1016 -> PMSPA.aobjA FF a n)
by (intros a n X1 X2; exists (fb, 4, rs); split; [exact Hfb|]; cbn [ff_addr ff_class fst snd]; change (ff_bytes 4) with 1024; lia).
pose proof INV as (IM & ID & IDP & ISH & ITB).
pose proof SD as (SDm & SDd & SDp & SDs).
pose proof PA as (_ & PDEF & _ & _ & _ & _ & _ & _ & _ & SRCF & _ & _ & C320 & TBV & VEC & _).
pose proof VEC as (V0 & V8 & V16 & Hk' & Hlen & Hal & DB & CB & AN & EL).
pose proof (PMBSK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HHc) as BRB.
pose proof (PMBSK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HHc) as FRB'.
assert (FRB : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47) by (intros f Hf; apply FRB'; right; exact Hf).
set (qc := PM.sr_qc (PM.p_src s)) in *. set (b := PM.p_b s) in *. set (k := PM.p_k s) in *.
set (LBXp := (qc, PM.CHUNK) :: (PM.vs_own (PM.p_tb s) ++ LBX)).
assert (HHs : ri_inv HI (PM.vec_own b k ++ LBXp) FF' LKc crc Ac Mc (vml_of modelc)) by (apply ri_swap12; exact HHc).
assert (Iv : In (b, 32 * 2 ^ k) (PM.parser_own s ++ LBX)) by (apply in_or_app; left; right; left; reflexivity).
assert (Iq : In (qc, PM.CHUNK) (PM.parser_own s ++ LBX)) by (apply in_or_app; left; left; reflexivity).
destruct (WB _ Iv) as ((Bb4 & _ & _ & _ & _ & _) & _). cbn [fst snd] in Bb4.
assert (Lk : Z.of_nat (length (PM.p_stk s)) = Z.of_nat (length (PM.p_stk s0))) by (rewrite SDs; reflexivity).
assert (K10 : Z.of_nat (length (PM.p_stk s)) = 2 ^ k -> k <= 10).
{ intros E. destruct (Z.eq_dec k 11) as [E11|N11]; [|lia]. rewrite E11 in E. change (2 ^ 11) with 2048 in E. unfold PM.MAX_DEPTH in HL. lia. }
assert (Cap : PM.vs_cap (PM.p_tb s) <= 2 ^ 27).
{ pose proof TBV as (_ & _ & TBV'). destruct (PM.p_tb s) as [n0|c0 n0 q0]; cbn [PM.vs_cap]; [lia|]. destruct TBV' as (_ & _ & _ & _ & CB' & _). lia. }
assert (Bnz : Z.eqb b 0 = false) by (apply Z.eqb_neq; lia).
unfold PMBPQ.pushq_spec_at in SPEC.
apply (SPEC fx R Mc modelc K LBXp FF' LKc Ac crc (op + 360) b k (PM.p_stk s) (PM.vec_own b k) c (S - 160) X HQ HHs AMc K0).
{ exact (PMBBK.centry L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT
PEEK IGN SRD GLS MKE CMI SMI CMS SMS CMSU SMSU F fl LK2 M2 model2 G R Mc X 0 ASTKc EKc A1 RAX A2 A3 A4 ltac:(lia)). }
{ apply (PMBUAR.ffrsA_push FF S (S - 160) F 0 (S - 160 + 32) FRS); lia. }
{ rewrite L5K.rl10. exact A10. }
{ apply PMBUAR.aobjA_push. apply AOF; unfold PMBBK.op; lia. }
{ unfold PMBBK.op. rewrite Eop. pose proof (Z.div_mod fb 1024 ltac:(lia)) as Dm. rewrite Fal, Z.add_0_r in Dm. rewrite Dm.
replace (1024 * (fb / 1024) + 464 + 360) with ((128 * (fb / 1024) + 103) * 8) by lia. apply Z_mod_mult. }
{ apply (aacc_sub Mc (PMSPA.o_p AD fb + 320) 64); [exact C320| unfold PMBBK.op; lia| unfold PMBBK.op; lia]. }
{ right. split; [exact VEC| reflexivity]. }
{ intros [E|E]; [discriminate E| exact (K10 E)]. }
{ exact CELLS. }
{ intros [E|E]; [discriminate E|]. rewrite Bnz. exact (proj1 (stk_credit s crc TBOK Cap ltac:(pose proof (K10 E); lia) CRL)). }
intros fx' R' M' model' LK' Aw' b' k' cr' RP' VEC' ACC' PO' A0' HP' MRT' ILK' IAW' AM' HH'.
change (PMSPA.pm_scr 0) with 12288 in HP'.
set (s' := push_st s b' k' c).
assert (HH1 : ri_inv HI (PM.parser_own s' ++ LBX) FF' LK' cr' Aw' M' (vml_of model')) by (apply ri_swap12; exact HH').
set (Wc := [(op + 360, 24)]) in HP'.
assert (DF1 : 0 <= F / 8) by (apply Z.div_pos; lia). assert (DF2 : F / 8 <= 17592186044408) by (apply Z.div_le_upper_bound; lia).
pose proof FSAPP as (FA0 & FA1 & FA2). unfold BIGSHADOW_LO, BIGSHADOW_HI in FA1.
pose proof (PMBSK.fs_above_img L ar C HI LY HIok _ _ _ _ _ _ _ HHc) as FSI.
assert (BI' : binv' (PM.parser_own s') M' model' LK' cr' Aw').
{ apply (PMBUK.binv_callee L ar C HI HIok M0 model0 LBX FF LK0 Aw0 S 26624 (S - 160) (S - 104) S ocell own F fl 0 LK2 M2 model2 cr0 (PM.parser_own s0) G
WR WR (PM.parser_own s) ((qc, PM.CHUNK) :: PM.vs_own (PM.p_tb s)) (PM.parser_own s') Mc modelc LKc crc Ac M' model' LK' cr' Aw' 12288 Wc BI HP' HH1 AM' MRT' IAW' ILK');
[lia| lia| | | intros a X0; exact X0].
- intros rr a [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. unfold PMBBK.ocell, PMBBK.op in *. change (ff_bytes 0 / 8) with 8. unfold SB.
split; [lia|]. destruct FA1; lia.
- intros a _ O rr [<-|[]] Hr. apply (O (PMSPA.o_vec AD fb, 24)); [| exact Hr].
unfold PMBBK.WR, PMSPA.W_run, PMSPA.W_srcf, PMSPA.err_W. cbn [app]. do 5 right. left. reflexivity. }
assert (EKp : L5SAR.ek L ar LBXp FF S 26624 Wc Mc M')
by exact (L5SAR.ek_callee L ar LBXp [] FF [(F, 0, S - 160 + 32)] S 26624 (S - 160) 12288 Wc Wc Mc M' HP' ltac:(lia) ltac:(lia) (fun a _ X0 => X0)).
assert (WAPPc : PMKB.wapp Wc).
{ apply PMKB.wapp_cons; [| apply PMKB.wapp_nil]. cbn [fst snd]. unfold PMBBK.op. unfold BIGSHADOW_LO, BIGSHADOW_HI. destruct FA1; lia. }
assert (BRBp : forall bb, In bb LBXp -> 0 <= fst bb /\ fst bb + snd bb <= 2 ^ 47).
{ intros bb Hbb. apply BRB. unfold LBXp in Hbb. destruct Hbb as [<-|Hbb]; [exact Iq|]. apply in_app_or in Hbb. destruct Hbb as [Hbb|Hbb].
- apply in_or_app; left. unfold PM.parser_own. apply in_or_app; right. right. exact Hbb.
- apply in_or_app; right; exact Hbb. }
assert (OUTc : forall a n, a + n <= op + 360 \/ op + 384 <= a -> forall i, a <= i < a + n -> L5.outside Wc i).
{ intros a n X0 i Hi rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. lia. }
assert (OUTB : forall q m, In (q, m) LBXp -> forall i, q <= i < q + m -> L5.outside Wc i).
{ intros q m Hq i Hi rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr.
assert (Hq' : In (q, m) (PM.parser_own s ++ LBX)) by (unfold LBXp in Hq; destruct Hq as [E|Hq];
[rewrite <- E; exact Iq| apply in_app_or in Hq; destruct Hq as [Hq|Hq]; [apply in_or_app; left; unfold PM.parser_own; apply in_or_app; right; right; exact Hq| apply in_or_app; right; exact Hq]]).
destruct (PMBSK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q m (PMSPA.o_p AD fb + 360) 24 HHc Hq' (PMBUAR.aobjA_push FF (PMSPA.o_p AD fb + 360) 24 (F, 0, S - 160 + 32) (AOF (PMSPA.o_p AD fb + 360) 24 ltac:(lia) ltac:(lia)))) as [Z0|Z0];
unfold PMBBK.op in Hr; lia. }
assert (DEF' : L5.defined M' (PMSPA.o_p AD fb) 384).
{ intros i Hi. apply (proj2 (proj2 HP')); [lia| | apply PDEF; exact Hi].
apply (L5SAR.fframe_client L ar _ FF' _ _ fb 4 rs); [exact HfbF| change (ff_bytes 4) with 1024; lia]. }
assert (PA' : PM.parser_at RSEGS AD PMSPA.accA PMSPA.annA M' (PMSPA.o_p AD fb) (PMSPA.o_is AD fb) s').
{ apply (parser_push_updA Mc M' _ _ s b' k' c PA); [clear - Eop Ff1 FA0; lia| clear - Eop Ff2 FA2; lia| | | exact DEF'| exact VEC'| unfold qc; clear - BRB Iq; destruct (BRB _ Iq) as (Q1 & Q2); cbn [fst snd] in *; lia| | |].
- apply (PMKB.agA_obj L ar _ FF S 26624 Wc Mc M' EKp WAPPc FRB (PMSPA.o_p AD fb) 360 (AOF (PMSPA.o_p AD fb) 360 ltac:(lia) ltac:(lia))). apply OUTc. unfold PMBBK.op; lia.
- exact (PMKB.agsh_obj L ar _ FF S 26624 Wc Mc M' EKp WAPPc FRB (PMSPA.o_p AD fb) 384 (AOF (PMSPA.o_p AD fb) 384 ltac:(lia) ltac:(lia))).
- destruct (BRB _ Iq) as (Q1 & Q2). cbn [fst snd] in Q2. unfold qc in Q2. lia.
- apply (PMKB.agA_blk L ar _ FF S 26624 Wc Mc M' EKp WAPPc BRBp _ _ (or_introl eq_refl)). apply OUTB. left; reflexivity.
- intros c0 n0 p0 Etb. assert (Ip : In (p0, c0) LBXp) by (unfold LBXp; right; apply in_or_app; left; rewrite Etb; left; reflexivity).
apply (PMKB.agA_blk L ar _ FF S 26624 Wc Mc M' EKp WAPPc BRBp _ _ Ip). apply OUTB. exact Ip. }
assert (KPa : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LBXp FF' (S - 160) 12288 a -> L5.outside Wc a -> M' (Z_to_bv 64 a) = Mc (Z_to_bv 64 a))
by (intros a X1 X2 X3; apply (proj1 HP'); split; [exact X1| split; assumption]).
assert (KPR : forall a, S - 160 <= a < S -> M' (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)).
{ intros a Ha. apply KPa; [lia| apply (L5SAR.stack_client L ar _ FF' _ _ a); lia|]. intros rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. unfold PMBBK.op in Hr. lia. }
assert (HD' : hdr M').
{ pose proof HD as (H0 & H8 & H16 & H128).
assert (KPF : forall a, F <= a < F + 24 -> M' (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)).
{ intros a Ha. apply KPa; [lia| apply (L5SAR.fframe_client L ar _ FF' _ _ F 0 (S - 160 + 32)); [left; reflexivity| change (ff_bytes 0) with 64; lia]|].
intros rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. unfold PMBBK.op in Hr. destruct FAP; lia. }
split; [apply (L5C.u64_at_agree RSEGS Mc M'); [intros i Hi; apply KPF; lia| lia| lia| exact H0]|].
split; [apply (L5C.u64_at_agree RSEGS Mc M'); [intros i Hi; apply KPF; lia| lia| lia| exact H8]|].
split; [apply (L5C.u64_at_agree RSEGS Mc M'); [intros i Hi; apply KPF; lia| lia| lia| exact H16]|].
apply (L5C.u64_at_agree RSEGS Mc M'); [intros i Hi; apply KPR; lia| lia| lia| exact H128]. }
assert (FSH' : fsh typed M').
{ apply (fsh_agree typed Mc M'); [| exact DF1| lia| exact FSH].
intros x Hx. apply KPa; [lia| apply (L5SAR.fframe_shadow_client L ar _ FF' _ _ F 0 (S - 160 + 32)); [left; reflexivity|]|].
- change (ff_bytes 0) with 64. unfold in_shadow_of, HeapIfaceA.S, SB. change (ff_bytes 0) with 64 in F8. rewrite (proj1 (proj2 F8)). change (64 / 8) with 8. lia.
- intros rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. unfold PMBBK.op in Hr. destruct FA1; lia. }
assert (EC' : PMSPA.ec_at RSEGS M' oec 0 cat).
{ apply (PMKB.ec_keepA RSEGS L ar _ FF S 26624 Wc Mc M' EKp WAPPc FRB oec 0 cat (AOF oec 16 ltac:(unfold PMBBK.oec; lia) ltac:(unfold PMBBK.oec; lia))); [| exact EC].
apply OUTc. unfold PMBBK.oec, PMBBK.op. lia. }
assert (RUN' : PMSPA.run_pre RSEGS AD PMB.AAD M' fb s' str sm e).
{ split; [exact PA'|].
split; [apply (PMKB.iss_keepA RSEGS AD L ar _ FF S 26624 Wc Mc M' EKp WAPPc FRB BRBp _ str sm (AOF (PMSPA.o_is AD fb) 272 ltac:(lia) ltac:(lia)));
[intros x Hx; unfold LBXp; right; apply in_or_app; right; apply INCS; exact Hx| apply OUTc; unfold PMBBK.op; lia
| intros c0 n0 p0 Etb i Hi; apply (OUTB p0 c0); [unfold LBXp; right; apply in_or_app; right; apply INCS; rewrite Etb; left; reflexivity| exact Hi]
| exact IA]|].
split; [apply (PMKB.visitor_keepA RSEGS AD L ar _ FF S 26624 Wc Mc M' EKp WAPPc FRB (PMSPA.o_v AD fb) (AOF (PMSPA.o_v AD fb) 8 ltac:(lia) ltac:(lia))); [apply OUTc; unfold PMBBK.op; lia| exact VIS]|].
split; [apply (PMKB.u64_keepA RSEGS L ar _ FF S 26624 Wc Mc M' EKp WAPPc FRB (PMSPA.o_p AD fb + 384) (PMSPA.o_v AD fb) (AOF (PMSPA.o_p AD fb + 384) 8 ltac:(lia) ltac:(lia)));
[apply OUTc; unfold PMBBK.op; lia| exact VREF]|].
split; [apply (PMBSK.base_keep L ar C LY _ FF S 26624 Wc Mc M' EKp); [| exact BASE]; intros a Ha rr [<-|[]] Hr; unfold L5.in_rng in Hr; cbn [fst snd] in Hr; unfold PMBBK.op in Hr; lia|].
split; [apply (PMKB.err_okA_keep RSEGS AD PMB.AAD L ar _ FF S 26624 Wc Mc M' EKp e PMB.addrs_wf_A); [| exact ERR];
intros a D; pose proof (PMBSK.dep_img a D) as DI; rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa); split; [lia|];
split; [exact (PMB.ly_static L C LY a D)| intros rr [<-|[]] Hr; unfold L5.in_rng in Hr; cbn [fst snd] in Hr; unfold PMBBK.op in Hr; lia]|].
exact TBOK. }
assert (INV' : PM.inv s').
{ unfold PM.inv, s', push_st. cbn [PM.p_more PM.p_done PM.p_depth PM.p_stk PM.p_tb PM.p_tg].
split; [rewrite SDm; exact IM|]. split; [rewrite SDd; exact ID|].
split; [rewrite SDp, SDs, length_app; cbn [length]; lia|].
split; [rewrite SDs; exact (stack_shape_push _ c ISH HL Hc Hm)| exact TBOK]. }
assert (PV' : PMSPA.prog_value s0 s' sm0 sm).
{ right. exists c. split; [unfold s', push_st; cbn [PM.p_stk]; rewrite SDs; reflexivity|]. split; [exact Hc|]. split; [exact Hidx|]. split; [exact Hm| exact Hcnt]. }
apply (NEXT fx' R' M' model' LK' Aw' s' cr' RP' A0' eq_refl PO'); [| reflexivity| exact KPR].
destruct PO' as [(_ & _ & _ & Eb & Ek & Ecr)|(Hg & Ek & Ecr)].
- assert (EP : pot s' = pot s) by (unfold s', push_st, PM.pot_parser; cbn [PM.p_k PM.p_tb PM.p_tg]; rewrite Ek; reflexivity).
subst cr'. split; [exact BI'|]. split; [exact RUN'|]. split; [exact EC'|]. split; [exact HD'|]. split; [exact FSH'|]. split; [exact STEP0|].
split; [exact E0|]. split; [exact INV'|]. split; [exact PV'|]. rewrite EP. split; [exact CRL| split; [exact CRK| apply (L5C.u64_at_agree RSEGS Mc M'); [intros i Hi; apply KPR; lia| lia| lia| exact VSL]]].
- rewrite Bnz in Ek. subst k' cr'.
destruct (stk_credit s crc TBOK Cap) as (_ & CKs).
{ destruct Hg as [Hg|Hg]; [discriminate Hg|]. pose proof (K10 Hg). lia. }
{ exact CRL. }
specialize (CKs s' eq_refl eq_refl eq_refl).
split; [exact BI'|]. split; [exact RUN'|]. split; [exact EC'|]. split; [exact HD'|]. split; [exact FSH'|]. split; [exact STEP0|].
split; [exact E0|]. split; [exact INV'|]. split; [exact PV'|].
split; [exact (PMBPAR.credit_le_keepA _ _ _ _ CRL CKs)| split; [exact (PMBPAR.credit_keep_transA _ _ _ _ _ _ CRK CKs)| apply (L5C.u64_at_agree RSEGS Mc M'); [intros i Hi; apply KPR; lia| lia| lia| exact VSL]]].
Qed.
Lemma vsl_vis : ltac2:(TCodec.tc2 tcn__PmBBaK3 "QL';'>'B%2211%411'THyR0%211'=y8%511%311p051'N&Q?%?11&Q9&QGvHvSHvFvQ7vQ2vT;vIvDvLv4vS:vT4vCr6r5r4r3r2r1%DCCBA@?>=<;:987654321&QD&S9&SC+T8%22>1&QK%11?%746>31&Q8&Q>%12>Ar7%4221%=4<197p071p0@1p4QB1pX4Q71pQLQ91pXJQ<1pR8Q>1p<QG1").
Proof using All. intros BX Mc modelc LKc crc Ac.
intros BI VS. pose proof G as G'. destruct G' as [Hk SPTg SLOg SHIg SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
pose proof (PMBUK.vis_facts L ar C HI LYa HIok M0 model0 LBX FF LK0 Aw0 S SCR (S - 160) (S - 104) S ocell own F fl 0 LK2 M2 model2 cr0 (PM.parser_own s0) G WR BX Mc modelc LKc crc Ac BI)
as (_ & _ & _ & (_ & _ & _ & SV8 & _)).
apply (proj2 (L5A.u64_at_vis _ Mc (S - 136) ov (L5A.avis_sub _ (S - 160) (S - (S - 160)) (S - 136) 8 SV8 ltac:(lia) ltac:(lia)) ltac:(unfold SCR in *; lia) ltac:(unfold SCR in *; lia))).
exact VS.
Qed.
Lemma bst_of0 : ltac2:(TCodec.tc2 tcn__PmBBaK3 "R9'7'R?'RE'THyR0%211'=y8%511%311p051'N';&Q?%211&Q9'>'B%2211%711&QIvHvSHvFvQ7vQ2vT;vIvDvLv4vT0vS:vT4vSLvTDvTJvTFvT3vCr9r8r7r6r5r4r3r2r1%MLLKJIHGFEDCBA@?>=<;:987654321&QD&S9&SC+T8%22F1&QK%11G%746>31&QHr;r:%3LQ8Q7Q6Q5Q4Q3Q2Q1Q0ONMLKJIHGF21EDCBA@?p051p0>1p4Q=1pX4QB1pQLQD1pXJQH1pR8QJ1pX6R51pY<R41pY6R61pYHR81").
Proof. intros typed s sm e Mc modelc LKc crc Ac. intros (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10) V. exact (conj A1 (conj A2 (conj A3 (conj A4 (conj A5 (conj A6 (conj A7 (conj A8 (conj A9 (conj A10 V)))))))))). Qed.
Lemma S_of_binv : ltac2:(TCodec.tc2 tcn__PmBBaK3 "QG';'>'B%2211%411'THyR0%211'=y8%511%311p051'N&Q?%?11&Q9&QGvHvSHvFvQ7vQ2vT;vIvDvLv4vS:vT4vCr6r5r4r3r2r1%DCCBA@?>=<;:987654321'?&S>+SoomohPTV0%221=&SB+2+Q?%3221%72B1%9261p0;1p4Q=1pX4Q21pQLQ41pXJQ71pR8Q91p<QB1").
Proof using All. intros BX Mc modelc LKc crc Ac.
intros BI. pose proof BI as (HHc & AMc & MRTc & IAc & ILKc & ASTKc & _).
pose proof (PMBSK.stk_vis L ar C HI LY HIok _ FF' LKc crc Ac Mc modelc S 26624 192 HHc ASTKc ltac:(lia)) as (SL & SH & _).
pose proof ASTKc as (_ & _ & X3 & X4 & _). lia.
Qed.
End Frame.
End Call.
End WithHeap.
End PMBBK3.
