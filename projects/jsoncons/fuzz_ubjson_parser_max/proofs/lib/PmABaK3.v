(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceA LibIface
AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsA L5CoreA L5CoreSpecsA L5StepAR L5CoreBR L5ADetailHR
PmLayout PmLayoutA PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceAJx PmSpecsA PmSpecsAX PmSpecsAa
PmModelFactsA PmStepA PmStep PmParStep PmParKit PmASrcKit PmAParKit PmAReset1 PmAUarK PmAUar PmAUarKS PmABaK PmABaK2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmABaK3 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmABaK.PMABK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmABaK3.PMABK3."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmABaK3.PMABK3.WithHeap.Call.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModelFactsA.PMFA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsAX.PMSAX."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0Ac"; "0Aw"; "0Aw'"; "0Aw0"; "1app"; "1bool"; "1cons"; "1false"; "1length"; "1list"; "1nil"; "1option"; "1prod"; "2and"; "2eq"; "2not"]; ["3Z"; "0F"; "0FF"; "0FF1"; "0HI"; "0K"; "0L"; "0LBX"; "0LK"; "0LK'"; "0LK0"; "0LKc"; "4Model"; "5bvmap"; "0M"; "0M'"]; ["0M0"; "0Mc"; "0R"; "0R'"; "0R0"; "6credit"; "6regs_preserved"; "7aacc"; "7acredit_ok"; "7adebit"; "7fframe"; "7ri_inv"; "7vml"; "9defined"; "9ra_ok"; "8SCFG"]; [":FF'"; ":bst"; ":op"; "<bstp"; ";push_st"; "=ADDR_A"; ">CHUNK"; ">MAX_DEPTH"; ">VLong"; ">mode_bottom"; ">mode_counted"; ">p_k"; ">p_src"; ">p_stk"; ">p_tb"; ">p_tg"]; [">parser_at"; ">pot_parser"; ">ps_idx"; ">ps_mode"; ">pst"; ">pstate"; ">pstate_ok"; ">sr_qc"; ">srcst"; ">stack_shape"; ">strm"; ">tb_ok"; ">unread"; ">vec_at"; ">vs_cap"; ">vstr"]; ["?agA"; "?agsh"; "@HV"; "@accA"; "@annA"; "@cfg"; "@credit_keep"; "@credit_le"; "@scA"; "Apush_spec_at"; "BFPState"; "Bgetr"; "Csrealizes"; "Dloaded_segments"; "0S"; "0SCFG_P"]; ["0SPEC"; "Eadd"; "Ele"; "Elt"; "Emul"; "Eof_nat"; "Epow"; "Esub"; "0V"; "0X"; "0a"; "0a'"; "0ar"; "0b'"; "0c"; "0c0"]; ["0cat"; "0cells"; "0cr"; "0cr'"; "0cr0"; "0crc"; "0e"; "0e0"; "0fb"; "0fx"; "0fx'"; "0k"; "0k'"; "0l"; "0model'"; "0model0"]; ["0modelc"; "0n"; "0ois"; "0op"; "0p"; "0pc"; "0s"; "0s'"; "0s0"; "0sm"; "0sm0"; "FZ_to_bv"; "Fbv"; "0stk"; "0str"; "0typed"]; ["0x"; "0y"]]).
Local Ltac lia := L5FastLia.plia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PMABK3.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation AD := PMA.AD.
Definition push_st (s : PM.pst) (b k : Z) (c : PM.pstate) : PM.pst :=
PM.PST (PM.p_more s) (PM.p_done s) (PM.p_depth s) (PM.p_src s) (PM.p_tb s) (PM.p_tg s) b k (PM.p_stk s ++ [c]).
Lemma aacc_sub : ltac2:(TCodec.tc2 tcn__PmABaK3 "O'T<yR0%211';y8%511%311p051'@&Q7r5r4r3%43321&S2%1253&S1%1265r6%3219%6231r8%=31<;p031p091p0<1pWJB1pVHC1pWHD1pVFE1pQNG1").
Proof. intros M a k a' k'. intros AC H1 H2 x Hx. apply AC. lia. Qed.
Lemma parser_push_updA : ltac2:(TCodec.tc2 tcn__PmABaK3 "SA'T<yR0%211';y8%511%311p051'@'R4'R5&R0&RM&QE&RC&RDr8r6r5r4%9887654321&S2zr7%3221&S1+\0%22;1&S6+2+R0%3221%;251&R@r;r:r9+[8%544321&RAr<%24176?&Q=%1339A&R=r=%E269&4&QM%11>(6(:%11Q:%33Q;N1%73Q<51%;8Q;Q9Q8:9CQ71&R7&QL%11H%311%Q72Q61%41E%611&QF%Q7221%Q<21Q2rAr@%;1G%=11%Q544317'>'R?&QN%118(QHr3r2r1%43321%93861rFrE%QB4216R0p041pX:R=1pX4R>1pW0R?1rB&QDr?r>%3421Q?QD%RB8RAR@R?R>5KJ1p071p0I1p0O1p0Q51p0Q;1p0QH1p0QK1p0QO1p0R61p0R?1p0RD1pVNRO1pWJS21pVLS31pX>S31pX6S51pX8S61pR0S81pQNS91").
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
split; [apply (PMFA.nullis_at_agreeA RSEGS PMA.AD M M' (op + 32)); [lia|lia| apply AG4; lia| exact NI]|].
split; [apply (PMFA.src_fields_at_agreeA RSEGS M M' (op + 24)); [lia|lia|exact Hq|exact Hq'| apply AG4; lia| exact AGQ| exact SRC]|].
split; [apply (PMF.u32_at_agree RSEGS M M'); [apply (AG4 (op + 320) 4); lia|lia|lia|exact H320]|].
split; [apply (L5C.u64_at_agree RSEGS M M'); [apply (AG4 (op + 328) 8); lia|lia|lia|exact H328]|].
split; [apply (PMFA.accA_agree M M' (op + 320) 64); [intros x Hx; apply SH; lia| exact C320]|].
split; [apply (PMFA.vstr_at_agreeA RSEGS M M' (op + 336)); [lia|lia| apply AG4; lia| exact AGT| exact TB]|].
split; [exact VEC'|].
split; [exact B1|]. split; [exact B2| exact B3].
Qed.
Lemma stack_shape_push : ltac2:(TCodec.tc2 tcn__PmABaK3 "Q6'9'R5%211&R9r2%211&S2&S5&8r3%2291%411&QG%7221&R6%116&?&QI&R3r4%211%411%611&4r6(6r5(:%11K%43L31%73M61%L11p0:1p0B1p0E1p0N1pVNQ31pXLQ31").
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
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.
Lemma ri_swap12 : ltac2:(TCodec.tc2 tcn__PmABaK3 "Q>'<'@%2211'9%112&Q:%311&Q5'T<yR0%211';y8%511%311p051&Q<&Q;vD(6r9r8r7%43E21%53F41r6r5r4r3r2r1%>8=7654321r:%>3O1<%?3Q0>1%B8A1=:9876p051pVBE1pQNG1p4Q31pW6Q11pQBQ31pQ8Q41pWLQ71pY4Q:1pY2Q;1").
Proof. intros x y l FF1 LK cr Aw M V. exact (PMARS1.ri_swap12 L ar C HI HIok x y l FF1 LK cr Aw M V). Qed.
Lemma stk_credit : ltac2:(TCodec.tc2 tcn__PmABaK3 "RJ'R4&Q5&R;&QNr2%211&QO%113%6231&S2&R>r3%911%311&S6+2+K%3221%9251'=z&QKr4%211%?241+:%A231%8231&RG&RHvF&R1&RBvS<%2241r5%5221%8271%:21@&Q8&S4+Q0&S1r6%G11+1%4221%Q12Q01%8271%:3C>1'>'@r1%Q011r7%Q211%>21;%73641'R?r8%QI11%;33QH1%QH1QCr9%QJ11%?3>31&RF&Q9r:%Q@11%L21I%QI2QH1%Q02O1%63Q;:1%Q;2Q86%Q>2Q=1%Q=2Q:QF%Q@2Q?1%<4?531p0>1p0C1p0H1pX@RB1%R02Q21p0Q>1p0QJ1p0R41p0R?1pW<RG1pX>RI1").
Proof. intros s crc.
intros (Tg & Tc & _) Cap Hk (CR1 & CR2). pose proof (PMA.ly_cost L C LY) as (K8 & B3 & BO).
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
Hypothesis RPRE : PMSPA.run_pre RSEGS AD PMA.AAD M0 fb s0 str sm0 e0.
Hypothesis INCS : incl (PM.vs_own str) LBX.
Hypothesis INV : PM.inv s0.
Hypothesis EC0 : PMSPA.ec_at RSEGS M0 (PMSPA.o_ec AD fb) 0 cat.
Hypothesis UNR : PM.unread (PM.p_src s0) sm0 < 2 ^ 26.
Hypothesis CRED : PMSPA.credit_le (PMSPA.scA L (PM.pot_parser (PMSPA.HV L ar) s0)) cr0.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (s' : PM.pst) (sm' : PM.strm) (e' : bool) (cr' : credit),
regs_preserved R0 R' ->
PMSPA.run_post RSEGS AD PMA.AAD (fun _ => PMSPA.prog_value) R' M' fb s0 s' str sm0 sm' e0 e' cat ->
L5CA.ahpres L ar LBX FF S (PMSPA.pm_scr 7) (PMSPA.W_run AD fb) M0 M' ->
PMSPA.credit_keep cr0 cr' (PMSPA.scA L (PM.pot_parser (PMSPA.HV L ar) s0)) (PMSPA.scA L (PM.pot_parser (PMSPA.HV L ar) s')) ->
model_rt model0 model' -> incl LK' LK0 -> incl Aw0 Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (PM.parser_own s' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx' R' r M' model') K.
Hypothesis PEEK : PMA.peek_spec L ar HI.
Hypothesis IGN : PMA.ignore_spec L ar HI.
Hypothesis SRD : PMA.src_read_spec L ar HI.
Hypothesis GLS : PMA.get_length_spec L ar HI.
Hypothesis MKE : PMA.make_ec_spec L ar HI.
Hypothesis PMI : PMA.push_mi_spec L ar HI.
Hypothesis PMS : PMA.push_ms_spec L ar HI.
Hypothesis PMSU : PMA.push_msu_spec L ar HI.
Local Abbreviation SCR := PMABK.SCR.
Local Abbreviation BARR := PMABK.BARR.
Local Abbreviation op := (PMABK.op fb).
Local Abbreviation ois := (PMABK.ois fb).
Local Abbreviation ov := (PMABK.ov fb).
Local Abbreviation oec := (PMABK.oec fb).
Local Abbreviation WR := (PMABK.WR fb).
Local Abbreviation U := (PMABK.U R0).
Local Abbreviation ocell := (PMABK.ocell S).
Local Abbreviation own := (PMABK.own R0 S).
Local Abbreviation own_agree := (PMABK.own_agree R0 S).
Local Abbreviation sd := (PMABK.sd s0).
Local Abbreviation sdl := (PMABK.sdl s0).
Local Abbreviation spush := (PMABK.spush s0).
Local Abbreviation frame_geo := (PMABK.frame_geo fb).
Section Frame.
Variables (F fl : Z) (LK2 : list fframe) (M2 : word -> option byte) (model2 : Model).
Hypothesis G : PMAUK.gctx L ar HI LBX FF LK0 Aw0 S SCR (S - 128) (S - 104) S ocell own F fl 0 LK2 M2 model2 cr0 (PM.parser_own s0).
Local Abbreviation FF' := (PMABK.FF' FF S F).
Local Abbreviation binv' := (PMABK.binv' L ar HI R0 M0 model0 LBX FF LK0 Aw0 S fb F).
Local Abbreviation hdr := (PMABK.hdr S F).
Local Abbreviation fsh := (PMABK.fsh F).
Local Abbreviation bst := (PMABK.bst L ar HI R0 M0 model0 LBX FF LK0 Aw0 cr0 S fb cat s0 str sm0 e0 F).
Local Abbreviation bste := (PMABK.bste L ar HI R0 M0 model0 LBX FF LK0 Aw0 cr0 S fb s0 str sm0 F).
Local Abbreviation vfacts := (PMABK.vfacts R0 S fb F fl).
Local Abbreviation vpack := (PMABK.vpack L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE PMI PMS PMSU F fl LK2 M2 model2 G).
Local Abbreviation centry := (PMABK.centry L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE PMI PMS PMSU F fl LK2 M2 model2 G).
Local Abbreviation own_with_src := PMABK.own_with_src.
Local Abbreviation call_src := (PMABK.call_src L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE PMI PMS PMSU F fl LK2 M2 model2 G).
Local Abbreviation call_mkec := (PMABK.call_mkec L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE PMI PMS PMSU F fl LK2 M2 model2 G).
Local Abbreviation fsh_nc := (PMABK2.fsh_nc L ar C HI HIok R0 LBX FF LK0 Aw0 cr0 S s0 F fl LK2 M2 model2 G).
Local Abbreviation fsh_agree := (PMABK2.fsh_agree S F).
Local Abbreviation step_piece := (PMABK2.step_piece L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE PMI PMS PMSU F fl LK2 M2 model2 G).
Local Abbreviation wr_rng := (PMABK2.wr_rng fb).
Local Abbreviation bsterr := (PMABK2.bsterr L ar HI R0 M0 model0 LBX FF LK0 Aw0 cr0 S fb s0 str sm0 F).
Local Abbreviation call_gl := (PMABK2.call_gl L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE PMI PMS PMSU F fl LK2 M2 model2 G).
Abbreviation pot := (fun (s : PM.pst) => PMSPA.scA L (PM.pot_parser (PMSPA.HV L ar) s)).
Definition bstp (typed : bool) (s : PM.pst) (sm : PM.strm) (e : bool) (Mc : word -> option byte) (modelc : Model) (LKc : list fframe) (crc : credit) (Ac : list (Z * Z)) : Prop :=
binv' (PM.parser_own s) Mc modelc LKc crc Ac
/\ PMSPA.run_pre RSEGS AD PMA.AAD Mc fb s str sm e /\ PMSPA.ec_at RSEGS Mc oec 0 cat
/\ hdr Mc /\ fsh typed Mc
/\ PMSPA.src_step (PM.p_src s0) (PM.p_src s) sm0 sm /\ (e0 = true -> e = true)
/\ PM.inv s /\ PMSPA.prog_value s0 s sm0 sm
/\ PMSPA.credit_le (pot s) crc /\ PMSPA.credit_keep cr0 crc (pot s0) (pot s).
Lemma call_push : ltac2:(TCodec.tc2 tcn__PmABaK3 "W9'@'9&Q:%211'T<yR0%211';y8%511%311p051&My5%2218'R5!p021p041p081p0D1p0E1p0C1&RIvRO&RM&QEvFvS<vDr2(7r1%:9987654321'5'R4'R:'RJ'L&Q5'<%12Q9Q9%Q911&QAvQ4vQ0vSOvGvBvJv3vSDvRNvSHvS@vT8vT>vT:vSGvAr=r<r;r:r7r6r5r4r3%JLQ:Q9Q8IHGFEDCBA@?>=<;:987654321'>&RKr9&T;&S5u1%211%42R01%7261%62R:;%:3R:21&Q>%11?u2%:11%<2R81%?2H1&S7+T0%22Q51%A2RE1%E3RE51u3%C11%E2RA1%H2Q21%I2QD2%K3RK21u4%I11%K2RG1%N2Q91%O2QJ2%Q13S121r>u:%Q011%Q22RN1%Q5241&S1&QB%11QJ+[8%4221%Q92S=1%Q=3S=71rF&Q@%13R6R2QKr?r8%563Q08A21&R6%11QC&R2%11QNz%QI3SO21&?&QI&R3%11R5%311%511&QJ%51R:%211&S3&R<&QLrH%211rG%5221%51RI%721RH%9231p0;1&S2&8&QM%11S0%32T91%R?11&QG%7221&Q6rM%221RN&QCrQ3rQ1rQ0%493RO21S3S2S1T5S0'R8%J1S2%K16%S13321'=%E2R@T9%Q12T:SF%3221%S32U7T>%S?11%=12%S93U521p051pVFUA1'RL&Q?%11TL&RErK%26TNSJSI1SHS?vE%74U0521p091p0D1p0I1p0O1pW8TG1pX@TL1p6TF1pQDUN1pWNTL1pR0UH1pR8UF1pWFU01rNrErD%D6U@QKRE321%H4UAF1Bp061p0QA1p0QJ1p0R91p0R@1p0RE1p0RH1p0RO1p0S<1p0SC1p0SJ1p0T41p0T71p0TC1pVNV:1pVDVJ1p2UA1pW<UE1pQHVJ1pX2UH1pR4VD1pR6VB1pWDUL1pW>V01pXDUO1pX>V11pY0V31pV2V51pW4VA1pX<W81").
Proof using All. intros pc cells SPEC typed s sm e fx R Mc modelc LKc crc Ac X c.
intros BS A1 RAX A2 A3 A4 A10 CELLS Hc Hidx Hm Hcnt HL NEXT.
pose proof BS as (BI & RP & EC & HD & FSH & STEP0 & E0 & SD & CRL & CRK).
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
{ destruct (WF (F, 0, S - 128 + 32) (or_introl eq_refl)) as (_ & _ & _ & _ & _ & APF). cbn [ff_addr ff_class fst snd] in APF. change (ff_bytes 0) with 64 in APF.
assert (Iin : In (fb, 4, rs) (ff_remove F FF' ++ LKc)).
{ apply in_or_app. left. unfold PMABK.FF'. cbn [ff_remove ff_addr]. rewrite Z.eqb_refl. exact Hfb. }
destruct (APF _ Iin) as [X0|X0]; cbn [ff_addr ff_class fst snd] in X0; change (ff_bytes 4) with 1024 in X0; [left| right]; lia. }
assert (AOF : forall a n, fb + 32 <= a -> a + n <= fb + 1016 -> PMSPA.aobjA FF a n)
by (intros a n X1 X2; exists (fb, 4, rs); split; [exact Hfb|]; cbn [ff_addr ff_class fst snd]; change (ff_bytes 4) with 1024; lia).
pose proof INV as (IM & ID & IDP & ISH & ITB).
pose proof SD as (SDm & SDd & SDp & SDs).
pose proof PA as (_ & PDEF & _ & _ & _ & _ & _ & _ & _ & SRCF & _ & _ & C320 & TBV & VEC & _).
pose proof VEC as (V0 & V8 & V16 & Hk' & Hlen & Hal & DB & CB & AN & EL).
pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HHc) as BRB.
pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HHc) as FRB'.
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
unfold PMSAX.push_spec_at in SPEC.
apply (SPEC fx R Mc modelc K LBXp FF' LKc Ac crc (op + 360) b k (PM.p_stk s) (PM.vec_own b k) c (S - 128) X HHs AMc K0).
{ exact (PMABK.centry L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT
PEEK IGN SRD GLS MKE PMI PMS PMSU F fl LK2 M2 model2 G R Mc X 0 ASTKc EKc A1 RAX A2 A3 A4 ltac:(lia)). }
{ apply (PMAUAR.ffrsA_push FF S (S - 128) F 0 (S - 128 + 32) FRS); lia. }
{ rewrite L5K.rl10. exact A10. }
{ apply PMAUAR.aobjA_push. apply AOF; unfold PMABK.op; lia. }
{ unfold PMABK.op. rewrite Eop. pose proof (Z.div_mod fb 1024 ltac:(lia)) as Dm. rewrite Fal, Z.add_0_r in Dm. rewrite Dm.
replace (1024 * (fb / 1024) + 464 + 360) with ((128 * (fb / 1024) + 103) * 8) by lia. apply Z_mod_mult. }
{ apply (aacc_sub Mc (PMSPA.o_p AD fb + 320) 64); [exact C320| unfold PMABK.op; lia| unfold PMABK.op; lia]. }
{ right. split; [exact VEC| reflexivity]. }
{ intros X0. discriminate X0. }
{ intros [E|E]; [discriminate E| exact (K10 E)]. }
{ exact CELLS. }
{ intros [E|E]; [discriminate E|]. rewrite Bnz. exact (proj1 (stk_credit s crc TBOK Cap ltac:(pose proof (K10 E); lia) CRL)). }
intros fx' R' M' model' LK' Aw' b' k' cr' RP' VEC' ACC' PO' HP' MRT' ILK' IAW' AM' HH'.
change (PMSPA.pm_scr 0) with 12288 in HP'.
set (s' := push_st s b' k' c).
assert (HH1 : ri_inv HI (PM.parser_own s' ++ LBX) FF' LK' cr' Aw' M' (vml_of model')) by (apply ri_swap12; exact HH').
set (Wc := [(op + 360, 24)]) in HP'.
assert (DF1 : 0 <= F / 8) by (apply Z.div_pos; lia). assert (DF2 : F / 8 <= 17592186044408) by (apply Z.div_le_upper_bound; lia).
pose proof FSAPP as (FA0 & FA1 & FA2). unfold BIGSHADOW_LO, BIGSHADOW_HI in FA1.
pose proof (PMASK.fs_above_img L ar C HI LY HIok _ _ _ _ _ _ _ HHc) as FSI.
assert (BI' : binv' (PM.parser_own s') M' model' LK' cr' Aw').
{ apply (PMAUK.binv_callee L ar C HI HIok M0 model0 LBX FF LK0 Aw0 S 26624 (S - 128) (S - 104) S ocell own F fl 0 LK2 M2 model2 cr0 (PM.parser_own s0) G
WR WR (PM.parser_own s) ((qc, PM.CHUNK) :: PM.vs_own (PM.p_tb s)) (PM.parser_own s') Mc modelc LKc crc Ac M' model' LK' cr' Aw' 12288 Wc BI HP' HH1 AM' MRT' IAW' ILK');
[lia| lia| | | intros a X0; exact X0].
- intros rr a [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. unfold PMABK.ocell, PMABK.op in *. change (ff_bytes 0 / 8) with 8. unfold SB.
split; [lia|]. destruct FA1; lia.
- intros a _ O rr [<-|[]] Hr. apply (O (PMSPA.o_vec AD fb, 24)); [| exact Hr].
unfold PMABK.WR, PMSPA.W_run, PMSPA.W_srcf, PMSPA.err_W. cbn [app]. do 5 right. left. reflexivity. }
assert (EKp : L5SAR.ek L ar LBXp FF S 26624 Wc Mc M')
by exact (L5SAR.ek_callee L ar LBXp [] FF [(F, 0, S - 128 + 32)] S 26624 (S - 128) 12288 Wc Wc Mc M' HP' ltac:(lia) ltac:(lia) (fun a _ X0 => X0)).
assert (WAPPc : PMKA.wapp Wc).
{ apply PMKA.wapp_cons; [| apply PMKA.wapp_nil]. cbn [fst snd]. unfold PMABK.op. unfold BIGSHADOW_LO, BIGSHADOW_HI. destruct FA1; lia. }
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
destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q m (PMSPA.o_p AD fb + 360) 24 HHc Hq' (PMAUAR.aobjA_push FF (PMSPA.o_p AD fb + 360) 24 (F, 0, S - 128 + 32) (AOF (PMSPA.o_p AD fb + 360) 24 ltac:(lia) ltac:(lia)))) as [Z0|Z0];
unfold PMABK.op in Hr; lia. }
assert (DEF' : L5.defined M' (PMSPA.o_p AD fb) 384).
{ intros i Hi. apply (proj2 (proj2 HP')); [lia| | apply PDEF; exact Hi].
apply (L5SAR.fframe_client L ar _ FF' _ _ fb 4 rs); [exact HfbF| change (ff_bytes 4) with 1024; lia]. }
assert (PA' : PM.parser_at RSEGS AD PMSPA.accA PMSPA.annA M' (PMSPA.o_p AD fb) (PMSPA.o_is AD fb) s').
{ apply (parser_push_updA Mc M' _ _ s b' k' c PA); [clear - Eop Ff1 FA0; lia| clear - Eop Ff2 FA2; lia| | | exact DEF'| exact VEC'| unfold qc; clear - BRB Iq; destruct (BRB _ Iq) as (Q1 & Q2); cbn [fst snd] in *; lia| | |].
- apply (PMKA.agA_obj L ar _ FF S 26624 Wc Mc M' EKp WAPPc FRB (PMSPA.o_p AD fb) 360 (AOF (PMSPA.o_p AD fb) 360 ltac:(lia) ltac:(lia))). apply OUTc. unfold PMABK.op; lia.
- exact (PMKA.agsh_obj L ar _ FF S 26624 Wc Mc M' EKp WAPPc FRB (PMSPA.o_p AD fb) 384 (AOF (PMSPA.o_p AD fb) 384 ltac:(lia) ltac:(lia))).
- destruct (BRB _ Iq) as (Q1 & Q2). cbn [fst snd] in Q2. unfold qc in Q2. lia.
- apply (PMKA.agA_blk L ar _ FF S 26624 Wc Mc M' EKp WAPPc BRBp _ _ (or_introl eq_refl)). apply OUTB. left; reflexivity.
- intros c0 n0 p0 Etb. assert (Ip : In (p0, c0) LBXp) by (unfold LBXp; right; apply in_or_app; left; rewrite Etb; left; reflexivity).
apply (PMKA.agA_blk L ar _ FF S 26624 Wc Mc M' EKp WAPPc BRBp _ _ Ip). apply OUTB. exact Ip. }
assert (KPa : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LBXp FF' (S - 128) 12288 a -> L5.outside Wc a -> M' (Z_to_bv 64 a) = Mc (Z_to_bv 64 a))
by (intros a X1 X2 X3; apply (proj1 HP'); split; [exact X1| split; assumption]).
assert (KPR : forall a, S - 128 <= a < S -> M' (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)).
{ intros a Ha. apply KPa; [lia| apply (L5SAR.stack_client L ar _ FF' _ _ a); lia|]. intros rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. unfold PMABK.op in Hr. lia. }
assert (HD' : hdr M').
{ pose proof HD as (H0 & H8 & H16 & H128).
assert (KPF : forall a, F <= a < F + 24 -> M' (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)).
{ intros a Ha. apply KPa; [lia| apply (L5SAR.fframe_client L ar _ FF' _ _ F 0 (S - 128 + 32)); [left; reflexivity| change (ff_bytes 0) with 64; lia]|].
intros rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. unfold PMABK.op in Hr. destruct FAP; lia. }
split; [apply (L5C.u64_at_agree RSEGS Mc M'); [intros i Hi; apply KPF; lia| lia| lia| exact H0]|].
split; [apply (L5C.u64_at_agree RSEGS Mc M'); [intros i Hi; apply KPF; lia| lia| lia| exact H8]|].
split; [apply (L5C.u64_at_agree RSEGS Mc M'); [intros i Hi; apply KPF; lia| lia| lia| exact H16]|].
apply (L5C.u64_at_agree RSEGS Mc M'); [intros i Hi; apply KPR; lia| lia| lia| exact H128]. }
assert (FSH' : fsh typed M').
{ apply (fsh_agree typed Mc M'); [| exact DF1| lia| exact FSH].
intros x Hx. apply KPa; [lia| apply (L5SAR.fframe_shadow_client L ar _ FF' _ _ F 0 (S - 128 + 32)); [left; reflexivity|]|].
- change (ff_bytes 0) with 64. unfold in_shadow_of, HeapIfaceA.S, SB. change (ff_bytes 0) with 64 in F8. rewrite (proj1 (proj2 F8)). change (64 / 8) with 8. lia.
- intros rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. unfold PMABK.op in Hr. destruct FA1; lia. }
assert (EC' : PMSPA.ec_at RSEGS M' oec 0 cat).
{ apply (PMKA.ec_keepA RSEGS L ar _ FF S 26624 Wc Mc M' EKp WAPPc FRB oec 0 cat (AOF oec 16 ltac:(unfold PMABK.oec; lia) ltac:(unfold PMABK.oec; lia))); [| exact EC].
apply OUTc. unfold PMABK.oec, PMABK.op. lia. }
assert (RUN' : PMSPA.run_pre RSEGS AD PMA.AAD M' fb s' str sm e).
{ split; [exact PA'|].
split; [apply (PMKA.iss_keepA RSEGS AD L ar _ FF S 26624 Wc Mc M' EKp WAPPc FRB BRBp _ str sm (AOF (PMSPA.o_is AD fb) 272 ltac:(lia) ltac:(lia)));
[intros x Hx; unfold LBXp; right; apply in_or_app; right; apply INCS; exact Hx| apply OUTc; unfold PMABK.op; lia
| intros c0 n0 p0 Etb i Hi; apply (OUTB p0 c0); [unfold LBXp; right; apply in_or_app; right; apply INCS; rewrite Etb; left; reflexivity| exact Hi]
| exact IA]|].
split; [apply (PMKA.visitor_keepA RSEGS AD L ar _ FF S 26624 Wc Mc M' EKp WAPPc FRB (PMSPA.o_v AD fb) (AOF (PMSPA.o_v AD fb) 8 ltac:(lia) ltac:(lia))); [apply OUTc; unfold PMABK.op; lia| exact VIS]|].
split; [apply (PMKA.u64_keepA RSEGS L ar _ FF S 26624 Wc Mc M' EKp WAPPc FRB (PMSPA.o_p AD fb + 384) (PMSPA.o_v AD fb) (AOF (PMSPA.o_p AD fb + 384) 8 ltac:(lia) ltac:(lia)));
[apply OUTc; unfold PMABK.op; lia| exact VREF]|].
split; [apply (PMASK.base_keep L ar C LY _ FF S 26624 Wc Mc M' EKp); [| exact BASE]; intros a Ha rr [<-|[]] Hr; unfold L5.in_rng in Hr; cbn [fst snd] in Hr; unfold PMABK.op in Hr; lia|].
split; [apply (PMKA.err_okA_keep RSEGS AD PMA.AAD L ar _ FF S 26624 Wc Mc M' EKp e PMA.addrs_wf_A); [| exact ERR];
intros a D; pose proof (PMASK.dep_img a D) as DI; rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa); split; [lia|];
split; [exact (PMA.ly_static L C LY a D)| intros rr [<-|[]] Hr; unfold L5.in_rng in Hr; cbn [fst snd] in Hr; unfold PMABK.op in Hr; lia]|].
exact TBOK. }
assert (INV' : PM.inv s').
{ unfold PM.inv, s', push_st. cbn [PM.p_more PM.p_done PM.p_depth PM.p_stk PM.p_tb PM.p_tg].
split; [rewrite SDm; exact IM|]. split; [rewrite SDd; exact ID|].
split; [rewrite SDp, SDs, length_app; cbn [length]; lia|].
split; [rewrite SDs; exact (stack_shape_push _ c ISH HL Hc Hm)| exact TBOK]. }
assert (PV' : PMSPA.prog_value s0 s' sm0 sm).
{ right. exists c. split; [unfold s', push_st; cbn [PM.p_stk]; rewrite SDs; reflexivity|]. split; [exact Hc|]. split; [exact Hidx|]. split; [exact Hm| exact Hcnt]. }
apply (NEXT fx' R' M' model' LK' Aw' s' cr' RP'); [| reflexivity| exact KPR].
destruct PO' as [(_ & _ & _ & Eb & Ek & Ecr)|(Hg & Ek & Ecr)].
- assert (EP : pot s' = pot s) by (unfold s', push_st, PM.pot_parser; cbn [PM.p_k PM.p_tb PM.p_tg]; rewrite Ek; reflexivity).
subst cr'. split; [exact BI'|]. split; [exact RUN'|]. split; [exact EC'|]. split; [exact HD'|]. split; [exact FSH'|]. split; [exact STEP0|].
split; [exact E0|]. split; [exact INV'|]. split; [exact PV'|]. rewrite EP. split; [exact CRL| exact CRK].
- rewrite Bnz in Ek. subst k' cr'.
destruct (stk_credit s crc TBOK Cap) as (_ & CKs).
{ destruct Hg as [Hg|Hg]; [discriminate Hg|]. pose proof (K10 Hg). lia. }
{ exact CRL. }
specialize (CKs s' eq_refl eq_refl eq_refl).
split; [exact BI'|]. split; [exact RUN'|]. split; [exact EC'|]. split; [exact HD'|]. split; [exact FSH'|]. split; [exact STEP0|].
split; [exact E0|]. split; [exact INV'|]. split; [exact PV'|].
split; [exact (PMAPAR.credit_le_keepA _ _ _ _ CRL CKs)| exact (PMAPAR.credit_keep_transA _ _ _ _ _ _ CRK CKs)].
Qed.
End Frame.
End Call.
End WithHeap.
End PMABK3.
