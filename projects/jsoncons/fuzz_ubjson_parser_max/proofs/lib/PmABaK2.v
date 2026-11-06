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
PmModelFactsA PmStepA PmStep PmParStep PmParKit PmASrcKit PmAParKit PmAReset1 PmAUarK PmAUar PmAUarKS PmABaK.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmABaK2 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmABaK.PMABK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmABaK2.PMABK2.WithHeap.Call.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0Ac"; "0Aw'"; "0Aw0"; "0BX"; "1app"; "1bool"; "1list"; "1option"; "1prod"; "2and"; "2eq"; "2ex"; "2not"; "2or"; "3Z"; "0F"]; ["0FF"; "0HI"; "0K"; "0L"; "0LBX"; "0LK'"; "0LK0"; "0LKc"; "4Model"; "5bvmap"; "0M'"; "0M0"; "0M1"; "0M1v"; "0Ma"; "0Mb"]; ["0Mc"; "0R"; "0R'"; "0R0"; "0R1"; "6mrestrict"; "7msteps"; "8credit"; "8regs_preserved"; "9aclient"; "9ahid"; "9fframe"; "9ri_inv"; "9vml"; ";in_rng"; ";ra_ok"]; [";range"; ":SCFG"; "<FF'"; "<SCR"; "<WR"; "<binv'"; "<bst"; "<fsh"; "<hdr"; "<oec"; "<op"; "=bsterr"; ">AADDR_A"; ">ADDR_A"; "?p_src"; "?parser_own"]; ["?pst"; "?strm"; "?unread"; "@cfg"; "@ec_at"; "@run_pre"; "AFPState"; "Agetr"; "Amkst"; "Aseg_rom"; "Bsrealizes"; "Cmem_grows"; "Dloaded_segments"; "0S"; "0SCFG_P"; "EIn"]; ["Fadd"; "Fdiv"; "Fle"; "Flt"; "Fof_nat"; "Fpow"; "Fsub"; "0V"; "0Wp"; "0X"; "0a"; "0ar"; "0c"; "0cat"; "0cr'"; "0cr0"]; ["0crc"; "0e"; "0e'"; "0e0"; "0fb"; "0fx"; "0fx'"; "0fx1"; "0len"; "0model'"; "0model0"; "0model1"; "0modelc"; "0pc"; "0pc1"; "0rr"]; ["0s"; "0s'"; "0s0"; "0sm"; "0sm'"; "0sm0"; "GZ_to_bv"; "Gbv"; "0str"; "0typed"; "0typed'"; "0v"]]).
Local Ltac lia := L5FastLia.plia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PMABK2.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation AD := PMA.AD.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.
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
Lemma fsh_nc : ltac2:(TCodec.tc2 tcn__PmABaK2 "R2'6'8'>%2211%411&Q;%611&Q7'SGyR0%211'7y8%511%311p051&Q=&Q<vA&4r6vD%33C21&QBv@vR=v?%43321r5r4r3r2r1%@8?;654321'9&RB&R@&RA+8%22=1+QoooPP0%5221%721:&RC+QoooPP8%9261%32>1%=251&<&Q9vCvRKr9%Q23QB1Q0&QC%67542ON1H%811p0:1pUFQH1p0J1pU@Q<1pR2Q>1p2QJ1pV2QH1pQ@QJ1p8QM1").
Proof using G HIok. intros BX LKc crc Ac Mc V.
intros HH a Ha.
pose proof G as G'. destruct G' as [Hk SPTg SLOg SHIg SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
change (ff_bytes 0) with 64 in *. unfold FS_BYTES in *. destruct F8 as (F8a & F8b & F8c).
assert (NC0 : ~ aclient L ar LBX FF S SCR a).
{ apply NCF. right. unfold HeapIfaceA.S, SB. split; [lia|].
assert (E : (F + 64 - 1) / 8 = F / 8 + 7) by (rewrite F8b; change (64 / 8) with 8; lia). lia. }
pose proof (L5ADHR.blocks_off_fs L ar C HI HIok _ _ _ _ _ _ _ BX LBX HH eq_refl) as BOF.
clear HH. revert BOF. induction BX as [|b BX IH]; intros HB; [exact NC0|]. cbn [app]. intros X.
destruct (L5SAR.aclient_consb_inv L ar (BX ++ LBX) FF b S SCR a X) as [Y|[Y|Y]].
- exact (IH (fun b' H' => HB b' (or_intror H')) Y).
- destruct (HB b (or_introl eq_refl)) as ((_ & _ & _ & _ & _ & AMb) & _). unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in AMb.
assert (F / 8 <= 17592186044408) by (apply Z.div_le_upper_bound; lia). lia.
- destruct (HB b (or_introl eq_refl)) as ((B4 & _ & _ & Bn & _) & Z0). unfold in_shadow_of, HeapIfaceA.S, SB in Y. unfold FS_BYTES in Z0.
destruct Z0 as [Z0|Z0].
+ assert (D : (fst b + snd b - 1) / 8 <= (F - 1) / 8) by (apply Z.div_le_mono; lia).
assert (E : (F - 1) / 8 = F / 8 - 1).
{ assert (E1 : F - 1 = 7 + (F / 8 - 1) * 8) by (rewrite <- F8a at 1; ring). rewrite E1. rewrite Z.div_add by lia. change (7 / 8) with 0. ring. } lia.
+ assert (D : (F + 64) / 8 <= fst b / 8) by (apply Z.div_le_mono; lia).
assert (E : (F + 64) / 8 = F / 8 + 8).
{ assert (E1 : F + 64 = (F / 8 + 8) * 8) by (rewrite <- F8a at 1; ring). rewrite E1. rewrite Z.div_mul by lia. ring. } lia.
Qed.
Lemma fsh_agree : ltac2:(TCodec.tc2 tcn__PmABaK2 "QI'5'SGyR0%211'7y8%511%311p051'>'9&RB&R@&RAv?+8%3221+QoooPP0%6221r1%9221&RC+QoooPP8%;271%3251%?251':r3&SFr2%22L1%411r4%113%83K31p0:1pUFK1z%K21F&RE+2+R0%3221%Q02D1&QGr6r5%33Q121r7%53Q313p031p081p0>1p0A1pR0Q>1pQNQ?1pWDQH1").
Proof. intros typed Ma Mb.
intros AG H1 H2 (Y0 & Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7).
unfold PMABK.fsh. repeat split; (apply (L5C.u8_at_agree RSEGS Ma Mb); [intros i Hi; apply AG; lia| lia| lia| assumption]).
Qed.
Lemma step_piece : ltac2:(TCodec.tc2 tcn__PmABaK2 "VI'5'R0'R1'>'R6&Iy5'SGyR0%211%5241'7y8%611%311p061'H'6&Q;%211&Q7'8%12CC%611!p0F1&QEvCvRKvAvQ3vKvS:vDv@vFv2vR=vS4v?&QOrB%211r6r5r4r3r2%FCEDCBA@?>=<;:9654321&R5&R<&QM&QLr7rCvSHrA%897654C32@1&R4r8&QI%11Gr@%55=4271&QHr9%23MK1'Q6&R8r?&SFr>%22R01&Q5&Q:%12Q0:r:%4221&R9%11M%<5H;831r=r<%=2R;1r;%A5G4216%C3Q461&R;%>2Q3<%@215%3218'9&RBzr1%3221&RC&RE+2+R0%3221%5271%;271&<%Q71QI%211':%Q52S3QM%Q>11%Q32IQ6%Q531Q93%53S131p071p0;1pUFS?1%QB1E'=&RF+SH%22RB1%L21R9+S8%52RE1%K2R<1%Q1241&R@&RA+8%22RI1+QoooPP4%5221%I3T0RD1%@281p0B1pUFT31&QGrK%23S21R4rM%S311%SBCSAS@S?S>S=S<S;S:S9S8S7S6S51RMQ>R7R5QKrNrL%RN9RMRLRKS1S92RH51%RF5RNS3RC28%RA3S<S:S5rQ2%<3S<1S8rE%R;2S<1%R=21S1rG%Q>3T921p0T@TI%R@2S4S5rF%RB2S61%QC3431%:1S?%QH11%R>1QE%I1QF%QH3TD21p041p0QN1pUFU21'R:&QAvR>%211&R3rO%26SJ1NQ4S0S;vB%84SL521p0:1p0C1p0I1p0O1p0Q21p0Q41p0Q61p0Q:1pVHU71pQJU91rD%@6T8Q3Q61SLSE%E4T9B1>p041p0QD1p0QH1p0R=1p0S61p0S;1p0T01p0T41p0T;1p0TE1pUBU=1p2U@1pV2UD1pQ@UF1pVJUJ1pR2UL1pQLUM1pVNV:1pR:V41pVLV<1pR4V61pV@V=1pV<V>1pUJV@1pWHVA1pV4VE1pW8VD1pW2VF1pWFVH1").
Proof using All. intros typed' s sm e v c fx fx1 R pc R1 pc1 M1v Mc modelc LKc crc Ac Wp.
intros BI RP EC HD MS MG FZ WPin FSH1 NEXT.
pose proof BI as BI'. destruct BI' as (HHc & AMc & MRTc & IAc & ILKc & ASTKc & EKc & DKc & OWNc & SHDc).
pose proof RP as (PA & IA & VIS & VREF & BASE & ERR & TBOK).
pose proof G as G'. destruct G' as [Hk SPTg SLOg SHIg SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
change (ff_bytes 0) with 64 in *. unfold SCR in *.
pose proof (PMAUK.vis_facts L ar C HI LYa HIok M0 model0 LBX FF LK0 Aw0 S SCR (S - 128) (S - 104) S ocell own F fl 0 LK2 M2 model2 cr0 (PM.parser_own s0) G WR _ Mc modelc LKc crc Ac BI)
as (_ & _ & _ & (_ & _ & _ & _ & SHV8)). change (ff_bytes 0 / 8) with 8 in SHV8.
assert (DF1 : 0 <= F / 8) by (apply Z.div_pos; lia). assert (DF2 : F / 8 <= 17592186044408) by (apply Z.div_le_upper_bound; lia).
apply (L5SAR.apiece L ar C HI LYa HIok (PM.parser_own s ++ LBX) FF' LKc crc Ac Mc modelc fx fx1 R pc R1 pc1 M1v Wp K HHc AMc MS MG FZ).
{ intros a Ha Wa. destruct (WPin a Wa) as [X|X].
- split; [unfold aclientw, aclient_g; right; left; split; [lia| intros Y; lia]| lia].
- split; [| lia]. apply (L5SAR.fframe_shadow_client L ar _ FF' 0 0 F 0 (S - 128 + 32)); [left; reflexivity|].
change (ff_bytes 0) with 64. unfold in_shadow_of, HeapIfaceA.S, SB. change (ff_bytes 0) with 64 in F8. rewrite (proj1 (proj2 F8)). change (64 / 8) with 8. lia. }
intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
assert (BI1 : binv' (PM.parser_own s) M1 model1 LKc crc Ac).
{ apply (PMAUK.binv_pieceW L ar HI M0 model0 LBX FF LK0 Aw0 S SCR (S - 128) (S - 104) S ocell own F fl 0 LK2 M2 model2 cr0 (PM.parser_own s0) G
WR (PM.parser_own s) Mc modelc LKc crc Ac M1 model1 Wp BI HH1 AM1 MRT1 MGM1 FR1).
intros a Wa. unfold PMABK.ocell. destruct (WPin a Wa) as [X|X]; (split; [lia|]).
- left; lia.
- right; right; left. unfold SB. change (ff_bytes 0 / 8) with 8. lia. }
assert (EK1 : L5SAR.ek L ar (PM.parser_own s ++ LBX) FF S 26624 [] Mc M1).
{ apply (L5SAR.ek_piece L ar _ FF S 26624 [] Mc M1 Wp FR1). intros a Ha Hc _ Wa. destruct (WPin a Wa) as [X|X].
- destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF' LKc crc Ac Mc _ S 26624 a HHc SPTg (L5SAR.aclient_cons L ar _ FF _ _ _ _ Hc)) as [Y|Y]; lia.
- apply (fsh_nc (PM.parser_own s) LKc crc Ac Mc _ HHc a ltac:(lia)). unfold SCR. exact Hc. }
pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HHc) as FRB'. pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HHc) as BRB.
assert (FRB : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47) by (intros f Hf; apply FRB'; right; exact Hf).
pose proof FOK as ((rs & Hfb) & Fal).
assert (AOF : forall a n, fb + 32 <= a -> a + n <= fb + 1016 -> PMSPA.aobjA FF a n)
by (intros a n X1 X2; exists (fb, 4, rs); split; [exact Hfb|]; cbn [ff_addr ff_class fst snd]; change (ff_bytes 4) with 1024; lia).
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHc) as (WB & WF & FSAPP & FSCEIL & _).
destruct (WF _ (or_intror Hfb)) as (Ff1 & Ff2 & _). cbn [ff_addr ff_class fst snd] in Ff1, Ff2. change (ff_bytes 4) with 1024 in Ff2.
pose proof (PMABK.frame_geo fb) as (Eop & Eois & Eov & Eoec & Eos).
apply (NEXT M1 model1 BI1).
- split; [apply (PMKA.parser_keepA RSEGS AD L ar _ FF S 26624 [] Mc M1 EK1 PMKA.wapp_nil FRB BRB _ _ _ (AOF (PMSPA.o_p AD fb) 384 ltac:(lia) ltac:(lia)));
[apply incl_appl, incl_refl| intros i _ r0 []| intros i _ r0 []| intros i _ r0 []| intros c0 n0 p0 _ i _ r0 []| exact PA]|].
split; [apply (PMKA.iss_keepA RSEGS AD L ar _ FF S 26624 [] Mc M1 EK1 PMKA.wapp_nil FRB BRB _ str sm (AOF (PMSPA.o_is AD fb) 272 ltac:(lia) ltac:(lia)));
[intros x Hx; apply in_or_app; right; apply INCS; exact Hx| intros i _ r0 []| intros c0 n0 p0 _ i _ r0 []| exact IA]|].
split; [apply (PMKA.visitor_keepA RSEGS AD L ar _ FF S 26624 [] Mc M1 EK1 PMKA.wapp_nil FRB (PMSPA.o_v AD fb) (AOF (PMSPA.o_v AD fb) 8 ltac:(lia) ltac:(lia))); [intros i _ r0 []| exact VIS]|].
split; [apply (PMKA.u64_keepA RSEGS L ar _ FF S 26624 [] Mc M1 EK1 PMKA.wapp_nil FRB (PMSPA.o_p AD fb + 384) (PMSPA.o_v AD fb) (AOF (PMSPA.o_p AD fb + 384) 8 ltac:(lia) ltac:(lia)));
[intros i _ r0 []| exact VREF]|].
split; [apply (PMASK.base_keep L ar C LY _ FF S 26624 [] Mc M1 EK1); [intros a _ r0 []| exact BASE]|].
split; [apply (PMKA.err_okA_keep RSEGS AD PMA.AAD L ar _ FF S 26624 [] Mc M1 EK1 e PMA.addrs_wf_A); [| exact ERR];
intros a D; pose proof (PMASK.dep_img a D) as DI; rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa); split; [lia|];
split; [exact (PMA.ly_static L C LY a D)| intros r0 []]|].
exact TBOK.
- apply (PMKA.ec_keepA RSEGS L ar _ FF S 26624 [] Mc M1 EK1 PMKA.wapp_nil FRB oec v c (AOF oec 16 ltac:(unfold PMABK.oec; lia) ltac:(unfold PMABK.oec; lia))); [intros i _ r0 []| exact EC].
- pose proof HD as (H0 & H8 & H16 & H128).
assert (KP : forall a, (F <= a < F + 24 \/ S - 128 <= a < S - 120) -> M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a))
by (intros a Ha; apply FR1; [lia| intros Wa; destruct (WPin a Wa) as [X|X]; lia]).
split; [apply (L5C.u64_at_agree RSEGS Mc M1); [intros i Hi; apply KP; lia| lia| lia| exact H0]|].
split; [apply (L5C.u64_at_agree RSEGS Mc M1); [intros i Hi; apply KP; lia| lia| lia| exact H8]|].
split; [apply (L5C.u64_at_agree RSEGS Mc M1); [intros i Hi; apply KP; lia| lia| lia| exact H16]|].
apply (L5C.u64_at_agree RSEGS Mc M1); [intros i Hi; apply KP; lia| lia| lia| exact H128].
- apply (fsh_agree typed' M1v M1); [| exact DF1| lia| exact FSH1].
intros a Ha. rewrite <- VIS1. symmetry. apply mrestrict_visible. replace a with (F / 8 + SB + (a - (F / 8 + SB))) by (unfold SB; lia). apply SHV8. unfold SB; lia.
- exact VIS1.
- exact HID1.
- exact FR1.
Qed.
Lemma wr_rng : ltac2:(TCodec.tc2 tcn__PmABaK2 "Q7&Q@'>&R?r2&QDvS4%211%53741&Q>r3%2217'='9&RB&R@+Q0%22;1%4218&RC+oH%62?1%32<1%:251+V]dl0%;21?+V]dl2%82A1%?231+Vak^@%@21D+Vako@%=2F1%D231%F261%G2<1p0I1p0M1pUFQ41pW0Q61").
Proof. intros rr a.
intros Hin Hr. unfold PMABK.WR, PMSPA.W_run, PMSPA.W_srcf, PMSPA.err_W, PMSPA.o_src, PMSPA.o_is, PMSPA.o_tb, PMSPA.o_vec, PMSPA.o_ec, PMSPA.o_p in Hin.
cbn [app pa_off_p pa_off_is pa_off_ec pa_errcat_guard pa_atexit PMA.AD ADDR_A] in Hin. unfold L5.in_rng in Hr.
repeat (destruct Hin as [<-|Hin]; [cbn [fst snd] in Hr; lia|]). destruct Hin.
Qed.
Definition bsterr (typed : bool) (s : PM.pst) (sm : PM.strm) (Mc : word -> option byte) (modelc : Model) (LKc : list fframe) (crc : credit) (Ac : list (Z * Z)) : Prop :=
binv' (PM.parser_own s) Mc modelc LKc crc Ac
/\ PMSPA.run_pre RSEGS AD PMA.AAD Mc fb s str sm true /\ (exists v, 1 <= v <= 64 /\ PMSPA.ec_at RSEGS Mc oec v (pa_errcat_obj AD)) /\ PM.p_more s = 0
/\ hdr Mc /\ fsh typed Mc
/\ PMSPA.src_step (PM.p_src s0) (PM.p_src s) sm0 sm
/\ PMSPA.credit_le (PMSPA.scA L (PM.pot_parser (PMSPA.HV L ar) s)) crc
/\ PMSPA.credit_keep cr0 crc (PMSPA.scA L (PM.pot_parser (PMSPA.HV L ar) s0)) (PMSPA.scA L (PM.pot_parser (PMSPA.HV L ar) s)).
Lemma call_gl : ltac2:(TCodec.tc2 tcn__PmABaK2 "V3'5'R0'R1'R6&Iy5'SGyR0%211%5241'7y8%611%311p061'H'6&Q;%211&Q7'8'>%2211%711&QFvCvRKvAvQ3vKvS:vDv@vFv2vROvR=vS4vRMvSBvSHvSEvS3v?r<r;r:r9r6r5r4r3r2%MLLKJIHGFEDCBA@?>=<;:987654321':&R7r8&SF&RDu1%211%42QH1%7261%62QH;%:3QH21&Q?%11?u2%:11%<2R01%?2H1&RF+T0%22Q51%A2R31%E3R351u3%C11%E2R91%H2Q21%I2QD2%K3R921u4%I11%K2R?1%N2Q91%O2QJ2%Q13R?21r=u:%Q011%Q22RF1%Q5241&QJ%11QI%Q62RH1%Q:3RH41r>u;%Q911%Q;2RO1%Q>241&QI%11R2%Q?2S11%QC3S141&Q8rI%221QM'='9rOr7%RILRHRGRFRERDRCRBRAR@R?R>R=R<R;R:R9R8R7R62R0QOQNR2QI1QMR1&RC&R2&QN%11R4%321R4rN%411rM%7221%9251';&RBzr1%3221&RE+2+R0%3221%C261%H261%R@2RJQ<%R?2T19%RC3T121%L241qVBSF1%@2SG1%O2B1%Q02M1&QK%18Q1RORNS1RHQ0RLS0%Q4231'R:&R<&QAvR>%211&R3rE%266S=S<1S;S:vB%948521p0;1p0QA1pUNT;1pV6TO1pW:TN1pW4U01p4T;1pQ<TA1pVDTE1pQFTG1pR6TM1pV>U41rAr@+eoa<r?%E6I4321R;%K4JG1Cp071p0R61p0R@1p0RJ1p0S11p0S81p0SB1p0SE1p0T11pUDU21p2U11pV2U61pQ@U81pVJU<1pR2U>1pR4UD1pV<UK1pV4UO1pW8UN1pW2V01pWDV21").
Proof using All. intros typed s sm e fx R Mc modelc LKc crc Ac X.
intros BS A1 RAX A2 A3 A4 A10 A11 NEXT.
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
pose proof INV as (IM & ID & IDP & ISH & ITB).
pose proof SD as (SDm & SDd & SDp & SDs).
pose proof STEP0 as (_ & _ & _ & _ & UNR').
unfold PMA.get_length_spec, PMSPA.get_length_spec in GLS. cbn [pa_get_length PMA.AD ADDR_A] in GLS.
apply (GLS 1 ltac:(lia) fx R Mc modelc K LBX FF' LKc Ac crc (S - 128) X fb cat s str sm e HHc AMc K0).
{ exact (PMABK.centry L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT
PEEK IGN SRD GLS MKE PMI PMS PMSU F fl LK2 M2 model2 G R Mc X 5 ASTKc EKc A1 RAX A2 A3 A4 ltac:(lia)). }
{ apply (PMAUAR.ffroomA_push 7 5 FF LK0 LKc _ FRM ILKc); [exact NDF| lia]. }
{ apply (PMAUAR.ffrsA_push FF S (S - 128) F 0 (S - 128 + 32) FRS); lia. }
{ apply PMAUAR.frame_okA_push. exact FOK. }
{ replace (S - 128) with (S + (-4) * 32) by lia. rewrite Z_mod_plus_full. exact SP32. }
{ split; [rewrite L5K.rl10; exact A10| rewrite L5SAR.r11; exact A11]. }
{ exact RP. }
{ exact INCS. }
{ unfold PM.inv_d. rewrite SDm, SDd, SDp, SDs. split; [exact IM|]. split; [exact ID|]. split; [lia|]. split; [exact ISH| exact TBOK]. }
{ exact EC. }
{ lia. }
{ exact CRL. }
intros fx' R' M' model' LK' Aw' s' sm' e' cr' RP' POST' HP' CK' MRT' ILK' IAW' AM' HH'.
change (PMSPA.pm_scr 5) with 22528 in HP'.
destruct POST' as (RUN' & STEP' & E' & OUT').
pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HHc) as FRB'.
assert (DF1 : 0 <= F / 8) by (apply Z.div_pos; lia). assert (DF2 : F / 8 <= 17592186044408) by (apply Z.div_le_upper_bound; lia).
pose proof FSAPP as (FA0 & FA1 & FA2). unfold BIGSHADOW_LO, BIGSHADOW_HI in FA1.
assert (BI' : binv' (PM.parser_own s') M' model' LK' cr' Aw').
{ apply (PMAUK.binv_callee L ar C HI HIok M0 model0 LBX FF LK0 Aw0 S 26624 (S - 128) (S - 104) S ocell own F fl 0 LK2 M2 model2 cr0 (PM.parser_own s0) G
WR WR (PM.parser_own s) [] (PM.parser_own s') Mc modelc LKc crc Ac M' model' LK' cr' Aw' 22528 WR BI HP' HH' AM' MRT' IAW' ILK');
[lia| lia| | intros a _ X0; exact X0| intros a X0; exact X0].
intros rr a Hin Hr. unfold PMABK.ocell. change (ff_bytes 0 / 8) with 8. unfold SB.
destruct (wr_rng rr a Hin Hr) as [X0|[X0|X0]]; (split; [lia|]); [destruct FA1; lia| lia| lia]. }
assert (KPa : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LBX FF' (S - 128) 22528 a -> L5.outside WR a -> M' (Z_to_bv 64 a) = Mc (Z_to_bv 64 a))
by (intros a X1 X2 X3; apply (proj1 HP'); split; [exact X1| split; assumption]).
assert (HD' : hdr M').
{ pose proof HD as (H0 & H8 & H16 & H128).
assert (KPF : forall a, F <= a < F + 24 -> M' (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)).
{ intros a Ha. apply KPa; [lia| apply (L5SAR.fframe_client L ar _ FF' _ _ F 0 (S - 128 + 32)); [left; reflexivity| change (ff_bytes 0) with 64; lia]|].
intros rr Hin Hr. destruct (wr_rng rr a Hin Hr) as [X0|[X0|X0]]; [destruct FAP; lia| lia| lia]. }
assert (KPS : forall a, S - 128 <= a < S - 120 -> M' (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)).
{ intros a Ha. apply KPa; [lia| apply (L5SAR.stack_client L ar _ FF' _ _ a); lia|]. intros rr Hin Hr. destruct (wr_rng rr a Hin Hr) as [X0|[X0|X0]]; lia. }
split; [apply (L5C.u64_at_agree RSEGS Mc M'); [intros i Hi; apply KPF; lia| lia| lia| exact H0]|].
split; [apply (L5C.u64_at_agree RSEGS Mc M'); [intros i Hi; apply KPF; lia| lia| lia| exact H8]|].
split; [apply (L5C.u64_at_agree RSEGS Mc M'); [intros i Hi; apply KPF; lia| lia| lia| exact H16]|].
apply (L5C.u64_at_agree RSEGS Mc M'); [intros i Hi; apply KPS; lia| lia| lia| exact H128]. }
assert (FSH' : fsh typed M').
{ apply (fsh_agree typed Mc M'); [| exact DF1| lia| exact FSH].
intros x Hx. apply KPa; [lia| apply (L5SAR.fframe_shadow_client L ar _ FF' _ _ F 0 (S - 128 + 32)); [left; reflexivity|]|].
- change (ff_bytes 0) with 64. unfold in_shadow_of, HeapIfaceA.S, SB. change (ff_bytes 0) with 64 in F8. rewrite (proj1 (proj2 F8)). change (64 / 8) with 8. lia.
- intros rr Hin Hr. destruct (wr_rng rr x Hin Hr) as [X0|[X0|X0]]; unfold BIGSHADOW_LO, BIGSHADOW_HI in *; [destruct FA1; lia| lia| lia]. }
pose proof (PMAPAR.credit_keep_transA _ _ _ _ _ _ CRK CK') as CK0.
pose proof (PMAPAR.credit_le_keepA _ _ _ _ CRL CK') as CL'.
apply (NEXT fx' R' M' model' LK' Aw' s' sm' e' cr' RP').
destruct OUT' as [(v & Hv & ECv & MO & Et)|(ECo & INVd & (PST & PUN & PLEN))].
- right. subst e'. split; [exact BI'|]. split; [exact RUN'|]. split; [exists v; split; [exact Hv| exact ECv]|]. split; [exact MO|].
split; [exact HD'|]. split; [exact FSH'|]. split; [exact (PMAPAR.src_step_transA _ _ _ _ _ _ STEP0 STEP')|]. split; [exact CL'| exact CK0].
- left. split; [| split; [exact PUN| exact PLEN]].
split; [exact BI'|]. split; [exact RUN'|]. split; [exact ECo|]. split; [exact HD'|]. split; [exact FSH'|].
split; [exact (PMAPAR.src_step_transA _ _ _ _ _ _ STEP0 STEP')|]. split; [intros X0; exact (E' (E0 X0))|].
split; [pose proof INVd as (Jm & Jd & Jp & _); unfold PMABK.sdl; split; [rewrite Jm, IM; reflexivity|]; split; [rewrite Jd, ID; reflexivity|];
split; [rewrite PST, SDs in Jp; lia| rewrite PST; exact SDs]|].
split; [exact CL'| exact CK0].
Qed.
End Frame.
End Call.
End WithHeap.
End PMABK2.
