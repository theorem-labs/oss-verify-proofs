(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceA LibIface AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsA L5CoreA L5CoreSpecsA L5StepAR L5CoreBR L5ADetailHR PmLayout PmLayoutA PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceAJx PmSpecsA PmSpecsAX PmSpecsAa PmModelFactsA PmStepA PmStep PmParStep PmParKit PmASrcKit PmAParKit PmAReset1 PmAUarK PmAUar PmAUarKS PmABaK PmABaK2 PmABaK3.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmABa1 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmABaK.PMABK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayout."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmParKit.PMPK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0Ac"; "0Aw0"; "0BX"; "1app"; "1bool"; "1cons"; "1list"; "1nat"; "1nil"; "1option"; "1prod"; "1true"; "2and"; "2eq"; "2ex"; "2not"]; ["2or"; "3Z"; "0F"; "0FF"; "0HI"; "0K"; "0L"; "0LBX"; "0LK0"; "0LKc"; "4Model"; "5bvmap"; "0M0"; "0M9v"; "0Mc"; "0R0"]; ["0R9"; "0Rc"; "6mrestrict"; "7msteps"; "8credit"; "9aclient"; "9ahid"; "9fframe"; "9ri_inv"; "9vml"; ";u8_at"; ":SCFG"; "<FF'"; "<SCR"; "<U"; "<binv'"]; ["<oec"; "<op"; "=pa_errcat_obj"; ">AADDR_A"; ">ADDR_A"; "?inv"; "?p_src"; "?parser_own"; "?pot_parser"; "?pst"; "?strm"; "@set_more"; "AHV"; "Acfg"; "Acredit_keep"; "Aec_at"]; ["Aprog_value"; "Arun_pre"; "AscA"; "Asrc_step"; "BFPState"; "Bgetr"; "Bmkst"; "Bseg_rom"; "Csrealizes"; "Dmem_grows"; "Eloaded_segments"; "0S"; "0SCFG_P"; "FIn"; "Gadd"; "Gdiv"]; ["Gle"; "Glt"; "Gof_nat"; "Gpow"; "Gsub"; "0V"; "0Wy"; "0a"; "0ar"; "0cat"; "0cr0"; "0crc"; "0e'"; "0e0"; "0fb"; "0fl"]; ["0fx"; "0fx9"; "0j"; "0model0"; "0modelc"; "0pc"; "0s"; "0s0"; "0sm"; "0sm0"; "HZ_to_bv"; "Hbv"; "0str"; "0v"; "0vm"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc. Local Ltac lia := L5FastLia.plia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PMABA1.
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
Local Abbreviation fsh_nc := (PMABK2.fsh_nc L ar C HI HIok R0 LBX FF LK0 Aw0 cr0 S s0 F fl LK2 M2 model2 G).
Local Abbreviation fsh_agree := (PMABK2.fsh_agree S F).
Local Abbreviation step_piece := (PMABK2.step_piece L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE PMI PMS PMSU F fl LK2 M2 model2 G).
Local Abbreviation wr_rng := (PMABK2.wr_rng fb).
Local Abbreviation bsterr := (PMABK2.bsterr L ar HI R0 M0 model0 LBX FF LK0 Aw0 cr0 S fb s0 str sm0 F).
Local Abbreviation call_gl := (PMABK2.call_gl L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE PMI PMS PMSU F fl LK2 M2 model2 G).
Local Abbreviation push_st := PMABK3.push_st.
Local Abbreviation aacc_sub := PMABK3.aacc_sub.
Local Abbreviation parser_push_updA := PMABK3.parser_push_updA.
Local Abbreviation stack_shape_push := PMABK3.stack_shape_push.
Local Abbreviation ri_swap12 := (PMABK3.ri_swap12 L ar C HI HIok).
Local Abbreviation stk_credit := (PMABK3.stk_credit L ar C LY).
Local Abbreviation bstp := (PMABK3.bstp L ar HI R0 M0 model0 LBX FF LK0 Aw0 cr0 S fb cat s0 str sm0 e0 F).
Local Abbreviation call_push := (PMABK3.call_push L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE PMI PMS PMSU F fl LK2 M2 model2 G).
Abbreviation pot := (fun (s : PM.pst) => PMSPA.scA L (PM.pot_parser (PMSPA.HV L ar) s)).
Lemma fframe_nc : ltac2:(TCodec.tc2 tcn__PmABa1 "QM'6':'A%2211%411&Q7%611&Q4'S;yR0%211'9y8%511%311p051&Q9&Q8vD&3r6vG%33C21&Q<vCvR;vB%43321r5r4r3r2r1%@8?;654321'<&R@%12:4&RA&R>+R0%22>1%4291%8261&?&Q5vFvRHr9%M3Q=1K&Q=%67542JI1C%811p0:1pU@QC1p0E1pU<Q71pQNQ91p2QE1pUHQC1pQDQE1p6QH1").
Proof using G HIok. intros BX LKc crc Ac Mc V.
intros HH a Ha.
pose proof G as G'. destruct G' as [Hk SPTg SLOg SHIg SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
change (ff_bytes 0) with 64 in *. unfold FS_BYTES in *.
assert (NC0 : ~ aclient L ar LBX FF S SCR a) by (apply NCF; left; lia).
pose proof (L5ADHR.blocks_off_fs L ar C HI HIok _ _ _ _ _ _ _ BX LBX HH eq_refl) as BOF.
clear HH. revert BOF. induction BX as [|b BX IH]; intros HB; [exact NC0|]. cbn [app]. intros X.
destruct (L5SAR.aclient_consb_inv L ar (BX ++ LBX) FF b S SCR a X) as [Y|[Y|Y]].
- exact (IH (fun b' H' => HB b' (or_intror H')) Y).
- destruct (HB b (or_introl eq_refl)) as (_ & Z0). unfold FS_BYTES in Z0. lia.
- destruct (HB b (or_introl eq_refl)) as ((B4 & _ & _ & Bn & Bc & AMb) & _). unfold in_shadow_of, HeapIfaceA.S, SB in Y. unfold app_mem in AMb.
assert (D : (fst b + snd b - 1) / 8 <= (2 ^ 47 - 1) / 8) by (apply Z.div_le_mono; lia). change ((2 ^ 47 - 1) / 8) with 17592186044415 in D.
assert (D0 : 0 <= fst b / 8) by (apply Z.div_pos; lia). lia.
Qed.
Lemma fin_any : ltac2:(TCodec.tc2 tcn__PmABa1 "[6'QI'QJ'4'A!p021'R4&Ky5'S;yR0%211%5241'9y8%611%311p061'J'6&Q7%211&Q4':%12EE%611&Q?vFvRHvDvOvLvS3vGvCvHv1vR;vRNvB&QGr@%211r5r4r3r2r1%FCEDCBA@?>=<;:9654321&R1&R:&QD&QCr6rAvS<r?%897654C32@1'@'=z%23QJ51+1%43QL71%6231%H1B'<&R@&RD+U0%22Q11%421I&RA+T0%62Q51%32M1%:251+S@%:2Q91%<21Q1+S8%=2Q<1%:2Q41%A241%J281p0D1pU@RC1%Q11Q8&?%112%Q0231pU@RH1'Q3&R6r>&S:r=%22RG1&Q2&Q6r9%22Q@1r:%5221&R7%11QG%=5R1<931r<+fSWL%>2S31r;%B5QG4216%D3QN61&R9r7%@21=%B216%421:%QC2QJR7&RC+2+R0%3221%QC2R<1%QJ261&R>&QA%11RI+8%4221%QO21RD+9%7251%QM2RG1%R4241%Q?11rF%11RL%QB11%R82S4RO%?2S5<%R52S11%R<231%QG11&R?%12S:A+QoooPP0%F221%RA21S9+QoooPP8%I251%R?2S<1%RF241%R111vRO%S03THS61%R411rD%QO2TDQ<%211rB%QN2S91rC%R13215%S93TD51p091p0=1p0H1p0N1p0Q21p0Q>1pU@U81&Q:%14SKR?CSA%24SLSFQ=Q6&R5&RBu1%211%RD2U;1%52SN1&Q>%12TH5%RH2U=1%SM3U=41u2%:11%RL2UC1%=2L1%RN2UCTH%T33UC21u8%@11%S22UI1%C2Q01%>2U54%S52UJ1%T:3UJ31u9%G11%S92V01%J2Q<1%E2U<4%S<2V11%TA3V131'7&R=(5uBuCuDuEuFuGuHuIuJuK(8%11>%=3?31%>3@51%?3A71%@3B91%A3C;1%B3D=1%C3E?1%D3FA1%E3GC1%F3HE1%H3IUG1rG%QH1UJ%T:2W11%QK231%QF2V=UM%T=2W21%UB3W231p081pV6Q21u3%R111%TC2W:1%R42S;1%R52VF2%UJ3W:21u4%R711%TI2W@1%R:2B1%R;2VL2%V03W@21&R3&QFvS7%211rQ1%411vS9rQ0%845321vRM(;%V<3X521%V=3X682p021'>%V82V=VL%V92VMTC%V;221&QOrI&Q@%11W;&QB%11W0%65W253W51%VC281qVLXC1%=2XD1%VM3XEEVL%VG21A%VH231rHvRI%?5W;2<W11&QE&QKrQ3%221N%411&R0rQ2%24Q75Q31%W4241%W52:1%W>2>1&QNvRJ&R2&QH&QL%12XCXB%321X0%52XE1qV>YA1%11QDrQ4%311%<4;U=31'R8&Q;vR<%211&QMrNrMrJ%46X<QK321Q?vE%:4X>721p0<1p0J1p0QJ1p0R01p0R:1p0RA1p0RH1p0SL1p0T41p0T<1p0TC1p0TN1p0U01p0U31p0VJ1p0W01p0WF1p0WL1p0XC1p0XK1p0Y51p2YM1pUHZ11pQDZ31pV:Z71pQNZ91pQLZ:1pR2Z@1pV<ZJ1pR4ZB1pV4ZI1pV2ZJ1pU>ZL1pVNZO1pUJ[11pVB[31pV>[51").
Proof using All. intros s sm e' vm Wy fx fx9 Rc pc R9 M9v Mc modelc LKc crc Ac.
intros BI RP Hvm WYin WYD MS MG FZ FL0 MO E1 E2 E8 E9 E18 E3 E4 STEP E0' OUT CRK.
pose proof BI as BI'. destruct BI' as (HHc & AMc & MRTc & IAc & ILKc & ASTKc & EKc & DKc & OWNc & SHDc).
pose proof RP as (PA & IA & VIS & VREF & BASE & ERR & TBOK).
pose proof G as G'. destruct G' as [Hk SPTg SLOg SHIg SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
change (ff_bytes 0) with 64 in *. unfold SCR in *.
pose proof ENT as (Rra0 & RAok0 & Rsp0 & Rgp0 & Rtp0 & ASTK0 & _). pose proof RAok0 as (Hr1 & Hr2).
rewrite L5K.rl1 in Rra0. rewrite L5K.rl2 in Rsp0.
pose proof ASTK0 as (A16 & SLO & SHI & SPT & SDEF & SUP). change (PMSPA.pm_scr 7) with 26624 in *.
pose proof frame_geo as (Eop & Eois & Eov & Eoec & Eos).
pose proof FOK as ((rs & Hfb) & Fal).
assert (HfbF : In (fb, 4, rs) FF') by (right; exact Hfb).
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHc) as (WB & WF & FSAPP & FSCEIL & _).
destruct (WF _ HfbF) as (Ff1 & Ff2 & _). cbn [ff_addr ff_class fst snd] in Ff1, Ff2. change (ff_bytes 4) with 1024 in Ff2.
unfold app_mem, FS_BYTES in FSAPP, FSCEIL, Ff1, Ff2, FS2.
pose proof FSAPP as (FA0 & FA1 & FA2). unfold BIGSHADOW_LO, BIGSHADOW_HI in FA1.
pose proof (PMASK.fs_above_img L ar C HI LY HIok _ _ _ _ _ _ _ HHc) as FSI.
assert (AOF : forall a n, fb + 32 <= a -> a + n <= fb + 1016 -> PMSPA.aobjA FF a n)
by (intros a n X1 X2; exists (fb, 4, rs); split; [exact Hfb|]; cbn [ff_addr ff_class fst snd]; change (ff_bytes 4) with 1024; lia).
assert (R9ra : getr R9 (reg 1) = Z_to_bv 64 r) by (rewrite E1; unfold PMABK.U; rewrite Z_to_bv_bv_unsigned; exact Rra0).
pose proof (PMK.ret_to RSEGS fx9 R9 M9v 0xb0cfc (ltac:(oW' 0xb0cfc%Z)) r (ltac:(oF' 0xb0cfc%Z)) eq_refl (ltac:(oD' 0xb0cfc%Z)) R9ra Hr1 Hr2) as MSr.
set (Wx := fun a => op + 8 <= a < op + 9).
assert (WX : forall a, Wx a -> aclientw L ar (PM.parser_own s ++ LBX) FF' 0 0 a /\ ~ L5.outside WR a).
{ intros a Wa. unfold Wx, PMABK.op in Wa. split.
- apply (L5SAR.fframe_client L ar _ FF' 0 0 fb 4 rs); [exact HfbF| change (ff_bytes 4) with 1024; lia].
- intros O. apply (O (PMSPA.o_p AD fb + 8, 8)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]. }
assert (WXD : forall a, Wx a \/ ~ Wx a) by (intros a; unfold Wx; destruct (L5SAR.rng_dec a (op + 8) (op + 9)) as [X|X]; [left; exact X| right; exact X]).
assert (WY : forall a, Wy a -> S - 26624 <= a < S /\ ~ aclient L ar LBX FF S 26624 a).
{ intros a Wa. split; [destruct (WYin a Wa); lia|]. intros Hc.
destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF' LKc crc Ac Mc _ S 26624 a HHc SPTg (L5SAR.aclient_cons L ar _ FF _ _ _ _ (L5SAR.aclient_appb L ar _ (PM.parser_own s) _ _ _ _ Hc))) as [Y|Y];
destruct (WYin a Wa); lia. }
apply (PMAUKS.retire_coreS L ar C HI LYa HIok M0 model0 LBX FF LK0 Aw0 S 26624 (S - 128) (S - 104) S ocell own F fl 0 LK2 M2 model2 cr0 (PM.parser_own s0) G
WR (PM.parser_own s) Mc modelc LKc crc Ac Wx Wy fx fx9 Rc pc R9 r M9v K BI WX WXD WY WYD (msteps_trans _ _ _ _ MS MSr) MG).
{ intros a Ha Nw. unfold PMAUKS.WretY, PMAUK.Wret in Nw. change (ff_bytes 0) with 64 in Nw. change (64 / 8) with 8 in Nw.
apply FZ; [exact Ha| intros X; apply Nw; right; left; exact X| intros X; apply Nw; right; right; exact X| intros X; apply Nw; left; left; left; exact X
| intros X; apply Nw; left; left; right; unfold SB; lia| intros X; apply Nw; left; right; exact X]. }
{ exact FL0. }
intros Mf modelf FZf MGf VISf AHf MRTf AMf HHf.
assert (EKf : L5SAR.ek L ar (PM.parser_own s ++ LBX) FF S 26624 [(op + 8, 1)] Mc Mf).
{ apply (L5SAR.ek_piece L ar _ FF S 26624 _ Mc Mf (PMAUKS.WretY F fl 0 Wx Wy) FZf). intros a Ha Hc Ho Wa.
unfold PMAUKS.WretY, PMAUK.Wret in Wa. change (ff_bytes 0) with 64 in Wa. change (64 / 8) with 8 in Wa.
destruct Wa as [[[Wa|Wa]|Wa]|[Wa|Wa]].
- exact (fframe_nc (PM.parser_own s) LKc crc Ac Mc _ HHc a ltac:(lia) Hc).
- exact (PMABK2.fsh_nc L ar C HI HIok R0 LBX FF LK0 Aw0 cr0 S s0 F fl LK2 M2 model2 G (PM.parser_own s) LKc crc Ac Mc _ HHc a ltac:(unfold SB in Wa; lia) Hc).
- subst a. apply (L5ADHR.not_client_bx L ar FF' fl (PM.parser_own s) LBX (L5ADHR.blocks_off_fs L ar C HI HIok _ _ _ _ _ _ _ (PM.parser_own s) LBX HHc eq_refl) FLP FLBIG FLNC).
apply (L5SAR.aclient_mono L ar _ FF' S 26624 0 0 fl); [apply (L5SAR.aclient_cons L ar _ FF _ _ _ _ Hc)| intros x Hx; lia].
- apply (Ho (op + 8, 1)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; unfold Wx in Wa; lia].
- destruct (WYin a Wa) as [X|X];
destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF' LKc crc Ac Mc _ S 26624 a HHc SPTg (L5SAR.aclient_cons L ar _ FF _ _ _ _ Hc)) as [Y|Y]; lia. }
pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HHc) as FRB'. pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HHc) as BRB.
assert (FRB : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47) by (intros f Hf; apply FRB'; right; exact Hf).
assert (WAPP8 : PMKA.wapp [(op + 8, 1)]).
{ apply PMKA.wapp_cons; [| apply PMKA.wapp_nil]. cbn [fst snd]. unfold PMABK.op. unfold BIGSHADOW_LO, BIGSHADOW_HI. destruct FA1; lia. }
assert (OUT8 : forall a n, (a + n <= op + 8 \/ op + 9 <= a) -> forall i, a <= i < a + n -> L5.outside [(op + 8, 1)] i).
{ intros a n X3 i Hi rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. lia. }
assert (OUTB8 : forall q m, In (q, m) (PM.parser_own s ++ LBX) -> forall i, q <= i < q + m -> L5.outside [(op + 8, 1)] i).
{ intros q m Hq i Hi rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr.
destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q m (PMSPA.o_p AD fb) 384 HHc Hq (PMAUAR.aobjA_push FF _ 384 (F, 0, S - 128 + 32) (AOF (PMSPA.o_p AD fb) 384 ltac:(lia) ltac:(lia))))
as [Z0|Z0]; unfold PMABK.op in Hr; lia. }
assert (Ivb : In (PM.p_b s, 32 * 2 ^ PM.p_k s) (PM.parser_own s ++ LBX)) by (apply in_or_app; left; unfold PM.parser_own, PM.vec_own; right; left; reflexivity).
assert (Iqc : In (PM.sr_qc (PM.p_src s), PM.CHUNK) (PM.parser_own s ++ LBX)) by (apply in_or_app; left; unfold PM.parser_own, PM.src_own; left; reflexivity).
destruct (BRB _ Iqc) as (Xq1 & Xq2). destruct (BRB _ Ivb) as (Xb1 & Xb2). cbn [fst snd] in Xq1, Xq2, Xb1, Xb2.
pose proof (PMAPAR.op_vis L ar C HI LY HIok _ FF' LKc crc Ac Mc modelc fb _ s HHc (PMAUAR.frame_okA_push FF fb F 0 (S - 128 + 32) FOK) PA)
as (_ & _ & _ & _ & _ & _ & OAV & _ & _).
assert (PAf : PM.parser_at RSEGS AD PMSPA.accA PMSPA.annA Mf (PMSPA.o_p AD fb) (PMSPA.o_is AD fb) (PMPK.set_more s vm)).
{ apply (PMAPAR.parser_more_updA Mc Mf _ _ s vm PA).
- lia.
- lia.
- apply (PMKA.agA_obj L ar _ FF S 26624 _ Mc Mf EKf WAPP8 FRB (PMSPA.o_p AD fb) 8 (AOF (PMSPA.o_p AD fb) 8 ltac:(lia) ltac:(lia))). apply OUT8. unfold PMABK.op; lia.
- apply (PMKA.agA_obj L ar _ FF S 26624 _ Mc Mf EKf WAPP8 FRB (PMSPA.o_p AD fb + 9) 375 (AOF (PMSPA.o_p AD fb + 9) 375 ltac:(lia) ltac:(lia))). apply OUT8. unfold PMABK.op; lia.
- exact (PMKA.agsh_obj L ar _ FF S 26624 _ Mc Mf EKf WAPP8 FRB (PMSPA.o_p AD fb) 384 (AOF (PMSPA.o_p AD fb) 384 ltac:(lia) ltac:(lia))).
- pose proof PA as (_ & PD & _). apply (L5.defined_grows Mc Mf _ _ MGf PD).
- apply (proj1 (L5A.u8_at_vis (ahid Ac modelc) Mf (op + 8) vm (OAV (op + 8) 1 ltac:(unfold PMABK.op; lia) ltac:(unfold PMABK.op; lia)) ltac:(unfold PMABK.op; lia) ltac:(unfold PMABK.op; lia))).
rewrite VISf. exact MO.
- exact Hvm.
- exact Xq1.
- lia.
- apply (PMKA.agA_blk L ar _ FF S 26624 _ Mc Mf EKf WAPP8 BRB _ _ Iqc). apply OUTB8. exact Iqc.
- exact Xb1.
- lia.
- apply (PMKA.agA_blk L ar _ FF S 26624 _ Mc Mf EKf WAPP8 BRB _ _ Ivb). apply OUTB8. exact Ivb.
- intros c0 n0 p0 Etb. assert (Ip : In (p0, c0) (PM.parser_own s ++ LBX)) by (apply in_or_app; left; unfold PM.parser_own, PM.vs_own; rewrite Etb; right; right; left; reflexivity).
apply (PMKA.agA_blk L ar _ FF S 26624 _ Mc Mf EKf WAPP8 BRB _ _ Ip). apply OUTB8. exact Ip. }
assert (OUTo : forall a n, fb + 32 <= a -> a + n <= fb + 1016 -> (a + n <= op + 8 \/ op + 9 <= a) -> forall i, a <= i < a + n -> L5.outside [(op + 8, 1)] i)
by (intros a n _ _ X; exact (OUT8 a n X)).
assert (EC' : forall v c, PMSPA.ec_at RSEGS Mc oec v c -> PMSPA.ec_at RSEGS Mf oec v c).
{ intros v c X. apply (PMKA.ec_keepA RSEGS L ar _ FF S 26624 _ Mc Mf EKf WAPP8 FRB oec v c (AOF oec 16 ltac:(unfold PMABK.oec; lia) ltac:(unfold PMABK.oec; lia))); [| exact X].
apply OUT8. unfold PMABK.oec, PMABK.op; lia. }
assert (RUNf : PMSPA.run_pre RSEGS AD PMA.AAD Mf fb (PMPK.set_more s vm) str sm e').
{ split; [exact PAf|].
split; [apply (PMKA.iss_keepA RSEGS AD L ar _ FF S 26624 _ Mc Mf EKf WAPP8 FRB BRB _ str sm (AOF (PMSPA.o_is AD fb) 272 ltac:(lia) ltac:(lia)));
[intros x Hx; apply in_or_app; right; apply INCS; exact Hx| apply OUT8; unfold PMABK.op; lia
| intros c0 n0 p0 Etb i Hi; apply (OUTB8 p0 c0); [apply in_or_app; right; apply INCS; rewrite Etb; left; reflexivity| exact Hi]
| exact IA]|].
split; [apply (PMKA.visitor_keepA RSEGS AD L ar _ FF S 26624 _ Mc Mf EKf WAPP8 FRB (PMSPA.o_v AD fb) (AOF (PMSPA.o_v AD fb) 8 ltac:(lia) ltac:(lia))); [apply OUT8; unfold PMABK.op; lia| exact VIS]|].
split; [apply (PMKA.u64_keepA RSEGS L ar _ FF S 26624 _ Mc Mf EKf WAPP8 FRB (PMSPA.o_p AD fb + 384) (PMSPA.o_v AD fb) (AOF (PMSPA.o_p AD fb + 384) 8 ltac:(lia) ltac:(lia)));
[apply OUT8; unfold PMABK.op; lia| exact VREF]|].
split; [apply (PMASK.base_keep L ar C LY _ FF S 26624 _ Mc Mf EKf); [| exact BASE]; intros a Ha rr [<-|[]] Hr; unfold L5.in_rng in Hr; cbn [fst snd] in Hr; unfold PMABK.op in Hr; lia|].
split; [apply (PMKA.err_okA_keep RSEGS AD PMA.AAD L ar _ FF S 26624 _ Mc Mf EKf e' PMA.addrs_wf_A); [| exact ERR];
intros a D; pose proof (PMASK.dep_img a D) as DI; rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa); split; [lia|];
split; [exact (PMA.ly_static L C LY a D)| intros rr [<-|[]] Hr; unfold L5.in_rng in Hr; cbn [fst snd] in Hr; unfold PMABK.op in Hr; lia]|].
exact TBOK. }
apply (KONT fx9 R9 Mf modelf LKc Ac (PMPK.set_more s vm) sm e' crc).
- apply L5SAR.preserved_by_index. intros j Hj. unfold L5SAR.cs_all in Hj.
assert (UU : forall x, Z_to_bv 64 (U x) = getr R0 (reg x)) by (intros x; unfold PMABK.U; apply Z_to_bv_bv_unsigned).
destruct Hj as [<-|[<-|[<-|[<-|[<-|Hj]]]]].
+ rewrite E2. exact (eq_sym Rsp0).
+ exact E3.
+ exact E4.
+ rewrite E8. apply UU.
+ rewrite E9. apply UU.
+ rewrite (E18 j Hj). apply UU.
- split; [exact RUNf|]. split; [exact STEP|]. split; [exact E0'|].
destruct OUT as [((v & Hv & ECv) & Evm & Ee)|(EC0' & INV' & PV)].
+ left. exists v. split; [exact Hv|]. split; [exact (EC' _ _ ECv)|]. split; [exact Evm| exact Ee].
+ right. split; [exact (EC' _ _ EC0')|]. split; [exact INV'| exact PV].
- exact AHf.
- exact CRK.
- exact MRTf.
- exact ILKc.
- exact IAc.
- exact AMf.
- exact HHf.
Qed.
End Frame.
End Call.
End WithHeap.
End PMABA1.
