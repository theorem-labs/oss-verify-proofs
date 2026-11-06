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
PmModelFactsA PmStepA PmStep PmParStep PmParKit PmASrcKit PmAParKit PmAReset1 PmAUarK PmAUar PmAUarKS PmABaK PmABaK2 PmABaK3 Ja0_code_b0cfc_b0d00 PmABa1 PmABaP1 PmABaP2 PmABa2 PmABa3 PmABa4 PmCertKitG PmABa5 PmABa6.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmABa7 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5KnA.L5KA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmABa7.PMABA7.WithHeap.Call."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmABa7.PMABA7.WithHeap.Call.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmABaK.PMABK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModelFactsA.PMFA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsAa.PMA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0Ac"; "0Aw0"; "0BX"; "1bool"; "1false"; "1list"; "1nat"; "1option"; "1prod"; "2and"; "2eq"; "2not"; "3Z"; "0DEP"; "0F"; "0FF"]; ["0HI"; "0K"; "0L"; "0LBX"; "0LK0"; "0LK2"; "0LKc"; "4Model"; "5bvmap"; "0M"; "0M'"; "0M0"; "0M2"; "0M3"; "0M3v"; "0Mc"]; ["0R"; "0R0"; "0R3"; "6mrestrict"; "7msteps"; "8credit"; "9ahid"; "9fframe"; ";defined"; ";u32_at"; ";u64_at"; ":SCFG"; "<zeros_at"; ">sregs"; ">vfacts0"; "=vfactsE"]; ["?U"; "?binv'"; "?bst"; "?fsh"; "?oec"; "?op"; "?sd"; "@AADDR_A"; "@ADDR_A"; "ACHUNK"; "AMAX_DEPTH"; "APST"; "AVLong"; "Ap_b"; "Ap_depth"; "Ap_done"]; ["Ap_k"; "Ap_more"; "Ap_src"; "Ap_stk"; "Ap_tb"; "Ap_tg"; "Aparser_at"; "Aparser_own"; "Apst"; "Asr_qc"; "Astrm"; "Avstr"; "BagA"; "Bagsh"; "CaccA"; "CannA"]; ["Ccfg"; "Cec_at"; "Crun_pre"; "Dbegin_array_spec"; "Dget_length_spec"; "Dignore_spec"; "Dmake_ec_spec"; "Dpeek_spec"; "Dpush_mi_spec"; "Dpush_ms_spec"; "Dpush_msu_spec"; "Dsrc_read_spec"; "EFPState"; "Emkst"; "Eseg_rom"; "Fsrealizes"]; ["Gmem_grows"; "Hloaded_segments"; "0S"; "0SCFG_P"; "Iadd"; "Idiv"; "Ile"; "Ilt"; "Imul"; "Ipow"; "Isub"; "0ar"; "0c"; "0cat"; "0cr0"; "0crc"]; ["0d"; "0e"; "0e0"; "0fb"; "0fx"; "0fx3"; "0i"; "0model0"; "0model2"; "0model3"; "0modelc"; "0n"; "0ois"; "0op"; "0p"; "0pc3"]; ["0s"; "0s0"; "0sm"; "0sm0"; "JZ_to_bv"; "Jbv"; "0str"; "0x"]]).
Local Ltac lia := L5FastLia.plia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PMABA7.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation AD := PMA.AD.
Lemma parser_depth_updA : ltac2:(TCodec.tc2 tcn__PmABa7 "TF'T5yR0%211'7y8%511%311p051'<'R8&R6&S1&QH&R>&R?r6r4r3r2%9887654321&S6zr5%3221&S4+\0%22;1&S9+2+R0%3221%;251&R<r9r8r7+<%544321r:+@%@261+[@%:44921&R=r;%2417<D&Q8%1339F&Q9r<%J26>%34Q821A'9%Q12Q0D&QJ+1%Q0221%Q52H1%6251&R9&R2%11A%311%Q;2Q:1%41?%611&QI%Q;221%Q@21Q6rAr@r=%<11%>11%Q:45418&QMr>%211%QJ2QI1r?%511&S8+Q0&R0%115%QJ2QI1%5241%QO271%R421QJrDrC%@1E%91F%R22R11%=2<1%QO46541':'R;&R4%11:(QLr1%23RERD1%73641rIrH%R:421RHRJp041pWNS41pWHS51pVJS61rE(QK&R1rB%211&QO%113%QJ14%E15&R5%117%Q?18%Q819&R3%11;%>9;9QI875431%SE8SDSCSBSA@Q6Q51p0B1p0Q21p0Q:1p0QE1p0QJ1p0R11p0R71p0R=1p0RE1p0RJ1p0RM1p0S11p0S71p0S>1p0SG1p0SL1pW2T81pX2T81pWJT:1pWLT;1pQFT=1pQDT>1").
Proof. intros M M' op ois s d.
intros (H0 & D & C24 & H8 & H9 & H12 & H16 & H20 & NI & SRC & H320 & H328 & C320 & TB & VEC & B1 & B2 & B3) Ho Ho'
[AG1 _] AG2 SH D' C12 Hd Hq Hq' AGQ Hb Hb' AGV AGT.
pose proof AG2 as [AG2d _].
unfold PM.parser_at. cbn [PM.p_more PM.p_done PM.p_depth PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk].
assert (AG4 : forall a n, op + 16 <= a -> a + n <= op + 384 -> PMFA.agA M M' a n).
{ intros a n X1 X2. split; [eapply (L5C.agree_on_sub M M'); [exact AG2d|lia|lia]| intros x Hx; apply SH; lia]. }
split; [apply (L5C.u64_at_agree RSEGS M M'); [eapply L5C.agree_on_sub; [exact AG1|lia|lia]| lia| lia| exact H0]|].
split; [exact D'|].
split; [apply (PMFA.accA_agree M M' op 24); [intros x Hx; apply SH; lia| exact C24]|].
split; [apply (L5C.u8_at_agree RSEGS M M'); [eapply L5C.agree_on_sub; [exact AG1|lia|lia]|lia|lia|exact H8]|].
split; [apply (L5C.u8_at_agree RSEGS M M'); [eapply L5C.agree_on_sub; [exact AG1|lia|lia]|lia|lia|exact H9]|].
split; [exact C12|].
split; [apply (L5C.u8_at_agree RSEGS M M'); [apply (AG4 (op + 16) 1); lia|lia|lia|exact H16]|].
split; [apply (PMF.u32_at_agree RSEGS M M'); [apply (AG4 (op + 20) 4); lia|lia|lia|exact H20]|].
split; [apply (PMFA.nullis_at_agreeA RSEGS PMA.AD M M' (op + 32)); [lia|lia| apply AG4; lia| exact NI]|].
split; [apply (PMFA.src_fields_at_agreeA RSEGS M M' (op + 24)); [lia|lia|exact Hq|exact Hq'| apply AG4; lia| exact AGQ| exact SRC]|].
split; [apply (PMF.u32_at_agree RSEGS M M'); [apply (AG4 (op + 320) 4); lia|lia|lia|exact H320]|].
split; [apply (L5C.u64_at_agree RSEGS M M'); [apply (AG4 (op + 328) 8); lia|lia|lia|exact H328]|].
split; [apply (PMFA.accA_agree M M' (op + 320) 64); [intros x Hx; apply SH; lia| exact C320]|].
split; [apply (PMFA.vstr_at_agreeA RSEGS M M' (op + 336)); [lia|lia| apply AG4; lia| exact AGT| exact TB]|].
split; [apply (PMFA.vec_at_agreeA RSEGS M M' (op + 360)); [lia|lia|exact Hb|exact Hb'| eapply (L5C.agree_on_sub M M'); [exact AG2d|lia|lia]| exact AGV| exact VEC]|].
split; [exact B1|]. split; [exact B2| exact Hd].
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
Local Abbreviation fin_any := (PMABA1.fin_any L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE PMI PMS PMSU F fl LK2 M2 model2 G).
Local Abbreviation mregs0 := (PMABA2.mregs0 R0 S fb F).
Local Abbreviation mregs := (PMABA2.mregs R0 S fb F).
Local Abbreviation tregs := (PMABA2.tregs R0 S fb F).
Local Abbreviation UB := (PMABA2.UB R0).
Local Abbreviation mk_Z1 := (PMABA2.mk_Z1 L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE PMI PMS PMSU F fl LK2 M2 model2 G).
Local Abbreviation mk_Z11 := (PMABA2.mk_Z11 L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE PMI PMS PMSU F fl LK2 M2 model2 G).
Local Abbreviation mk_Zc := (PMABA2.mk_Zc L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE PMI PMS PMSU F fl LK2 M2 model2 G).
Local Abbreviation mk_Zt := (PMABA2.mk_Zt L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE PMI PMS PMSU F fl LK2 M2 model2 G).
Local Abbreviation mk_Zt13 := (PMABA2.mk_Zt13 L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE PMI PMS PMSU F fl LK2 M2 model2 G).
Local Abbreviation gl_err_C := (PMABA2.gl_err_C L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE PMI PMS PMSU F fl LK2 M2 model2 G).
Local Abbreviation gl_err_T := (PMABA2.gl_err_T L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE PMI PMS PMSU F fl LK2 M2 model2 G).
Local Abbreviation tail_I := (PMABA3.tail_I L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE PMI PMS PMSU F fl LK2 M2 model2 G).
Local Abbreviation tail_C := (PMABA3.tail_C L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE PMI PMS PMSU F fl LK2 M2 model2 G).
Local Abbreviation tail_T := (PMABA3.tail_T L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE PMI PMS PMSU F fl LK2 M2 model2 G).
Local Abbreviation mregs0_keep := (PMABA2.mregs0_keep R0 S fb F).
Local Abbreviation mregs_keep := (PMABA2.mregs_keep R0 S fb F).
Local Abbreviation tregs_keep := (PMABA2.tregs_keep R0 S fb F).
Local Abbreviation vf_rng := (PMABA2.vf_rng R0 S fb F fl).
Local Abbreviation op8_apart := (PMABA2.op8_apart R0 S fb F fl).
Local Abbreviation VT := (PMABA3.VT R0 S fb F fl).
Local Abbreviation vf_fsh := (PMABA4.vf_fsh R0 S fb F fl).
Local Abbreviation vf_fb := (PMABA4.vf_fb R0 S fb F fl).
Local Abbreviation mi_vis := (PMABA4.mi_vis L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE PMI PMS PMSU F fl LK2 M2 model2 G).
Local Abbreviation stk_bz := (PMABA4.stk_bz L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE PMI PMS PMSU F fl LK2 M2 model2 G).
Local Abbreviation stk_cell := (PMABA4.stk_cell L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE PMI PMS PMSU F fl LK2 M2 model2 G).
Local Abbreviation modsub := PMABA4.modsub.
Local Abbreviation mod32_d := PMABA4.mod32_d.
Local Abbreviation sp_mod := (PMABA4.sp_mod S SP32).
Local Abbreviation pow_bnd_ra := PMABA4.pow_bnd_ra.
Local Abbreviation c_stage := (PMABA4.c_stage L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE PMI PMS PMSU F fl LK2 M2 model2 G).
Local Abbreviation VK := (PMABA4.VK R0 S fb F fl).
Local Abbreviation i_stage := (PMABA4.i_stage L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE PMI PMS PMSU F fl LK2 M2 model2 G).
Local Abbreviation tregs0 := (PMABA2.tregs0 R0 S fb F).
Local Abbreviation tregs0_keep := (PMABA2.tregs0_keep R0 S fb F).
Local Abbreviation tregs0_of := (PMABA2.tregs0_of R0 S fb F).
Ltac vopen VF := unfold PMABK.vfacts, PMABK.hdr, PMABK.own, PMABK.fsh in VF; cbn iota in VF; decompose [and] VF; clear VF.
Ltac hx := match goal with |- ?G => match goal with H : G |- _ => exact H end end.
Ltac vfeed := first [ hx | (split; hx) | apply UB | (unfold PMABAP1.aligned; hx) | (unfold PMABAP2.aligned; hx) ].
Ltac vfeedV VF := first [ assumption | apply UB | unfold PMABAP1.aligned; assumption | unfold PMABAP2.aligned; assumption
| let W := fresh "W" in pose proof VF as W; vopen W; vfeed ].
Ltac feedV P VF :=
let T := type of P in
let C := L5SAR.feed_concl T in
let Q := fresh "SC" in
assert (Q : C) by (let W := fresh "W" in pose proof VF as W; vopen W; apply P; clear P;
first [ vfeed | lazymatch goal with |- ?A => fail 1 "feedV: cannot prove premise" A end ]);
move Q after P; clear P; rename Q into P.
Ltac bst_of BI RUN EC HD FSH STEP E0 SD CRL CRK :=
split; [exact BI|]; split; [exact RUN|]; split; [exact EC|]; split; [exact HD|]; split; [exact FSH|]; split; [exact STEP|]; split; [exact E0|];
split; [exact SD|]; split; [exact CRL| exact CRK].
Local Abbreviation t4_stage := (PMABA5.t4_stage L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE PMI PMS PMSU F fl LK2 M2 model2 G).
Local Abbreviation t3_stage := (PMABA5.t3_stage L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE PMI PMS PMSU F fl LK2 M2 model2 G).
Local Abbreviation t2_stage := (PMABA5.t2_stage L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE PMI PMS PMSU F fl LK2 M2 model2 G).
Local Abbreviation t1_stage := (PMABA5.t1_stage L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE PMI PMS PMSU F fl LK2 M2 model2 G).
Local Abbreviation fap_of := (PMABA5.fap_of L ar C HI HIok R0 M0 model0 LBX FF LK0 Aw0 cr0 S fb s0 FOK F fl LK2 M2 model2 G).
Local Abbreviation vf_opF := (PMABA5.vf_opF R0 S fb F fl).
Local Abbreviation reg_lit := PMABA5.reg_lit.
Ltac mregs_ks KS := unfold PMABA2.tregs, PMABA2.tregs0, PMABA2.mregs, PMABA2.mregs0; repeat split; first [ hx | (rewrite (KS _) by inl; hx) ].
Ltac mid0 conc V typed VF BS s sm e Mc modelc LKc crc Ac MV fx R pc pc1 :=
let BI := fresh "BI" in let RUN := fresh "RUN" in let EC := fresh "EC" in let HD := fresh "HD" in let FSH := fresh "FSH" in
let STEP := fresh "STEP" in let E0 := fresh "E0" in let SD := fresh "SD" in let CRL := fresh "CRL" in let CRK := fresh "CRK" in
pose proof BS as (BI & RUN & EC & HD & FSH & STEP & E0 & SD & CRL & CRK);
let P := fresh "P" in pose proof (conc fx R MV V) as P; unfold PMABA3.VT in P; cbn beta iota in P; feedV P VF;
let fx1 := fresh "fx1" in let R1 := fresh "R1" in let M1v := fresh "M1v" in let MG1 := fresh "MG1" in let FRZ1 := fresh "FRZ1" in
let MS1 := fresh "MS1" in let KS1 := fresh "KS1" in let PR := fresh "PR" in
destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & PR); decompose [and] PR; clear PR;
let DF1 := fresh "DF1" in let DF2 := fresh "DF2" in pose proof (vf_fb typed 0 MV VF) as (DF1 & DF2);
apply (step_piece typed s sm e 0 cat fx fx1 R pc R1 pc1 M1v Mc modelc LKc crc Ac (fun _ => False) BI RUN EC HD MS1 MG1);
[ intros a Ha _; apply FRZ1; exact Ha
| intros a []
| apply (fsh_agree typed MV M1v); [intros a Ha; apply FRZ1; lia| exact DF1| exact DF2| exact (vf_fsh typed 0 MV VF)]
| let M1 := fresh "M1" in let model1 := fresh "model1" in let BI1 := fresh "BI1" in let RUN1 := fresh "RUN1" in let EC1 := fresh "EC1" in
let HD1 := fresh "HD1" in let FSH1 := fresh "FSH1" in let VIS1 := fresh "VIS1" in let HID1 := fresh "HID1" in let FR1 := fresh "FR1" in
intros M1 model1 BI1 RUN1 EC1 HD1 FSH1 VIS1 HID1 FR1;
let BS1 := fresh "BS1" in assert (BS1 : bst typed s sm e M1 model1 LKc crc Ac) by (bst_of BI1 RUN1 EC1 HD1 FSH1 STEP E0 SD CRL CRK) ].
Local Abbreviation kdisp := (PMABA6.kdisp L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE PMI PMS PMSU F fl LK2 M2 model2 G).
Local Abbreviation fframe_nc := (PMABA1.fframe_nc L ar C HI HIok R0 LBX FF LK0 Aw0 cr0 S s0 F fl LK2 M2 model2 G).
Definition vfacts0 (d : Z) (MV : word -> option byte) : Prop :=
(0 <= S < 2 ^ 64 /\ 0 <= op < 2 ^ 64 /\ 0 <= ov < 2 ^ 64 /\ 0 <= oec < 2 ^ 64 /\ 0 <= F < 2 ^ 64 /\ 0 <= fl < 2 ^ 64)
/\ L5.img_clear MV 65536 1261568 /\ L5.u64_at RSEGS MV 1289464 2147450880 /\ L5.u32_at RSEGS MV 1289472 1
/\ 140735332487328 <= S <= 140737488355328 /\ S mod 32 = 0 /\ L5.writable RSEGS MV (S - 160) 160
/\ 6885376 <= op <= 140737488354944 /\ op mod 8 = 0 /\ (2147446784 + 17592186048512 <= op \/ op + 384 <= 2147446784)
/\ L5KA.zeros_at MV ((op / 8) + 2147450880) 3 /\ L5KA.zeros_at MV (((op + 32) / 8) + 2147450880) 44 /\ L5KA.zeros_at MV (((op + 20) / 8) + 2147450880) 1
/\ L5.writable RSEGS MV op 384 /\ ((S - 160) + 160 <= op \/ op + 384 <= (S - 160))
/\ 6885376 <= oec <= 140737488355312 /\ oec mod 8 = 0 /\ (2147446784 + 17592186048512 <= oec \/ oec + 16 <= 2147446784)
/\ L5KA.zeros_at MV ((oec / 8) + 2147450880) 2 /\ L5.writable RSEGS MV oec 16 /\ ((S - 160) + 160 <= oec \/ oec + 16 <= (S - 160))
/\ 6885376 <= ov <= 140737488355320 /\ ov mod 8 = 0 /\ (2147446784 + 17592186048512 <= ov \/ ov + 8 <= 2147446784)
/\ L5KA.zeros_at MV ((ov / 8) + 2147450880) 1 /\ L5.writable RSEGS MV ov 8 /\ ((S - 160) + 160 <= ov \/ ov + 8 <= (S - 160))
/\ (op + 384 <= oec \/ oec + 16 <= op) /\ (op + 384 <= ov \/ ov + 8 <= op) /\ (oec + 16 <= ov \/ ov + 8 <= oec)
/\ 6885376 <= F <= 140737488355264 /\ F mod 32 = 0 /\ L5.defined MV F 64 /\ L5.writable RSEGS MV F 64
/\ (2147446784 + 17592186048512 <= F \/ F + 64 <= 2147446784) /\ L5.writable RSEGS MV ((F / 8) + 2147450880) 8 /\ L5.u64_at RSEGS MV (F + 56) fl
/\ 4096 <= fl <= 140737488355327 /\ L5.writable RSEGS MV fl 1 /\ (2147446784 + 17592186048512 <= fl \/ fl + 1 <= 2147446784) /\ (F + 64 <= fl \/ fl + 1 <= F)
/\ ((S - 160) + 160 <= F \/ F + 64 <= (S - 160)) /\ ((S - 160) + 160 <= fl \/ fl + 1 <= (S - 160))
/\ (op + 384 <= F \/ F + 64 <= op) /\ (op + 384 <= fl \/ fl + 1 <= op)
/\ (((op / 8) + 2147450880) + 48 <= ((F / 8) + 2147450880) \/ ((F / 8) + 2147450880) + 8 <= ((op / 8) + 2147450880))
/\ (oec + 16 <= F \/ F + 64 <= oec) /\ (oec + 16 <= fl \/ fl + 1 <= oec)
/\ (((oec / 8) + 2147450880) + 2 <= ((F / 8) + 2147450880) \/ ((F / 8) + 2147450880) + 8 <= ((oec / 8) + 2147450880))
/\ (ov + 8 <= F \/ F + 64 <= ov) /\ (ov + 8 <= fl \/ fl + 1 <= ov)
/\ (((ov / 8) + 2147450880) + 1 <= ((F / 8) + 2147450880) \/ ((F / 8) + 2147450880) + 8 <= ((ov / 8) + 2147450880))
/\ (F + 64 <= 65536 \/ 65536 + 1196032 <= F)
/\ own MV /\ L5KA.zeros_at MV ((F / 8) + 2147450880) 8 /\ L5.u32_at RSEGS MV (op + 12) d /\ L5.u32_at RSEGS MV (op + 320) 1024.
Lemma vpack0 : ltac2:(TCodec.tc2 tcn__PmABa7 "RI'5'8'<%2211%411'R8'R:'3'T5yR0%211'7y8%511%311p051'G&Q7%B11&Q5&QAvBvS;v@vQ1vKvSGvCv?vDv1vS2vSCv>r:r5r4r3r2r1%DCCBA@?>=<;:987654321&RB&S1&QH&QGr6vT6r9r8%897654A?321&RAr7&QD%11Ez%55=4217&Q<&Q3&Q6%12G8%321<&S4&S5+8%22O1+QoooPP0%5221%;3714&Q>&QNr=%211%>2Q5H%@21J%6231p081p0E1p0L1p0Q61p2R;1pW0QM1pQ>QO1pWFR21pR0R41pVJRB1pW4R>1pX6R@1pX2RB1p6RD1").
Proof using All. intros BX s sm e c Mc modelc LKc crc Ac.
intros BI RP EC ZF.
pose proof BI as BI'. destruct BI' as (HHc & AMc & MRTc & IAc & ILKc & ASTKc & EKc & DKc & OWNc & SHDc).
pose proof RP as (PA & IA & VIS & VREF & BASE & ERR & TBOK).
pose proof G as G'. destruct G' as [Hk SPTg SLOg SHIg SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
pose proof frame_geo as (Eop & Eois & Eov & Eoec & Eos).
pose proof FOK as ((rs & Hfb) & Fal).
assert (FOK' : PMSPA.frame_okA FF' fb) by (split; [exists rs; right; exact Hfb| exact Fal]).
pose proof (PMAPAR.op_vis L ar C HI LY HIok _ FF' LKc crc Ac Mc modelc fb _ s HHc FOK' PA) as ((O1 & O8 & ONSH) & Zop & Z32 & Z20 & OWR & OCE & OAV & AOP & _).
pose proof (PMAPAR.ov_vis L ar C HI LY HIok _ FF' LKc crc Ac Mc modelc fb HHc FOK' VIS) as ((V1 & V8 & VNSH) & Zv & VWR & VCE & VU & AOV & _).
pose proof (PMAPAR.oec_vis L ar C HI LY HIok _ FF' LKc crc Ac Mc modelc fb 0 c HHc FOK' EC) as ((E1 & E8 & ENSH) & Ze & EWR & ECE & EU & AOE & _).
pose proof (PMASK.mach_vis L ar C HI LY HIok _ FF' LKc crc Ac Mc modelc HHc BASE) as (VM0 & VM1 & VM2).
unfold SCR in ASTKc.
pose proof (PMASK.stk_vis L ar C HI LY HIok _ FF' LKc crc Ac Mc modelc S 26624 160 HHc ASTKc ltac:(lia)) as (SL160 & SH160 & SWR).
pose proof (PMAUK.vis_facts L ar C HI LYa HIok M0 model0 LBX FF LK0 Aw0 S SCR (S - 128) (S - 104) S ocell own F fl 0 LK2 M2 model2 cr0 (PM.parser_own s0) G WR BX Mc modelc LKc crc Ac BI)
as ((WSv & IMGC & CSB & CUAR & RMS) & OWNv & (FDEF & FW & FSHW & FLU & FLW) & (FLC8 & FLV8 & FV8 & SV8 & SHV8)).
pose proof (PMASK.img_shz_vis L ar C HI LY IL ICok ILY _ FF' LKc crc Ac Mc modelc 1231256 1 HHc ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia)) as ZV88.
pose proof (PMASK.img_shz_vis L ar C HI LY IL ICok ILY _ FF' LKc crc Ac Mc modelc 1231184 1 HHc ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia)) as ZV16.
change (1231256 / 8 + 2147450880) with 2147604787 in ZV88. change (1231184 / 8 + 2147450880) with 2147604778 in ZV16.
change (ff_bytes 0) with 64 in *. change (64 / 8) with 8 in *. replace (F + 64 - 8) with (F + 56) in FLU by lia.
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHc) as (WB & WF & FSAPP & FSCEIL & _ & _ & _ & _ & _ & STOP & _ & NDF & _).
assert (HfbF : In (fb, 4, rs) FF') by (right; exact Hfb).
assert (FAP : F + 64 <= fb \/ fb + 1024 <= F).
{ destruct (WF (F, 0, S - 128 + 32) (or_introl eq_refl)) as (_ & _ & _ & _ & _ & APF). cbn [ff_addr ff_class fst snd] in APF. change (ff_bytes 0) with 64 in APF.
assert (Iin : In (fb, 4, rs) (ff_remove F FF' ++ LKc)).
{ apply in_or_app. left. unfold PMABK.FF'. cbn [ff_remove ff_addr]. rewrite Z.eqb_refl. exact Hfb. }
destruct (APF _ Iin) as [X0|X0]; cbn [ff_addr ff_class fst snd] in X0; change (ff_bytes 4) with 1024 in X0; [left| right]; lia. }
assert (FLo : forall o n, fb + 32 <= o -> o + n <= fb + 1016 -> o + n <= fl \/ fl + 1 <= o).
{ intros o n X1 X2. destruct (Z_lt_le_dec fl o) as [Y|Y]; [right; lia|]. destruct (Z_lt_le_dec fl (o + n)) as [Y'|Y']; [|left; lia]. exfalso. apply FLNC.
apply (L5SAR.fframe_client L ar LBX FF' 0 0 fb 4 rs); [exact HfbF| change (ff_bytes 4) with 1024; lia]. }
unfold SB in *. fold op ov oec in *.
assert (Fd : F = 8 * (F / 8)) by lia.
assert (Od : op = 8 * (op / 8)) by (pose proof (Z.div_mod op 8 ltac:(lia)); lia).
assert (Ed : oec = 8 * (oec / 8)) by (pose proof (Z.div_mod oec 8 ltac:(lia)); lia).
assert (Vd : ov = 8 * (ov / 8)) by (pose proof (Z.div_mod ov 8 ltac:(lia)); lia).
unfold vfacts0.
split; [lia|]. split; [exact VM0|]. split; [exact VM1|]. split; [exact VM2|].
split; [lia|]. split; [exact SP32|]. split; [exact SWR|].
split; [lia|]. split; [exact O8|]. split; [exact ONSH|]. split; [exact Zop|]. split; [exact Z32|]. split; [exact Z20|]. split; [exact OWR|]. split; [lia|].
split; [lia|]. split; [exact E8|]. split; [exact ENSH|]. split; [exact Ze|]. split; [exact EWR|]. split; [lia|].
split; [lia|]. split; [exact V8|]. split; [exact VNSH|]. split; [exact Zv|]. split; [exact VWR|]. split; [lia|].
split; [lia|]. split; [lia|]. split; [lia|].
split; [lia|]. split; [exact F32|]. split; [exact FDEF|]. split; [exact FW|]. split; [exact FBIG|]. split; [exact FSHW|]. split; [exact FLU|].
split; [lia|]. split; [exact FLW|]. split; [exact FLBIG|]. split; [exact FLA|].
split; [lia|]. split; [lia|].
split; [lia|]. split; [apply (FLo op 384); lia|].
split; [lia|].
split; [lia|]. split; [apply (FLo oec 16); lia|].
split; [lia|].
split; [lia|]. split; [apply (FLo ov 8); lia|].
split; [lia|].
split; [lia|].
split; [exact OWNv|]. split; [exact ZF|].
pose proof PA as (_ & _ & _ & _ & _ & P12 & _ & _ & _ & _ & P320 & _). change PM.MAX_DEPTH with 1024 in P320.
split; [apply (proj2 (L5A.u32_at_vis _ Mc (op + 12) _ (OAV (op + 12) 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact P12|].
apply (proj2 (L5A.u32_at_vis _ Mc (op + 320) _ (OAV (op + 320) 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact P320.
Qed.
Ltac vopen0 VF := unfold vfacts0, PMABK.own in VF; decompose [and] VF; clear VF.
Ltac feedV0 P VF :=
let T := type of P in
let C := L5SAR.feed_concl T in
let Q := fresh "SC" in
assert (Q : C) by (let W := fresh "W" in pose proof VF as W; vopen0 W; apply P; clear P;
first [ vfeed | lazymatch goal with |- ?A => fail 1 "feedV0: cannot prove premise" A end ]);
move Q after P; clear P; rename Q into P.
Definition VB (x33 : Z) (j : nat) : Z := match j with 33%nat => x33 | _ => PMABA3.VT R0 S fb F fl 0 0 j end.
Definition sregs (R : bvmap 5 word) : Prop :=
getr R (reg 2) = Z_to_bv 64 (S - 128) /\ getr R (reg 8) = Z_to_bv 64 S /\ getr R (reg 9) = Z_to_bv 64 (S - 128) /\ getr R (reg 10) = Z_to_bv 64 F
/\ getr R (reg 19) = Z_to_bv 64 op /\ getr R (reg 20) = Z_to_bv 64 oec /\ getr R (reg 21) = Z_to_bv 64 ov /\ getr R (reg 27) = Z_to_bv 64 2147450880
/\ getr R (reg 3) = getr R0 (reg 3) /\ getr R (reg 4) = getr R0 (reg 4).
Lemma b0_core : ltac2:(TCodec.tc2 tcn__PmABa7 "VB'RL&Hy5'T5yR0%211%5241'<&QAvBvS;v@vQ1vKvSGvCv?vDv1vS2vSCv>&R7vT1%211vLvSHvEvS>%ECDCBA@?>=<;:9854321;&RB&S1&QH&QGvT6vT3vSB%79654<A>321&RA&QD%11DzvS=%55<B321&Q<&Q3&Q6%12ME%321G&S4&S5+8%22O1+QoooPP0%5221%;3714&Q=r6%211'7y8%QJ11%311p0QJ1'Q4&RMr<r;&T4+fRVL%22R21&RN%11Q9%85763I1r4r3r1%92R91r2%>554217%@3QA71&S0%12Q27'9&S6%12Q<9&S7&S9+2+R0%3221%52?1%9271&;&S:+T0%22R=1%=21C+SH%52R@1%>2F1%B241%911%C2RBL+H%QH2RD1%D2O1%H241%?11%I2QGQ3+QoooPP8%QN2QK1%J2Q61%N241%E11&QE%11S0+<%R5221r5%Q4221+@%R9261%Q5241%Q9241%Q011':r:%QL2SLR7%211%RE3RCS92%53R521p071p0C1p0J1p0Q11p0Q<1pW>T21&Q9&QN%11SE+1%RM221%54S@HI1&Q:%14SBRHQASLr7+QPk[ReC%44SE2SO1r8%S52T1S3+RlZ=%84SI321r9%S92T5Q1+fRS4%<4SM321&QC(4%23T:1Q0'G&QB&QF&R2%11T=%32T>1%5LTMTLTKTJTITHTGTFTETDT:TCTBSLT?T4T3T2TA81T3T2RHRJT;T:TD%SJ2SHRLr>%Q;3S:21'RO&Q;vS3%211&R@rAr@%36TB219S7S6vA%94TD621p0;1p0?1pWDF1pQLSH1rFrE%<6TK21SEU1U0%A4TL>19p051p0N1p0Q21p0Q71p0Q<1p0Q@1p0QC1p0QJ1p0SB1p0SE1pX0UO1pQNT81pR6V21pW<V91p0T@1p0TD1p0U11p0U81p0UA1pLV81pR2V:1pW:VA1").
Proof using All. intros fx R DEP.
intros BI RUN EC ZF SR fx3 R3 M3v pc3 MS3 MG3 FRZ3 D3 C128 H0 H8 H16 FSH3 NEXT.
pose proof BI as BI'. destruct BI' as (HHc & AMc & MRTc & IAc & ILKc & ASTKc & EKc & DKc & OWNc & SHDc).
pose proof RUN as (PA & IA & VIS & VREF & BASE & ERR & TBOK).
pose proof G as G'. destruct G' as [Hk SPTg SLOg SHIg SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
change (ff_bytes 0) with 64 in *. unfold SCR in *.
pose proof (PMAUK.vis_facts L ar C HI LYa HIok M0 model0 LBX FF LK0 Aw0 S SCR (S - 128) (S - 104) S ocell own F fl 0 LK2 M2 model2 cr0 (PM.parser_own s0) G WR _ M2 model2 LK2 cr0 Aw0 BI)
as (_ & _ & _ & (_ & _ & FV8 & SV8 & SHV8)). change (ff_bytes 0) with 64 in FV8. change (64 / 8) with 8 in SHV8.
pose proof frame_geo as (Eop & Eois & Eov & Eoec & Eos).
pose proof FOK as ((rs & Hfb) & Fal).
assert (HfbF : In (fb, 4, rs) FF') by (right; exact Hfb).
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHc) as (WB & WF & FSAPP & FSCEIL & _).
destruct (WF _ HfbF) as (Ff1 & Ff2 & _). cbn [ff_addr ff_class fst snd] in Ff1, Ff2. change (ff_bytes 4) with 1024 in Ff2.
unfold app_mem, FS_BYTES in FSAPP, FSCEIL, Ff1, Ff2, FS2.
pose proof FSAPP as (FA0 & FA1 & FA2). unfold BIGSHADOW_LO, BIGSHADOW_HI in FA1.
pose proof (PMASK.fs_above_img L ar C HI LY HIok _ _ _ _ _ _ _ HHc) as FSI.
pose proof (PMABA5.fap_of L ar C HI HIok R0 M0 model0 LBX FF LK0 Aw0 cr0 S fb s0 FOK F fl LK2 M2 model2 G _ M2 model2 LK2 cr0 Aw0 BI) as FAP.
assert (DF1 : 0 <= F / 8) by (apply Z.div_pos; lia). assert (DF2 : F / 8 <= 17592186044408) by (apply Z.div_le_upper_bound; lia).
set (W3 := fun a => (S - 128 <= a < S - 120) \/ (F <= a < F + 24) \/ (F / 8 + 2147450880 <= a < F / 8 + 2147450888) \/ (op + 12 <= a < op + 16)).
apply (L5SAR.apiece L ar C HI LYa HIok (PM.parser_own s0 ++ LBX) FF' LK2 cr0 Aw0 M2 model2 fx fx3 R 0xb08dc R3 pc3 M3v W3 K HHc AMc MS3 MG3).
{ intros a Ha Nw. apply FRZ3; [exact Ha| intros X; apply Nw; left; exact X| intros X; apply Nw; right; left; exact X
| intros X; apply Nw; right; right; left; exact X| intros X; apply Nw; right; right; right; exact X]. }
{ intros a Ha Wa. destruct Wa as [X|[X|[X|X]]].
- split; [unfold aclientw, aclient_g; right; left; split; [lia| intros Y; lia]| lia].
- split; [apply (L5SAR.fframe_client L ar _ FF' 0 0 F 0 (S - 128 + 32)); [left; reflexivity| change (ff_bytes 0) with 64; lia]| lia].
- split; [| unfold SB in *; lia]. apply (L5SAR.fframe_shadow_client L ar _ FF' 0 0 F 0 (S - 128 + 32)); [left; reflexivity|].
change (ff_bytes 0) with 64. unfold in_shadow_of, HeapIfaceA.S, SB. change (ff_bytes 0) with 64 in F8. rewrite (proj1 (proj2 F8)). change (64 / 8) with 8. lia.
- split; [apply (L5SAR.fframe_client L ar _ FF' 0 0 fb 4 rs); [exact HfbF| change (ff_bytes 4) with 1024; unfold PMABK.op in X; lia]| unfold PMABK.op in X; lia]. }
intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3.
assert (BI3 : binv' (PM.parser_own s0) M3 model3 LK2 cr0 Aw0).
{ apply (PMAUK.binv_pieceW L ar HI M0 model0 LBX FF LK0 Aw0 S SCR (S - 128) (S - 104) S ocell own F fl 0 LK2 M2 model2 cr0 (PM.parser_own s0) G
WR (PM.parser_own s0) M2 model2 LK2 cr0 Aw0 M3 model3 W3 BI HH3 AM3 MRT3 MGM3 FR3).
intros a Wa. unfold PMABK.ocell. destruct Wa as [X|[X|[X|X]]]; (split; [unfold PMABK.op in *; lia|]).
- left; lia.
- right; left. change (ff_bytes 0) with 64. lia.
- right; right; left. unfold SB. change (ff_bytes 0 / 8) with 8. lia.
- right; right; right. intros O. apply (O (PMSPA.o_p AD fb + 8, 8)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; unfold PMABK.op in X; lia]. }
assert (EK3 : L5SAR.ek L ar (PM.parser_own s0 ++ LBX) FF S 26624 [(op + 12, 4)] M2 M3).
{ apply (L5SAR.ek_piece L ar _ FF S 26624 _ M2 M3 W3 FR3). intros a Ha Hc Ho Wa. destruct Wa as [X|[X|[X|X]]].
- destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF' LK2 cr0 Aw0 M2 _ S 26624 a HHc SPTg (L5SAR.aclient_cons L ar _ FF _ _ _ _ Hc)) as [Y|Y]; lia.
- exact (fframe_nc (PM.parser_own s0) LK2 cr0 Aw0 M2 _ HHc a ltac:(lia) Hc).
- exact (PMABK2.fsh_nc L ar C HI HIok R0 LBX FF LK0 Aw0 cr0 S s0 F fl LK2 M2 model2 G (PM.parser_own s0) LK2 cr0 Aw0 M2 _ HHc a ltac:(lia) Hc).
- apply (Ho (op + 12, 4)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]. }
pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HHc) as FRB'. pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HHc) as BRB.
assert (FRB : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47) by (intros f Hf; apply FRB'; right; exact Hf).
assert (AOF : forall a n, fb + 32 <= a -> a + n <= fb + 1016 -> PMSPA.aobjA FF a n)
by (intros a n X1 X2; exists (fb, 4, rs); split; [exact Hfb|]; cbn [ff_addr ff_class fst snd]; change (ff_bytes 4) with 1024; lia).
assert (WAPP : PMKA.wapp [(op + 12, 4)]).
{ apply PMKA.wapp_cons; [| apply PMKA.wapp_nil]. cbn [fst snd]. unfold PMABK.op. unfold BIGSHADOW_LO, BIGSHADOW_HI. destruct FA1; lia. }
assert (OUT : forall a n, (a + n <= op + 12 \/ op + 16 <= a) -> forall i, a <= i < a + n -> L5.outside [(op + 12, 4)] i).
{ intros a n X3 i Hi rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. lia. }
assert (OUTB : forall q m, In (q, m) (PM.parser_own s0 ++ LBX) -> forall i, q <= i < q + m -> L5.outside [(op + 12, 4)] i).
{ intros q m Hq i Hi rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr.
destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q m (PMSPA.o_p AD fb) 384 HHc Hq (PMAUAR.aobjA_push FF _ 384 (F, 0, S - 128 + 32) (AOF (PMSPA.o_p AD fb) 384 ltac:(lia) ltac:(lia))))
as [Z0|Z0]; unfold PMABK.op in Hr; lia. }
assert (Ivb : In (PM.p_b s0, 32 * 2 ^ PM.p_k s0) (PM.parser_own s0 ++ LBX)) by (apply in_or_app; left; unfold PM.parser_own, PM.vec_own; right; left; reflexivity).
assert (Iqc : In (PM.sr_qc (PM.p_src s0), PM.CHUNK) (PM.parser_own s0 ++ LBX)) by (apply in_or_app; left; unfold PM.parser_own, PM.src_own; left; reflexivity).
destruct (BRB _ Iqc) as (Xq1 & Xq2). destruct (BRB _ Ivb) as (Xb1 & Xb2). cbn [fst snd] in Xq1, Xq2, Xb1, Xb2.
pose proof (PMAPAR.op_vis L ar C HI LY HIok _ FF' LK2 cr0 Aw0 M2 model2 fb _ s0 HHc (PMAUAR.frame_okA_push FF fb F 0 (S - 128 + 32) FOK) PA)
as (_ & _ & _ & _ & _ & _ & OAV & _ & _).
pose proof INV as (IM & ID & IDP & ISH & ITB). pose proof ISH as (SH1 & SH2 & _). unfold PM.MAX_DEPTH in SH2.
assert (PA3 : PM.parser_at RSEGS AD PMSPA.accA PMSPA.annA M3 (PMSPA.o_p AD fb) (PMSPA.o_is AD fb) (PMABK.sd s0 (PM.p_src s0))).
{ unfold PMABK.sd. apply (parser_depth_updA M2 M3 _ _ s0 (PM.p_depth s0 + 1) PA).
- lia.
- lia.
- apply (PMKA.agA_obj L ar _ FF S 26624 _ M2 M3 EK3 WAPP FRB (PMSPA.o_p AD fb) 12 (AOF (PMSPA.o_p AD fb) 12 ltac:(lia) ltac:(lia))). apply OUT. unfold PMABK.op; lia.
- apply (PMKA.agA_obj L ar _ FF S 26624 _ M2 M3 EK3 WAPP FRB (PMSPA.o_p AD fb + 16) 368 (AOF (PMSPA.o_p AD fb + 16) 368 ltac:(lia) ltac:(lia))). apply OUT. unfold PMABK.op; lia.
- exact (PMKA.agsh_obj L ar _ FF S 26624 _ M2 M3 EK3 WAPP FRB (PMSPA.o_p AD fb) 384 (AOF (PMSPA.o_p AD fb) 384 ltac:(lia) ltac:(lia))).
- pose proof PA as (_ & PD & _). apply (L5.defined_grows M2 M3 _ _ MGM3 PD).
- apply (proj1 (L5A.u32_at_vis (ahid Aw0 model2) M3 (op + 12) _ (OAV (op + 12) 4 ltac:(unfold PMABK.op; lia) ltac:(unfold PMABK.op; lia)) ltac:(unfold PMABK.op; lia) ltac:(unfold PMABK.op; lia))).
rewrite VIS3. exact D3.
- unfold PM.MAX_DEPTH. lia.
- exact Xq1.
- lia.
- apply (PMKA.agA_blk L ar _ FF S 26624 _ M2 M3 EK3 WAPP BRB _ _ Iqc). apply OUTB. exact Iqc.
- exact Xb1.
- lia.
- apply (PMKA.agA_blk L ar _ FF S 26624 _ M2 M3 EK3 WAPP BRB _ _ Ivb). apply OUTB. exact Ivb.
- intros c0 n0 p0 Etb. assert (Ip : In (p0, c0) (PM.parser_own s0 ++ LBX)) by (apply in_or_app; left; unfold PM.parser_own, PM.vs_own; rewrite Etb; right; right; left; reflexivity).
apply (PMKA.agA_blk L ar _ FF S 26624 _ M2 M3 EK3 WAPP BRB _ _ Ip). apply OUTB. exact Ip. }
assert (RUN3 : PMSPA.run_pre RSEGS AD PMA.AAD M3 fb (PMABK.sd s0 (PM.p_src s0)) str sm0 e0).
{ split; [exact PA3|].
split; [apply (PMKA.iss_keepA RSEGS AD L ar _ FF S 26624 _ M2 M3 EK3 WAPP FRB BRB _ str sm0 (AOF (PMSPA.o_is AD fb) 272 ltac:(lia) ltac:(lia)));
[intros x Hx; apply in_or_app; right; apply INCS; exact Hx| apply OUT; unfold PMABK.op; lia
| intros c0 n0 p0 Etb i Hi; apply (OUTB p0 c0); [apply in_or_app; right; apply INCS; rewrite Etb; left; reflexivity| exact Hi]
| exact IA]|].
split; [apply (PMKA.visitor_keepA RSEGS AD L ar _ FF S 26624 _ M2 M3 EK3 WAPP FRB (PMSPA.o_v AD fb) (AOF (PMSPA.o_v AD fb) 8 ltac:(lia) ltac:(lia))); [apply OUT; unfold PMABK.op; lia| exact VIS]|].
split; [apply (PMKA.u64_keepA RSEGS L ar _ FF S 26624 _ M2 M3 EK3 WAPP FRB (PMSPA.o_p AD fb + 384) (PMSPA.o_v AD fb) (AOF (PMSPA.o_p AD fb + 384) 8 ltac:(lia) ltac:(lia)));
[apply OUT; unfold PMABK.op; lia| exact VREF]|].
split; [apply (PMASK.base_keep L ar C LY _ FF S 26624 _ M2 M3 EK3); [| exact BASE]; intros a Ha rr [<-|[]] Hr; unfold L5.in_rng in Hr; cbn [fst snd] in Hr; unfold PMABK.op in Hr; lia|].
split; [apply (PMKA.err_okA_keep RSEGS AD PMA.AAD L ar _ FF S 26624 _ M2 M3 EK3 e0 PMA.addrs_wf_A); [| exact ERR];
intros a D; pose proof (PMASK.dep_img a D) as DI; rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa); split; [lia|];
split; [exact (PMA.ly_static L C LY a D)| intros rr [<-|[]] Hr; unfold L5.in_rng in Hr; cbn [fst snd] in Hr; unfold PMABK.op in Hr; lia]|].
exact TBOK. }
assert (EC3 : PMSPA.ec_at RSEGS M3 oec 0 cat).
{ apply (PMKA.ec_keepA RSEGS L ar _ FF S 26624 _ M2 M3 EK3 WAPP FRB oec 0 cat (AOF oec 16 ltac:(unfold PMABK.oec; lia) ltac:(unfold PMABK.oec; lia))); [| exact EC].
apply OUT. unfold PMABK.oec, PMABK.op. lia. }
assert (UP64 : forall a v, (F <= a /\ a + 8 <= F + 64) \/ (S - 128 <= a /\ a + 8 <= S) -> L5.u64_at RSEGS M3v a v -> L5.u64_at RSEGS M3 a v).
{ intros a v Ha X. rewrite <- VIS3 in X. destruct Ha as [Ha|Ha].
- exact (proj1 (L5A.u64_at_vis _ M3 a v (L5A.avis_sub _ F 64 a 8 FV8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) X).
- exact (proj1 (L5A.u64_at_vis _ M3 a v (L5A.avis_sub _ (S - 128) (S - (S - 128)) a 8 SV8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) X). }
assert (UP8 : forall a v, F / 8 + 2147450880 <= a < F / 8 + 2147450888 -> L5.u8_at RSEGS M3v a v -> L5.u8_at RSEGS M3 a v).
{ intros a v Ha X. rewrite <- VIS3 in X. exact (proj1 (L5A.u8_at_vis _ M3 a v (L5A.avis_sub _ (F / 8 + SB) 8 a 1 SHV8 ltac:(unfold SB; lia) ltac:(unfold SB; lia)) ltac:(lia) ltac:(lia)) X). }
apply (NEXT M3 model3); [| exact VIS3].
split; [exact BI3|]. split; [exact RUN3|]. split; [exact EC3|].
split; [split; [apply UP64; [left; lia| exact H0]|]; split; [apply UP64; [left; lia| exact H8]|]; split; [apply UP64; [left; lia| exact H16]| apply UP64; [right; lia| exact C128]]|].
split; [pose proof FSH3 as (Y0 & Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7); repeat split; (apply UP8; [lia| assumption])|].
split; [unfold PMSPA.src_step, PMABK.sd; cbn [PM.p_src]; split; [reflexivity|]; split; [reflexivity|]; split; [lia|]; split; [intros X; exact X| lia]|].
split; [intros X; exact X|].
split; [unfold PMABK.sdl, PMABK.sd; cbn [PM.p_more PM.p_done PM.p_depth PM.p_stk]; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity| reflexivity]|].
split; [exact CRED| unfold PMSPA.credit_keep; change (PM.pot_parser (PMSPA.HV L ar) (PMABK.sd s0 (PM.p_src s0))) with (PM.pot_parser (PMSPA.HV L ar) s0); lia].
Qed.
Lemma b0_stage : ltac2:(TCodec.tc2 tcn__PmABa7 "R<'RL&Hy5'T5yR0%211%5241&QAvBvS;v@vQ1vKvSGvCv?vDv1vS2vSCv>&R7vT1%211vLvSHvEvS>%ECDCBA@?>=<;:9854321;&RB&S1&QH&QGvT6vT3vSB%79654<A>321&RA&QD%11DzvS=%55<B321&Q<&Q3&Q6%12ME%321G&S4&S5+8%22O1+QoooPP0%5221%;3714&Q=r5%211'RO&Q;vS3%211&R@r7r6+fRVL%46Q4321Q:Q9vA%:4Q6721p0<1p0@1p0M1p0Q41p0Q=1pR2R41pW:R;1").
Proof using All. intros fx R.
intros BI RUN EC ZF SR. pose proof SR as (X2 & X8 & X9 & X10 & X19 & X20 & X21 & X27 & X3 & X4).
pose proof (vpack0 _ s0 sm0 e0 cat M2 model2 LK2 cr0 Aw0 BI RUN EC ZF) as VF0.
set (MV := mrestrict (ahid Aw0 model2) M2) in *.
pose proof INV as (IM & ID & IDP & ISH & ITB). pose proof ISH as (SH1 & SH2 & _). unfold PM.MAX_DEPTH in SH2.
assert (DB : 0 <= PM.p_depth s0 < 2 ^ 64) by lia.
destruct (Z_le_gt_dec (PM.p_depth s0) 1023) as [Dle|Dgt].
-
assert (Dle' : 0 <= PM.p_depth s0 <= 1023) by lia.
pose proof (PMABAP1.abaB0_conc fx R MV (VB (PM.p_depth s0))) as P. unfold VB, PMABA3.VT in P. cbn beta iota in P. feedV0 P VF0.
destruct P as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & PR). decompose [and] PR. clear PR.
apply (b0_core fx R (PM.p_depth s0) BI RUN EC ZF SR fx3 R3 M3v 0xae850 MS3 MG3).
+ intros i Hi N1 N2 N3 N4. apply FRZ3; [exact Hi| intros X; apply N1; lia| intros X; apply N2; lia| intros X; apply N3; lia| intros X; apply N4; lia].
+ hx.
+ hx.
+ hx.
+ hx.
+ hx.
+ unfold PMABK.fsh. cbn iota. repeat split; hx.
+ intros M3 model3 BS3 VIS3.
assert (MR3 : mregs R3).
{ unfold PMABA2.mregs, PMABA2.mregs0. repeat split; first [ hx | (rewrite (KS3 _) by inl; hx) ]. }
assert (B1 : getr R3 (reg 1) = Z_to_bv 64 0xb09b0) by hx. assert (B10 : getr R3 (reg 10) = Z_to_bv 64 (op + 24)) by hx.
pose proof MR3 as ((Y2 & Y8 & Y9 & Y18 & Y19 & Y20 & Y21 & Y25 & Y26 & Y27 & Y3 & Y4) & Y23).
pose proof PEEK as PEEK'. unfold PMA.peek_spec, PMSPA.peek_spec in PEEK'. cbn [pa_peek PMA.AD ADDR_A] in PEEK'.
apply (call_src 0xae850 4 PMSPA.no_args PMSPA.no_W PMSPA.peek_res PEEK' false (PMABK.sd s0 (PM.p_src s0)) sm0 e0 fx3 R3 M3 model3 LK2 cr0 Aw0 0xb09b0 [] BS3 B1
ltac:(apply pow_bnd_ra; [lia| reflexivity]) Y2 Y3 Y4 B10 ltac:(lia)).
* exact I.
* reflexivity.
* intros rr [].
* intros fx4 R4 M4 model4 LK4 Aw4 src4 sm4 RP4 RES4 _ BS4.
destruct RES4 as (_ & RES4).
apply (kdisp (PMSPA.with_src (PMABK.sd s0 (PM.p_src s0)) src4) sm4 e0 fx4 R4 M4 model4 LK4 cr0 Aw4 Dle BS4 (mregs_keep R3 R4 MR3 RP4)).
rewrite !L5K.rl10 in RES4. destruct RES4 as [Y|(c & Hc & Y & _)]; [left; exact Y| right; exists c; split; [exact Hc| exact Y]].
-
assert (Ed : PM.p_depth s0 = 1024) by lia.
rewrite Ed in VF0.
pose proof (PMABAP1.abaB1_conc fx R MV (VB 1024)) as P. unfold VB, PMABA3.VT in P. cbn beta iota in P. feedV0 P VF0.
destruct P as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & PR). decompose [and] PR. clear PR.
apply (b0_core fx R 1024 BI RUN EC ZF SR fx3 R3 M3v 0xae974 MS3 MG3).
+ intros i Hi N1 N2 N3 N4. apply FRZ3; [exact Hi| intros X; apply N1; lia| intros X; apply N2; lia| intros X; apply N3; lia| intros X; apply N4; lia].
+ rewrite Ed. change (1024 + 1) with 1025. hx.
+ hx.
+ hx.
+ hx.
+ hx.
+ unfold PMABK.fsh. cbn iota. repeat split; hx.
+ intros M3 model3 BS3 VIS3.
assert (MR3 : mregs0 R3).
{ unfold PMABA2.mregs0. repeat split; first [ hx | (rewrite (KS3 _) by inl; hx) ]. }
assert (B1 : getr R3 (reg 1) = Z_to_bv 64 0xb0da8) by hx. assert (B10 : getr R3 (reg 10) = Z_to_bv 64 oec) by hx. assert (B11 : getr R3 (reg 11) = Z_to_bv 64 11) by hx.
exact (mk_Z11 (PMABK.sd s0 (PM.p_src s0)) sm0 e0 fx3 R3 M3 model3 LK2 cr0 Aw0 11 BS3 MR3 B1 B10 B11 ltac:(lia)).
Qed.
End Frame.
Definition vfactsE (MV : word -> option byte) : Prop :=
(0 <= S < 2 ^ 64 /\ 0 <= op < 2 ^ 64 /\ 0 <= ov < 2 ^ 64 /\ 0 <= oec < 2 ^ 64)
/\ L5.img_clear MV 65536 1261568 /\ L5.u64_at RSEGS MV 1289464 2147450880 /\ L5.u32_at RSEGS MV 1289472 1
/\ 140735332487328 <= S <= 140737488355328 /\ S mod 32 = 0 /\ L5.writable RSEGS MV (S - 160) 160
/\ 6885376 <= op <= 140737488354944 /\ op mod 8 = 0 /\ (2147446784 + 17592186048512 <= op \/ op + 384 <= 2147446784)
/\ L5KA.zeros_at MV ((op / 8) + 2147450880) 3 /\ L5KA.zeros_at MV (((op + 32) / 8) + 2147450880) 44 /\ L5KA.zeros_at MV (((op + 20) / 8) + 2147450880) 1
/\ L5.writable RSEGS MV op 384 /\ ((S - 160) + 160 <= op \/ op + 384 <= (S - 160))
/\ 6885376 <= oec <= 140737488355312 /\ oec mod 8 = 0 /\ (2147446784 + 17592186048512 <= oec \/ oec + 16 <= 2147446784)
/\ L5KA.zeros_at MV ((oec / 8) + 2147450880) 2 /\ L5.writable RSEGS MV oec 16 /\ ((S - 160) + 160 <= oec \/ oec + 16 <= (S - 160))
/\ 6885376 <= ov <= 140737488355320 /\ ov mod 8 = 0 /\ (2147446784 + 17592186048512 <= ov \/ ov + 8 <= 2147446784)
/\ L5KA.zeros_at MV ((ov / 8) + 2147450880) 1 /\ L5.writable RSEGS MV ov 8 /\ ((S - 160) + 160 <= ov \/ ov + 8 <= (S - 160))
/\ (op + 384 <= oec \/ oec + 16 <= op) /\ (op + 384 <= ov \/ ov + 8 <= op) /\ (oec + 16 <= ov \/ ov + 8 <= oec).
Lemma vpackE : ltac2:(TCodec.tc2 tcn__PmABa7 "9&Q?&Q3&Q6v1vSG%3221vK%6221%811").
Proof using All.
pose proof RPRE as (PA & IA & VIS & VREF & BASE & ERR & TBOK).
pose proof ENT as (_ & _ & _ & _ & _ & ASTK0 & _). change (PMSPA.pm_scr 7) with 26624 in ASTK0.
pose proof ASTK0 as (A16 & SLO & SHI & SPT & SDEF & SUP).
pose proof (PMABK.frame_geo fb) as (Eop & Eois & Eov & Eoec & Eos).
pose proof (PMAPAR.op_vis L ar C HI LY HIok _ FF LK0 cr0 Aw0 M0 model0 fb _ s0 HH0 FOK PA) as ((O1 & O8 & ONSH) & Zop & Z32 & Z20 & OWR & OCE & OAV & AOP & _).
pose proof (PMAPAR.ov_vis L ar C HI LY HIok _ FF LK0 cr0 Aw0 M0 model0 fb HH0 FOK VIS) as ((V1 & V8 & VNSH) & Zv & VWR & VCE & VU & AOV & _).
pose proof (PMAPAR.oec_vis L ar C HI LY HIok _ FF LK0 cr0 Aw0 M0 model0 fb 0 cat HH0 FOK EC0) as ((E1 & E8 & ENSH) & Ze & EWR & ECE & EU & AOE & _).
pose proof (PMASK.mach_vis L ar C HI LY HIok _ FF LK0 cr0 Aw0 M0 model0 HH0 BASE) as (VM0 & VM1 & VM2).
pose proof (PMASK.stk_vis L ar C HI LY HIok _ FF LK0 cr0 Aw0 M0 model0 S 26624 160 HH0 ASTK0 ltac:(lia)) as (SL160 & SH160 & SWR).
fold op ov oec in *.
unfold vfactsE.
split; [lia|]. split; [exact VM0|]. split; [exact VM1|]. split; [exact VM2|].
split; [lia|]. split; [exact SP32|]. split; [exact SWR|].
split; [lia|]. split; [exact O8|]. split; [exact ONSH|]. split; [exact Zop|]. split; [exact Z32|]. split; [exact Z20|]. split; [exact OWR|]. split; [lia|].
split; [lia|]. split; [exact E8|]. split; [exact ENSH|]. split; [exact Ze|]. split; [exact EWR|]. split; [lia|].
split; [lia|]. split; [exact V8|]. split; [exact VNSH|]. split; [exact Zv|]. split; [exact VWR|]. split; [lia|].
split; [lia|]. split; lia.
Qed.
Ltac hx := match goal with |- ?G => match goal with H : G |- _ => exact H end end.
Lemma UB' : ltac2:(TCodec.tc2 tcn__PmABa7 "A'6'9&S6z&Q@vQ1r1%3221%6251&S7&S9+2+R0%3221%5271%>271pX@@1").
Proof. intros x. unfold PMABK.U. pose proof (bv_unsigned_in_range 64 (getr R0 (reg x))) as B. change (bv_modulus 64) with (2 ^ 64) in B. exact B. Qed.
Ltac vfeed := first [ hx | (split; hx) | apply UB' | (unfold PMABAP1.aligned; hx) | (unfold PMABAP2.aligned; hx) ].
Ltac vopenE VF := unfold vfactsE in VF; decompose [and] VF; clear VF.
Ltac feedVE P VF :=
let T := type of P in
let C := L5SAR.feed_concl T in
let Q := fresh "SC" in
assert (Q : C) by (let W := fresh "W" in pose proof VF as W; vopenE W; apply P; clear P;
first [ vfeed | lazymatch goal with |- ?A => fail 1 "feedVE: cannot prove premise" A end ]);
move Q after P; clear P; rename Q into P.
Lemma entry : ltac2:(TCodec.tc2 tcn__PmABa7 "@'RL'RO&S1&Q;vS3%211&R@r1vQ1+fRS4vKvSG%66:54321vA%=4<921pW:?1").
Proof using All. intros fx.
pose proof ENT as (Rra0 & RAok0 & Rsp0 & Rgp0 & Rtp0 & ASTK0 & STKSH0). change (PMSPA.pm_scr 7) with 26624 in *.
pose proof ASTK0 as (A16 & SLO & SHI & SPT & SDEF & SUP).
pose proof ARGS as (A10 & A11 & A12).
rewrite L5K.rl2 in Rsp0. rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11. rewrite L5K.rl12 in A12.
change (PMSPA.o_p AD fb) with op in A10. change (PMSPA.o_v AD fb) with ov in A11. change (PMSPA.o_ec AD fb) with oec in A12.
pose proof vpackE as VFE.
set (MV0 := mrestrict (ahid Aw0 model0) M0) in *.
pose proof (PMABAP1.abaA_conc fx R0 MV0 (fun j => match j with 2%nat => S | 36%nat => op | 37%nat => ov | 38%nat => oec | _ => 0 end)) as P.
cbn beta iota in P. feedVE P VFE.
destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & PR). decompose [and] PR. clear PR.
apply (L5SAR.apiece L ar C HI LYa HIok (PM.parser_own s0 ++ LBX) FF LK0 cr0 Aw0 M0 model0 fx fx1 R0 0xb0864 R1 0x5d22c M1v (fun a => S - 128 <= a < S) K HH0 AM0 MS1 MG1).
{ intros a Ha N. apply FRZ1; [exact Ha| intros X; apply N; lia]. }
{ intros a Ha Wa. split; [|lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros Y; lia]. }
intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK0 cr0 Aw0 M0 model0 HH0) as (_ & VISs & _).
assert (SV1 : forall a v, S - 128 <= a -> a + 8 <= S -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v).
{ intros a v Ha1 Ha2 X. apply (proj1 (L5A.u64_at_vis _ M1 a v (VISs a 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). rewrite VIS1. exact X. }
assert (OWN1 : own M1).
{ unfold PMABK.own, PMABK.U. repeat split; (apply SV1; [lia| lia| hx]). }
assert (NCS0 : forall a, S - 128 <= a < S -> ~ aclient L ar (PM.parser_own s0 ++ LBX) FF S 26624 a).
{ intros a Xa Hc. destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK0 cr0 Aw0 M0 _ S 26624 a HH0 SPT Hc) as [Y|Y]; lia. }
assert (EK01f : L5SAR.ek L ar (PM.parser_own s0 ++ LBX) FF S 26624 [] M0 M1).
{ apply (L5SAR.ek_piece L ar _ FF S 26624 [] M0 M1 (fun a => S - 128 <= a < S) FR1). intros a Ha Hc _ X. exact (NCS0 a X Hc). }
assert (INCX : incl LBX (PM.parser_own s0 ++ LBX)) by (apply incl_appr; apply incl_refl).
pose proof (PMKA.ek_sublb L ar _ LBX FF S 26624 [] M0 M1 INCX EK01f) as EK01.
pose proof (PMKA.dk_sublb L ar _ LBX FF S 26624 M0 M1 INCX (L5SAR.dk_grows L ar _ FF S 26624 M0 M1 MGM1)) as DK01.
assert (FRk0 : ff_room 0 FF LK0) by (apply (PMAUAR.ff_room_of 7 FF LK0 0 FRM); [lia| left; reflexivity]).
assert (R12 : getr R1 (reg 2) = Z_to_bv 64 (S - 128)) by hx.
assert (R11 : getr R1 (reg 1) = Z_to_bv 64 0xb08dc) by hx.
change 0x5d22c with (PMA.SM_PC 0).
apply (PMAUAR.uar_sm L ar C HI LY HIok 0 LBX (PM.parser_own s0) FF LK0 cr0 Aw0 S 26624 (S - 128) (S - 104) S ocell own
fx1 R1 M0 M1 model0 model1 K 0xb08dc ltac:(left; reflexivity) HH0 HH1 AM1 K0 ASTK0 MGM1 EK01 DK01).
{ rewrite L5K.rl2. exact R12. }
{ rewrite L5K.rl4. rewrite (KS1 4%nat) by inl. rewrite <- L5K.rl4. exact Rtp0. }
{ rewrite L5K.rl1. exact R11. }
{ reflexivity. }
{ lia. }
{ replace (S - 128) with (S + (-8) * 16) by lia. rewrite Z_mod_plus_full. exact A16. }
{ lia. } { lia. } { lia. } { lia. }
{ intros a Ha. exact Ha. }
{ intros Ma Mb OW AG. exact (PMABK.own_agree R0 S Ma Mb ltac:(lia) ltac:(lia) OW AG). }
{ exact FRk0. }
{ exact FRS. }
intros R2 M2 model2 F fl LK2 G G10 RP2 AM2 MRT2 ASTK2 EK02 DK02 EK12 DK12 AGF FW FSHW FSHZ FLC FLW FDEF VF VSH VFL APART.
change (ff_bytes 0) with 64 in *. change (64 / 8) with 8 in *.
pose proof G as G'. destruct G' as [Hk SPTg SLOg SHIg SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC' FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
assert (BI2 : PMABK.binv' L ar HI R0 M0 model0 LBX FF LK0 Aw0 S fb F (PM.parser_own s0) M2 model2 LK2 cr0 Aw0).
{ unfold PMABK.binv', PMAUK.binv. split; [exact HH2|]. split; [exact AM2|]. split; [exact (L5LZ.model_rt_trans _ _ _ MRT1 MRT2)|].
split; [apply incl_refl|]. split; [exact LKI2|]. split; [exact ASTK2|].
split; [exact (L5SAR.ek_W L ar LBX FF S 26624 WR [] M0 M2 EK02 (fun a _ rr H0 => match H0 with end))|].
split; [exact DK02|].
split; [apply (PMABK.own_agree R0 S M1 M2 ltac:(lia) ltac:(lia) OWN1); intros a Ha; apply AGF; unfold PMABK.ocell in Ha; lia|].
intros i Hi. pose proof (FSHZ i Hi) as Y. unfold byte_at in Y. unfold mrestrict in Y. rewrite (VSH i Hi) in Y. unfold SB in *. change (ff_bytes 0 / 8) with 8. rewrite Y. discriminate. }
pose proof RPRE as (PA & IA & VIS & VREF & BASE & ERR & TBOK).
pose proof (L5SAR.ek_trans L ar _ FF S 26624 [] M0 M1 M2 EK01f EK12) as EK02f.
pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH0) as FRB. pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH0) as BRB.
pose proof FOK as ((rs & Hfb) & Fal).
assert (AOF : forall a n, fb + 32 <= a -> a + n <= fb + 1016 -> PMSPA.aobjA FF a n)
by (intros a n X1 X2; exists (fb, 4, rs); split; [exact Hfb|]; cbn [ff_addr ff_class fst snd]; change (ff_bytes 4) with 1024; lia).
pose proof (PMABK.frame_geo fb) as (Eop & Eois & Eov & Eoec & Eos).
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH0) as (WB & WF & FSAPP & FSCEIL & _).
destruct (WF _ Hfb) as (Ff1 & Ff2 & _). cbn [ff_addr ff_class fst snd] in Ff1, Ff2. change (ff_bytes 4) with 1024 in Ff2.
unfold app_mem, FS_BYTES in FSAPP, FSCEIL, Ff1, Ff2.
assert (RUN2 : PMSPA.run_pre RSEGS AD PMA.AAD M2 fb s0 str sm0 e0).
{ split; [apply (PMKA.parser_keepA RSEGS AD L ar _ FF S 26624 [] M0 M2 EK02f PMKA.wapp_nil FRB BRB _ _ _ (AOF (PMSPA.o_p AD fb) 384 ltac:(lia) ltac:(lia)));
[apply incl_appl, incl_refl| intros i _ r0 []| intros i _ r0 []| intros i _ r0 []| intros c0 n0 p0 _ i _ r0 []| exact PA]|].
split; [apply (PMKA.iss_keepA RSEGS AD L ar _ FF S 26624 [] M0 M2 EK02f PMKA.wapp_nil FRB BRB _ str sm0 (AOF (PMSPA.o_is AD fb) 272 ltac:(lia) ltac:(lia)));
[intros x Hx; apply in_or_app; right; apply INCS; exact Hx| intros i _ r0 []| intros c0 n0 p0 _ i _ r0 []| exact IA]|].
split; [apply (PMKA.visitor_keepA RSEGS AD L ar _ FF S 26624 [] M0 M2 EK02f PMKA.wapp_nil FRB (PMSPA.o_v AD fb) (AOF (PMSPA.o_v AD fb) 8 ltac:(lia) ltac:(lia))); [intros i _ r0 []| exact VIS]|].
split; [apply (PMKA.u64_keepA RSEGS L ar _ FF S 26624 [] M0 M2 EK02f PMKA.wapp_nil FRB (PMSPA.o_p AD fb + 384) (PMSPA.o_v AD fb) (AOF (PMSPA.o_p AD fb + 384) 8 ltac:(lia) ltac:(lia)));
[intros i _ r0 []| exact VREF]|].
split; [apply (PMASK.base_keep L ar C LY _ FF S 26624 [] M0 M2 EK02f); [intros a _ r0 []| exact BASE]|].
split; [apply (PMKA.err_okA_keep RSEGS AD PMA.AAD L ar _ FF S 26624 [] M0 M2 EK02f e0 PMA.addrs_wf_A); [| exact ERR];
intros a D; pose proof (PMASK.dep_img a D) as DI; rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa); split; [lia|];
split; [exact (PMA.ly_static L C LY a D)| intros r0 []]|].
exact TBOK. }
assert (EC2 : PMSPA.ec_at RSEGS M2 oec 0 cat).
{ apply (PMKA.ec_keepA RSEGS L ar _ FF S 26624 [] M0 M2 EK02f PMKA.wapp_nil FRB oec 0 cat (AOF oec 16 ltac:(unfold PMABK.oec; lia) ltac:(unfold PMABK.oec; lia))); [intros i _ r0 []| exact EC0]. }
assert (ZF : L5KA.zeros_at (mrestrict (ahid Aw0 model2) M2) (F / 8 + 2147450880) 8) by (unfold SB in FSHZ; exact FSHZ).
assert (R2c : forall j, In j L5SAR.cs_all -> getr R2 (reg j) = getr R1 (reg j)) by (intros j Hj; exact (L5SAR.cs_of_preserved R1 R2 j RP2 Hj)).
assert (SR : sregs F R2).
{ unfold sregs. rewrite L5K.rl10 in G10.
repeat split; first [ exact G10 | (rewrite R2c by (cbn; tauto); hx) | (rewrite R2c by (cbn; tauto); rewrite (KS1 _) by inl; reflexivity) ]. }
exact (b0_stage F fl LK2 M2 model2 G fx1 R2 BI2 RUN2 EC2 ZF SR).
Qed.
End Call.
Theorem begin_array_ok : ltac2:(TCodec.tc2 tcn__PmABa7 "N&RGvS3vBvS;v@%544321&RE%146543&RK%148765&RD%14:987&RF%14<;:9&RH%14>=<;&RI%14@?>=&RJ%14BA@?&RC%14DCBAp031p061p091p0<1p0?1p0B1p0E1p0H1").
Proof.
intros PEEK IGN SRD GLS MKE PMI PMS PMSU.
unfold PMA.begin_array_spec, PMSPA.begin_array_spec, PMSPA.run_spec, PMSPA.run_spec_r.
intros fx R M model K LBX FF LK Aw cr sp r fb cat s str sm e HH AM K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT.
cbn [pa_begin_array PMA.AD ADDR_A].
exact (entry R M model K LBX FF LK Aw cr sp r fb cat s str sm e HH AM K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT
PEEK IGN SRD GLS MKE PMI PMS PMSU fx).
Qed.
End WithHeap.
End PMABA7.
