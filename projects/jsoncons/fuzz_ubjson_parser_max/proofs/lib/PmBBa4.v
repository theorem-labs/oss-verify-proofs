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
PmModelFactsA PmStepAB0 PmStep PmParStep PmParKit PmBSrcKit PmBParKit PmBReset1 PmBUarK PmBUar PmBUarKS PmBBaK PmBBaK2 PmBBaK3 Jb0_code_b2664_b2668 PmBBa1 PmBBaP1 PmBBaP2 PmBBaP3 PmBBa2 PmBBa3.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmBBa4 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBBa2.PMBBA2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBBaK.PMBBK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0Ac"; "0Aw0"; "0BX"; "1bool"; "1false"; "1length"; "1list"; "1option"; "1prod"; "2and"; "2eq"; "2or"; "3Z"; "0F"; "0FF"; "0HI"]; ["0K"; "0L"; "0LBX"; "0LK0"; "0LKc"; "4Model"; "5bvmap"; "0M0"; "0MV"; "0Mc"; "0R"; "0R0"; "6mrestrict"; "7credit"; "8S"; "8ahid"]; ["8byte_at"; "8fframe"; ":ra_ok"; ":u64_at"; "9SCFG"; ";mregs"; "<binv'"; "<bst"; "<fsh"; "<op"; "<vfacts"; "=AADDR_B"; "=ADDR_B"; ">p_b"; ">p_depth"; ">p_k"]; [">p_stk"; ">pst"; ">pstate"; ">strm"; "?cfg"; "?run_pre"; "@FPState"; "@getr"; "Asrealizes"; "Bloaded_segments"; "0S"; "0SCFG_P"; "Cadd"; "Cdiv"; "Cdivide"; "Cle"]; ["Clt"; "Cmodulo"; "Cmul"; "Cof_nat"; "Cpow"; "Csub"; "0a"; "0ar"; "0b"; "0c"; "0cat"; "0cr0"; "0crc"; "0d"; "0e"; "0e0"]; ["0fb"; "0fl"; "0fx"; "0k"; "0model0"; "0modelc"; "0n"; "0p"; "0s"; "0s0"; "0sm"; "0sm0"; "DZ_to_bv"; "Dbv"; "0str"; "0typed"]; ["0v"; "0x"]]).
Local Ltac lia := L5FastLia.plia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PMBBA4.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation AD := PMB.AD.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMB.ly_as0 L C LY.
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
Local Abbreviation bst0 := (PMBBK.bst0 L ar HI R0 M0 model0 LBX FF LK0 Aw0 cr0 S fb cat s0 str sm0 e0 F).
Local Abbreviation bste := (PMBBK.bste L ar HI R0 M0 model0 LBX FF LK0 Aw0 cr0 S fb s0 str sm0 F).
Local Abbreviation vfacts := (PMBBK.vfacts R0 S fb F fl).
Local Abbreviation vpack := (PMBBK.vpack L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE CMI SMI CMS SMS CMSU SMSU F fl LK2 M2 model2 G).
Local Abbreviation centry := (PMBBK.centry L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE CMI SMI CMS SMS CMSU SMSU F fl LK2 M2 model2 G).
Local Abbreviation own_with_src := PMBBK.own_with_src.
Local Abbreviation call_src := (PMBBK.call_src L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE CMI SMI CMS SMS CMSU SMSU F fl LK2 M2 model2 G).
Local Abbreviation call_mkec := (PMBBK.call_mkec L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE CMI SMI CMS SMS CMSU SMSU F fl LK2 M2 model2 G).
Local Abbreviation call_mkec0 := (PMBBK.call_mkec0 L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE CMI SMI CMS SMS CMSU SMSU F fl LK2 M2 model2 G).
Local Abbreviation fsh_nc := (PMBBK2.fsh_nc L ar C HI HIok R0 LBX FF LK0 Aw0 cr0 S s0 F fl LK2 M2 model2 G).
Local Abbreviation fsh_agree := (PMBBK2.fsh_agree S F).
Local Abbreviation step_piece := (PMBBK2.step_piece L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE CMI SMI CMS SMS CMSU SMSU F fl LK2 M2 model2 G).
Local Abbreviation wr_rng := (PMBBK2.wr_rng fb).
Local Abbreviation bsterr := (PMBBK2.bsterr L ar HI R0 M0 model0 LBX FF LK0 Aw0 cr0 S fb s0 str sm0 F).
Local Abbreviation call_gl := (PMBBK2.call_gl L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE CMI SMI CMS SMS CMSU SMSU F fl LK2 M2 model2 G).
Local Abbreviation push_st := PMBBK3.push_st.
Local Abbreviation aacc_sub := PMBBK3.aacc_sub.
Local Abbreviation parser_push_updA := PMBBK3.parser_push_updA.
Local Abbreviation stack_shape_push := PMBBK3.stack_shape_push.
Local Abbreviation ri_swap12 := (PMBBK3.ri_swap12 L ar C HI HIok).
Local Abbreviation stk_credit := (PMBBK3.stk_credit L ar C LY).
Local Abbreviation bstp := (PMBBK3.bstp L ar HI R0 M0 model0 LBX FF LK0 Aw0 cr0 S fb cat s0 str sm0 e0 F).
Local Abbreviation call_push := (PMBBK3.call_push L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE CMI SMI CMS SMS CMSU SMSU F fl LK2 M2 model2 G).
Local Abbreviation S_of_binv := (PMBBK3.S_of_binv L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE CMI SMI CMS SMS CMSU SMSU F fl LK2 M2 model2 G).
Local Abbreviation fin_any := (PMBBA1.fin_any L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE CMI SMI CMS SMS CMSU SMSU F fl LK2 M2 model2 G).
Local Abbreviation mregs0 := (PMBBA2.mregs0 R0 S fb F).
Local Abbreviation mregs := (PMBBA2.mregs R0 S fb F).
Local Abbreviation pregsT := (PMBBA3.pregsT R0 S fb F).
Local Abbreviation pregsI := (PMBBA3.pregsI R0 S fb F).
Local Abbreviation pregs := (PMBBA3.pregs R0 S fb F).
Local Abbreviation tregs := (PMBBA2.tregs R0 S fb F).
Local Abbreviation UB := (PMBBA2.UB R0).
Local Abbreviation mk_Z1 := (PMBBA2.mk_Z1 L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE CMI SMI CMS SMS CMSU SMSU F fl LK2 M2 model2 G).
Local Abbreviation mk_Z11 := (PMBBA2.mk_Z11 L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE CMI SMI CMS SMS CMSU SMSU F fl LK2 M2 model2 G).
Local Abbreviation mk_Zc := (PMBBA2.mk_Zc L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE CMI SMI CMS SMS CMSU SMSU F fl LK2 M2 model2 G).
Local Abbreviation mk_Zt := (PMBBA2.mk_Zt L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE CMI SMI CMS SMS CMSU SMSU F fl LK2 M2 model2 G).
Local Abbreviation mk_Zt13 := (PMBBA2.mk_Zt13 L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE CMI SMI CMS SMS CMSU SMSU F fl LK2 M2 model2 G).
Local Abbreviation gl_err_C := (PMBBA2.gl_err_C L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE CMI SMI CMS SMS CMSU SMSU F fl LK2 M2 model2 G).
Local Abbreviation gl_err_T := (PMBBA2.gl_err_T L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE CMI SMI CMS SMS CMSU SMSU F fl LK2 M2 model2 G).
Local Abbreviation vec_end := (PMBBA3.vec_end L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE CMI SMI CMS SMS CMSU SMSU F fl LK2 M2 model2 G).
Local Abbreviation tail_Is := (PMBBA3.tail_Is L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE CMI SMI CMS SMS CMSU SMSU F fl LK2 M2 model2 G).
Local Abbreviation tail_Ic := (PMBBA3.tail_Ic L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE CMI SMI CMS SMS CMSU SMSU F fl LK2 M2 model2 G).
Local Abbreviation tail_Cs := (PMBBA3.tail_Cs L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE CMI SMI CMS SMS CMSU SMSU F fl LK2 M2 model2 G).
Local Abbreviation tail_Cc := (PMBBA3.tail_Cc L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE CMI SMI CMS SMS CMSU SMSU F fl LK2 M2 model2 G).
Local Abbreviation tail_Ts := (PMBBA3.tail_Ts L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE CMI SMI CMS SMS CMSU SMSU F fl LK2 M2 model2 G).
Local Abbreviation tail_Tc := (PMBBA3.tail_Tc L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE CMI SMI CMS SMS CMSU SMSU F fl LK2 M2 model2 G).
Local Abbreviation mregs0_keep := (PMBBA2.mregs0_keep R0 S fb F).
Local Abbreviation mregs_keep := (PMBBA2.mregs_keep R0 S fb F).
Local Abbreviation pregsT_keep := (PMBBA3.pregsT_keep R0 S fb F).
Local Abbreviation pregsI_keep := (PMBBA3.pregsI_keep R0 S fb F).
Local Abbreviation tregs_keep := (PMBBA2.tregs_keep R0 S fb F).
Local Abbreviation vf_rng := (PMBBA2.vf_rng R0 S fb F fl).
Local Abbreviation op8_apart := (PMBBA2.op8_apart R0 S fb F fl).
Local Abbreviation VT := (PMBBA3.VT R0 S fb F fl).
Ltac vopen VF := unfold PMBBK.vfacts, PMBBK.hdr, PMBBK.own, PMBBK.fsh in VF; cbn iota in VF; decompose [and] VF; clear VF.
Ltac hx := match goal with |- ?G => match goal with H : G |- _ => exact H end end.
Ltac vfeed := first [ hx | (split; hx) | apply UB | (unfold PMBBAP1.aligned; hx) | (unfold PMBBAP2.aligned; hx) | (unfold PMBBAP3.aligned; hx) ].
Ltac vfeedV VF := first [ assumption | apply UB | unfold PMBBAP1.aligned; assumption | unfold PMBBAP2.aligned; assumption | unfold PMBBAP3.aligned; assumption
| let W := fresh "W" in pose proof VF as W; vopen W; vfeed ].
Ltac feedV P VF :=
let T := type of P in
let C := L5SAR.feed_concl T in
let Q := fresh "SC" in
assert (Q : C) by (let W := fresh "W" in pose proof VF as W; vopen W; apply P; clear P;
first [ vfeed | lazymatch goal with |- ?A => fail 1 "feedV: cannot prove premise" A end ]);
move Q after P; clear P; rename Q into P.
Lemma vf_fsh : ltac2:(TCodec.tc2 tcn__PmBBa4 "K'3'<'RMyR0%211'7y8%511%311p051&Q:vKvQJvR@v=vRAr3r2r1%9887654321&Q8r4%23815p041pQB?1pV2H1pV0J1").
Proof. intros typed v MV. intros VF. unfold PMBBK.vfacts in VF. destruct VF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _ & _ & _ & _ & _). exact X. Qed.
Lemma vf_fb : ltac2:(TCodec.tc2 tcn__PmBBa4 "Q8'3'<'RMyR0%211'7y8%511%311p051&Q:vKvQJvR@v=vRAr3r2r1%9887654321'9&QOz&QM+8%22;1%5241&QL+QoooPP8%2241&R4+2+R0%3221%=251%?291p0A1pQBL1pV2Q51pV0Q71").
Proof. intros typed v MV.
intros VF. unfold PMBBK.vfacts in VF. destruct VF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
split; [apply Z.div_pos; lia|]. assert (F / 8 <= 17592186044408) by (apply Z.div_le_upper_bound; lia). lia.
Qed.
Lemma mi_vis : ltac2:(TCodec.tc2 tcn__PmBBa4 "R9'6'8'<%2211%411'QA'QC'3'RMyR0%211'7y8%511%311p051'E&Q1%B11&M&Q6vAvR7v?vKvGvRDvBv>vCv1vQJvR@v=r9r5r4r3r2r1%DCCBA@?>=<;:987654321&QE&QI&Q<&Q;r6vRNr8r7%897654A?321&Q3&L&O%12@8%3216&QL&Q9%11I+Z8%4221+`PPP0%;4C721p0=1p0G1p2QL1pTJQ>1pQ:Q@1pU<QC1pQDQE1pTNQN1pUFR01pUBR21p6R41").
Proof using All. intros BX s sm e Mc modelc LKc crc Ac.
intros BI RUN. pose proof BI as (HHc & _). pose proof RUN as (PA & _).
pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & P328 & _).
pose proof (PMBPAR.op_vis L ar C HI LY HIok _ FF' LKc crc Ac Mc modelc fb _ s HHc (PMBUAR.frame_okA_push FF fb F 0 (S - 160 + 32) FOK) PA)
as ((O1 & _) & _ & _ & _ & _ & _ & OAV & _ & _).
apply (proj2 (L5A.u64_at_vis (ahid Ac modelc) Mc (op + 328) 16777216 (OAV (op + 328) 8 ltac:(unfold PMBBK.op; lia) ltac:(unfold PMBBK.op; lia)) ltac:(unfold PMBBK.op; lia) ltac:(unfold PMBBK.op; lia))).
exact P328.
Qed.
Lemma stk_bz : ltac2:(TCodec.tc2 tcn__PmBBa4 "QN'6'8'<%2211%411'RMyR0%211'7y8%511%311p051'E&Q1%?11&M&Q6vAvR7v?vKvGvRDvBv>vCv1vQJvR@v=r6r5r4r3r2r1%DCCBA@?>=<;:987654321'9&QO&R5+jP0%22>1%4217&R0%129A%8231&Q0r8&N%11?z%53421p071pU@QD1p0B1p2QD1pTJQ91pQ:Q;1pU<Q>1pQDQ@1p6QI1").
Proof using All. intros BX Mc modelc LKc crc Ac.
intros BI p Hp. pose proof BI as (HHc & AMc & MRTc & IAc & ILKc & ASTKc & EKc & _).
pose proof ENT as (_ & _ & _ & _ & _ & ASTK0 & STKSH0). change (PMSPA.pm_scr 7) with 26624 in *. change (26624 / 8) with 3328 in STKSH0.
pose proof ASTK0 as (A16 & SLO & SHI & SPT & SDEF & SUP).
assert (M8a : (S - 26624) mod 8 = 0) by (apply PMKB.mod16_8'; replace (S - 26624) with (S + (-1664) * 16) by lia; rewrite Z_mod_plus_full; exact A16).
pose proof (PMBBK.wappR L ar C HI HIok M0 model0 LBX FF LK0 Aw0 cr0 fb s0 HH0 FOK) as WAPP.
pose proof (PMKB.stksh_keepA L ar LBX FF S 26624 WR M0 Mc EKc WAPP (S - 26624) 3328 ltac:(lia) ltac:(lia) ltac:(lia) M8a ltac:(lia) STKSH0) as SZ.
assert (E : HeapIfaceA.S p = HeapIfaceA.S (S - 26624) + (p / 8 - (S - 26624) / 8)) by (unfold HeapIfaceA.S; lia).
rewrite E. apply SZ.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). clear - Hp M8a. lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma stk_cell BX Mc modelc LKc crc Ac p n : binv' BX Mc modelc LKc crc Ac -> S - 160 <= p -> p + n <= S - 104 -> 0 < n ->
PMSPA.accA Mc p n /\ byte_at Mc (HeapIfaceA.S p) 0 /\ PMSAX.arg_ok ar FF' (S - 160) (op + 360) p n
/\ (forall v, L5.u32_at RSEGS (mrestrict (ahid Ac modelc) Mc) p v -> n = 4 -> L5.u32_at RSEGS Mc p v)
/\ (forall v, L5.u64_at RSEGS (mrestrict (ahid Ac modelc) Mc) p v -> n = 8 -> L5.u64_at RSEGS Mc p v).
Proof using All.
intros BI H1 H2 Hn. pose proof G as G'. destruct G' as [Hk SPTg SLOg SHIg SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
unfold SCR in *.
pose proof (PMBUK.vis_facts L ar C HI LYa HIok M0 model0 LBX FF LK0 Aw0 S SCR (S - 160) (S - 104) S ocell own F fl 0 LK2 M2 model2 cr0 (PM.parser_own s0) G WR _ Mc modelc LKc crc Ac BI)
as (_ & _ & _ & (_ & _ & _ & SV8 & _)).
pose proof BI as (HHc & _ & _ & _ & _ & ASTKc & _).
pose proof FOK as ((rs & Hfb) & Fal).
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHc) as (WB & WF & FSAPP & FSCEIL & _).
destruct (WF _ (or_intror Hfb)) as (Ff1 & Ff2 & _). cbn [ff_addr ff_class fst snd] in Ff1, Ff2. change (ff_bytes 4) with 1024 in Ff2.
unfold app_mem, FS_BYTES in FSAPP, FSCEIL, Ff1, Ff2.
split.
{ intros a Ha. left. apply (stk_bz BX Mc modelc LKc crc Ac BI). lia. }
split; [apply (stk_bz BX Mc modelc LKc crc Ac BI); lia|].
split.
{ unfold PMSAX.arg_ok. split; [right; split; [lia|]|].
- pose proof ASTKc as (_ & _ & SHI' & _). lia.
- right. unfold PMBBK.op. pose proof (PMBBK.frame_geo fb) as (Eop & _). lia. }
split.
{ intros v X En. subst n. apply (proj1 (L5A.u32_at_vis _ Mc p v (L5A.avis_sub _ (S - 160) (S - (S - 160)) p 4 SV8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact X. }
{ intros v X En. subst n. apply (proj1 (L5A.u64_at_vis _ Mc p v (L5A.avis_sub _ (S - 160) (S - (S - 160)) p 8 SV8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact X. }
Qed.
Ltac bst_of BI RUN EC HD FSH STEP E0 SD CRL CRK VSL :=
split; [exact BI|]; split; [exact RUN|]; split; [exact EC|]; split; [exact HD|]; split; [exact FSH|]; split; [exact STEP|]; split; [exact E0|];
split; [exact SD|]; split; [exact CRL| split; [exact CRK| exact VSL]].
Lemma modsub : ltac2:(TCodec.tc2 tcn__PmBBa4 "J'<&R0zr1%3221':&R1r4r2%3221%53:18r3%6251%83=1;&R5r6r5%3221%<21;%>3C1Ap071p0;1p0B1pU>G1pTBH1pT>I1").
Proof. intros a b n. intros Hn Ha Hb. apply Z.mod_divide in Ha; [|lia]. apply Z.mod_divide in Hb; [|lia]. apply Z.mod_divide; [lia|]. apply Z.divide_sub_r; assumption. Qed.
Lemma mod32_d : ltac2:(TCodec.tc2 tcn__PmBBa4 "F'<&QNr1+Q0%3221&R0zr2%3221':&R1r4%2219%43=17r5%5214%73@1:p041p0:1p0?1pTLD1pV4E1").
Proof. intros x d. intros Hd Hp H. apply Z.mod_divide in H; [|lia]. apply Z.mod_divide; [lia|]. eapply Z.divide_trans; eassumption. Qed.
Lemma sp_mod : ltac2:(TCodec.tc2 tcn__PmBBa4 "J'<&QNr1+Q0%3221&R0zr2%3221':&R1r4r3%3221%53>18&R5vQJr5%3221%9218%;3D1>p071p0>1p0C1pTLH1pU8I1").
Proof using SP32. intros k d. intros Hd Hp Hk. apply modsub; [exact Hp| exact (mod32_d S d Hd Hp SP32)| exact Hk]. Qed.
Ltac mregs_ks KS := unfold PMBBA2.tregs, PMBBA2.mregs, PMBBA2.mregs0; repeat split; (rewrite (KS _) by inl; hx).
Lemma pow_bnd_ra : ltac2:(TCodec.tc2 tcn__PmBBa4 "H'<'9&QOzr1%3221&R0&R4+2+Q?%3221%5271%;271':&R1r2%2218%43A1>&Q2r3%211p041p0:1pV4G1").
Proof. intros x. intros H1 H2. split; assumption. Qed.
Lemma vec_pre_facts : ltac2:(TCodec.tc2 tcn__PmBBa4 "SA'3'QA'QC'RMyR0%211'7y8%511%311p051'E'6&Q1%211&M'8'<%2211%711&Q7vAvR7v?vKvGvRDvBv>vCv1vR;vQJvR@vR:vRIvRNvRKvR?v=r9r8r7r6r5r4r3r2r1%MLLKJIHGFEDCBA@?>=<;:987654321'9&Q3&QI&L&O%128;%321=&QL&Q9%11J+[@%4221&Q=%11G&R2+Q0&R3&5'QB&Q@%11N%4231%611%9281%A2;1%H4GC>1+[H%D2B1&R4+2&Q?%11Q9%4231%C2B1%K2E1%Q24Q1M81&QO+TP0%221I+Q?%<2;1%5271z%721<+;%92>1%Q>231%;2I?%Q@221%QA281%QB2<1%QC2@1%QD2K1p0QF1p2RE1pTJRJ1pQ:RL1pU<S01pQDS21pTNS=1pUFS<1pUBS>1pV0S@1").
Proof using All. intros typed s sm e Mc modelc LKc crc Ac.
intros BS. unfold PMBBK.op. pose proof BS as (BI & RUN & EC & HD & FSH & STEP & E0' & SD & CRL & CRK & VSL).
pose proof BI as BI'. destruct BI' as (HHc & AMc & MRTc & IAc & ILKc & ASTKc & EKc & DKc & OWNc & SHDc).
pose proof RUN as (PA & IA & VIS & VREF & BASE & ERR & TBOK).
pose proof FOK as ((rs & Hfb) & Fal).
assert (FOK' : PMSPA.frame_okA FF' fb) by (split; [exists rs; right; exact Hfb| exact Fal]).
pose proof (PMBPAR.op_vis L ar C HI LY HIok _ FF' LKc crc Ac Mc modelc fb _ s HHc FOK' PA) as ((O1 & O8 & ONSH) & Zop & Z32 & Z20 & OWR & OCE & OAV & AOP & _).
pose proof PA as (_ & PDEF & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & VEC & _).
pose proof VEC as (V0 & V8 & V16 & Hk' & Hlen & Hal & DB & CB & AN & EL).
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHc) as (WB & _).
assert (Iv : In (PM.p_b s, 32 * 2 ^ PM.p_k s) (PM.parser_own s ++ LBX)) by (apply in_or_app; left; right; left; reflexivity).
destruct (WB _ Iv) as ((Bb4 & _ & _ & _ & _ & _) & _). cbn [fst snd] in Bb4.
pose proof (PMBSK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HHc _ Iv) as (Bq1 & Bq2). cbn [fst snd] in Bq1, Bq2.
replace (PMSPA.o_p AD fb + 360 + 8) with (PMSPA.o_p AD fb + 368) in V8 by lia.
replace (PMSPA.o_p AD fb + 360 + 16) with (PMSPA.o_p AD fb + 376) in V16 by lia.
split; [apply (proj2 (L5A.u64_at_vis _ Mc (PMSPA.o_p AD fb + 368) _ (OAV (PMSPA.o_p AD fb + 368) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact V8|].
split; [apply (proj2 (L5A.u64_at_vis _ Mc (PMSPA.o_p AD fb + 376) _ (OAV (PMSPA.o_p AD fb + 376) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact V16|].
split; [lia|]. split; [lia|]. split; [lia| exact Hlen].
Qed.
Definition VTv (x50 x53 x54 : Z) (j : nat) : Z := match j with 53%nat => x53 | 54%nat => x54 | _ => PMBBA3.VT R0 S fb F fl 0 x50 j end.
Definition VKv (x39 x53 x54 : Z) (j : nat) : Z := match j with 39%nat => x39 | 53%nat => x53 | 54%nat => x54 | _ => PMBBA3.VT R0 S fb F fl 0 0 j end.
Ltac pregs_ks KS := unfold PMBBA3.pregsI, PMBBA3.pregsT, PMBBA3.pregs; repeat split; first [ hx | (rewrite (KS _) by inl; hx) ].
Lemma c_stage : ltac2:(TCodec.tc2 tcn__PmBBa4 "RF'QA'QC'3'QF&Fy5'RMyR0%211%5241'7y8%611%311p061'E'6&Q1%211&M'8'<%2211%711&QO&Q>vRI%211+oO%5221&Q7vAvR7v?vKvGvRDvBv>vCv1vR;vQJvR@vR:vRNvRKvR?v=(4r;r:r9r6r5r4r3r2%LLKJIHGFEDCBA@?>Q0=<;:987654321&Q5r8%25KCB=1'QH&QI&Q4vQK%211&QD+fXgLr7%367CB2:1v@%:49621p0<1p0@1p0Q>1p2QE1pTJQJ1pQ:QL1pU<R01pQDR21pQFR81pU6R?1pTNRA1pUFRC1pUBRE1").
Proof using All. intros s sm e fx R Mc modelc LKc crc Ac.
intros DEP BS MR. pose proof MR as ((X2 & X8 & X9 & X18 & X19 & X20 & X21 & X25 & X26 & X27 & X3 & X4) & X23).
pose proof BS as (BI & RUN & EC & HD & FSH & STEP & E0 & SD & CRL & CRK & VSL). pose proof (S_of_binv _ _ _ _ _ _ BI) as SRB.
pose proof (vpack false _ s sm e 0 cat Mc modelc LKc crc Ac BI RUN EC HD FSH) as VF.
set (MV := mrestrict (ahid Ac modelc) Mc) in *.
pose proof (PMBBAP3.abaC1_conc fx R MV (VT 0 0)) as P. unfold PMBBA3.VT in P. cbn beta iota in P. feedV P VF.
destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & PR). decompose [and] PR. clear PR.
pose proof (vf_fb false 0 MV VF) as (DF1 & DF2).
apply (step_piece false s sm e 0 cat fx fx1 R 0xb22fc R1 0xb160c M1v Mc modelc LKc crc Ac (fun _ => False) BI RUN EC HD MS1 MG1).
{ intros a Ha _. apply FRZ1. exact Ha. }
{ intros a []. }
{ apply (fsh_agree false MV M1v); [intros a Ha; apply FRZ1; lia| exact DF1| exact DF2| exact (vf_fsh false 0 MV VF)]. }
intros M1 model1 BI1 RUN1 EC1 HD1 FSH1 VIS1 HID1 FR1.
assert (VSL1 : L5.u64_at RSEGS M1 (S - 136) ov) by (apply (L5C.u64_at_agree RSEGS Mc M1); [intros i Hi; apply FR1; [lia| intros X; exact X]| lia| lia| exact VSL]).
assert (BS1 : bst false s sm e M1 model1 LKc crc Ac) by (bst_of BI1 RUN1 EC1 HD1 FSH1 STEP E0 SD CRL CRK VSL1).
assert (MR1 : mregs R1) by mregs_ks KS1.
assert (A1 : getr R1 (reg 1) = Z_to_bv 64 0xb2308) by hx.
assert (A10 : getr R1 (reg 10) = Z_to_bv 64 op) by hx.
assert (A11 : getr R1 (reg 11) = Z_to_bv 64 oec) by hx.
pose proof MR1 as ((Y2 & Y8 & Y9 & Y18 & Y19 & Y20 & Y21 & Y25 & Y26 & Y27 & Y3 & Y4) & Y23).
apply (call_gl false s sm e fx1 R1 M1 model1 LKc crc Ac 0xb2308 BS1 A1 ltac:(apply pow_bnd_ra; [lia| reflexivity]) Y2 Y3 Y4 A10 A11).
intros fx2 R2 M2' model2' LK2' Aw2 s2 sm2 e2 cr2 RP2 OUT2.
pose proof (mregs_keep R1 R2 MR1 RP2) as MR2.
destruct OUT2 as [(BS2 & UN2 & (len & Hlen & A10'))|BE2].
2: { exact (gl_err_C s2 sm2 fx2 R2 M2' model2' LK2' cr2 Aw2 BE2 MR2). }
pose proof BS2 as (BI2 & RUN2 & EC2 & HD2 & FSH2 & STEP2 & E02 & SD2 & CRL2 & CRK2 & VSL2). pose proof (S_of_binv _ _ _ _ _ _ BI2) as SRB2.
pose proof (vpack false _ s2 sm2 e2 0 cat M2' model2' LK2' cr2 Aw2 BI2 RUN2 EC2 HD2 FSH2) as VF2.
pose proof (mi_vis _ s2 sm2 e2 M2' model2' LK2' cr2 Aw2 BI2 RUN2) as MI2.
set (MV2 := mrestrict (ahid Aw2 model2') M2') in *.
pose proof MR2 as ((Z2 & Z8 & Z9 & Z18 & Z19 & Z20 & Z21 & Z25 & Z26 & Z27 & Z3 & Z4) & Z23).
pose proof (vf_fb false 0 MV2 VF2) as (DF1b & DF2b). pose proof (vf_rng false 0 MV2 VF2) as (Rop & RS & RF & Rfl).
destruct (Z_le_gt_dec len 16777216) as [Le|Gt].
-
assert (HL2 : 0 <= len <= 16777216) by lia.
destruct (vec_pre_facts false s2 sm2 e2 M2' model2' LK2' cr2 Aw2 BS2) as (VE & VC & Vb & Vbc & Vk & Vn).
change (mrestrict (ahid Aw2 model2') M2') with MV2 in VE, VC.
set (nn := Z.of_nat (length (PM.p_stk s2))) in *. pose proof (PM.pow2_pos (PM.p_k s2) (proj1 Vk)) as P2.
assert (R53 : 0 <= PM.p_b s2 + 32 * nn <= 140737488355328) by lia. assert (B53 : 0 <= PM.p_b s2 + 32 * nn < 2 ^ 64) by lia.
assert (R54 : 0 <= PM.p_b s2 + 32 * 2 ^ PM.p_k s2 <= 140737488355328) by lia. assert (B54 : 0 <= PM.p_b s2 + 32 * 2 ^ PM.p_k s2 < 2 ^ 64) by lia.
pose proof (PMBBAP3.abaCf_conc fx2 R2 MV2 (VTv len (PM.p_b s2 + 32 * nn) (PM.p_b s2 + 32 * 2 ^ PM.p_k s2))) as P. unfold VTv, PMBBA3.VT in P. cbn beta iota in P. feedV P VF2.
destruct P as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & PR).
assert (STEP3 : forall pc3, msteps RSEGS (L5A.st fx2 R2 0xb2308 MV2) (L5A.st fx3 R3 pc3 M3v) ->
(forall M3 model3, bst false s2 sm2 e2 M3 model3 LK2' cr2 Aw2 -> mrestrict (ahid Aw2 model2') M3 = M3v -> ahid Aw2 model3 = ahid Aw2 model2' ->
srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx3 R3 pc3 M3 model3) K) ->
srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx2 R2 0xb2308 M2' model2') K).
{ intros pc3 MS3 NX.
apply (step_piece false s2 sm2 e2 0 cat fx2 fx3 R2 0xb2308 R3 pc3 M3v M2' model2' LK2' cr2 Aw2 (fun a => S - 116 <= a < S - 104) BI2 RUN2 EC2 HD2 MS3 MG3).
{ intros a Ha N. apply FRZ3; [exact Ha| intros X; apply N; lia]. }
{ intros a X. left. lia. }
{ apply (fsh_agree false MV2 M3v); [intros a Ha; apply FRZ3; [lia| intros X; unfold SB in *; lia]| exact DF1b| exact DF2b| exact (vf_fsh false 0 MV2 VF2)]. }
intros M3 model3 BI3 RUN3 EC3 HD3 FSH3 VIS3 HID3 FR3.
assert (VSL3 : L5.u64_at RSEGS M3 (S - 136) ov) by (apply (L5C.u64_at_agree RSEGS M2' M3); [intros i Hi; apply FR3; [lia| intros X; lia]| lia| lia| exact VSL2]).
apply (NX M3 model3); [bst_of BI3 RUN3 EC3 HD3 FSH3 STEP2 E02 SD2 CRL2 CRK2 VSL3| exact VIS3| exact HID3]. }
pose proof SD2 as (_ & _ & SDp & SDs). pose proof INV as (_ & _ & IDP & _).
pose proof STEP2 as (_ & _ & _ & _ & UN02).
destruct PR as [(MS3 & KS3 & PR)|(MS3 & KS3 & PR)]; decompose [and] PR; clear PR.
+
apply (STEP3 0xb39e4 MS3). intros M3 model3 BS3 VIS3 HID3.
destruct (stk_cell _ M3 model3 LK2' cr2 Aw2 (S - 116) 4 (proj1 BS3) ltac:(lia) ltac:(lia) ltac:(lia)) as (AC1 & BZ1 & AO1 & U1 & _).
destruct (stk_cell _ M3 model3 LK2' cr2 Aw2 (S - 112) 8 (proj1 BS3) ltac:(lia) ltac:(lia) ltac:(lia)) as (AC2 & BZ2 & AO2 & _ & U2).
rewrite HID3, VIS3 in U1, U2.
assert (C116 : L5.u32_at RSEGS M3 (S - 116) 2) by (apply U1; [hx| reflexivity]).
assert (C112 : L5.u64_at RSEGS M3 (S - 112) len) by (apply U2; [hx| reflexivity]).
assert (PR3 : pregsI R3) by pregs_ks KS3.
assert (B1 : getr R3 (reg 1) = Z_to_bv 64 0xb24c8) by hx.
assert (B10 : getr R3 (reg 10) = Z_to_bv 64 (op + 360)) by hx.
assert (B11 : getr R3 (reg 11) = Z_to_bv 64 (S - 116)) by hx.
assert (B12 : getr R3 (reg 12) = Z_to_bv 64 (S - 112)) by hx.
assert (B21 : getr R3 (reg 21) = Z_to_bv 64 (PM.p_b s2 + 32 * nn)) by hx.
pose proof PR3 as ((W2 & W8 & W9 & W18 & W19 & W20 & W25 & W26 & W27 & W3 & W4) & W22 & W23).
pose proof CMS as CMS'. unfold PMBX.cone_ms_spec in CMS'.
apply (call_push 0xb39e4 PMBPQ.Qcone PMBPQ.A0none (PMSAX.cells_ms RSEGS ar) (PMBPQ.cone_pushq RSEGS AD L ar HI 0xb39e4 _ CMS') false s2 sm2 e2 fx3 R3 M3 model3 LK2' cr2 Aw2 0xb24c8 (PM.PS 2 len 0 0) BS3 B1
ltac:(apply pow_bnd_ra; [lia| reflexivity]) W2 W3 W4 B10).
* unfold PMSAX.cells_ms. exists (S - 116), (S - 112), 2, len.
split; [rewrite L5SAR.r11; exact B11|]. split; [rewrite L5K.rl12; exact B12|].
split; [apply sp_mod; [exists 8; reflexivity| lia| reflexivity]|]. split; [apply sp_mod; [exists 4; reflexivity| lia| reflexivity]|].
split; [exact AC1|]. split; [exact AC2|]. split; [exact AO1|]. split; [exact AO2|]. split; [exact BZ1|]. split; [exact BZ2|].
split; [exact C116|]. split; [exact C112|]. split; [lia|]. split; [lia| reflexivity].
* split; [reflexivity| lia].
* unfold PM.pstate_ok. cbn [PM.ps_type PM.ps_mode PM.ps_len PM.ps_idx]. split; [lia|]. left. split; [unfold PM.mode_counted; left; reflexivity|]. unfold PM.MAX_ITEMS. lia.
* reflexivity.
* unfold PM.mode_bottom. cbn [PM.ps_mode]. lia.
* intros _. pose proof STEP as (_ & _ & _ & _ & UN0). lia.
* unfold PM.MAX_DEPTH. lia.
* intros fx4 R4 M4 model4 LK4 Aw4 s4 cr4 RP4 A04 STK4 PO4 BSP4 SRC4 KPR4.
assert (Eb4 : PM.p_b s4 = PM.p_b s2).
{ destruct PO4 as [(_ & _ & _ & Eb & _ & _)|([Eo|Eo] & _ & _)]; [exact Eb| discriminate Eo| lia]. }
apply (tail_Cc s4 sm2 e2 fx4 R4 M4 model4 LK4 cr4 Aw4 len BSP4 (pregsI_keep R3 R4 PR3 RP4)); [| exact HL2|].
-- rewrite (L5SAR.cs_of_preserved R3 R4 21 RP4) by inl. rewrite B21, Eb4, STK4, length_app. cbn [length]. f_equal. unfold nn. lia.
-- apply (L5C.u64_at_agree RSEGS M3 M4); [intros i Hi; apply KPR4; lia| lia| lia| exact C112].
+
apply (STEP3 0xb3b60 MS3). intros M3 model3 BS3 VIS3 HID3.
destruct (stk_cell _ M3 model3 LK2' cr2 Aw2 (S - 116) 4 (proj1 BS3) ltac:(lia) ltac:(lia) ltac:(lia)) as (AC1 & BZ1 & AO1 & U1 & _).
destruct (stk_cell _ M3 model3 LK2' cr2 Aw2 (S - 112) 8 (proj1 BS3) ltac:(lia) ltac:(lia) ltac:(lia)) as (AC2 & BZ2 & AO2 & _ & U2).
rewrite HID3, VIS3 in U1, U2.
assert (C116 : L5.u32_at RSEGS M3 (S - 116) 2) by (apply U1; [hx| reflexivity]).
assert (C112 : L5.u64_at RSEGS M3 (S - 112) len) by (apply U2; [hx| reflexivity]).
assert (PR3 : pregsI R3) by pregs_ks KS3.
assert (B1 : getr R3 (reg 1) = Z_to_bv 64 0xb251c) by hx.
assert (B10 : getr R3 (reg 10) = Z_to_bv 64 (op + 360)) by hx.
assert (B11 : getr R3 (reg 11) = Z_to_bv 64 (S - 116)) by hx.
assert (B12 : getr R3 (reg 12) = Z_to_bv 64 (S - 112)) by hx.
pose proof PR3 as ((W2 & W8 & W9 & W18 & W19 & W20 & W25 & W26 & W27 & W3 & W4) & W22 & W23).
pose proof SMS as SMS'. unfold PMBX.slow_ms_spec in SMS'. cbn [paa_esp_ms PMB.AAD AADDR_B] in SMS'.
apply (call_push 0xb3b60 PMBPQ.Qslow PMBPQ.A0end (PMSAX.cells_ms RSEGS ar) (PMBPQ.slow_pushq RSEGS AD L ar HI 0xb3b60 _ SMS') false s2 sm2 e2 fx3 R3 M3 model3 LK2' cr2 Aw2 0xb251c (PM.PS 2 len 0 0) BS3 B1
ltac:(apply pow_bnd_ra; [lia| reflexivity]) W2 W3 W4 B10).
* unfold PMSAX.cells_ms. exists (S - 116), (S - 112), 2, len.
split; [rewrite L5SAR.r11; exact B11|]. split; [rewrite L5K.rl12; exact B12|].
split; [apply sp_mod; [exists 8; reflexivity| lia| reflexivity]|]. split; [apply sp_mod; [exists 4; reflexivity| lia| reflexivity]|].
split; [exact AC1|]. split; [exact AC2|]. split; [exact AO1|]. split; [exact AO2|]. split; [exact BZ1|]. split; [exact BZ2|].
split; [exact C116|]. split; [exact C112|]. split; [lia|]. split; [lia| reflexivity].
* right. unfold nn in *. lia.
* unfold PM.pstate_ok. cbn [PM.ps_type PM.ps_mode PM.ps_len PM.ps_idx]. split; [lia|]. left. split; [unfold PM.mode_counted; left; reflexivity|]. unfold PM.MAX_ITEMS. lia.
* reflexivity.
* unfold PM.mode_bottom. cbn [PM.ps_mode]. lia.
* intros _. pose proof STEP as (_ & _ & _ & _ & UN0). lia.
* unfold PM.MAX_DEPTH. lia.
* intros fx4 R4 M4 model4 LK4 Aw4 s4 cr4 RP4 A04 STK4 PO4 BSP4 SRC4 KPR4.
apply (tail_Cs s4 sm2 e2 fx4 R4 M4 model4 LK4 cr4 Aw4 len BSP4 (pregsI_keep R3 R4 PR3 RP4)); [| exact HL2|].
-- unfold PMBPQ.A0end in A04. rewrite L5K.rl10 in A04. exact A04.
-- apply (L5C.u64_at_agree RSEGS M3 M4); [intros i Hi; apply KPR4; lia| lia| lia| exact C112].
-
assert (HL2 : 16777217 <= len <= 18446744073709551615) by lia.
pose proof (PMBBAP3.abaCx_conc fx2 R2 MV2 (VT 0 len)) as P. unfold PMBBA3.VT in P. cbn beta iota in P. feedV P VF2.
destruct P as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & PR). decompose [and] PR. clear PR.
apply (step_piece false s2 sm2 e2 0 cat fx2 fx3 R2 0xb2308 R3 0xafa18 M3v M2' model2' LK2' cr2 Aw2 (fun a => S - 112 <= a < S - 104) BI2 RUN2 EC2 HD2 MS3 MG3).
{ intros a Ha N. apply FRZ3; [exact Ha| intros X; apply N; lia]. }
{ intros a X. left. lia. }
{ apply (fsh_agree false MV2 M3v); [intros a Ha; apply FRZ3; [lia| intros X; unfold SB in *; lia]| exact DF1b| exact DF2b| exact (vf_fsh false 0 MV2 VF2)]. }
intros M3 model3 BI3 RUN3 EC3 HD3 FSH3 VIS3 HID3 FR3.
assert (VSL3 : L5.u64_at RSEGS M3 (S - 136) ov) by (apply (L5C.u64_at_agree RSEGS M2' M3); [intros i Hi; apply FR3; [lia| intros X; lia]| lia| lia| exact VSL2]).
assert (BS3 : bst false s2 sm2 e2 M3 model3 LK2' cr2 Aw2) by (bst_of BI3 RUN3 EC3 HD3 FSH3 STEP2 E02 SD2 CRL2 CRK2 VSL3).
assert (MR3 : mregs R3) by mregs_ks KS3.
assert (B1 : getr R3 (reg 1) = Z_to_bv 64 0xb234c) by hx.
assert (B10 : getr R3 (reg 10) = Z_to_bv 64 oec) by hx.
assert (B11 : getr R3 (reg 11) = Z_to_bv 64 13) by hx.
exact (mk_Zc s2 sm2 e2 fx3 R3 M3 model3 LK2' cr2 Aw2 13 BS3 MR3 B1 B10 B11 ltac:(lia)).
Qed.
Definition VK (x39 : Z) (j : nat) : Z := match j with 39%nat => x39 | _ => PMBBA3.VT R0 S fb F fl 0 0 j end.
Lemma i_stage : ltac2:(TCodec.tc2 tcn__PmBBa4 "S@'QA'QC'3'QF&Fy5'RMyR0%211%5241'7y8%611%311p061'E'6&Q1%211&M'8'<%2211%711&QO&Q>vRI%211+oO%5221&Q7vAvR7v?vKvGvRDvBv>vCv1vR;vQJvR@vR:vRNvRKvR?v=(4r<r;r:r7r6r5r4r3%LLKJIHGFEDCBA@?>Q0=<;:987654321&Q5r9%25KCB=1':&QG&RL&R3u:%211%42QO1%62A1%62QO>%93QO21';'9z%QC21D+Q2%QE2F1%5231+Q5%QH21I+WO%QJ2K1%:231%<261'QH&QI&Q4vQK%211&QDr=+fX`0%3672Q;1Q:Q9v@%:49621p0<1p0J1p0Q51p0Q91p0R71pTDR@1p2R?1pTJRD1pQ:RF1pU<RJ1pQDRL1pQFS21pU6S91pTNS;1pUFS=1pUBS?1").
Proof using All. intros s sm e fx R Mc modelc LKc crc Ac c.
intros DEP BS MR A10c Hc. pose proof MR as ((X2 & X8 & X9 & X18 & X19 & X20 & X21 & X25 & X26 & X27 & X3 & X4) & X23).
pose proof BS as (BI & RUN & EC & HD & FSH & STEP & E0 & SD & CRL & CRK & VSL).
pose proof (vpack false _ s sm e 0 cat Mc modelc LKc crc Ac BI RUN EC HD FSH) as VF.
destruct (vec_pre_facts false s sm e Mc modelc LKc crc Ac BS) as (VE & VC & Vb & Vbc & Vk & Vn).
set (MV := mrestrict (ahid Ac modelc) Mc) in *.
set (nn := Z.of_nat (length (PM.p_stk s))) in *. pose proof (PM.pow2_pos (PM.p_k s) (proj1 Vk)) as P2.
assert (R53 : 0 <= PM.p_b s + 32 * nn <= 140737488355328) by lia. assert (B53 : 0 <= PM.p_b s + 32 * nn < 2 ^ 64) by lia.
assert (R54 : 0 <= PM.p_b s + 32 * 2 ^ PM.p_k s <= 140737488355328) by lia. assert (B54 : 0 <= PM.p_b s + 32 * 2 ^ PM.p_k s < 2 ^ 64) by lia.
pose proof (vf_fb false 0 MV VF) as (DF1 & DF2). pose proof (vf_rng false 0 MV VF) as (Rop & RS & RF & Rfl).
assert (Hcb : 0 <= c < 2 ^ 64) by lia.
assert (PKL : exists (fx1 : FPState) R1 M1v, mem_grows MV M1v
/\ (forall i, 0 <= i < 2 ^ 64 -> ~ (S - 116 <= i < S - 108) -> M1v (Z_to_bv 64 i) = MV (Z_to_bv 64 i))
/\ (forall x, In x [2; 3; 4; 8; 9; 18; 19; 20; 24; 25; 26; 27]%nat -> getr R1 (reg x) = getr R (reg x))
/\ getr R1 (reg 10) = Z_to_bv 64 (op + 360) /\ getr R1 (reg 11) = Z_to_bv 64 (S - 112)
/\ getr R1 (reg 12) = Z_to_bv 64 (S - 116) /\ getr R1 (reg 21) = Z_to_bv 64 (PM.p_b s + 32 * nn)
/\ getr R1 (reg 22) = Z_to_bv 64 (op + 368) /\ getr R1 (reg 23) = Z_to_bv 64 ((op + 368) / 8 + 2147450880)
/\ L5.u32_at RSEGS M1v (S - 116) 0 /\ L5.u32_at RSEGS M1v (S - 112) 3
/\ ((msteps RSEGS (L5A.st fx R 0xb2200 MV) (L5A.st fx1 R1 0xac324 M1v) /\ getr R1 (reg 1) = Z_to_bv 64 0xb23b8 /\ nn < 2 ^ PM.p_k s)
\/ (msteps RSEGS (L5A.st fx R 0xb2200 MV) (L5A.st fx1 R1 0xac4ac M1v) /\ getr R1 (reg 1) = Z_to_bv 64 0xb23d8 /\ 2 ^ PM.p_k s <= nn))).
{ destruct Hc as [Hc|Hc].
- pose proof (PMBBAP1.abaKl_conc fx R MV (VKv c (PM.p_b s + 32 * nn) (PM.p_b s + 32 * 2 ^ PM.p_k s))) as P. unfold VKv, PMBBA3.VT in P. cbn beta iota in P. feedV P VF.
destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & [(MS1 & KS1 & PR)|(MS1 & KS1 & PR)]); decompose [and] PR; clear PR;
exists fx1, R1, M1v; (split; [exact MG1|]); (split; [intros i Hi N; apply FRZ1; [exact Hi| intros X; apply N; lia]|]);
(split; [intros x Hx; apply KS1; revert x Hx; apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 24; 25; 26; 27]%nat); vm_compute; reflexivity|]);
do 8 (split; [hx|]).
+ left. split; [exact MS1|]. split; [hx| lia].
+ right. split; [exact MS1|]. split; [hx| lia].
- pose proof (PMBBAP1.abaKu_conc fx R MV (VKv c (PM.p_b s + 32 * nn) (PM.p_b s + 32 * 2 ^ PM.p_k s))) as P. unfold VKv, PMBBA3.VT in P. cbn beta iota in P. feedV P VF.
destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & [(MS1 & KS1 & PR)|(MS1 & KS1 & PR)]); decompose [and] PR; clear PR;
exists fx1, R1, M1v; (split; [exact MG1|]); (split; [intros i Hi N; apply FRZ1; [exact Hi| intros X; apply N; lia]|]);
(split; [intros x Hx; apply KS1; revert x Hx; apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 24; 25; 26; 27]%nat); vm_compute; reflexivity|]);
do 8 (split; [hx|]).
+ left. split; [exact MS1|]. split; [hx| lia].
+ right. split; [exact MS1|]. split; [hx| lia]. }
destruct PKL as (fx1 & R1 & M1v & MG1 & FRZ1 & KS1 & B10 & B11 & B12 & B21 & B22 & B23 & C116v & C112v & EXK).
assert (PR1 : pregsI R1).
{ unfold PMBBA3.pregsI, PMBBA3.pregs. repeat split; first [ hx | (rewrite (KS1 _) by inl; hx) ]. }
pose proof PR1 as ((W2 & W8 & W9 & W18 & W19 & W20 & W25 & W26 & W27 & W3 & W4) & W22 & W23).
pose proof INV as (_ & _ & IDP & _).
assert (STEP1 : forall pc1, msteps RSEGS (L5A.st fx R 0xb2200 MV) (L5A.st fx1 R1 pc1 M1v) ->
(forall M1 model1, bst false s sm e M1 model1 LKc crc Ac -> L5.u32_at RSEGS M1 (S - 112) 3 -> L5.u32_at RSEGS M1 (S - 116) 0 ->
PMSAX.cells_mi RSEGS ar FF' (S - 160) (op + 360) M1 R1 (PM.PS 3 0 0 0) ->
srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx1 R1 pc1 M1 model1) K) ->
srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xb2200 Mc modelc) K).
{ intros pc1 MS1 NX.
apply (step_piece false s sm e 0 cat fx fx1 R 0xb2200 R1 pc1 M1v Mc modelc LKc crc Ac (fun a => S - 116 <= a < S - 108) BI RUN EC HD MS1 MG1).
{ intros a Ha N. apply FRZ1; [exact Ha| exact N]. }
{ intros a X. left. lia. }
{ apply (fsh_agree false MV M1v); [intros a Ha; apply FRZ1; [lia| intros X; unfold SB in *; lia]| exact DF1| exact DF2| exact (vf_fsh false 0 MV VF)]. }
intros M1 model1 BI1 RUN1 EC1 HD1 FSH1 VIS1 HID1 FR1.
assert (VSL1 : L5.u64_at RSEGS M1 (S - 136) ov) by (apply (L5C.u64_at_agree RSEGS Mc M1); [intros i Hi; apply FR1; [lia| intros X; lia]| lia| lia| exact VSL]).
assert (BS1 : bst false s sm e M1 model1 LKc crc Ac) by (bst_of BI1 RUN1 EC1 HD1 FSH1 STEP E0 SD CRL CRK VSL1).
destruct (stk_cell _ M1 model1 LKc crc Ac (S - 112) 4 BI1 ltac:(lia) ltac:(lia) ltac:(lia)) as (AC1 & BZ1 & AO1 & U1 & _).
destruct (stk_cell _ M1 model1 LKc crc Ac (S - 116) 4 BI1 ltac:(lia) ltac:(lia) ltac:(lia)) as (AC2 & BZ2 & AO2 & U2 & _).
rewrite HID1, VIS1 in U1, U2.
assert (C112 : L5.u32_at RSEGS M1 (S - 112) 3) by (apply U1; [exact C112v| reflexivity]).
assert (C116 : L5.u32_at RSEGS M1 (S - 116) 0) by (apply U2; [exact C116v| reflexivity]).
apply (NX M1 model1 BS1 C112 C116).
unfold PMSAX.cells_mi. exists (S - 112), (S - 116), 3, 0.
split; [rewrite L5SAR.r11; exact B11|]. split; [rewrite L5K.rl12; exact B12|].
split; [apply sp_mod; [exists 8; reflexivity| lia| reflexivity]|]. split; [apply sp_mod; [exists 8; reflexivity| lia| reflexivity]|].
split; [exact AC1|]. split; [exact AC2|]. split; [exact AO1|]. split; [exact AO2|]. split; [exact BZ1|]. split; [exact BZ2|].
split; [exact C112|]. split; [exact C116|]. split; [lia|]. split; [lia| reflexivity]. }
destruct EXK as [(MS1 & B1 & LT)|(MS1 & B1 & GE)].
-
apply (STEP1 0xac324 MS1). intros M1 model1 BS1 C112 C116 CELLS.
pose proof CMI as CMI'. unfold PMBX.cone_mi_spec in CMI'.
apply (call_push 0xac324 PMBPQ.Qcone PMBPQ.A0none (PMSAX.cells_mi RSEGS ar) (PMBPQ.cone_pushq RSEGS AD L ar HI 0xac324 _ CMI') false s sm e fx1 R1 M1 model1 LKc crc Ac 0xb23b8 (PM.PS 3 0 0 0) BS1 B1
ltac:(apply pow_bnd_ra; [lia| reflexivity]) W2 W3 W4 B10 CELLS).
+ split; [reflexivity| lia].
+ unfold PM.pstate_ok. cbn [PM.ps_type PM.ps_mode PM.ps_len PM.ps_idx]. split; [lia|]. right. left. split; [unfold PM.mode_indef; left; reflexivity|]. unfold PM.MAX_ITEMS. lia.
+ reflexivity.
+ unfold PM.mode_bottom. cbn [PM.ps_mode]. lia.
+ unfold PM.mode_counted. cbn [PM.ps_mode]. lia.
+ unfold PM.MAX_DEPTH. lia.
+ intros fx4 R4 M4 model4 LK4 Aw4 s4 cr4 RP4 A04 STK4 PO4 BSP4 SRC4 KPR4.
assert (Eb4 : PM.p_b s4 = PM.p_b s).
{ destruct PO4 as [(_ & _ & _ & Eb & _ & _)|([Eo|Eo] & _ & _)]; [exact Eb| discriminate Eo| lia]. }
apply (tail_Ic s4 sm e fx4 R4 M4 model4 LK4 cr4 Aw4 BSP4 (pregsI_keep R1 R4 PR1 RP4)).
rewrite (L5SAR.cs_of_preserved R1 R4 21 RP4) by inl. rewrite B21, Eb4, STK4, length_app. cbn [length]. f_equal. unfold nn. lia.
-
apply (STEP1 0xac4ac MS1). intros M1 model1 BS1 C112 C116 CELLS.
pose proof SMI as SMI'. unfold PMBX.slow_mi_spec in SMI'. cbn [paa_esp_mi PMB.AAD AADDR_B] in SMI'.
apply (call_push 0xac4ac PMBPQ.Qslow PMBPQ.A0end (PMSAX.cells_mi RSEGS ar) (PMBPQ.slow_pushq RSEGS AD L ar HI 0xac4ac _ SMI') false s sm e fx1 R1 M1 model1 LKc crc Ac 0xb23d8 (PM.PS 3 0 0 0) BS1 B1
ltac:(apply pow_bnd_ra; [lia| reflexivity]) W2 W3 W4 B10 CELLS).
+ right. unfold nn in *. lia.
+ unfold PM.pstate_ok. cbn [PM.ps_type PM.ps_mode PM.ps_len PM.ps_idx]. split; [lia|]. right. left. split; [unfold PM.mode_indef; left; reflexivity|]. unfold PM.MAX_ITEMS. lia.
+ reflexivity.
+ unfold PM.mode_bottom. cbn [PM.ps_mode]. lia.
+ unfold PM.mode_counted. cbn [PM.ps_mode]. lia.
+ unfold PM.MAX_DEPTH. lia.
+ intros fx4 R4 M4 model4 LK4 Aw4 s4 cr4 RP4 A04 STK4 PO4 BSP4 SRC4 KPR4.
apply (tail_Is s4 sm e fx4 R4 M4 model4 LK4 cr4 Aw4 BSP4 (pregsI_keep R1 R4 PR1 RP4)).
unfold PMBPQ.A0end in A04. rewrite L5K.rl10 in A04. exact A04.
Qed.
End Frame.
End Call.
End WithHeap.
End PMBBA4.
