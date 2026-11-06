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
PmModelFactsA PmStepAB0 PmStep PmParStep PmParKit PmBSrcKit PmBParKit PmBReset1 PmBUarK PmBUar PmBUarKS PmBBaK PmBBaK2 PmBBaK3 Jb0_code_b2664_b2668 PmBBa1 PmBBaP1 PmBBaP2 PmBBaP3 PmBBa2 PmBBa3 PmBBa4 PmCertKitG.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmBBa5 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBBa2.PMBBA2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBBaK.PMBBK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0Ac"; "0Aw0"; "0BX"; "1bool"; "1false"; "1length"; "1list"; "1nat"; "1option"; "1prod"; "1true"; "2and"; "2eq"; "2ex"; "2or"; "3Z"]; ["0F"; "0FF"; "0HI"; "0K"; "0L"; "0LBX"; "0LK0"; "0LKc"; "4Model"; "5bvmap"; "0M0"; "0MV"; "0Mc"; "0R"; "0R0"; "6mrestrict"]; ["7credit"; "8ahid"; "8fframe"; ":u64_at"; "9SCFG"; ";tregs"; "<binv'"; "<bst"; "<op"; "<vfacts"; "=p_b"; "=p_depth"; "=p_k"; "=p_stk"; "=pst"; "=pstate"]; ["=strm"; ">cfg"; "?FPState"; "?getr"; "@srealizes"; "Aloaded_segments"; "0S"; "0SCFG_P"; "Badd"; "Ble"; "Blt"; "Bmul"; "Bof_nat"; "Bpow"; "0a"; "0ar"]; ["0b"; "0c"; "0cat"; "0cr0"; "0crc"; "0d"; "0e"; "0e0"; "0fb"; "0fl"; "0fx"; "0model0"; "0modelc"; "0s"; "0s0"; "0sm"]; ["0sm0"; "CZ_to_bv"; "Cbv"; "0str"; "0typed"; "0v"; "0x"]]).
Local Ltac lia := L5FastLia.plia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PMBBA5.
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
Local Abbreviation vf_fsh := (PMBBA4.vf_fsh R0 S fb F fl).
Local Abbreviation vf_fb := (PMBBA4.vf_fb R0 S fb F fl).
Local Abbreviation mi_vis := (PMBBA4.mi_vis L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE CMI SMI CMS SMS CMSU SMSU F fl LK2 M2 model2 G).
Local Abbreviation stk_bz := (PMBBA4.stk_bz L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE CMI SMI CMS SMS CMSU SMSU F fl LK2 M2 model2 G).
Local Abbreviation stk_cell := (PMBBA4.stk_cell L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE CMI SMI CMS SMS CMSU SMSU F fl LK2 M2 model2 G).
Local Abbreviation modsub := PMBBA4.modsub.
Local Abbreviation mod32_d := PMBBA4.mod32_d.
Local Abbreviation sp_mod := (PMBBA4.sp_mod S SP32).
Local Abbreviation pow_bnd_ra := PMBBA4.pow_bnd_ra.
Local Abbreviation c_stage := (PMBBA4.c_stage L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE CMI SMI CMS SMS CMSU SMSU F fl LK2 M2 model2 G).
Local Abbreviation VK := (PMBBA4.VK R0 S fb F fl).
Local Abbreviation i_stage := (PMBBA4.i_stage L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE CMI SMI CMS SMS CMSU SMSU F fl LK2 M2 model2 G).
Local Abbreviation tregs0 := (PMBBA2.tregs0 R0 S fb F).
Local Abbreviation tregs0_keep := (PMBBA2.tregs0_keep R0 S fb F).
Local Abbreviation tregs0_of := (PMBBA2.tregs0_of R0 S fb F).
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
Lemma vf_opF : ltac2:(TCodec.tc2 tcn__PmBBa5 "Q4'3'?'RByR0%211'8y8%511%311p051&Q9vNvQFvR8v@vR9r3r2r1%9887654321'>&QI&QH&Q8%11;+\0%4221%621=+R0%72?1%9216%;241p0=1pQHH1pU<Q11pU:Q31").
Proof. intros typed v MV. intros VF. unfold PMBBK.vfacts in VF. destruct VF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _). exact X. Qed.
Ltac bst_of BI RUN EC HD FSH STEP E0 SD CRL CRK :=
split; [exact BI|]; split; [exact RUN|]; split; [exact EC|]; split; [exact HD|]; split; [exact FSH|]; split; [exact STEP|]; split; [exact E0|];
split; [exact SD|]; split; [exact CRL| exact CRK].
Ltac bst_ofV BI RUN EC HD FSH STEP E0 SD CRL CRK VSL FR :=
split; [exact BI|]; split; [exact RUN|]; split; [exact EC|]; split; [exact HD|]; split; [exact FSH|]; split; [exact STEP|]; split; [exact E0|];
split; [exact SD|]; split; [exact CRL|]; split; [exact CRK|];
lazymatch type of VSL with L5.u64_at _ ?Mo _ _ => apply (L5C.u64_at_agree RSEGS Mo _ (S - 136) _); [intros i Hi; apply FR; [lia| intros X; cbv beta in X; first [exact X| lia]]| lia| lia| exact VSL] end.
Lemma fap_of : ltac2:(TCodec.tc2 tcn__PmBBa5 "QG'6'9'?%2211%411'RByR0%211'8y8%511%311p051'H&Q2%?11&Q0&Q6vDvQOvBvNvJvR;vEvAvFv1vQFvR8v@r6r5r4r3r2r1%DCCBA@?>=<;:987654321'>&QI&QH+R0%22<1%421>+QP0%52@1%721@%9241p0;1p2Q=1pT:Q21pQ@Q41pTJQ71pQJQ91p6QB1").
Proof using G HIok FOK. intros BX Mc modelc LKc crc Ac.
intros BI. pose proof BI as (HHc & _). pose proof FOK as ((rs & Hfb) & Fal).
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHc) as (WB & WF & _).
destruct (WF (F, 0, S - 160 + 32) (or_introl eq_refl)) as (_ & _ & _ & _ & _ & APF). cbn [ff_addr ff_class fst snd] in APF. change (ff_bytes 0) with 64 in APF.
assert (Iin : In (fb, 4, rs) (ff_remove F FF' ++ LKc)).
{ apply in_or_app. left. unfold PMBBK.FF'. cbn [ff_remove ff_addr]. rewrite Z.eqb_refl. exact Hfb. }
destruct (APF _ Iin) as [X0|X0]; cbn [ff_addr ff_class fst snd] in X0; change (ff_bytes 4) with 1024 in X0; [left| right]; lia.
Qed.
Ltac mregs_ks KS := unfold PMBBA2.tregs, PMBBA2.tregs0, PMBBA2.mregs, PMBBA2.mregs0; repeat split; (rewrite (KS _) by inl; hx).
Lemma vec_pre_factsT : ltac2:(TCodec.tc2 tcn__PmBBa5 "SA'3'Q>'Q@'RByR0%211'8y8%511%311p051'H'6&Q2%211&Q0'9'?%2211%711&Q7vDvQOvBvNvJvR;vEvAvFv1vR3vQFvR8vR2vR>vRCvR@vR7v@r9r8r7r6r5r4r3r2r1%MLLKJIHGFEDCBA@?>=<;:987654321';&Q3&QE&O&Q1%128;%321=&QH&Q8%11J+[@%4221&Q:%11G&QK+Q0&QL&5'Q?&Q=%11N%4231%611%9281%A2;1%H4GC>1+[H%D2B1&QM+2&Q<%11Q9%4231%C2B1%K2E1%Q24Q1M81&QI+TP0%221I+Q?%<2;1%5271z%721<+;%92>1%Q>231%;2I?%Q@221%QA281%QB2<1%QC2@1%QD2K1p0QF1p2RE1pT:RJ1pQ@RL1pTJS01pQJS21pT>S=1pU0S<1pTLS>1pU:S@1").
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
Lemma t4_stage : ltac2:(TCodec.tc2 tcn__PmBBa5 "RF'Q>'Q@'3'QB&Iy5'RByR0%211%5241'8y8%611%311p061'H'6&Q2%211&Q0'9'?%2211%711&QI&Q;vR>%211+oO%5221&Q7vDvQOvBvNvJvR;vEvAvFv1vR3vQFvR8vR2vRCvR@vR7v@(:r;r:r9r6r5r4r3r2%LLKJIHGFEDCBA@?>Q0=<;:987654321&Q5r8%25KCB=1'QD&QE&Q4vQG%211&QA+fXd0r7%367CB2:1vC%:49621p0<1p0@1p0Q>1p2QE1pT:QJ1pQ@QL1pTJR01pQJR21pQLR81pTFR?1pT>RA1pU0RC1pTLRE1").
Proof using All. intros s sm e fx R Mc modelc LKc crc Ac.
intros DEP BS MR. pose proof MR as (((X2 & X8 & X9 & X18 & X19 & X20 & X21 & X25 & X26 & X27 & X3 & X4) & X23) & X22 & X24).
pose proof BS as (BI & RUN & EC & HD & FSH & STEP & E0 & SD & CRL & CRK & VSL). pose proof (S_of_binv _ _ _ _ _ _ BI) as SRB.
pose proof (vpack true _ s sm e 0 cat Mc modelc LKc crc Ac BI RUN EC HD FSH) as VF.
set (MV := mrestrict (ahid Ac modelc) Mc) in *.
pose proof (PMBBAP2.abaT4_conc fx R MV (VT 0 0)) as P. unfold PMBBA3.VT in P. cbn beta iota in P. feedV P VF.
destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & PR). decompose [and] PR. clear PR.
pose proof (vf_fb true 0 MV VF) as (DF1 & DF2).
apply (step_piece true s sm e 0 cat fx fx1 R 0xb2280 R1 0xb160c M1v Mc modelc LKc crc Ac (fun _ => False) BI RUN EC HD MS1 MG1).
{ intros a Ha _. apply FRZ1. exact Ha. }
{ intros a []. }
{ apply (fsh_agree true MV M1v); [intros a Ha; apply FRZ1; lia| exact DF1| exact DF2| exact (vf_fsh true 0 MV VF)]. }
intros M1 model1 BI1 RUN1 EC1 HD1 FSH1 VIS1 HID1 FR1.
assert (BS1 : bst true s sm e M1 model1 LKc crc Ac) by (bst_ofV BI1 RUN1 EC1 HD1 FSH1 STEP E0 SD CRL CRK VSL FR1).
assert (MR1 : tregs R1) by mregs_ks KS1.
assert (A1 : getr R1 (reg 1) = Z_to_bv 64 0xb228c) by hx.
assert (A10 : getr R1 (reg 10) = Z_to_bv 64 op) by hx.
assert (A11 : getr R1 (reg 11) = Z_to_bv 64 oec) by hx.
pose proof MR1 as (((Y2 & Y8 & Y9 & Y18 & Y19 & Y20 & Y21 & Y25 & Y26 & Y27 & Y3 & Y4) & Y23) & Y22 & Y24).
apply (call_gl true s sm e fx1 R1 M1 model1 LKc crc Ac 0xb228c BS1 A1 ltac:(apply pow_bnd_ra; [lia| reflexivity]) Y2 Y3 Y4 A10 A11).
intros fx2 R2 M2' model2' LK2' Aw2 s2 sm2 e2 cr2 RP2 OUT2.
pose proof (tregs_keep R1 R2 MR1 RP2) as MR2.
destruct OUT2 as [(BS2 & UN2 & (len & Hlen & A10'))|BE2].
2: { exact (gl_err_T s2 sm2 fx2 R2 M2' model2' LK2' cr2 Aw2 BE2 MR2). }
pose proof BS2 as (BI2 & RUN2 & EC2 & HD2 & FSH2 & STEP2 & E02 & SD2 & CRL2 & CRK2 & VSL2). pose proof (S_of_binv _ _ _ _ _ _ BI2) as SRB2.
pose proof (vpack true _ s2 sm2 e2 0 cat M2' model2' LK2' cr2 Aw2 BI2 RUN2 EC2 HD2 FSH2) as VF2.
pose proof (mi_vis _ s2 sm2 e2 M2' model2' LK2' cr2 Aw2 BI2 RUN2) as MI2.
set (MV2 := mrestrict (ahid Aw2 model2') M2') in *.
pose proof MR2 as (((Z2 & Z8 & Z9 & Z18 & Z19 & Z20 & Z21 & Z25 & Z26 & Z27 & Z3 & Z4) & Z23) & Z22 & Z24).
pose proof (vf_fb true 0 MV2 VF2) as (DF1b & DF2b). pose proof (vf_rng true 0 MV2 VF2) as (Rop & RS & RF & Rfl).
destruct (Z_le_gt_dec len 16777216) as [Le|Gt].
-
assert (HL2 : 0 <= len <= 16777216) by lia.
destruct (vec_pre_factsT true s2 sm2 e2 M2' model2' LK2' cr2 Aw2 BS2) as (VE & VC & Vb & Vbc & Vk & Vn).
change (mrestrict (ahid Aw2 model2') M2') with MV2 in VE, VC.
set (nn := Z.of_nat (length (PM.p_stk s2))) in *. pose proof (PM.pow2_pos (PM.p_k s2) (proj1 Vk)) as P2.
assert (R53 : 0 <= PM.p_b s2 + 32 * nn <= 140737488355328) by lia. assert (B53 : 0 <= PM.p_b s2 + 32 * nn < 2 ^ 64) by lia.
assert (R54 : 0 <= PM.p_b s2 + 32 * 2 ^ PM.p_k s2 <= 140737488355328) by lia. assert (B54 : 0 <= PM.p_b s2 + 32 * 2 ^ PM.p_k s2 < 2 ^ 64) by lia.
pose proof (PMBBAP2.abaTf_conc fx2 R2 MV2 (VTv len (PM.p_b s2 + 32 * nn) (PM.p_b s2 + 32 * 2 ^ PM.p_k s2))) as P. unfold VTv, PMBBA3.VT in P. cbn beta iota in P. feedV P VF2.
destruct P as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & PR).
assert (STEP3 : forall pc3, msteps RSEGS (L5A.st fx2 R2 0xb228c MV2) (L5A.st fx3 R3 pc3 M3v) ->
(forall M3 model3, bst true s2 sm2 e2 M3 model3 LK2' cr2 Aw2 -> mrestrict (ahid Aw2 model2') M3 = M3v -> ahid Aw2 model3 = ahid Aw2 model2' ->
srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx3 R3 pc3 M3 model3) K) ->
srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx2 R2 0xb228c M2' model2') K).
{ intros pc3 MS3 NX.
apply (step_piece true s2 sm2 e2 0 cat fx2 fx3 R2 0xb228c R3 pc3 M3v M2' model2' LK2' cr2 Aw2 (fun a => S - 116 <= a < S - 104) BI2 RUN2 EC2 HD2 MS3 MG3).
{ intros a Ha N. apply FRZ3; [exact Ha| intros X; apply N; lia]. }
{ intros a X. left. lia. }
{ apply (fsh_agree true MV2 M3v); [intros a Ha; apply FRZ3; [lia| intros X; unfold SB in *; lia]| exact DF1b| exact DF2b| exact (vf_fsh true 0 MV2 VF2)]. }
intros M3 model3 BI3 RUN3 EC3 HD3 FSH3 VIS3 HID3 FR3.
apply (NX M3 model3); [bst_ofV BI3 RUN3 EC3 HD3 FSH3 STEP2 E02 SD2 CRL2 CRK2 VSL2 FR3| exact VIS3| exact HID3]. }
pose proof SD2 as (_ & _ & SDp & SDs). pose proof INV as (_ & _ & IDP & _).
pose proof STEP2 as (_ & _ & _ & _ & UN02).
destruct PR as [(MS3 & KS3 & PR)|(MS3 & KS3 & PR)]; decompose [and] PR; clear PR.
+
apply (STEP3 0xb35d4 MS3). intros M3 model3 BS3 VIS3 HID3.
pose proof BS3 as (BI3 & _ & _ & _ & FSH3 & _).
destruct (stk_cell _ M3 model3 LK2' cr2 Aw2 (S - 116) 4 (proj1 BS3) ltac:(lia) ltac:(lia) ltac:(lia)) as (AC1 & BZ1 & AO1 & U1 & _).
destruct (stk_cell _ M3 model3 LK2' cr2 Aw2 (S - 112) 8 (proj1 BS3) ltac:(lia) ltac:(lia) ltac:(lia)) as (AC2 & BZ2 & AO2 & _ & U2).
rewrite HID3, VIS3 in U1, U2.
assert (C116 : L5.u32_at RSEGS M3 (S - 116) 4) by (apply U1; [hx| reflexivity]).
assert (C112 : L5.u64_at RSEGS M3 (S - 112) len) by (apply U2; [hx| reflexivity]).
assert (PR3 : pregsT R3) by pregs_ks KS3.
assert (B1 : getr R3 (reg 1) = Z_to_bv 64 0xb26b8) by hx.
assert (B10 : getr R3 (reg 10) = Z_to_bv 64 (op + 360)) by hx.
assert (B11 : getr R3 (reg 11) = Z_to_bv 64 (S - 116)) by hx.
assert (B12 : getr R3 (reg 12) = Z_to_bv 64 (S - 112)) by hx.
assert (B13 : getr R3 (reg 13) = Z_to_bv 64 (F + 32)) by hx.
pose proof PR3 as ((W2 & W8 & W9 & W18 & W19 & W20 & W25 & W26 & W27 & W3 & W4) & W22 & W23 & W24).
pose proof (PMBUK.vis_facts L ar C HI LYa HIok M0 model0 LBX FF LK0 Aw0 S SCR (S - 160) (S - 104) S ocell own F fl 0 LK2 M2 model2 cr0 (PM.parser_own s0) G WR _ M3 model3 LK2' cr2 Aw2 BI3)
as (_ & _ & (FDEF3 & _) & (_ & _ & FV3 & _ & _)). change (ff_bytes 0) with 64 in FDEF3, FV3.
assert (DT : L5.defined M3 (F + 32) 1).
{ intros i Hi. pose proof (FDEF3 (32 + i) ltac:(lia)) as Y. unfold mrestrict in Y. rewrite (FV3 (32 + i) ltac:(lia)) in Y.
replace (F + 32 + i) with (F + (32 + i)) by lia. exact Y. }
destruct (PMCG.u8_of_defined RSEGS M3 (F + 32) ltac:(lia) ltac:(lia) DT) as (t & Ht & C32).
pose proof FSH3 as (_ & _ & _ & _ & SH4 & _).
assert (BZ3 : byte_at M3 (HeapIfaceA.S (F + 32)) 1).
{ unfold HeapIfaceA.S, SB, byte_at. replace ((F + 32) / 8 + 2147450880) with (F / 8 + 2147450884).
- apply (L5ADHR.byte_of_u8 M3 _ 1 SH4); lia.
- replace (F + 32) with (4 * 8 + F) by lia. rewrite Z.div_add_l by lia. lia. }
assert (FM32 : F mod 32 = 0).
{ pose proof G as G'. destruct G' as [Hk SPTg SLOg SHIg SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS]. exact F32. }
assert (F32m : (F + 32) mod 8 = 0).
{ replace (F + 32) with ((F / 8 + 4) * 8) by (pose proof (Z.div_mod F 8 ltac:(lia)); pose proof (mod32_d F 8 ltac:(exists 4; reflexivity) ltac:(lia) FM32); lia). apply Z_mod_mult. }
pose proof (vf_opF true 0 MV2 VF2) as OPF.
assert (B21 : getr R3 (reg 21) = Z_to_bv 64 (PM.p_b s2 + 32 * nn)) by hx.
pose proof CMSU as CMSU'. unfold PMBX.cone_msu_spec in CMSU'.
apply (call_push 0xb35d4 PMBPQ.Qcone PMBPQ.A0none (PMSAX.cells_msu RSEGS ar) (PMBPQ.cone_pushq RSEGS AD L ar HI 0xb35d4 _ CMSU') true s2 sm2 e2 fx3 R3 M3 model3 LK2' cr2 Aw2 0xb26b8 (PM.PS 4 len t 0) BS3 B1
ltac:(apply pow_bnd_ra; [lia| reflexivity]) W2 W3 W4 B10).
* unfold PMSAX.cells_msu. exists (S - 116), (S - 112), (F + 32), 4, len, t.
split; [rewrite L5SAR.r11; exact B11|]. split; [rewrite L5K.rl12; exact B12|]. split; [rewrite L5K.rl13; exact B13|].
split; [apply sp_mod; [exists 8; reflexivity| lia| reflexivity]|]. split; [apply sp_mod; [exists 4; reflexivity| lia| reflexivity]|].
split; [exact AC1|]. split; [exact AC2|].
split; [intros a Ha; right; exists 1; split; [replace a with (F + 32) by lia; exact BZ3| split; [lia| replace a with (F + 32) by lia; rewrite F32m; lia]]|].
split; [exact AO1|]. split; [exact AO2|].
split; [split; [left; exists (F, 0, S - 160 + 32); split; [left; reflexivity| cbn [ff_addr ff_class fst snd]; change (ff_bytes 0) with 64; lia]
| destruct OPF as [Y|Y]; [right| left]; lia]|].
split; [exact BZ1|]. split; [exact BZ2|]. split; [split; [exact BZ3| exact F32m]|].
split; [exact C116|]. split; [exact C112|]. split; [exact C32|]. split; [lia|]. split; [lia|]. split; [lia| reflexivity].
* split; [reflexivity| lia].
* unfold PM.pstate_ok. cbn [PM.ps_type PM.ps_mode PM.ps_len PM.ps_idx]. split; [lia|]. left. split; [unfold PM.mode_counted; right; left; reflexivity|]. unfold PM.MAX_ITEMS. lia.
* reflexivity.
* unfold PM.mode_bottom. cbn [PM.ps_mode]. lia.
* intros _. pose proof STEP as (_ & _ & _ & _ & UN0). lia.
* unfold PM.MAX_DEPTH. lia.
* intros fx4 R4 M4 model4 LK4 Aw4 s4 cr4 RP4 A04 STK4 PO4 BSP4 SRC4 KPR4.
assert (Eb4 : PM.p_b s4 = PM.p_b s2).
{ destruct PO4 as [(_ & _ & _ & Eb & _ & _)|([Eo|Eo] & _ & _)]; [exact Eb| discriminate Eo| lia]. }
apply (tail_Tc s4 sm2 e2 fx4 R4 M4 model4 LK4 cr4 Aw4 len BSP4 (pregsT_keep R3 R4 PR3 RP4)); [| exact HL2|].
-- rewrite (L5SAR.cs_of_preserved R3 R4 21 RP4) by inl. rewrite B21, Eb4, STK4, length_app. cbn [length]. f_equal. unfold nn. lia.
-- apply (L5C.u64_at_agree RSEGS M3 M4); [intros i Hi; apply KPR4; lia| lia| lia| exact C112].
+
apply (STEP3 0xb3780 MS3). intros M3 model3 BS3 VIS3 HID3.
pose proof BS3 as (BI3 & _ & _ & _ & FSH3 & _).
destruct (stk_cell _ M3 model3 LK2' cr2 Aw2 (S - 116) 4 (proj1 BS3) ltac:(lia) ltac:(lia) ltac:(lia)) as (AC1 & BZ1 & AO1 & U1 & _).
destruct (stk_cell _ M3 model3 LK2' cr2 Aw2 (S - 112) 8 (proj1 BS3) ltac:(lia) ltac:(lia) ltac:(lia)) as (AC2 & BZ2 & AO2 & _ & U2).
rewrite HID3, VIS3 in U1, U2.
assert (C116 : L5.u32_at RSEGS M3 (S - 116) 4) by (apply U1; [hx| reflexivity]).
assert (C112 : L5.u64_at RSEGS M3 (S - 112) len) by (apply U2; [hx| reflexivity]).
assert (PR3 : pregsT R3) by pregs_ks KS3.
assert (B1 : getr R3 (reg 1) = Z_to_bv 64 0xb26dc) by hx.
assert (B10 : getr R3 (reg 10) = Z_to_bv 64 (op + 360)) by hx.
assert (B11 : getr R3 (reg 11) = Z_to_bv 64 (S - 116)) by hx.
assert (B12 : getr R3 (reg 12) = Z_to_bv 64 (S - 112)) by hx.
assert (B13 : getr R3 (reg 13) = Z_to_bv 64 (F + 32)) by hx.
pose proof PR3 as ((W2 & W8 & W9 & W18 & W19 & W20 & W25 & W26 & W27 & W3 & W4) & W22 & W23 & W24).
pose proof (PMBUK.vis_facts L ar C HI LYa HIok M0 model0 LBX FF LK0 Aw0 S SCR (S - 160) (S - 104) S ocell own F fl 0 LK2 M2 model2 cr0 (PM.parser_own s0) G WR _ M3 model3 LK2' cr2 Aw2 BI3)
as (_ & _ & (FDEF3 & _) & (_ & _ & FV3 & _ & _)). change (ff_bytes 0) with 64 in FDEF3, FV3.
assert (DT : L5.defined M3 (F + 32) 1).
{ intros i Hi. pose proof (FDEF3 (32 + i) ltac:(lia)) as Y. unfold mrestrict in Y. rewrite (FV3 (32 + i) ltac:(lia)) in Y.
replace (F + 32 + i) with (F + (32 + i)) by lia. exact Y. }
destruct (PMCG.u8_of_defined RSEGS M3 (F + 32) ltac:(lia) ltac:(lia) DT) as (t & Ht & C32).
pose proof FSH3 as (_ & _ & _ & _ & SH4 & _).
assert (BZ3 : byte_at M3 (HeapIfaceA.S (F + 32)) 1).
{ unfold HeapIfaceA.S, SB, byte_at. replace ((F + 32) / 8 + 2147450880) with (F / 8 + 2147450884).
- apply (L5ADHR.byte_of_u8 M3 _ 1 SH4); lia.
- replace (F + 32) with (4 * 8 + F) by lia. rewrite Z.div_add_l by lia. lia. }
assert (FM32 : F mod 32 = 0).
{ pose proof G as G'. destruct G' as [Hk SPTg SLOg SHIg SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS]. exact F32. }
assert (F32m : (F + 32) mod 8 = 0).
{ replace (F + 32) with ((F / 8 + 4) * 8) by (pose proof (Z.div_mod F 8 ltac:(lia)); pose proof (mod32_d F 8 ltac:(exists 4; reflexivity) ltac:(lia) FM32); lia). apply Z_mod_mult. }
pose proof (vf_opF true 0 MV2 VF2) as OPF.
pose proof SMSU as SMSU'. unfold PMBX.slow_msu_spec in SMSU'. cbn [paa_esp_msu PMB.AAD AADDR_B] in SMSU'.
apply (call_push 0xb3780 PMBPQ.Qslow PMBPQ.A0end (PMSAX.cells_msu RSEGS ar) (PMBPQ.slow_pushq RSEGS AD L ar HI 0xb3780 _ SMSU') true s2 sm2 e2 fx3 R3 M3 model3 LK2' cr2 Aw2 0xb26dc (PM.PS 4 len t 0) BS3 B1
ltac:(apply pow_bnd_ra; [lia| reflexivity]) W2 W3 W4 B10).
* unfold PMSAX.cells_msu. exists (S - 116), (S - 112), (F + 32), 4, len, t.
split; [rewrite L5SAR.r11; exact B11|]. split; [rewrite L5K.rl12; exact B12|]. split; [rewrite L5K.rl13; exact B13|].
split; [apply sp_mod; [exists 8; reflexivity| lia| reflexivity]|]. split; [apply sp_mod; [exists 4; reflexivity| lia| reflexivity]|].
split; [exact AC1|]. split; [exact AC2|].
split; [intros a Ha; right; exists 1; split; [replace a with (F + 32) by lia; exact BZ3| split; [lia| replace a with (F + 32) by lia; rewrite F32m; lia]]|].
split; [exact AO1|]. split; [exact AO2|].
split; [split; [left; exists (F, 0, S - 160 + 32); split; [left; reflexivity| cbn [ff_addr ff_class fst snd]; change (ff_bytes 0) with 64; lia]
| destruct OPF as [Y|Y]; [right| left]; lia]|].
split; [exact BZ1|]. split; [exact BZ2|]. split; [split; [exact BZ3| exact F32m]|].
split; [exact C116|]. split; [exact C112|]. split; [exact C32|]. split; [lia|]. split; [lia|]. split; [lia| reflexivity].
* right. unfold nn in *. lia.
* unfold PM.pstate_ok. cbn [PM.ps_type PM.ps_mode PM.ps_len PM.ps_idx]. split; [lia|]. left. split; [unfold PM.mode_counted; right; left; reflexivity|]. unfold PM.MAX_ITEMS. lia.
* reflexivity.
* unfold PM.mode_bottom. cbn [PM.ps_mode]. lia.
* intros _. pose proof STEP as (_ & _ & _ & _ & UN0). lia.
* unfold PM.MAX_DEPTH. lia.
* intros fx4 R4 M4 model4 LK4 Aw4 s4 cr4 RP4 A04 STK4 PO4 BSP4 SRC4 KPR4.
apply (tail_Ts s4 sm2 e2 fx4 R4 M4 model4 LK4 cr4 Aw4 len BSP4 (pregsT_keep R3 R4 PR3 RP4)); [| exact HL2|].
-- unfold PMBPQ.A0end in A04. rewrite L5K.rl10 in A04. exact A04.
-- apply (L5C.u64_at_agree RSEGS M3 M4); [intros i Hi; apply KPR4; lia| lia| lia| exact C112].
-
assert (HL2 : 16777217 <= len <= 18446744073709551615) by lia.
pose proof (PMBBAP2.abaTx_conc fx2 R2 MV2 (VT 0 len)) as P. unfold PMBBA3.VT in P. cbn beta iota in P. feedV P VF2.
destruct P as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & PR). decompose [and] PR. clear PR.
apply (step_piece true s2 sm2 e2 0 cat fx2 fx3 R2 0xb228c R3 0xafa18 M3v M2' model2' LK2' cr2 Aw2 (fun a => S - 112 <= a < S - 104) BI2 RUN2 EC2 HD2 MS3 MG3).
{ intros a Ha N. apply FRZ3; [exact Ha| intros X; apply N; lia]. }
{ intros a X. left. lia. }
{ apply (fsh_agree true MV2 M3v); [intros a Ha; apply FRZ3; [lia| intros X; unfold SB in *; lia]| exact DF1b| exact DF2b| exact (vf_fsh true 0 MV2 VF2)]. }
intros M3 model3 BI3 RUN3 EC3 HD3 FSH3 VIS3 HID3 FR3.
assert (BS3 : bst true s2 sm2 e2 M3 model3 LK2' cr2 Aw2) by (bst_ofV BI3 RUN3 EC3 HD3 FSH3 STEP2 E02 SD2 CRL2 CRK2 VSL2 FR3).
assert (MR3 : tregs R3) by mregs_ks KS3.
assert (B1 : getr R3 (reg 1) = Z_to_bv 64 0xb22d0) by hx.
assert (B10 : getr R3 (reg 10) = Z_to_bv 64 oec) by hx.
assert (B11 : getr R3 (reg 11) = Z_to_bv 64 13) by hx.
exact (mk_Zt13 s2 sm2 e2 fx3 R3 M3 model3 LK2' cr2 Aw2 13 BS3 MR3 B1 B10 B11 ltac:(lia)).
Qed.
Lemma reg_lit : ltac2:(TCodec.tc2 tcn__PmBBa5 "Q>&Iy5'RByR0%211%5241'7'?'<&QCr4&RA&QLr3%211%42>1%7261r2%72?1%;3?31r5%91;%;2E1%>231%@3D16';&QIz%221B&QJ&QM+2+R0%3221%52H1%:271r6%M3N1Ap031p041p0@1p0F1pT2Q31pSNQ41pU>Q61pQLQ81").
Proof. intros R x a b. intros E1 E2 H1 H2. rewrite E1 in E2. apply (f_equal bv_unsigned) in E2. rewrite !L5.unsigned_lit in E2 by lia. exact E2. Qed.
Ltac mid0 conc V typed VF BS s sm e Mc modelc LKc crc Ac MV fx R pc pc1 :=
let BI := fresh "BI" in let RUN := fresh "RUN" in let EC := fresh "EC" in let HD := fresh "HD" in let FSH := fresh "FSH" in
let STEP := fresh "STEP" in let E0 := fresh "E0" in let SD := fresh "SD" in let CRL := fresh "CRL" in let CRK := fresh "CRK" in let VSL := fresh "VSL" in
pose proof BS as (BI & RUN & EC & HD & FSH & STEP & E0 & SD & CRL & CRK & VSL);
let P := fresh "P" in pose proof (conc fx R MV V) as P; unfold PMBBA3.VT in P; cbn beta iota in P; feedV P VF;
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
let BS1 := fresh "BS1" in assert (BS1 : bst typed s sm e M1 model1 LKc crc Ac) by (bst_ofV BI1 RUN1 EC1 HD1 FSH1 STEP E0 SD CRL CRK VSL FR1) ].
Lemma t3_stage : ltac2:(TCodec.tc2 tcn__PmBBa5 "SA'Q>'Q@'3'QB&Iy5'RByR0%211%5241'8y8%611%311p061'H'6&Q2%211&Q0'9'?%2211%711&QI&Q;vR>%211+oO%5221&Q7vDvQOvBvNvJvR;vEvAvFv1vR3vQFvR8vR2vRCvR@vR7v@(:r;r:r9r6r5r4r3r2%LLKJIHGFEDCBA@?>Q0=<;:987654321&Q5r8%25KCB=1'>'<&QC&RA&QLu:%211%42R01%62B1+X0%72R11%:3R131'=';zr1%QF221&QJ%1239%6231%B2O=%B2R<6%E3R<21%:241qT4R11%=2R21%J2?1'QD&QE&Q4vQG%211&QA+fXbH%266Q>Q=1Q<Q4vC%948521p0;1p0Q71p0Q;1p0R91p2R@1pT:RE1pQ@RG1pTJRK1pQJRM1pQLS31pTFS:1pT>S<1pU0S>1pTLS@1").
Proof using All. intros s sm e fx R Mc modelc LKc crc Ac.
intros DEP BS MR A10. pose proof MR as (((X2 & X8 & X9 & X18 & X19 & X20 & X21 & X25 & X26 & X27 & X3 & X4) & X23) & X22 & X24).
pose proof BS as (BI & RUN & EC & HD & FSH & STEP & E0 & SD & CRL & CRK & VSL). pose proof (S_of_binv _ _ _ _ _ _ BI) as SRB.
pose proof (vpack true _ s sm e 0 cat Mc modelc LKc crc Ac BI RUN EC HD FSH) as VF.
set (MV := mrestrict (ahid Ac modelc) Mc) in *.
destruct A10 as [A10|(c & Hc & A10)].
-
mid0 PMBBAP2.abaT3e_conc (VT 0 0) true VF BS s sm e Mc modelc LKc crc Ac MV fx R 0xb2258 0xafa18.
assert (MR1 : tregs0 R1) by mregs_ks KS1.
assert (B1 : getr R1 (reg 1) = Z_to_bv 64 0xb24ec) by hx. assert (B10 : getr R1 (reg 10) = Z_to_bv 64 oec) by hx. assert (B11 : getr R1 (reg 11) = Z_to_bv 64 1) by hx.
exact (mk_Zt s sm e fx1 R1 M1 model1 LKc crc Ac 1 BS1 MR1 B1 B10 B11 ltac:(lia)).
- assert (Hcb : 0 <= c < 2 ^ 64) by lia.
destruct (Z.eq_dec c 35) as [E35|N35].
+
subst c. mid0 PMBBAP2.abaT3h_conc (VT 0 0) true VF BS s sm e Mc modelc LKc crc Ac MV fx R 0xb2258 0xafaf4.
assert (MR1 : tregs R1) by mregs_ks KS1.
assert (B1 : getr R1 (reg 1) = Z_to_bv 64 0xb2280) by hx. assert (B10 : getr R1 (reg 10) = Z_to_bv 64 (op + 24)) by hx. assert (B11 : getr R1 (reg 11) = Z_to_bv 64 1) by hx.
pose proof MR1 as (((Y2 & Y8 & Y9 & Y18 & Y19 & Y20 & Y21 & Y25 & Y26 & Y27 & Y3 & Y4) & Y23) & Y22 & Y24).
pose proof IGN as IGN'. unfold PMB.ignore_spec, PMSPA.ignore_spec in IGN'. cbn [pa_ignore PMB.AD ADDR_B] in IGN'.
apply (call_src 0xafaf4 4 PMSPA.ignore_args PMSPA.no_W PMSPA.ignore_res IGN' true s sm e fx1 R1 M1 model1 LKc crc Ac 0xb2280 [] BS1 B1
ltac:(apply pow_bnd_ra; [lia| reflexivity]) Y2 Y3 Y4 B10 ltac:(lia)).
* unfold PMSPA.ignore_args. rewrite L5SAR.r11. exact B11.
* reflexivity.
* intros rr [].
* intros fx2 R2 M2' model2' LK2' Aw2 src2 sm2 RP2 _ _ BS2.
exact (t4_stage (PMSPA.with_src s src2) sm2 e fx2 R2 M2' model2' LK2' crc Aw2 DEP BS2 (tregs_keep R1 R2 MR1 RP2)).
+
assert (Hc' : 0 <= c <= 34 \/ 36 <= c <= 255) by lia.
assert (PK : exists (fx1 : FPState) R1 M1v, mem_grows MV M1v /\ (forall i, 0 <= i < 2 ^ 64 -> M1v (Z_to_bv 64 i) = MV (Z_to_bv 64 i))
/\ msteps RSEGS (L5A.st fx R 0xb2258 MV) (L5A.st fx1 R1 0xafa18 M1v)
/\ (forall x, In x [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 25; 26; 27]%nat -> getr R1 (reg x) = getr R (reg x))
/\ getr R1 (reg 1) = Z_to_bv 64 0xb24ec /\ getr R1 (reg 10) = Z_to_bv 64 oec /\ getr R1 (reg 11) = Z_to_bv 64 3).
{ destruct Hc' as [Hc'|Hc'].
- pose proof (PMBBAP2.abaT3l_conc fx R MV (VK c)) as P. unfold PMBBA4.VK, PMBBA3.VT in P. cbn beta iota in P. feedV P VF.
destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & PR). decompose [and] PR. clear PR.
exists fx1, R1, M1v. split; [exact MG1|]. split; [exact FRZ1|]. split; [exact MS1|].
split; [intros x Hx; apply KS1; revert x Hx; apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 25; 26; 27]%nat); vm_compute; reflexivity|].
split; [hx|]. split; [hx| hx].
- pose proof (PMBBAP2.abaT3u_conc fx R MV (VK c)) as P. unfold PMBBA4.VK, PMBBA3.VT in P. cbn beta iota in P. feedV P VF.
destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & PR). decompose [and] PR. clear PR.
exists fx1, R1, M1v. split; [exact MG1|]. split; [exact FRZ1|]. split; [exact MS1|].
split; [intros x Hx; apply KS1; revert x Hx; apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 25; 26; 27]%nat); vm_compute; reflexivity|].
split; [hx|]. split; [hx| hx]. }
destruct PK as (fx1 & R1 & M1v & MG1 & FRZ1 & MS1 & KS1 & B1 & B10 & B11).
pose proof (vf_fb true 0 MV VF) as (DF1 & DF2).
apply (step_piece true s sm e 0 cat fx fx1 R 0xb2258 R1 0xafa18 M1v Mc modelc LKc crc Ac (fun _ => False) BI RUN EC HD MS1 MG1).
{ intros a Ha _. apply FRZ1. exact Ha. }
{ intros a []. }
{ apply (fsh_agree true MV M1v); [intros a Ha; apply FRZ1; lia| exact DF1| exact DF2| exact (vf_fsh true 0 MV VF)]. }
intros M1 model1 BI1 RUN1 EC1 HD1 FSH1 VIS1 HID1 FR1.
assert (BS1 : bst true s sm e M1 model1 LKc crc Ac) by (bst_ofV BI1 RUN1 EC1 HD1 FSH1 STEP E0 SD CRL CRK VSL FR1).
assert (MR1 : tregs0 R1).
{ unfold PMBBA2.tregs0, PMBBA2.mregs, PMBBA2.mregs0. repeat split; (rewrite KS1 by (cbn; tauto); hx). }
exact (mk_Zt s sm e fx1 R1 M1 model1 LKc crc Ac 3 BS1 MR1 B1 B10 B11 ltac:(lia)).
Qed.
Lemma t2_stage : ltac2:(TCodec.tc2 tcn__PmBBa5 "S9'Q>'Q@'3'QB&Iy5'RByR0%211%5241'8y8%611%311p061'H'6&Q2%211&Q0'9'?%2211%711&QI&Q;vR>%211+oO%5221&Q7vDvQOvBvNvJvR;vEvAvFv1vR3vQFvR8vR2vRCvR@vR7v@(:r<r;r:r7r6r5r4r3%LLKJIHGFEDCBA@?>Q0=<;:987654321&Q5r9%25KCB=1'<&QC&RA&QLu:%211%42QO1%62A1%62QO>%93QO21'>z%<3QEC1+1%>3QGE1%5231'QD&QE&Q4vQG%211&QAr=+fXb<%3672Q41Q3Q2vC%:49621p0<1p0C1p0N1p0Q21p0R01pT<R91p2R81pT:R=1pQ@R?1pTJRC1pQJRE1pQLRK1pTFS21pT>S41pU0S61pTLS81").
Proof using All. intros s sm e fx R Mc modelc LKc crc Ac d.
intros DEP BS MR A10 Hd. pose proof MR as (((X2 & X8 & X9 & X18 & X19 & X20 & X21 & X25 & X26 & X27 & X3 & X4) & X23) & X22 & X24).
pose proof BS as (BI & RUN & EC & HD & FSH & STEP & E0 & SD & CRL & CRK & VSL). pose proof (S_of_binv _ _ _ _ _ _ BI) as SRB.
pose proof (vpack true _ s sm e 0 cat Mc modelc LKc crc Ac BI RUN EC HD FSH) as VF.
set (MV := mrestrict (ahid Ac modelc) Mc) in *.
destruct Hd as [Hd|Hd]; subst d.
- mid0 PMBBAP2.abaT2z_conc (VT 0 0) true VF BS s sm e Mc modelc LKc crc Ac MV fx R 0xb224c 0xafa18.
assert (MR1 : tregs0 R1) by mregs_ks KS1.
assert (B1 : getr R1 (reg 1) = Z_to_bv 64 0xb24ec) by hx. assert (B10 : getr R1 (reg 10) = Z_to_bv 64 oec) by hx. assert (B11 : getr R1 (reg 11) = Z_to_bv 64 1) by hx.
exact (mk_Zt s sm e fx1 R1 M1 model1 LKc crc Ac 1 BS1 MR1 B1 B10 B11 ltac:(lia)).
- mid0 PMBBAP2.abaT2p_conc (VT 0 0) true VF BS s sm e Mc modelc LKc crc Ac MV fx R 0xb224c 0xaf8ec.
assert (MR1 : tregs R1) by mregs_ks KS1.
assert (B1 : getr R1 (reg 1) = Z_to_bv 64 0xb2258) by hx. assert (B10 : getr R1 (reg 10) = Z_to_bv 64 (op + 24)) by hx.
pose proof MR1 as (((Y2 & Y8 & Y9 & Y18 & Y19 & Y20 & Y21 & Y25 & Y26 & Y27 & Y3 & Y4) & Y23) & Y22 & Y24).
pose proof PEEK as PEEK'. unfold PMB.peek_spec, PMSPA.peek_spec in PEEK'. cbn [pa_peek PMB.AD ADDR_B] in PEEK'.
apply (call_src 0xaf8ec 4 PMSPA.no_args PMSPA.no_W PMSPA.peek_res PEEK' true s sm e fx1 R1 M1 model1 LKc crc Ac 0xb2258 [] BS1 B1
ltac:(apply pow_bnd_ra; [lia| reflexivity]) Y2 Y3 Y4 B10 ltac:(lia)).
+ exact I.
+ reflexivity.
+ intros rr [].
+ intros fx2 R2 M2' model2' LK2' Aw2 src2 sm2 RP2 RES2 _ BS2.
destruct RES2 as (_ & RES2).
apply (t3_stage (PMSPA.with_src s src2) sm2 e fx2 R2 M2' model2' LK2' crc Aw2 DEP BS2 (tregs_keep R1 R2 MR1 RP2)).
rewrite !L5K.rl10 in RES2. destruct RES2 as [X|(c & Hc & X & _)]; [left; exact X| right; exists c; split; [exact Hc| exact X]].
Qed.
Lemma t1_stage : ltac2:(TCodec.tc2 tcn__PmBBa5 "RF'Q>'Q@'3'QB&Iy5'RByR0%211%5241'8y8%611%311p061'H'6&Q2%211&Q0'9'?%2211%711&QI&Q;vR>%211+oO%5221&Q7vDvQOvBvNvJvR;vEvAvFv1vR3vQFvR8vR2vRCvR@vR7v@(4r;r:r9r6r5r4r3r2%LLKJIHGFEDCBA@?>Q0=<;:987654321&Q5r8%25KCB=1'QD&QE&Q4vQG%211&QA+fXaHr7%367CB2:1vC%:49621p0<1p0@1p0Q>1p2QE1pT:QJ1pQ@QL1pTJR01pQJR21pQLR81pTFR?1pT>RA1pU0RC1pTLRE1").
Proof using All. intros s sm e fx R Mc modelc LKc crc Ac.
intros DEP BS MR. pose proof MR as (((X2 & X8 & X9 & X18 & X19 & X20 & X21 & X25 & X26 & X27 & X3 & X4) & X23) & X22 & X24).
pose proof BS as (BI & RUN & EC & HD & FSH & STEP & E0 & SD & CRL & CRK & VSL). pose proof (S_of_binv _ _ _ _ _ _ BI) as SRB.
pose proof (vpack false _ s sm e 0 cat Mc modelc LKc crc Ac BI RUN EC HD FSH) as VF.
set (MV := mrestrict (ahid Ac modelc) Mc) in *.
pose proof (PMBBAP2.abaT1_conc fx R MV (VT 0 0)) as P. unfold PMBBA3.VT in P. cbn beta iota in P. feedV P VF.
destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & PR). decompose [and] PR. clear PR.
pose proof (vf_fb false 0 MV VF) as (DF1 & DF2). pose proof (vf_rng false 0 MV VF) as (Rop & RS & RF & Rfl).
pose proof (vf_fsh false 0 MV VF) as (Y0 & Y1 & Y2' & Y3' & _ & Y5 & Y6 & Y7).
assert (SH4 : L5.u8_at RSEGS M1v (F / 8 + 2147450884) 1) by hx.
apply (step_piece true s sm e 0 cat fx fx1 R 0xb2238 R1 0xb065c M1v Mc modelc LKc crc Ac (fun a => a = F / 8 + 2147450884) BI RUN EC HD MS1 MG1).
{ intros a Ha N. apply FRZ1; [exact Ha| intros X; apply N; lia]. }
{ intros a X. right. exact X. }
{ assert (AG : forall a, F / 8 + 2147450880 <= a < F / 8 + 2147450888 -> a <> F / 8 + 2147450884 -> M1v (Z_to_bv 64 a) = MV (Z_to_bv 64 a))
by (intros a Ha N; apply FRZ1; [lia| intros X; apply N; lia]).
unfold PMBBK.fsh. cbn iota.
split; [apply (L5C.u8_at_agree RSEGS MV M1v); [intros i Hi; apply AG; lia| lia| lia| exact Y0]|].
split; [apply (L5C.u8_at_agree RSEGS MV M1v); [intros i Hi; apply AG; lia| lia| lia| exact Y1]|].
split; [apply (L5C.u8_at_agree RSEGS MV M1v); [intros i Hi; apply AG; lia| lia| lia| exact Y2']|].
split; [apply (L5C.u8_at_agree RSEGS MV M1v); [intros i Hi; apply AG; lia| lia| lia| exact Y3']|].
split; [exact SH4|].
split; [apply (L5C.u8_at_agree RSEGS MV M1v); [intros i Hi; apply AG; lia| lia| lia| exact Y5]|].
split; [apply (L5C.u8_at_agree RSEGS MV M1v); [intros i Hi; apply AG; lia| lia| lia| exact Y6]|].
apply (L5C.u8_at_agree RSEGS MV M1v); [intros i Hi; apply AG; lia| lia| lia| exact Y7]. }
intros M1 model1 BI1 RUN1 EC1 HD1 FSH1 VIS1 HID1 FR1.
assert (BS1 : bst true s sm e M1 model1 LKc crc Ac) by (bst_ofV BI1 RUN1 EC1 HD1 FSH1 STEP E0 SD CRL CRK VSL FR1).
assert (MR1 : tregs R1) by mregs_ks KS1.
assert (B1 : getr R1 (reg 1) = Z_to_bv 64 0xb224c) by hx. assert (B10 : getr R1 (reg 10) = Z_to_bv 64 (op + 24)) by hx.
assert (B11 : getr R1 (reg 11) = Z_to_bv 64 (F + 32)) by hx. assert (B12 : getr R1 (reg 12) = Z_to_bv 64 1) by hx.
pose proof MR1 as (((Z2 & Z8 & Z9 & Z18 & Z19 & Z20 & Z21 & Z25 & Z26 & Z27 & Z3 & Z4) & Z23) & Z22 & Z24).
pose proof (PMBUK.vis_facts L ar C HI LYa HIok M0 model0 LBX FF LK0 Aw0 S SCR (S - 160) (S - 104) S ocell own F fl 0 LK2 M2 model2 cr0 (PM.parser_own s0) G WR _ M1 model1 LKc crc Ac BI1)
as (_ & _ & (FDEF1 & _) & (_ & _ & FV1 & _ & _)). change (ff_bytes 0) with 64 in FDEF1, FV1.
assert (DT : L5.defined M1 (F + 32) 1).
{ intros i Hi. pose proof (FDEF1 (32 + i) ltac:(lia)) as Y. unfold mrestrict in Y. rewrite (FV1 (32 + i) ltac:(lia)) in Y.
replace (F + 32 + i) with (F + (32 + i)) by lia. exact Y. }
assert (FM32 : F mod 32 = 0).
{ pose proof G as G'. destruct G' as [Hk SPTg SLOg SHIg SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS]. exact F32. }
assert (F32m : (F + 32) mod 8 = 0).
{ replace (F + 32) with ((F / 8 + 4) * 8) by (pose proof (Z.div_mod F 8 ltac:(lia)); pose proof (mod32_d F 8 ltac:(exists 4; reflexivity) ltac:(lia) FM32); lia). apply Z_mod_mult. }
pose proof FSH1 as (_ & _ & _ & _ & SH4' & _).
assert (BZ : byte_at M1 (HeapIfaceA.S (F + 32)) 1).
{ unfold HeapIfaceA.S, SB, byte_at. replace ((F + 32) / 8 + 2147450880) with (F / 8 + 2147450884).
- apply (L5ADHR.byte_of_u8 M1 _ 1 SH4'); lia.
- replace (F + 32) with (4 * 8 + F) by lia. rewrite Z.div_add_l by lia. lia. }
pose proof (vf_opF false 0 MV VF) as OPF.
pose proof (PMBBK.frame_geo fb) as (Eop & Eois & _).
pose proof SRD as SRD'. unfold PMB.src_read_spec, PMSPA.src_read_spec in SRD'. cbn [pa_src_read PMB.AD ADDR_B] in SRD'.
apply (call_src 0xb065c 4 (PMSPA.read_args AD) PMSPA.read_W PMSPA.read_res SRD' true s sm e fx1 R1 M1 model1 LKc crc Ac 0xb224c [(F + 32, 1)] BS1 B1
ltac:(apply pow_bnd_ra; [lia| reflexivity]) Z2 Z3 Z4 B10 ltac:(lia)).
- unfold PMSPA.read_args. exists (F + 32), 1. split; [rewrite L5SAR.r11; exact B11|]. split; [rewrite L5K.rl12; exact B12|].
split; [unfold PM.CHUNK; lia|]. left.
split; [exists (F, 0, S - 160 + 32); split; [left; reflexivity| cbn [ff_addr ff_class fst snd]; change (ff_bytes 0) with 64; lia]|].
split; [lia|]. split; [exact DT|].
split; [intros a Ha; right; exists 1; split; [replace a with (F + 32) by lia; exact BZ| split; [lia| replace a with (F + 32) by lia; rewrite F32m; lia]]|].
pose proof (fap_of _ M1 model1 LKc crc Ac BI1) as FAP.
split; [destruct FAP as [Y|Y]; [left| right]; lia| destruct FAP as [Y|Y]; [left| right]; lia].
- unfold PMSPA.read_W. exists (F + 32), 1. split; [rewrite L5SAR.r11; exact B11|]. split; [rewrite L5K.rl12; exact B12|]. split; [lia|]. split; [lia| reflexivity].
- intros rr [<-|[]]. cbn [fst snd]. lia.
- intros fx2 R2 M2' model2' LK2' Aw2 src2 sm2 RP2 RES2 _ BS2.
destruct RES2 as (p & k & d & Yp & Yk & Hp & Hk & Yd & Hd & _).
assert (Ek : k = 1) by (apply (reg_lit R1 12 k 1); [rewrite L5K.rl12 in Yk; exact Yk| exact B12| unfold PM.CHUNK in Hk; lia| lia]).
subst k. rewrite L5K.rl10 in Yd.
apply (t2_stage (PMSPA.with_src s src2) sm2 e fx2 R2 M2' model2' LK2' crc Aw2 d DEP BS2 (tregs_keep R1 R2 MR1 RP2) Yd). lia.
Qed.
End Frame.
End Call.
End WithHeap.
End PMBBA5.
