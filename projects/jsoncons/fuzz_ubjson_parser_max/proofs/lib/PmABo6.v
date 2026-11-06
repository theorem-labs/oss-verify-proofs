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
PmModelFactsA PmStepA PmStep PmParStep PmParKit PmASrcKit PmAParKit PmAReset1 PmAUarK PmAUar PmAUarKS PmABoK PmABoK2 PmABoK3 Ja0_code_b1370_b1374 PmABo1 PmABoP1 PmABoP2 PmABoP3 PmABoP4 PmABo2 PmABo3 PmABo4 PmCertKitG PmABo5.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmABo6 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmABo2.PMABO2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmABoK.PMABOK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0Ac"; "0Aw0"; "1bool"; "1false"; "1list"; "1option"; "1prod"; "2and"; "2eq"; "2ex"; "2or"; "3Z"; "0F"; "0FF"; "0HI"; "0K"]; ["0L"; "0LBX"; "0LK0"; "0LKc"; "4Model"; "5bvmap"; "0M0"; "0Mc"; "0R"; "0R0"; "6credit"; "7fframe"; "8SCFG"; "9mregs"; ":bst"; ";p_depth"]; [";pst"; ";strm"; "<cfg"; "=FPState"; "=getr"; ">srealizes"; "?loaded_segments"; "0S"; "0SCFG_P"; "@le"; "@lt"; "@of_nat"; "0ar"; "0c"; "0cat"; "0cr0"]; ["0crc"; "0e"; "0e0"; "0fb"; "0fx"; "0model0"; "0modelc"; "0s"; "0s0"; "0sm"; "0sm0"; "AZ_to_bv"; "Abv"; "0str"]]).
Local Ltac lia := L5FastLia.plia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PMABO6.
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
Local Abbreviation SCR := PMABOK.SCR.
Local Abbreviation BARR := PMABOK.BARR.
Local Abbreviation op := (PMABOK.op fb).
Local Abbreviation ois := (PMABOK.ois fb).
Local Abbreviation ov := (PMABOK.ov fb).
Local Abbreviation oec := (PMABOK.oec fb).
Local Abbreviation WR := (PMABOK.WR fb).
Local Abbreviation U := (PMABOK.U R0).
Local Abbreviation ocell := (PMABOK.ocell S).
Local Abbreviation own := (PMABOK.own R0 S).
Local Abbreviation own_agree := (PMABOK.own_agree R0 S).
Local Abbreviation sd := (PMABOK.sd s0).
Local Abbreviation sdl := (PMABOK.sdl s0).
Local Abbreviation spush := (PMABOK.spush s0).
Local Abbreviation frame_geo := (PMABOK.frame_geo fb).
Section Frame.
Variables (F fl : Z) (LK2 : list fframe) (M2 : word -> option byte) (model2 : Model).
Hypothesis G : PMAUK.gctx L ar HI LBX FF LK0 Aw0 S SCR (S - 128) (S - 104) S ocell own F fl 0 LK2 M2 model2 cr0 (PM.parser_own s0).
Local Abbreviation FF' := (PMABOK.FF' FF S F).
Local Abbreviation binv' := (PMABOK.binv' L ar HI R0 M0 model0 LBX FF LK0 Aw0 S fb F).
Local Abbreviation hdr := (PMABOK.hdr S F).
Local Abbreviation fsh := (PMABOK.fsh F).
Local Abbreviation bst := (PMABOK.bst L ar HI R0 M0 model0 LBX FF LK0 Aw0 cr0 S fb cat s0 str sm0 e0 F).
Local Abbreviation bste := (PMABOK.bste L ar HI R0 M0 model0 LBX FF LK0 Aw0 cr0 S fb s0 str sm0 F).
Local Abbreviation vfacts := (PMABOK.vfacts R0 S fb F fl).
Local Abbreviation vpack := (PMABOK.vpack L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE PMI PMS PMSU F fl LK2 M2 model2 G).
Local Abbreviation centry := (PMABOK.centry L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE PMI PMS PMSU F fl LK2 M2 model2 G).
Local Abbreviation own_with_src := PMABOK.own_with_src.
Local Abbreviation call_src := (PMABOK.call_src L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE PMI PMS PMSU F fl LK2 M2 model2 G).
Local Abbreviation call_mkec := (PMABOK.call_mkec L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE PMI PMS PMSU F fl LK2 M2 model2 G).
Local Abbreviation fsh_nc := (PMABOK2.fsh_nc L ar C HI HIok R0 LBX FF LK0 Aw0 cr0 S s0 F fl LK2 M2 model2 G).
Local Abbreviation fsh_agree := (PMABOK2.fsh_agree S F).
Local Abbreviation step_piece := (PMABOK2.step_piece L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE PMI PMS PMSU F fl LK2 M2 model2 G).
Local Abbreviation wr_rng := (PMABOK2.wr_rng fb).
Local Abbreviation bsterr := (PMABOK2.bsterr L ar HI R0 M0 model0 LBX FF LK0 Aw0 cr0 S fb s0 str sm0 F).
Local Abbreviation call_gl := (PMABOK2.call_gl L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE PMI PMS PMSU F fl LK2 M2 model2 G).
Local Abbreviation push_st := PMABOK3.push_st.
Local Abbreviation aacc_sub := PMABOK3.aacc_sub.
Local Abbreviation parser_push_updA := PMABOK3.parser_push_updA.
Local Abbreviation stack_shape_push := PMABOK3.stack_shape_push.
Local Abbreviation ri_swap12 := (PMABOK3.ri_swap12 L ar C HI HIok).
Local Abbreviation stk_credit := (PMABOK3.stk_credit L ar C LY).
Local Abbreviation bstp := (PMABOK3.bstp L ar HI R0 M0 model0 LBX FF LK0 Aw0 cr0 S fb cat s0 str sm0 e0 F).
Local Abbreviation call_push := (PMABOK3.call_push L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE PMI PMS PMSU F fl LK2 M2 model2 G).
Local Abbreviation fin_any := (PMABO1.fin_any L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE PMI PMS PMSU F fl LK2 M2 model2 G).
Local Abbreviation mregs0 := (PMABO2.mregs0 R0 S fb F).
Local Abbreviation mregs := (PMABO2.mregs R0 S fb F).
Local Abbreviation tregs := (PMABO2.tregs R0 S fb F).
Local Abbreviation UB := (PMABO2.UB R0).
Local Abbreviation mk_Z1 := (PMABO2.mk_Z1 L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE PMI PMS PMSU F fl LK2 M2 model2 G).
Local Abbreviation mk_Z2 := (PMABO2.mk_Z2 L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE PMI PMS PMSU F fl LK2 M2 model2 G).
Local Abbreviation mk_Z11 := (PMABO2.mk_Z11 L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE PMI PMS PMSU F fl LK2 M2 model2 G).
Local Abbreviation mk_Zc := (PMABO2.mk_Zc L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE PMI PMS PMSU F fl LK2 M2 model2 G).
Local Abbreviation mk_Zt := (PMABO2.mk_Zt L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE PMI PMS PMSU F fl LK2 M2 model2 G).
Local Abbreviation mk_Zt13 := (PMABO2.mk_Zt13 L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE PMI PMS PMSU F fl LK2 M2 model2 G).
Local Abbreviation gl_err_C := (PMABO2.gl_err_C L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE PMI PMS PMSU F fl LK2 M2 model2 G).
Local Abbreviation gl_err_T := (PMABO2.gl_err_T L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE PMI PMS PMSU F fl LK2 M2 model2 G).
Local Abbreviation tail_I := (PMABO3.tail_I L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE PMI PMS PMSU F fl LK2 M2 model2 G).
Local Abbreviation tail_C := (PMABO3.tail_C L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE PMI PMS PMSU F fl LK2 M2 model2 G).
Local Abbreviation tail_T := (PMABO3.tail_T L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE PMI PMS PMSU F fl LK2 M2 model2 G).
Local Abbreviation mregs0_keep := (PMABO2.mregs0_keep R0 S fb F).
Local Abbreviation mregs_keep := (PMABO2.mregs_keep R0 S fb F).
Local Abbreviation tregs_keep := (PMABO2.tregs_keep R0 S fb F).
Local Abbreviation vf_rng := (PMABO2.vf_rng R0 S fb F fl).
Local Abbreviation op8_apart := (PMABO2.op8_apart R0 S fb F fl).
Local Abbreviation VT := (PMABO3.VT R0 S fb F fl).
Local Abbreviation vf_fsh := (PMABO4.vf_fsh R0 S fb F fl).
Local Abbreviation vf_fb := (PMABO4.vf_fb R0 S fb F fl).
Local Abbreviation mi_vis := (PMABO4.mi_vis L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE PMI PMS PMSU F fl LK2 M2 model2 G).
Local Abbreviation stk_bz := (PMABO4.stk_bz L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE PMI PMS PMSU F fl LK2 M2 model2 G).
Local Abbreviation stk_cell := (PMABO4.stk_cell L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE PMI PMS PMSU F fl LK2 M2 model2 G).
Local Abbreviation modsub := PMABO4.modsub.
Local Abbreviation mod32_d := PMABO4.mod32_d.
Local Abbreviation sp_mod := (PMABO4.sp_mod S SP32).
Local Abbreviation pow_bnd_ra := PMABO4.pow_bnd_ra.
Local Abbreviation c_stage := (PMABO4.c_stage L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE PMI PMS PMSU F fl LK2 M2 model2 G).
Local Abbreviation VK := (PMABO4.VK R0 S fb F fl).
Local Abbreviation i_stage := (PMABO4.i_stage L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE PMI PMS PMSU F fl LK2 M2 model2 G).
Local Abbreviation tregs0 := (PMABO2.tregs0 R0 S fb F).
Local Abbreviation tregs0_keep := (PMABO2.tregs0_keep R0 S fb F).
Local Abbreviation tregs0_of := (PMABO2.tregs0_of R0 S fb F).
Ltac vopen VF := unfold PMABOK.vfacts, PMABOK.hdr, PMABOK.own, PMABOK.fsh in VF; cbn iota in VF; decompose [and] VF; clear VF.
Ltac hx := match goal with |- ?G => match goal with H : G |- _ => exact H end end.
Ltac vfeed := first [ hx | (split; hx) | apply UB | (unfold PMABOP1.aligned; hx) | (unfold PMABOP2.aligned; hx) | (unfold PMABOP3.aligned; hx) | (unfold PMABOP4.aligned; hx) ].
Ltac vfeedV VF := first [ assumption | apply UB | unfold PMABOP1.aligned; assumption | unfold PMABOP2.aligned; assumption | unfold PMABOP3.aligned; assumption | unfold PMABOP4.aligned; assumption
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
Local Abbreviation t4_stage := (PMABO5.t4_stage L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE PMI PMS PMSU F fl LK2 M2 model2 G).
Local Abbreviation t3_stage := (PMABO5.t3_stage L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE PMI PMS PMSU F fl LK2 M2 model2 G).
Local Abbreviation t2_stage := (PMABO5.t2_stage L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE PMI PMS PMSU F fl LK2 M2 model2 G).
Local Abbreviation t1_stage := (PMABO5.t1_stage L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE PMI PMS PMSU F fl LK2 M2 model2 G).
Local Abbreviation fap_of := (PMABO5.fap_of L ar C HI HIok R0 M0 model0 LBX FF LK0 Aw0 cr0 S fb s0 FOK F fl LK2 M2 model2 G).
Local Abbreviation vf_opF := (PMABO5.vf_opF R0 S fb F fl).
Local Abbreviation reg_lit := PMABO5.reg_lit.
Ltac mregs_ks KS := unfold PMABO2.tregs, PMABO2.tregs0, PMABO2.mregs, PMABO2.mregs0; repeat split; first [ hx | (rewrite (KS _) by inl; hx) ].
Ltac mid0 conc V typed VF BS s sm e Mc modelc LKc crc Ac MV fx R pc pc1 :=
let BI := fresh "BI" in let RUN := fresh "RUN" in let EC := fresh "EC" in let HD := fresh "HD" in let FSH := fresh "FSH" in
let STEP := fresh "STEP" in let E0 := fresh "E0" in let SD := fresh "SD" in let CRL := fresh "CRL" in let CRK := fresh "CRK" in
pose proof BS as (BI & RUN & EC & HD & FSH & STEP & E0 & SD & CRL & CRK);
let P := fresh "P" in pose proof (conc fx R MV V) as P; unfold PMABO3.VT in P; cbn beta iota in P; feedV P VF;
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
Lemma kdisp2 : ltac2:(TCodec.tc2 tcn__PmABo6 "SA'Q0'Q1'2'Q3&Ey5'QLyR0%211%5241'5y8%611%311p061'D'4&K%211&J'6';%2211%711&Q9&OvQH%211+oO%5221&Nv@vQ<v>vIvFvQEvAv=vBv1vQ?vQ7vQCvQ>vQMvQJvQBv<(3r;r:r9r6r5r4r3r2%LLKJIHGFEDCBA@?>Q0=<;:987654321&Mr8%25KCB=1':'8&Q4&QK&Q;u:%211%42R01%62B1+X0%72R11%:3R131'9'7zr1%QF221&Q:%1239%6231%B2O=%B2R<6%E3R<21%:241qRLR11%=2R21%J2?1'Q5&Q6&LvQ8%211&Q2+fTW@%266Q>Q=1Q<Q4v?%948521p0;1p0Q71p0Q;1p0R91p2R@1pS2RE1pQ8RG1pS>RK1pQ@RM1pQBS31pS:S:1pS4S<1pSDS>1pS@S@1").
Proof using All. intros s sm e fx R Mc modelc LKc crc Ac.
intros DEP BS MR A10. pose proof MR as ((X2 & X8 & X9 & X18 & X19 & X20 & X21 & X25 & X26 & X27 & X3 & X4) & X23).
pose proof BS as (BI & RUN & EC & HD & FSH & STEP & E0 & SD & CRL & CRK).
pose proof (vpack false _ s sm e 0 cat Mc modelc LKc crc Ac BI RUN EC HD FSH) as VF.
set (MV := mrestrict (ahid Ac modelc) Mc) in *.
destruct A10 as [A10|(c & Hc & A10)].
-
mid0 PMABOP1.aboK2e_conc (VT 0 0) false VF BS s sm e Mc modelc LKc crc Ac MV fx R 0xb10f0 0xae974.
assert (MR1 : mregs R1) by mregs_ks KS1.
assert (B1 : getr R1 (reg 1) = Z_to_bv 64 0xb1474) by hx. assert (B10 : getr R1 (reg 10) = Z_to_bv 64 oec) by hx. assert (B11 : getr R1 (reg 11) = Z_to_bv 64 1) by hx.
exact (mk_Z2 s sm e fx1 R1 M1 model1 LKc crc Ac 1 BS1 MR1 B1 B10 B11 ltac:(lia)).
- assert (Hcb : 0 <= c < 2 ^ 64) by lia.
destruct (Z.eq_dec c 35) as [E35|N35].
+
subst c. mid0 PMABOP1.aboK2h_conc (VT 0 0) false VF BS s sm e Mc modelc LKc crc Ac MV fx R 0xb10f0 0xaea50.
assert (MR1 : mregs R1) by mregs_ks KS1.
assert (B1 : getr R1 (reg 1) = Z_to_bv 64 0xb1110) by hx. assert (B10 : getr R1 (reg 10) = Z_to_bv 64 (op + 24)) by hx. assert (B11 : getr R1 (reg 11) = Z_to_bv 64 1) by hx.
pose proof MR1 as ((Y2 & Y8 & Y9 & Y18 & Y19 & Y20 & Y21 & Y25 & Y26 & Y27 & Y3 & Y4) & Y23).
pose proof IGN as IGN'. unfold PMA.ignore_spec, PMSPA.ignore_spec in IGN'. cbn [pa_ignore PMA.AD ADDR_A] in IGN'.
apply (call_src 0xaea50 4 PMSPA.ignore_args PMSPA.no_W PMSPA.ignore_res IGN' false s sm e fx1 R1 M1 model1 LKc crc Ac 0xb1110 [] BS1 B1
ltac:(apply pow_bnd_ra; [lia| reflexivity]) Y2 Y3 Y4 B10 ltac:(lia)).
* unfold PMSPA.ignore_args. rewrite L5SAR.r11. exact B11.
* reflexivity.
* intros rr [].
* intros fx2 R2 M2' model2' LK2' Aw2 src2 sm2 RP2 _ _ BS2.
exact (c_stage (PMSPA.with_src s src2) sm2 e fx2 R2 M2' model2' LK2' crc Aw2 DEP BS2 (mregs_keep R1 R2 MR1 RP2)).
+
exact (i_stage s sm e fx R Mc modelc LKc crc Ac c DEP BS MR A10 ltac:(lia)).
Qed.
Lemma kdisp : ltac2:(TCodec.tc2 tcn__PmABo6 "SA'Q0'Q1'2'Q3&Ey5'QLyR0%211%5241'5y8%611%311p061'D'4&K%211&J'6';%2211%711&Q9&OvQH%211+oO%5221&Nv@vQ<v>vIvFvQEvAv=vBv1vQ?vQ7vQCvQ>vQMvQJvQBv<(3r;r:r9r6r5r4r3r2%LLKJIHGFEDCBA@?>Q0=<;:987654321&Mr8%25KCB=1':'8&Q4&QK&Q;u:%211%42R01%62B1+X0%72R11%:3R131'9'7zr1%QF221&Q:%1239%6231%B2O=%B2R<6%E3R<21%:241qRLR11%=2R21%J2?1'Q5&Q6&LvQ8%211&Q2+fTP@%266Q>Q=1Q<Q4v?%948521p0;1p0Q71p0Q;1p0R91p2R@1pS2RE1pQ8RG1pS>RK1pQ@RM1pQBS31pS:S:1pS4S<1pSDS>1pS@S@1").
Proof using All. intros s sm e fx R Mc modelc LKc crc Ac.
intros DEP BS MR A10. pose proof MR as ((X2 & X8 & X9 & X18 & X19 & X20 & X21 & X25 & X26 & X27 & X3 & X4) & X23).
pose proof BS as (BI & RUN & EC & HD & FSH & STEP & E0 & SD & CRL & CRK).
pose proof (vpack false _ s sm e 0 cat Mc modelc LKc crc Ac BI RUN EC HD FSH) as VF.
set (MV := mrestrict (ahid Ac modelc) Mc) in *.
destruct A10 as [A10|(c & Hc & A10)].
-
mid0 PMABOP1.aboKe_conc (VT 0 0) false VF BS s sm e Mc modelc LKc crc Ac MV fx R 0xb1010 0xae974.
assert (MR1 : mregs R1) by mregs_ks KS1.
assert (B1 : getr R1 (reg 1) = Z_to_bv 64 0xb1448) by hx. assert (B10 : getr R1 (reg 10) = Z_to_bv 64 oec) by hx. assert (B11 : getr R1 (reg 11) = Z_to_bv 64 1) by hx.
exact (mk_Z1 s sm e fx1 R1 M1 model1 LKc crc Ac 1 BS1 MR1 B1 B10 B11 ltac:(lia)).
- assert (Hcb : 0 <= c < 2 ^ 64) by lia.
destruct (Z.eq_dec c 36) as [E36|N36].
+
subst c. mid0 PMABOP1.aboKd_conc (VT 0 0) false VF BS s sm e Mc modelc LKc crc Ac MV fx R 0xb1010 0xaea50.
assert (MR1 : tregs R1) by mregs_ks KS1.
assert (B1 : getr R1 (reg 1) = Z_to_bv 64 0xb1038) by hx. assert (B10 : getr R1 (reg 10) = Z_to_bv 64 (op + 24)) by hx. assert (B11 : getr R1 (reg 11) = Z_to_bv 64 1) by hx.
pose proof MR1 as (((Y2 & Y8 & Y9 & Y18 & Y19 & Y20 & Y21 & Y25 & Y26 & Y27 & Y3 & Y4) & Y23) & Y22 & Y24).
pose proof IGN as IGN'. unfold PMA.ignore_spec, PMSPA.ignore_spec in IGN'. cbn [pa_ignore PMA.AD ADDR_A] in IGN'.
apply (call_src 0xaea50 4 PMSPA.ignore_args PMSPA.no_W PMSPA.ignore_res IGN' false s sm e fx1 R1 M1 model1 LKc crc Ac 0xb1038 [] BS1 B1
ltac:(apply pow_bnd_ra; [lia| reflexivity]) Y2 Y3 Y4 B10 ltac:(lia)).
* unfold PMSPA.ignore_args. rewrite L5SAR.r11. exact B11.
* reflexivity.
* intros rr [].
* intros fx2 R2 M2' model2' LK2' Aw2 src2 sm2 RP2 _ _ BS2.
exact (t1_stage (PMSPA.with_src s src2) sm2 e fx2 R2 M2' model2' LK2' crc Aw2 DEP BS2 (tregs_keep R1 R2 MR1 RP2)).
+
assert (PK2 : forall (fx1 : FPState) R1 M1 model1, bst false s sm e M1 model1 LKc crc Ac -> mregs R1 ->
getr R1 (reg 1) = Z_to_bv 64 0xb10f0 -> getr R1 (reg 10) = Z_to_bv 64 (op + 24) ->
srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx1 R1 0xae850 M1 model1) K).
{ intros fx1 R1 M1 model1 BS1 MR1 B1 B10.
pose proof MR1 as ((Y2 & Y8 & Y9 & Y18 & Y19 & Y20 & Y21 & Y25 & Y26 & Y27 & Y3 & Y4) & Y23).
pose proof PEEK as PEEK'. unfold PMA.peek_spec, PMSPA.peek_spec in PEEK'. cbn [pa_peek PMA.AD ADDR_A] in PEEK'.
apply (call_src 0xae850 4 PMSPA.no_args PMSPA.no_W PMSPA.peek_res PEEK' false s sm e fx1 R1 M1 model1 LKc crc Ac 0xb10f0 [] BS1 B1
ltac:(apply pow_bnd_ra; [lia| reflexivity]) Y2 Y3 Y4 B10 ltac:(lia)).
- exact I.
- reflexivity.
- intros rr [].
- intros fx2 R2 M2' model2' LK2' Aw2 src2 sm2 RP2 RES _ BS2.
apply (kdisp2 (PMSPA.with_src s src2) sm2 e fx2 R2 M2' model2' LK2' crc Aw2 DEP BS2 (mregs_keep R1 R2 MR1 RP2)).
destruct RES as (_ & [Y|(c2 & Hc2 & Y & _)]); [left; rewrite <- L5K.rl10; exact Y| right; exists c2; split; [exact Hc2| rewrite <- L5K.rl10; exact Y]]. }
destruct (Z_le_gt_dec c 35) as [Hl|Hu].
* assert (Hcl : 0 <= c <= 35) by lia.
mid0 PMABOP1.aboKl_conc (fun j : nat => match j with 39%nat => c | _ => VT 0 0 j end) false VF BS s sm e Mc modelc LKc crc Ac MV fx R 0xb1010 0xae850.
assert (MR1 : mregs R1) by mregs_ks KS1.
exact (PK2 fx1 R1 M1 model1 BS1 MR1 ltac:(hx) ltac:(hx)).
* assert (Hcu : 37 <= c <= 255) by lia.
mid0 PMABOP1.aboKu_conc (fun j : nat => match j with 39%nat => c | _ => VT 0 0 j end) false VF BS s sm e Mc modelc LKc crc Ac MV fx R 0xb1010 0xae850.
assert (MR1 : mregs R1) by mregs_ks KS1.
exact (PK2 fx1 R1 M1 model1 BS1 MR1 ltac:(hx) ltac:(hx)).
Qed.
End Frame.
End Call.
End WithHeap.
End PMABO6.
