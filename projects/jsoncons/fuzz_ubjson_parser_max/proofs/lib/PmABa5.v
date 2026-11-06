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
PmModelFactsA PmStepA PmStep PmParStep PmParKit PmASrcKit PmAParKit PmAReset1 PmAUarK PmAUar PmAUarKS PmABaK PmABaK2 PmABaK3 Ja0_code_b0cfc_b0d00 PmABa1 PmABaP1 PmABaP2 PmABa2 PmABa3 PmABa4 PmCertKitG.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmABa5 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmABa2.PMABA2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmABaK.PMABK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0Ac"; "0Aw0"; "0BX"; "1bool"; "1false"; "1list"; "1nat"; "1option"; "1prod"; "1true"; "2and"; "2eq"; "2ex"; "2or"; "3Z"; "0F"]; ["0FF"; "0HI"; "0K"; "0L"; "0LBX"; "0LK0"; "0LKc"; "4Model"; "5bvmap"; "0M0"; "0MV"; "0Mc"; "0R"; "0R0"; "6credit"; "7fframe"]; ["8SCFG"; "9tregs"; ":binv'"; ":bst"; ":op"; ":vfacts"; ";p_depth"; ";pst"; ";strm"; "<cfg"; "=FPState"; "=getr"; ">srealizes"; "?loaded_segments"; "0S"; "0SCFG_P"]; ["@add"; "@le"; "@lt"; "@of_nat"; "@pow"; "0a"; "0ar"; "0b"; "0c"; "0cat"; "0cr0"; "0crc"; "0d"; "0e"; "0e0"; "0fb"]; ["0fl"; "0fx"; "0model0"; "0modelc"; "0s"; "0s0"; "0sm"; "0sm0"; "AZ_to_bv"; "Abv"; "0str"; "0typed"; "0v"; "0x"]]).
Local Ltac lia := L5FastLia.plia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PMABA5.
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
Lemma vf_opF : ltac2:(TCodec.tc2 tcn__PmABa5 "Q4'3'>'R9yR0%211'7y8%511%311p051&Q5vMvQ>vQOv?vR0r3r2r1%9887654321'=&QA&Q@&Q4%11;+\0%4221%621=+R0%72?1%9216%;241p0=1pQFH1pTJQ11pTHQ31").
Proof. intros typed v MV. intros VF. unfold PMABK.vfacts in VF. destruct VF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _). exact X. Qed.
Ltac bst_of BI RUN EC HD FSH STEP E0 SD CRL CRK :=
split; [exact BI|]; split; [exact RUN|]; split; [exact EC|]; split; [exact HD|]; split; [exact FSH|]; split; [exact STEP|]; split; [exact E0|];
split; [exact SD|]; split; [exact CRL| exact CRK].
Lemma fap_of : ltac2:(TCodec.tc2 tcn__PmABa5 "QG'5'8'>%2211%411'R9yR0%211'7y8%511%311p051'G&O%?11&N&Q2vCvQFvAvMvIvR2vDv@vEv1vQ>vQOv?r6r5r4r3r2r1%DCCBA@?>=<;:987654321'=&QA&Q@+R0%22<1%421>+QP0%52@1%721@%9241p0;1p2Q=1pSHQ21pQ>Q41pT8Q71pQHQ91p6QB1").
Proof using G HIok FOK. intros BX Mc modelc LKc crc Ac.
intros BI. pose proof BI as (HHc & _). pose proof FOK as ((rs & Hfb) & Fal).
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHc) as (WB & WF & _).
destruct (WF (F, 0, S - 128 + 32) (or_introl eq_refl)) as (_ & _ & _ & _ & _ & APF). cbn [ff_addr ff_class fst snd] in APF. change (ff_bytes 0) with 64 in APF.
assert (Iin : In (fb, 4, rs) (ff_remove F FF' ++ LKc)).
{ apply in_or_app. left. unfold PMABK.FF'. cbn [ff_remove ff_addr]. rewrite Z.eqb_refl. exact Hfb. }
destruct (APF _ Iin) as [X0|X0]; cbn [ff_addr ff_class fst snd] in X0; change (ff_bytes 4) with 1024 in X0; [left| right]; lia.
Qed.
Ltac mregs_ks KS := unfold PMABA2.tregs, PMABA2.tregs0, PMABA2.mregs, PMABA2.mregs0; repeat split; (rewrite (KS _) by inl; hx).
Lemma t4_stage : ltac2:(TCodec.tc2 tcn__PmABa5 "RF'Q7'Q8'3'Q:&Hy5'R9yR0%211%5241'7y8%611%311p061'G'5&O%211&N'8'>%2211%711&QA&Q6vR5%211+oO%5221&Q3vCvQFvAvMvIvR2vDv@vEv1vQJvQ>vQOvQIvR:vR7vQNv?(9r;r:r9r6r5r4r3r2%LLKJIHGFEDCBA@?>Q0=<;:987654321&Q1r8%25KCB=1'Q<&Q=&Q0vQ?%211&Q9+fRa0r7%367CB2:1vB%:49621p0<1p0@1p0Q>1p2QE1pSHQJ1pQ>QL1pT8R01pQHR21pQJR81pT4R?1pSLRA1pT>RC1pT:RE1").
Proof using All. intros s sm e fx R Mc modelc LKc crc Ac.
intros DEP BS MR. pose proof MR as (((X2 & X8 & X9 & X18 & X19 & X20 & X21 & X25 & X26 & X27 & X3 & X4) & X23) & X22 & X24).
pose proof BS as (BI & RUN & EC & HD & FSH & STEP & E0 & SD & CRL & CRK).
pose proof (vpack true _ s sm e 0 cat Mc modelc LKc crc Ac BI RUN EC HD FSH) as VF.
set (MV := mrestrict (ahid Ac modelc) Mc) in *.
pose proof (PMABAP2.abaT4_conc fx R MV (VT 0 0)) as P. unfold PMABA3.VT in P. cbn beta iota in P. feedV P VF.
destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & PR). decompose [and] PR. clear PR.
pose proof (vf_fb true 0 MV VF) as (DF1 & DF2).
apply (step_piece true s sm e 0 cat fx fx1 R 0xb0a20 R1 0xafe2c M1v Mc modelc LKc crc Ac (fun _ => False) BI RUN EC HD MS1 MG1).
{ intros a Ha _. apply FRZ1. exact Ha. }
{ intros a []. }
{ apply (fsh_agree true MV M1v); [intros a Ha; apply FRZ1; lia| exact DF1| exact DF2| exact (vf_fsh true 0 MV VF)]. }
intros M1 model1 BI1 RUN1 EC1 HD1 FSH1 VIS1 HID1 FR1.
assert (BS1 : bst true s sm e M1 model1 LKc crc Ac) by (bst_of BI1 RUN1 EC1 HD1 FSH1 STEP E0 SD CRL CRK).
assert (MR1 : tregs R1) by mregs_ks KS1.
assert (A1 : getr R1 (reg 1) = Z_to_bv 64 0xb0a2c) by hx.
assert (A10 : getr R1 (reg 10) = Z_to_bv 64 op) by hx.
assert (A11 : getr R1 (reg 11) = Z_to_bv 64 oec) by hx.
pose proof MR1 as (((Y2 & Y8 & Y9 & Y18 & Y19 & Y20 & Y21 & Y25 & Y26 & Y27 & Y3 & Y4) & Y23) & Y22 & Y24).
apply (call_gl true s sm e fx1 R1 M1 model1 LKc crc Ac 0xb0a2c BS1 A1 ltac:(apply pow_bnd_ra; [lia| reflexivity]) Y2 Y3 Y4 A10 A11).
intros fx2 R2 M2' model2' LK2' Aw2 s2 sm2 e2 cr2 RP2 OUT2.
pose proof (tregs_keep R1 R2 MR1 RP2) as MR2.
destruct OUT2 as [(BS2 & UN2 & (len & Hlen & A10'))|BE2].
2: { exact (gl_err_T s2 sm2 fx2 R2 M2' model2' LK2' cr2 Aw2 BE2 MR2). }
pose proof BS2 as (BI2 & RUN2 & EC2 & HD2 & FSH2 & STEP2 & E02 & SD2 & CRL2 & CRK2).
pose proof (vpack true _ s2 sm2 e2 0 cat M2' model2' LK2' cr2 Aw2 BI2 RUN2 EC2 HD2 FSH2) as VF2.
pose proof (mi_vis _ s2 sm2 e2 M2' model2' LK2' cr2 Aw2 BI2 RUN2) as MI2.
set (MV2 := mrestrict (ahid Aw2 model2') M2') in *.
pose proof MR2 as (((Z2 & Z8 & Z9 & Z18 & Z19 & Z20 & Z21 & Z25 & Z26 & Z27 & Z3 & Z4) & Z23) & Z22 & Z24).
pose proof (vf_fb true 0 MV2 VF2) as (DF1b & DF2b). pose proof (vf_rng true 0 MV2 VF2) as (Rop & RS & RF & Rfl).
destruct (Z_le_gt_dec len 16777216) as [Le|Gt].
-
assert (HL2 : 0 <= len <= 16777216) by lia.
pose proof (PMABAP2.abaTf_conc fx2 R2 MV2 (VT 0 len)) as P. unfold PMABA3.VT in P. cbn beta iota in P. feedV P VF2.
destruct P as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & PR). decompose [and] PR. clear PR.
apply (step_piece true s2 sm2 e2 0 cat fx2 fx3 R2 0xb0a2c R3 0xb1920 M3v M2' model2' LK2' cr2 Aw2 (fun a => S - 116 <= a < S - 104) BI2 RUN2 EC2 HD2 MS3 MG3).
{ intros a Ha N. apply FRZ3; [exact Ha| intros X; apply N; lia]. }
{ intros a X. left. lia. }
{ apply (fsh_agree true MV2 M3v); [intros a Ha; apply FRZ3; [lia| intros X; unfold SB in *; lia]| exact DF1b| exact DF2b| exact (vf_fsh true 0 MV2 VF2)]. }
intros M3 model3 BI3 RUN3 EC3 HD3 FSH3 VIS3 HID3 FR3.
assert (BS3 : bst true s2 sm2 e2 M3 model3 LK2' cr2 Aw2) by (bst_of BI3 RUN3 EC3 HD3 FSH3 STEP2 E02 SD2 CRL2 CRK2).
destruct (stk_cell _ M3 model3 LK2' cr2 Aw2 (S - 116) 4 BI3 ltac:(lia) ltac:(lia) ltac:(lia)) as (AC1 & BZ1 & AO1 & U1 & _).
destruct (stk_cell _ M3 model3 LK2' cr2 Aw2 (S - 112) 8 BI3 ltac:(lia) ltac:(lia) ltac:(lia)) as (AC2 & BZ2 & AO2 & _ & U2).
rewrite HID3, VIS3 in U1, U2.
assert (C116 : L5.u32_at RSEGS M3 (S - 116) 4) by (apply U1; [hx| reflexivity]).
assert (C112 : L5.u64_at RSEGS M3 (S - 112) len) by (apply U2; [hx| reflexivity]).
assert (MR3 : tregs R3) by mregs_ks KS3.
assert (B1 : getr R3 (reg 1) = Z_to_bv 64 0xb0d1c) by hx.
assert (B10 : getr R3 (reg 10) = Z_to_bv 64 (op + 360)) by hx.
assert (B11 : getr R3 (reg 11) = Z_to_bv 64 (S - 116)) by hx.
assert (B12 : getr R3 (reg 12) = Z_to_bv 64 (S - 112)) by hx.
assert (B13 : getr R3 (reg 13) = Z_to_bv 64 (F + 32)) by hx.
pose proof MR3 as (((W2 & W8 & W9 & W18 & W19 & W20 & W21 & W25 & W26 & W27 & W3 & W4) & W23) & W22 & W24).
pose proof SD2 as (_ & _ & SDp & SDs). pose proof INV as (_ & _ & IDP & _).
pose proof STEP2 as (_ & _ & _ & _ & UN02).
pose proof (PMAUK.vis_facts L ar C HI LYa HIok M0 model0 LBX FF LK0 Aw0 S SCR (S - 128) (S - 104) S ocell own F fl 0 LK2 M2 model2 cr0 (PM.parser_own s0) G WR _ M3 model3 LK2' cr2 Aw2 BI3)
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
unfold PMA.push_msu_spec, PMSAX.push_msu_spec in PMSU. cbn [paa_esp_msu PMA.AAD AADDR_A] in PMSU.
apply (call_push 0xb1920 (PMSAX.cells_msu RSEGS ar) PMSU true s2 sm2 e2 fx3 R3 M3 model3 LK2' cr2 Aw2 0xb0d1c (PM.PS 4 len t 0) BS3 B1
ltac:(apply pow_bnd_ra; [lia| reflexivity]) W2 W3 W4 B10).
+ unfold PMSAX.cells_msu. exists (S - 116), (S - 112), (F + 32), 4, len, t.
split; [rewrite L5SAR.r11; exact B11|]. split; [rewrite L5K.rl12; exact B12|]. split; [rewrite L5K.rl13; exact B13|].
split; [apply sp_mod; [exists 8; reflexivity| lia| reflexivity]|]. split; [apply sp_mod; [exists 4; reflexivity| lia| reflexivity]|].
split; [exact AC1|]. split; [exact AC2|].
split; [intros a Ha; right; exists 1; split; [replace a with (F + 32) by lia; exact BZ3| split; [lia| replace a with (F + 32) by lia; rewrite F32m; lia]]|].
split; [exact AO1|]. split; [exact AO2|].
split; [split; [left; exists (F, 0, S - 128 + 32); split; [left; reflexivity| cbn [ff_addr ff_class fst snd]; change (ff_bytes 0) with 64; lia]
| destruct OPF as [Y|Y]; [right| left]; lia]|].
split; [exact BZ1|]. split; [exact BZ2|]. split; [split; [exact BZ3| exact F32m]|].
split; [exact C116|]. split; [exact C112|]. split; [exact C32|]. split; [lia|]. split; [lia|]. split; [lia| reflexivity].
+ unfold PM.pstate_ok. cbn [PM.ps_type PM.ps_mode PM.ps_len PM.ps_idx]. split; [lia|]. left. split; [unfold PM.mode_counted; right; left; reflexivity|]. unfold PM.MAX_ITEMS. lia.
+ reflexivity.
+ unfold PM.mode_bottom. cbn [PM.ps_mode]. lia.
+ intros _. pose proof STEP as (_ & _ & _ & _ & UN0). lia.
+ unfold PM.MAX_DEPTH. lia.
+ intros fx4 R4 M4 model4 LK4 Aw4 s4 cr4 RP4 BSP4 SRC4 KPR4.
apply (tail_T s4 sm2 e2 fx4 R4 M4 model4 LK4 cr4 Aw4 len BSP4 (tregs_keep R3 R4 MR3 RP4) HL2).
apply (L5C.u64_at_agree RSEGS M3 M4); [intros i Hi; apply KPR4; lia| lia| lia| exact C112].
-
assert (HL2 : 16777217 <= len <= 18446744073709551615) by lia.
pose proof (PMABAP2.abaTx_conc fx2 R2 MV2 (VT 0 len)) as P. unfold PMABA3.VT in P. cbn beta iota in P. feedV P VF2.
destruct P as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & PR). decompose [and] PR. clear PR.
apply (step_piece true s2 sm2 e2 0 cat fx2 fx3 R2 0xb0a2c R3 0xae974 M3v M2' model2' LK2' cr2 Aw2 (fun a => S - 112 <= a < S - 104) BI2 RUN2 EC2 HD2 MS3 MG3).
{ intros a Ha N. apply FRZ3; [exact Ha| intros X; apply N; lia]. }
{ intros a X. left. lia. }
{ apply (fsh_agree true MV2 M3v); [intros a Ha; apply FRZ3; [lia| intros X; unfold SB in *; lia]| exact DF1b| exact DF2b| exact (vf_fsh true 0 MV2 VF2)]. }
intros M3 model3 BI3 RUN3 EC3 HD3 FSH3 VIS3 HID3 FR3.
assert (BS3 : bst true s2 sm2 e2 M3 model3 LK2' cr2 Aw2) by (bst_of BI3 RUN3 EC3 HD3 FSH3 STEP2 E02 SD2 CRL2 CRK2).
assert (MR3 : tregs R3) by mregs_ks KS3.
assert (B1 : getr R3 (reg 1) = Z_to_bv 64 0xb0a70) by hx.
assert (B10 : getr R3 (reg 10) = Z_to_bv 64 oec) by hx.
assert (B11 : getr R3 (reg 11) = Z_to_bv 64 13) by hx.
exact (mk_Zt13 s2 sm2 e2 fx3 R3 M3 model3 LK2' cr2 Aw2 13 BS3 MR3 B1 B10 B11 ltac:(lia)).
Qed.
Lemma reg_lit : ltac2:(TCodec.tc2 tcn__PmABa5 "Q>&Hy5'R9yR0%211%5241'6'>';&Q;r4&R8&QCr3%211%42>1%7261r2%72?1%;3?31r5%91;%;2E1%>231%@3D16':&QAz%221B&QB&QD+2+R0%3221%52H1%:271r6%M3N1Ap031p041p0@1p0F1pS@Q31pS<Q41pTLQ61pQJQ81").
Proof. intros R x a b. intros E1 E2 H1 H2. rewrite E1 in E2. apply (f_equal bv_unsigned) in E2. rewrite !L5.unsigned_lit in E2 by lia. exact E2. Qed.
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
Lemma t3_stage : ltac2:(TCodec.tc2 tcn__PmABa5 "SA'Q7'Q8'3'Q:&Hy5'R9yR0%211%5241'7y8%611%311p061'G'5&O%211&N'8'>%2211%711&QA&Q6vR5%211+oO%5221&Q3vCvQFvAvMvIvR2vDv@vEv1vQJvQ>vQOvQIvR:vR7vQNv?(9r;r:r9r6r5r4r3r2%LLKJIHGFEDCBA@?>Q0=<;:987654321&Q1r8%25KCB=1'=';&Q;&R8&QCu:%211%42R01%62B1+X0%72R11%:3R131'<':zr1%QF221&QB%1239%6231%B2O=%B2R<6%E3R<21%:241qSBR11%=2R21%J2?1'Q<&Q=&Q0vQ?%211&Q9+fR`0%266Q>Q=1Q<Q4vB%948521p0;1p0Q71p0Q;1p0R91p2R@1pSHRE1pQ>RG1pT8RK1pQHRM1pQJS31pT4S:1pSLS<1pT>S>1pT:S@1").
Proof using All. intros s sm e fx R Mc modelc LKc crc Ac.
intros DEP BS MR A10. pose proof MR as (((X2 & X8 & X9 & X18 & X19 & X20 & X21 & X25 & X26 & X27 & X3 & X4) & X23) & X22 & X24).
pose proof BS as (BI & RUN & EC & HD & FSH & STEP & E0 & SD & CRL & CRK).
pose proof (vpack true _ s sm e 0 cat Mc modelc LKc crc Ac BI RUN EC HD FSH) as VF.
set (MV := mrestrict (ahid Ac modelc) Mc) in *.
destruct A10 as [A10|(c & Hc & A10)].
-
mid0 PMABAP2.abaT3e_conc (VT 0 0) true VF BS s sm e Mc modelc LKc crc Ac MV fx R 0xb0a00 0xae974.
assert (MR1 : tregs0 R1) by mregs_ks KS1.
assert (B1 : getr R1 (reg 1) = Z_to_bv 64 0xb0c40) by hx. assert (B10 : getr R1 (reg 10) = Z_to_bv 64 oec) by hx. assert (B11 : getr R1 (reg 11) = Z_to_bv 64 1) by hx.
exact (mk_Zt s sm e fx1 R1 M1 model1 LKc crc Ac 1 BS1 MR1 B1 B10 B11 ltac:(lia)).
- assert (Hcb : 0 <= c < 2 ^ 64) by lia.
destruct (Z.eq_dec c 35) as [E35|N35].
+
subst c. mid0 PMABAP2.abaT3h_conc (VT 0 0) true VF BS s sm e Mc modelc LKc crc Ac MV fx R 0xb0a00 0xaea50.
assert (MR1 : tregs R1) by mregs_ks KS1.
assert (B1 : getr R1 (reg 1) = Z_to_bv 64 0xb0a20) by hx. assert (B10 : getr R1 (reg 10) = Z_to_bv 64 (op + 24)) by hx. assert (B11 : getr R1 (reg 11) = Z_to_bv 64 1) by hx.
pose proof MR1 as (((Y2 & Y8 & Y9 & Y18 & Y19 & Y20 & Y21 & Y25 & Y26 & Y27 & Y3 & Y4) & Y23) & Y22 & Y24).
pose proof IGN as IGN'. unfold PMA.ignore_spec, PMSPA.ignore_spec in IGN'. cbn [pa_ignore PMA.AD ADDR_A] in IGN'.
apply (call_src 0xaea50 4 PMSPA.ignore_args PMSPA.no_W PMSPA.ignore_res IGN' true s sm e fx1 R1 M1 model1 LKc crc Ac 0xb0a20 [] BS1 B1
ltac:(apply pow_bnd_ra; [lia| reflexivity]) Y2 Y3 Y4 B10 ltac:(lia)).
* unfold PMSPA.ignore_args. rewrite L5SAR.r11. exact B11.
* reflexivity.
* intros rr [].
* intros fx2 R2 M2' model2' LK2' Aw2 src2 sm2 RP2 _ _ BS2.
exact (t4_stage (PMSPA.with_src s src2) sm2 e fx2 R2 M2' model2' LK2' crc Aw2 DEP BS2 (tregs_keep R1 R2 MR1 RP2)).
+
assert (Hc' : 0 <= c <= 34 \/ 36 <= c <= 255) by lia.
assert (PK : exists (fx1 : FPState) R1 M1v, mem_grows MV M1v /\ (forall i, 0 <= i < 2 ^ 64 -> M1v (Z_to_bv 64 i) = MV (Z_to_bv 64 i))
/\ msteps RSEGS (L5A.st fx R 0xb0a00 MV) (L5A.st fx1 R1 0xae974 M1v)
/\ (forall x, In x [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 25; 26; 27]%nat -> getr R1 (reg x) = getr R (reg x))
/\ getr R1 (reg 1) = Z_to_bv 64 0xb0c40 /\ getr R1 (reg 10) = Z_to_bv 64 oec /\ getr R1 (reg 11) = Z_to_bv 64 3).
{ destruct Hc' as [Hc'|Hc'].
- pose proof (PMABAP2.abaT3l_conc fx R MV (VK c)) as P. unfold PMABA4.VK, PMABA3.VT in P. cbn beta iota in P. feedV P VF.
destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & PR). decompose [and] PR. clear PR.
exists fx1, R1, M1v. split; [exact MG1|]. split; [exact FRZ1|]. split; [exact MS1|].
split; [intros x Hx; apply KS1; revert x Hx; apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 25; 26; 27]%nat); vm_compute; reflexivity|].
split; [hx|]. split; [hx| hx].
- pose proof (PMABAP2.abaT3u_conc fx R MV (VK c)) as P. unfold PMABA4.VK, PMABA3.VT in P. cbn beta iota in P. feedV P VF.
destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & PR). decompose [and] PR. clear PR.
exists fx1, R1, M1v. split; [exact MG1|]. split; [exact FRZ1|]. split; [exact MS1|].
split; [intros x Hx; apply KS1; revert x Hx; apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 25; 26; 27]%nat); vm_compute; reflexivity|].
split; [hx|]. split; [hx| hx]. }
destruct PK as (fx1 & R1 & M1v & MG1 & FRZ1 & MS1 & KS1 & B1 & B10 & B11).
pose proof (vf_fb true 0 MV VF) as (DF1 & DF2).
apply (step_piece true s sm e 0 cat fx fx1 R 0xb0a00 R1 0xae974 M1v Mc modelc LKc crc Ac (fun _ => False) BI RUN EC HD MS1 MG1).
{ intros a Ha _. apply FRZ1. exact Ha. }
{ intros a []. }
{ apply (fsh_agree true MV M1v); [intros a Ha; apply FRZ1; lia| exact DF1| exact DF2| exact (vf_fsh true 0 MV VF)]. }
intros M1 model1 BI1 RUN1 EC1 HD1 FSH1 VIS1 HID1 FR1.
assert (BS1 : bst true s sm e M1 model1 LKc crc Ac) by (bst_of BI1 RUN1 EC1 HD1 FSH1 STEP E0 SD CRL CRK).
assert (MR1 : tregs0 R1).
{ unfold PMABA2.tregs0, PMABA2.mregs, PMABA2.mregs0. repeat split; (rewrite KS1 by (cbn; tauto); hx). }
exact (mk_Zt s sm e fx1 R1 M1 model1 LKc crc Ac 3 BS1 MR1 B1 B10 B11 ltac:(lia)).
Qed.
Lemma t2_stage : ltac2:(TCodec.tc2 tcn__PmABa5 "S9'Q7'Q8'3'Q:&Hy5'R9yR0%211%5241'7y8%611%311p061'G'5&O%211&N'8'>%2211%711&QA&Q6vR5%211+oO%5221&Q3vCvQFvAvMvIvR2vDv@vEv1vQJvQ>vQOvQIvR:vR7vQNv?(9r<r;r:r7r6r5r4r3%LLKJIHGFEDCBA@?>Q0=<;:987654321&Q1r9%25KCB=1';&Q;&R8&QCu:%211%42QO1%62A1%62QO>%93QO21'=z%<3QEC1+1%>3QGE1%5231'Q<&Q=&Q0vQ?%211&Q9r=+fR_D%3672Q41Q3Q2vB%:49621p0<1p0C1p0N1p0Q21p0R01pSJR91p2R81pSHR=1pQ>R?1pT8RC1pQHRE1pQJRK1pT4S21pSLS41pT>S61pT:S81").
Proof using All. intros s sm e fx R Mc modelc LKc crc Ac d.
intros DEP BS MR A10 Hd. pose proof MR as (((X2 & X8 & X9 & X18 & X19 & X20 & X21 & X25 & X26 & X27 & X3 & X4) & X23) & X22 & X24).
pose proof BS as (BI & RUN & EC & HD & FSH & STEP & E0 & SD & CRL & CRK).
pose proof (vpack true _ s sm e 0 cat Mc modelc LKc crc Ac BI RUN EC HD FSH) as VF.
set (MV := mrestrict (ahid Ac modelc) Mc) in *.
destruct Hd as [Hd|Hd]; subst d.
- mid0 PMABAP2.abaT2z_conc (VT 0 0) true VF BS s sm e Mc modelc LKc crc Ac MV fx R 0xb09f4 0xae974.
assert (MR1 : tregs0 R1) by mregs_ks KS1.
assert (B1 : getr R1 (reg 1) = Z_to_bv 64 0xb0c40) by hx. assert (B10 : getr R1 (reg 10) = Z_to_bv 64 oec) by hx. assert (B11 : getr R1 (reg 11) = Z_to_bv 64 1) by hx.
exact (mk_Zt s sm e fx1 R1 M1 model1 LKc crc Ac 1 BS1 MR1 B1 B10 B11 ltac:(lia)).
- mid0 PMABAP2.abaT2p_conc (VT 0 0) true VF BS s sm e Mc modelc LKc crc Ac MV fx R 0xb09f4 0xae850.
assert (MR1 : tregs R1) by mregs_ks KS1.
assert (B1 : getr R1 (reg 1) = Z_to_bv 64 0xb0a00) by hx. assert (B10 : getr R1 (reg 10) = Z_to_bv 64 (op + 24)) by hx.
pose proof MR1 as (((Y2 & Y8 & Y9 & Y18 & Y19 & Y20 & Y21 & Y25 & Y26 & Y27 & Y3 & Y4) & Y23) & Y22 & Y24).
pose proof PEEK as PEEK'. unfold PMA.peek_spec, PMSPA.peek_spec in PEEK'. cbn [pa_peek PMA.AD ADDR_A] in PEEK'.
apply (call_src 0xae850 4 PMSPA.no_args PMSPA.no_W PMSPA.peek_res PEEK' true s sm e fx1 R1 M1 model1 LKc crc Ac 0xb0a00 [] BS1 B1
ltac:(apply pow_bnd_ra; [lia| reflexivity]) Y2 Y3 Y4 B10 ltac:(lia)).
+ exact I.
+ reflexivity.
+ intros rr [].
+ intros fx2 R2 M2' model2' LK2' Aw2 src2 sm2 RP2 RES2 _ BS2.
destruct RES2 as (_ & RES2).
apply (t3_stage (PMSPA.with_src s src2) sm2 e fx2 R2 M2' model2' LK2' crc Aw2 DEP BS2 (tregs_keep R1 R2 MR1 RP2)).
rewrite !L5K.rl10 in RES2. destruct RES2 as [X|(c & Hc & X & _)]; [left; exact X| right; exists c; split; [exact Hc| exact X]].
Qed.
Lemma t1_stage : ltac2:(TCodec.tc2 tcn__PmABa5 "RF'Q7'Q8'3'Q:&Hy5'R9yR0%211%5241'7y8%611%311p061'G'5&O%211&N'8'>%2211%711&QA&Q6vR5%211+oO%5221&Q3vCvQFvAvMvIvR2vDv@vEv1vQJvQ>vQOvQIvR:vR7vQNv?(4r;r:r9r6r5r4r3r2%LLKJIHGFEDCBA@?>Q0=<;:987654321&Q1r8%25KCB=1'Q<&Q=&Q0vQ?%211&Q9+fR_0r7%367CB2:1vB%:49621p0<1p0@1p0Q>1p2QE1pSHQJ1pQ>QL1pT8R01pQHR21pQJR81pT4R?1pSLRA1pT>RC1pT:RE1").
Proof using All. intros s sm e fx R Mc modelc LKc crc Ac.
intros DEP BS MR. pose proof MR as (((X2 & X8 & X9 & X18 & X19 & X20 & X21 & X25 & X26 & X27 & X3 & X4) & X23) & X22 & X24).
pose proof BS as (BI & RUN & EC & HD & FSH & STEP & E0 & SD & CRL & CRK).
pose proof (vpack false _ s sm e 0 cat Mc modelc LKc crc Ac BI RUN EC HD FSH) as VF.
set (MV := mrestrict (ahid Ac modelc) Mc) in *.
pose proof (PMABAP2.abaT1_conc fx R MV (VT 0 0)) as P. unfold PMABA3.VT in P. cbn beta iota in P. feedV P VF.
destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & PR). decompose [and] PR. clear PR.
pose proof (vf_fb false 0 MV VF) as (DF1 & DF2). pose proof (vf_rng false 0 MV VF) as (Rop & RS & RF & Rfl).
pose proof (vf_fsh false 0 MV VF) as (Y0 & Y1 & Y2' & Y3' & _ & Y5 & Y6 & Y7).
assert (SH4 : L5.u8_at RSEGS M1v (F / 8 + 2147450884) 1) by hx.
apply (step_piece true s sm e 0 cat fx fx1 R 0xb09e0 R1 0xaf334 M1v Mc modelc LKc crc Ac (fun a => a = F / 8 + 2147450884) BI RUN EC HD MS1 MG1).
{ intros a Ha N. apply FRZ1; [exact Ha| intros X; apply N; lia]. }
{ intros a X. right. exact X. }
{ assert (AG : forall a, F / 8 + 2147450880 <= a < F / 8 + 2147450888 -> a <> F / 8 + 2147450884 -> M1v (Z_to_bv 64 a) = MV (Z_to_bv 64 a))
by (intros a Ha N; apply FRZ1; [lia| intros X; apply N; lia]).
unfold PMABK.fsh. cbn iota.
split; [apply (L5C.u8_at_agree RSEGS MV M1v); [intros i Hi; apply AG; lia| lia| lia| exact Y0]|].
split; [apply (L5C.u8_at_agree RSEGS MV M1v); [intros i Hi; apply AG; lia| lia| lia| exact Y1]|].
split; [apply (L5C.u8_at_agree RSEGS MV M1v); [intros i Hi; apply AG; lia| lia| lia| exact Y2']|].
split; [apply (L5C.u8_at_agree RSEGS MV M1v); [intros i Hi; apply AG; lia| lia| lia| exact Y3']|].
split; [exact SH4|].
split; [apply (L5C.u8_at_agree RSEGS MV M1v); [intros i Hi; apply AG; lia| lia| lia| exact Y5]|].
split; [apply (L5C.u8_at_agree RSEGS MV M1v); [intros i Hi; apply AG; lia| lia| lia| exact Y6]|].
apply (L5C.u8_at_agree RSEGS MV M1v); [intros i Hi; apply AG; lia| lia| lia| exact Y7]. }
intros M1 model1 BI1 RUN1 EC1 HD1 FSH1 VIS1 HID1 FR1.
assert (BS1 : bst true s sm e M1 model1 LKc crc Ac) by (bst_of BI1 RUN1 EC1 HD1 FSH1 STEP E0 SD CRL CRK).
assert (MR1 : tregs R1) by mregs_ks KS1.
assert (B1 : getr R1 (reg 1) = Z_to_bv 64 0xb09f4) by hx. assert (B10 : getr R1 (reg 10) = Z_to_bv 64 (op + 24)) by hx.
assert (B11 : getr R1 (reg 11) = Z_to_bv 64 (F + 32)) by hx. assert (B12 : getr R1 (reg 12) = Z_to_bv 64 1) by hx.
pose proof MR1 as (((Z2 & Z8 & Z9 & Z18 & Z19 & Z20 & Z21 & Z25 & Z26 & Z27 & Z3 & Z4) & Z23) & Z22 & Z24).
pose proof (PMAUK.vis_facts L ar C HI LYa HIok M0 model0 LBX FF LK0 Aw0 S SCR (S - 128) (S - 104) S ocell own F fl 0 LK2 M2 model2 cr0 (PM.parser_own s0) G WR _ M1 model1 LKc crc Ac BI1)
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
pose proof (PMABK.frame_geo fb) as (Eop & Eois & _).
pose proof SRD as SRD'. unfold PMA.src_read_spec, PMSPA.src_read_spec in SRD'. cbn [pa_src_read PMA.AD ADDR_A] in SRD'.
apply (call_src 0xaf334 4 (PMSPA.read_args AD) PMSPA.read_W PMSPA.read_res SRD' true s sm e fx1 R1 M1 model1 LKc crc Ac 0xb09f4 [(F + 32, 1)] BS1 B1
ltac:(apply pow_bnd_ra; [lia| reflexivity]) Z2 Z3 Z4 B10 ltac:(lia)).
- unfold PMSPA.read_args. exists (F + 32), 1. split; [rewrite L5SAR.r11; exact B11|]. split; [rewrite L5K.rl12; exact B12|].
split; [unfold PM.CHUNK; lia|]. left.
split; [exists (F, 0, S - 128 + 32); split; [left; reflexivity| cbn [ff_addr ff_class fst snd]; change (ff_bytes 0) with 64; lia]|].
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
End PMABA5.
