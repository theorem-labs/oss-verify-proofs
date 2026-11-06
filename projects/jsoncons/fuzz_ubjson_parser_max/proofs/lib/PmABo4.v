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
PmModelFactsA PmStepA PmStep PmParStep PmParKit PmASrcKit PmAParKit PmAReset1 PmAUarK PmAUar PmAUarKS PmABoK PmABoK2 PmABoK3 Ja0_code_b1370_b1374 PmABo1 PmABoP1 PmABoP2 PmABoP3 PmABoP4 PmABo2 PmABo3.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmABo4 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmABo2.PMABO2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmABoK.PMABOK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0Ac"; "0Aw0"; "0BX"; "1bool"; "1false"; "1list"; "1option"; "1prod"; "2and"; "2eq"; "2or"; "3Z"; "0F"; "0FF"; "0HI"; "0K"]; ["0L"; "0LBX"; "0LK0"; "0LKc"; "4Model"; "5bvmap"; "0M0"; "0MV"; "0Mc"; "0R"; "0R0"; "6mrestrict"; "7credit"; "8S"; "8ahid"; "8byte_at"]; ["8fframe"; ":ra_ok"; ":u64_at"; "9SCFG"; ";mregs"; "<binv'"; "<bst"; "<fsh"; "<op"; "<vfacts"; "=AADDR_A"; "=ADDR_A"; ">p_depth"; ">pst"; ">strm"; "?cfg"]; ["?run_pre"; "@FPState"; "@getr"; "Asrealizes"; "Bloaded_segments"; "0S"; "0SCFG_P"; "Cadd"; "Cdiv"; "Cdivide"; "Cle"; "Clt"; "Cmodulo"; "Cof_nat"; "Cpow"; "Csub"]; ["0a"; "0ar"; "0b"; "0c"; "0cat"; "0cr0"; "0crc"; "0d"; "0e"; "0e0"; "0fb"; "0fl"; "0fx"; "0k"; "0model0"; "0modelc"]; ["0n"; "0p"; "0s"; "0s0"; "0sm"; "0sm0"; "DZ_to_bv"; "Dbv"; "0str"; "0typed"; "0v"; "0x"]]).
Local Ltac lia := L5FastLia.plia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PMABO4.
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
Lemma vf_fsh : ltac2:(TCodec.tc2 tcn__PmABo4 "K'3';'RGyR0%211'6y8%511%311p051&Q9vJvQEvR:v<vR;r3r2r1%9887654321&Q7r4%23815p041pQ@?1pUFH1pUDJ1").
Proof. intros typed v MV. intros VF. unfold PMABOK.vfacts in VF. destruct VF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _ & _ & _ & _ & _). exact X. Qed.
Lemma vf_fb : ltac2:(TCodec.tc2 tcn__PmABo4 "Q8'3';'RGyR0%211'6y8%511%311p051&Q9vJvQEvR:v<vR;r3r2r1%9887654321'8&QJz&QH+8%22;1%5241&QG+QoooPP8%2241&QN+2+R0%3221%=251%?291p0A1pQ@L1pUFQ51pUDQ71").
Proof. intros typed v MV.
intros VF. unfold PMABOK.vfacts in VF. destruct VF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
split; [apply Z.div_pos; lia|]. assert (F / 8 <= 17592186044408) by (apply Z.div_le_upper_bound; lia). lia.
Qed.
Lemma mi_vis : ltac2:(TCodec.tc2 tcn__PmABo4 "R9'5'7';%2211%411'Q='Q>'3'RGyR0%211'6y8%511%311p051'D&Q0%B11&L&Q5v@vR1v>vJvFvR>vAv=vBv1vQEvR:v<r9r5r4r3r2r1%DCCBA@?>=<;:987654321&Q@&QD&Q;&Q:r6vRHr8r7%897654A?321&Q2&K&N%12@8%3216&QG&Q8%11I+Z8%4221+`PPP0%;4C721p0=1p0G1p2QL1pT>Q>1pQ8Q@1pU0QC1pQBQE1pTBQN1pU:R01pU6R21p6R41").
Proof using All. intros BX s sm e Mc modelc LKc crc Ac.
intros BI RUN. pose proof BI as (HHc & _). pose proof RUN as (PA & _).
pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & P328 & _).
pose proof (PMAPAR.op_vis L ar C HI LY HIok _ FF' LKc crc Ac Mc modelc fb _ s HHc (PMAUAR.frame_okA_push FF fb F 0 (S - 128 + 32) FOK) PA)
as ((O1 & _) & _ & _ & _ & _ & _ & OAV & _ & _).
apply (proj2 (L5A.u64_at_vis (ahid Ac modelc) Mc (op + 328) 16777216 (OAV (op + 328) 8 ltac:(unfold PMABOK.op; lia) ltac:(unfold PMABOK.op; lia)) ltac:(unfold PMABOK.op; lia) ltac:(unfold PMABOK.op; lia))).
exact P328.
Qed.
Lemma stk_bz : ltac2:(TCodec.tc2 tcn__PmABo4 "QN'5'7';%2211%411'RGyR0%211'6y8%511%311p051'D&Q0%?11&L&Q5v@vR1v>vJvFvR>vAv=vBv1vQEvR:v<r6r5r4r3r2r1%DCCBA@?>=<;:987654321'8&QJ&QO+jP0%22>1%4217&QK%129A%8231&Or8&M%11?z%53421p071pU4QD1p0B1p2QD1pT>Q91pQ8Q;1pU0Q>1pQBQ@1p6QI1").
Proof using All. intros BX Mc modelc LKc crc Ac.
intros BI p Hp. pose proof BI as (HHc & AMc & MRTc & IAc & ILKc & ASTKc & EKc & _).
pose proof ENT as (_ & _ & _ & _ & _ & ASTK0 & STKSH0). change (PMSPA.pm_scr 7) with 26624 in *. change (26624 / 8) with 3328 in STKSH0.
pose proof ASTK0 as (A16 & SLO & SHI & SPT & SDEF & SUP).
assert (M8a : (S - 26624) mod 8 = 0) by (apply PMKA.mod16_8'; replace (S - 26624) with (S + (-1664) * 16) by lia; rewrite Z_mod_plus_full; exact A16).
pose proof (PMABOK.wappR L ar C HI HIok M0 model0 LBX FF LK0 Aw0 cr0 fb s0 HH0 FOK) as WAPP.
pose proof (PMKA.stksh_keepA L ar LBX FF S 26624 WR M0 Mc EKc WAPP (S - 26624) 3328 ltac:(lia) ltac:(lia) ltac:(lia) M8a ltac:(lia) STKSH0) as SZ.
assert (E : HeapIfaceA.S p = HeapIfaceA.S (S - 26624) + (p / 8 - (S - 26624) / 8)) by (unfold HeapIfaceA.S; lia).
rewrite E. apply SZ.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). clear - Hp M8a. lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma stk_cell BX Mc modelc LKc crc Ac p n : binv' BX Mc modelc LKc crc Ac -> S - 128 <= p -> p + n <= S - 104 -> 0 < n ->
PMSPA.accA Mc p n /\ byte_at Mc (HeapIfaceA.S p) 0 /\ PMSAX.arg_ok ar FF' (S - 128) (op + 360) p n
/\ (forall v, L5.u32_at RSEGS (mrestrict (ahid Ac modelc) Mc) p v -> n = 4 -> L5.u32_at RSEGS Mc p v)
/\ (forall v, L5.u64_at RSEGS (mrestrict (ahid Ac modelc) Mc) p v -> n = 8 -> L5.u64_at RSEGS Mc p v).
Proof using All.
intros BI H1 H2 Hn. pose proof G as G'. destruct G' as [Hk SPTg SLOg SHIg SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
unfold SCR in *.
pose proof (PMAUK.vis_facts L ar C HI LYa HIok M0 model0 LBX FF LK0 Aw0 S SCR (S - 128) (S - 104) S ocell own F fl 0 LK2 M2 model2 cr0 (PM.parser_own s0) G WR _ Mc modelc LKc crc Ac BI)
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
- right. unfold PMABOK.op. pose proof (PMABOK.frame_geo fb) as (Eop & _). lia. }
split.
{ intros v X En. subst n. apply (proj1 (L5A.u32_at_vis _ Mc p v (L5A.avis_sub _ (S - 128) (S - (S - 128)) p 4 SV8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact X. }
{ intros v X En. subst n. apply (proj1 (L5A.u64_at_vis _ Mc p v (L5A.avis_sub _ (S - 128) (S - (S - 128)) p 8 SV8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact X. }
Qed.
Ltac bst_of BI RUN EC HD FSH STEP E0 SD CRL CRK :=
split; [exact BI|]; split; [exact RUN|]; split; [exact EC|]; split; [exact HD|]; split; [exact FSH|]; split; [exact STEP|]; split; [exact E0|];
split; [exact SD|]; split; [exact CRL| exact CRK].
Lemma modsub : ltac2:(TCodec.tc2 tcn__PmABo4 "J';&QKzr1%3221'9&QLr4r2%3221%53:18r3%6251%83=1;&QOr6r5%3221%<21;%>3C1Ap071p0;1p0B1pU2G1pT6H1pT2I1").
Proof. intros a b n. intros Hn Ha Hb. apply Z.mod_divide in Ha; [|lia]. apply Z.mod_divide in Hb; [|lia]. apply Z.mod_divide; [lia|]. apply Z.divide_sub_r; assumption. Qed.
Lemma mod32_d : ltac2:(TCodec.tc2 tcn__PmABo4 "F';&QIr1+Q0%3221&QKzr2%3221'9&QLr4%2219%43=17r5%5214%73@1:p041p0:1p0?1pT@D1pUHE1").
Proof. intros x d. intros Hd Hp H. apply Z.mod_divide in H; [|lia]. apply Z.mod_divide; [lia|]. eapply Z.divide_trans; eassumption. Qed.
Lemma sp_mod : ltac2:(TCodec.tc2 tcn__PmABo4 "J';&QIr1+Q0%3221&QKzr2%3221'9&QLr4r3%3221%53>18&QOvQEr5%3221%9218%;3D1>p071p0>1p0C1pT@H1pTLI1").
Proof using SP32. intros k d. intros Hd Hp Hk. apply modsub; [exact Hp| exact (mod32_d S d Hd Hp SP32)| exact Hk]. Qed.
Ltac mregs_ks KS := unfold PMABO2.tregs, PMABO2.mregs, PMABO2.mregs0; repeat split; (rewrite (KS _) by inl; hx).
Lemma pow_bnd_ra : ltac2:(TCodec.tc2 tcn__PmABo4 "H';'8&QJzr1%3221&QK&QN+2+Q?%3221%5271%;271'9&QLr2%2218%43A1>&Q1r3%211p041p0:1pUHG1").
Proof. intros x. intros H1 H2. split; assumption. Qed.
Lemma c_stage : ltac2:(TCodec.tc2 tcn__PmABo4 "RF'Q='Q>'3'QA&Ey5'RGyR0%211%5241'6y8%611%311p061'D'5&Q0%211&L'7';%2211%711&QJ&Q<vRC%211+oO%5221&Q6v@vR1v>vJvFvR>vAv=vBv1vR5vQEvR:vR4vRHvREvR9v<(4r;r:r9r6r5r4r3r2%LLKJIHGFEDCBA@?>Q0=<;:987654321&Q4r8%25KCB=1'QC&QD&Q3vQF%211&Q?+fTX@r7%367CB2:1v?%:49621p0<1p0@1p0Q>1p2QE1pT>QJ1pQ8QL1pU0R01pQBR21pQDR81pTJR?1pTBRA1pU:RC1pU6RE1").
Proof using All. intros s sm e fx R Mc modelc LKc crc Ac.
intros DEP BS MR. pose proof MR as ((X2 & X8 & X9 & X18 & X19 & X20 & X21 & X25 & X26 & X27 & X3 & X4) & X23).
pose proof BS as (BI & RUN & EC & HD & FSH & STEP & E0 & SD & CRL & CRK).
pose proof (vpack false _ s sm e 0 cat Mc modelc LKc crc Ac BI RUN EC HD FSH) as VF.
set (MV := mrestrict (ahid Ac modelc) Mc) in *.
pose proof (PMABOP3.aboC1_conc fx R MV (VT 0 0)) as P. unfold PMABO3.VT in P. cbn beta iota in P. feedV P VF.
destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & PR). decompose [and] PR. clear PR.
pose proof (vf_fb false 0 MV VF) as (DF1 & DF2).
apply (step_piece false s sm e 0 cat fx fx1 R 0xb1110 R1 0xafe2c M1v Mc modelc LKc crc Ac (fun _ => False) BI RUN EC HD MS1 MG1).
{ intros a Ha _. apply FRZ1. exact Ha. }
{ intros a []. }
{ apply (fsh_agree false MV M1v); [intros a Ha; apply FRZ1; lia| exact DF1| exact DF2| exact (vf_fsh false 0 MV VF)]. }
intros M1 model1 BI1 RUN1 EC1 HD1 FSH1 VIS1 HID1 FR1.
assert (BS1 : bst false s sm e M1 model1 LKc crc Ac) by (bst_of BI1 RUN1 EC1 HD1 FSH1 STEP E0 SD CRL CRK).
assert (MR1 : mregs R1) by mregs_ks KS1.
assert (A1 : getr R1 (reg 1) = Z_to_bv 64 0xb111c) by hx.
assert (A10 : getr R1 (reg 10) = Z_to_bv 64 op) by hx.
assert (A11 : getr R1 (reg 11) = Z_to_bv 64 oec) by hx.
pose proof MR1 as ((Y2 & Y8 & Y9 & Y18 & Y19 & Y20 & Y21 & Y25 & Y26 & Y27 & Y3 & Y4) & Y23).
apply (call_gl false s sm e fx1 R1 M1 model1 LKc crc Ac 0xb111c BS1 A1 ltac:(apply pow_bnd_ra; [lia| reflexivity]) Y2 Y3 Y4 A10 A11).
intros fx2 R2 M2' model2' LK2' Aw2 s2 sm2 e2 cr2 RP2 OUT2.
pose proof (mregs_keep R1 R2 MR1 RP2) as MR2.
destruct OUT2 as [(BS2 & UN2 & (len & Hlen & A10'))|BE2].
2: { exact (gl_err_C s2 sm2 fx2 R2 M2' model2' LK2' cr2 Aw2 BE2 MR2). }
pose proof BS2 as (BI2 & RUN2 & EC2 & HD2 & FSH2 & STEP2 & E02 & SD2 & CRL2 & CRK2).
pose proof (vpack false _ s2 sm2 e2 0 cat M2' model2' LK2' cr2 Aw2 BI2 RUN2 EC2 HD2 FSH2) as VF2.
pose proof (mi_vis _ s2 sm2 e2 M2' model2' LK2' cr2 Aw2 BI2 RUN2) as MI2.
set (MV2 := mrestrict (ahid Aw2 model2') M2') in *.
pose proof MR2 as ((Z2 & Z8 & Z9 & Z18 & Z19 & Z20 & Z21 & Z25 & Z26 & Z27 & Z3 & Z4) & Z23).
pose proof (vf_fb false 0 MV2 VF2) as (DF1b & DF2b). pose proof (vf_rng false 0 MV2 VF2) as (Rop & RS & RF & Rfl).
destruct (Z_le_gt_dec len 16777216) as [Le|Gt].
-
assert (HL2 : 0 <= len <= 16777216) by lia.
pose proof (PMABOP3.aboCf_conc fx2 R2 MV2 (VT 0 len)) as P. unfold PMABO3.VT in P. cbn beta iota in P. feedV P VF2.
destruct P as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & PR). decompose [and] PR. clear PR.
apply (step_piece false s2 sm2 e2 0 cat fx2 fx3 R2 0xb111c R3 0xb1cc4 M3v M2' model2' LK2' cr2 Aw2 (fun a => S - 116 <= a < S - 104) BI2 RUN2 EC2 HD2 MS3 MG3).
{ intros a Ha N. apply FRZ3; [exact Ha| intros X; apply N; lia]. }
{ intros a X. left. lia. }
{ apply (fsh_agree false MV2 M3v); [intros a Ha; apply FRZ3; [lia| intros X; unfold SB in *; lia]| exact DF1b| exact DF2b| exact (vf_fsh false 0 MV2 VF2)]. }
intros M3 model3 BI3 RUN3 EC3 HD3 FSH3 VIS3 HID3 FR3.
assert (BS3 : bst false s2 sm2 e2 M3 model3 LK2' cr2 Aw2) by (bst_of BI3 RUN3 EC3 HD3 FSH3 STEP2 E02 SD2 CRL2 CRK2).
destruct (stk_cell _ M3 model3 LK2' cr2 Aw2 (S - 116) 4 BI3 ltac:(lia) ltac:(lia) ltac:(lia)) as (AC1 & BZ1 & AO1 & U1 & _).
destruct (stk_cell _ M3 model3 LK2' cr2 Aw2 (S - 112) 8 BI3 ltac:(lia) ltac:(lia) ltac:(lia)) as (AC2 & BZ2 & AO2 & _ & U2).
rewrite HID3, VIS3 in U1, U2.
assert (C116 : L5.u32_at RSEGS M3 (S - 116) 5) by (apply U1; [hx| reflexivity]).
assert (C112 : L5.u64_at RSEGS M3 (S - 112) len) by (apply U2; [hx| reflexivity]).
assert (MR3 : mregs R3) by mregs_ks KS3.
assert (B1 : getr R3 (reg 1) = Z_to_bv 64 0xb1258) by hx.
assert (B10 : getr R3 (reg 10) = Z_to_bv 64 (op + 360)) by hx.
assert (B11 : getr R3 (reg 11) = Z_to_bv 64 (S - 116)) by hx.
assert (B12 : getr R3 (reg 12) = Z_to_bv 64 (S - 112)) by hx.
pose proof MR3 as ((W2 & W8 & W9 & W18 & W19 & W20 & W21 & W25 & W26 & W27 & W3 & W4) & W23).
pose proof SD2 as (_ & _ & SDp & SDs). pose proof INV as (_ & _ & IDP & _).
pose proof STEP2 as (_ & _ & _ & _ & UN02).
unfold PMA.push_ms_spec, PMSAX.push_ms_spec in PMS. cbn [paa_esp_ms PMA.AAD AADDR_A] in PMS.
apply (call_push 0xb1cc4 (PMSAX.cells_ms RSEGS ar) PMS false s2 sm2 e2 fx3 R3 M3 model3 LK2' cr2 Aw2 0xb1258 (PM.PS 5 len 0 0) BS3 B1
ltac:(apply pow_bnd_ra; [lia| reflexivity]) W2 W3 W4 B10).
+ unfold PMSAX.cells_ms. exists (S - 116), (S - 112), 5, len.
split; [rewrite L5SAR.r11; exact B11|]. split; [rewrite L5K.rl12; exact B12|].
split; [apply sp_mod; [exists 8; reflexivity| lia| reflexivity]|]. split; [apply sp_mod; [exists 4; reflexivity| lia| reflexivity]|].
split; [exact AC1|]. split; [exact AC2|]. split; [exact AO1|]. split; [exact AO2|]. split; [exact BZ1|]. split; [exact BZ2|].
split; [exact C116|]. split; [exact C112|]. split; [lia|]. split; [lia| reflexivity].
+ unfold PM.pstate_ok. cbn [PM.ps_type PM.ps_mode PM.ps_len PM.ps_idx]. split; [lia|]. left. split; [unfold PM.mode_counted; right; right; left; reflexivity|]. unfold PM.MAX_ITEMS. lia.
+ reflexivity.
+ unfold PM.mode_bottom. cbn [PM.ps_mode]. lia.
+ intros _. pose proof STEP as (_ & _ & _ & _ & UN0). lia.
+ unfold PM.MAX_DEPTH. lia.
+ intros fx4 R4 M4 model4 LK4 Aw4 s4 cr4 RP4 BSP4 SRC4 KPR4.
apply (tail_C s4 sm2 e2 fx4 R4 M4 model4 LK4 cr4 Aw4 len BSP4 (mregs_keep R3 R4 MR3 RP4) HL2).
apply (L5C.u64_at_agree RSEGS M3 M4); [intros i Hi; apply KPR4; lia| lia| lia| exact C112].
-
assert (HL2 : 16777217 <= len <= 18446744073709551615) by lia.
pose proof (PMABOP3.aboCx_conc fx2 R2 MV2 (VT 0 len)) as P. unfold PMABO3.VT in P. cbn beta iota in P. feedV P VF2.
destruct P as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & PR). decompose [and] PR. clear PR.
apply (step_piece false s2 sm2 e2 0 cat fx2 fx3 R2 0xb111c R3 0xae974 M3v M2' model2' LK2' cr2 Aw2 (fun a => S - 112 <= a < S - 104) BI2 RUN2 EC2 HD2 MS3 MG3).
{ intros a Ha N. apply FRZ3; [exact Ha| intros X; apply N; lia]. }
{ intros a X. left. lia. }
{ apply (fsh_agree false MV2 M3v); [intros a Ha; apply FRZ3; [lia| intros X; unfold SB in *; lia]| exact DF1b| exact DF2b| exact (vf_fsh false 0 MV2 VF2)]. }
intros M3 model3 BI3 RUN3 EC3 HD3 FSH3 VIS3 HID3 FR3.
assert (BS3 : bst false s2 sm2 e2 M3 model3 LK2' cr2 Aw2) by (bst_of BI3 RUN3 EC3 HD3 FSH3 STEP2 E02 SD2 CRL2 CRK2).
assert (MR3 : mregs R3) by mregs_ks KS3.
assert (B1 : getr R3 (reg 1) = Z_to_bv 64 0xb1160) by hx.
assert (B10 : getr R3 (reg 10) = Z_to_bv 64 oec) by hx.
assert (B11 : getr R3 (reg 11) = Z_to_bv 64 13) by hx.
exact (mk_Zc s2 sm2 e2 fx3 R3 M3 model3 LK2' cr2 Aw2 13 BS3 MR3 B1 B10 B11 ltac:(lia)).
Qed.
Definition VK (x39 : Z) (j : nat) : Z := match j with 39%nat => x39 | _ => PMABO3.VT R0 S fb F fl 0 0 j end.
Lemma i_stage : ltac2:(TCodec.tc2 tcn__PmABo4 "S@'Q='Q>'3'QA&Ey5'RGyR0%211%5241'6y8%611%311p061'D'5&Q0%211&L'7';%2211%711&QJ&Q<vRC%211+oO%5221&Q6v@vR1v>vJvFvR>vAv=vBv1vR5vQEvR:vR4vRHvREvR9v<(4r<r;r:r7r6r5r4r3%LLKJIHGFEDCBA@?>Q0=<;:987654321&Q4r9%25KCB=1'9&QB&RF&QMu:%211%42QO1%62A1%62QO>%93QO21':'8z%QC21D+Q2%QE2F1%5231+Q4%QH21I+WO%QJ2K1%:231%<261'QC&QD&Q3vQF%211&Q?r=+fTW@%3672Q;1Q:Q9v?%:49621p0<1p0J1p0Q51p0Q91p0R71pT8R@1p2R?1pT>RD1pQ8RF1pU0RJ1pQBRL1pQDS21pTJS91pTBS;1pU:S=1pU6S?1").
Proof using All. intros s sm e fx R Mc modelc LKc crc Ac c.
intros DEP BS MR A10c Hc. pose proof MR as ((X2 & X8 & X9 & X18 & X19 & X20 & X21 & X25 & X26 & X27 & X3 & X4) & X23).
pose proof BS as (BI & RUN & EC & HD & FSH & STEP & E0 & SD & CRL & CRK).
pose proof (vpack false _ s sm e 0 cat Mc modelc LKc crc Ac BI RUN EC HD FSH) as VF.
set (MV := mrestrict (ahid Ac modelc) Mc) in *.
pose proof (vf_fb false 0 MV VF) as (DF1 & DF2). pose proof (vf_rng false 0 MV VF) as (Rop & RS & RF & Rfl).
assert (Hcb : 0 <= c < 2 ^ 64) by lia.
assert (PKL : exists (fx1 : FPState) R1 M1v, mem_grows MV M1v
/\ (forall i, 0 <= i < 2 ^ 64 -> ~ (S - 116 <= i < S - 108) -> M1v (Z_to_bv 64 i) = MV (Z_to_bv 64 i))
/\ msteps RSEGS (L5A.st fx R 0xb10f0 MV) (L5A.st fx1 R1 0xab610 M1v)
/\ (forall x, In x [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R1 (reg x) = getr R (reg x))
/\ getr R1 (reg 1) = Z_to_bv 64 0xb1198 /\ getr R1 (reg 10) = Z_to_bv 64 (op + 360) /\ getr R1 (reg 11) = Z_to_bv 64 (S - 112)
/\ getr R1 (reg 12) = Z_to_bv 64 (S - 116) /\ L5.u32_at RSEGS M1v (S - 116) 0 /\ L5.u32_at RSEGS M1v (S - 112) 9).
{ destruct Hc as [Hc|Hc].
- pose proof (PMABOP1.aboK2l_conc fx R MV (VK c)) as P. unfold VK, PMABO3.VT in P. cbn beta iota in P. feedV P VF.
destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & PR). decompose [and] PR. clear PR.
exists fx1, R1, M1v. split; [exact MG1|]. split; [intros i Hi N; apply FRZ1; [exact Hi| intros X; apply N; lia]|]. split; [exact MS1|].
split; [intros x Hx; apply KS1; revert x Hx; apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat); vm_compute; reflexivity|].
repeat (split; [hx|]). hx.
- pose proof (PMABOP1.aboK2u_conc fx R MV (VK c)) as P. unfold VK, PMABO3.VT in P. cbn beta iota in P. feedV P VF.
destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & PR). decompose [and] PR. clear PR.
exists fx1, R1, M1v. split; [exact MG1|]. split; [intros i Hi N; apply FRZ1; [exact Hi| intros X; apply N; lia]|]. split; [exact MS1|].
split; [intros x Hx; apply KS1; revert x Hx; apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat); vm_compute; reflexivity|].
repeat (split; [hx|]). hx. }
destruct PKL as (fx1 & R1 & M1v & MG1 & FRZ1 & MS1 & KS1 & B1 & B10 & B11 & B12 & C116v & C112v).
apply (step_piece false s sm e 0 cat fx fx1 R 0xb10f0 R1 0xab610 M1v Mc modelc LKc crc Ac (fun a => S - 116 <= a < S - 108) BI RUN EC HD MS1 MG1).
{ intros a Ha N. apply FRZ1; [exact Ha| exact N]. }
{ intros a X. left. lia. }
{ apply (fsh_agree false MV M1v); [intros a Ha; apply FRZ1; [lia| intros X; unfold SB in *; lia]| exact DF1| exact DF2| exact (vf_fsh false 0 MV VF)]. }
intros M1 model1 BI1 RUN1 EC1 HD1 FSH1 VIS1 HID1 FR1.
assert (BS1 : bst false s sm e M1 model1 LKc crc Ac) by (bst_of BI1 RUN1 EC1 HD1 FSH1 STEP E0 SD CRL CRK).
destruct (stk_cell _ M1 model1 LKc crc Ac (S - 112) 4 BI1 ltac:(lia) ltac:(lia) ltac:(lia)) as (AC1 & BZ1 & AO1 & U1 & _).
destruct (stk_cell _ M1 model1 LKc crc Ac (S - 116) 4 BI1 ltac:(lia) ltac:(lia) ltac:(lia)) as (AC2 & BZ2 & AO2 & U2 & _).
rewrite HID1, VIS1 in U1, U2.
assert (C112 : L5.u32_at RSEGS M1 (S - 112) 9) by (apply U1; [exact C112v| reflexivity]).
assert (C116 : L5.u32_at RSEGS M1 (S - 116) 0) by (apply U2; [exact C116v| reflexivity]).
assert (MR1 : mregs R1).
{ unfold PMABO2.mregs, PMABO2.mregs0. repeat split; (rewrite KS1 by (cbn; tauto); hx). }
pose proof MR1 as ((W2 & W8 & W9 & W18 & W19 & W20 & W21 & W25 & W26 & W27 & W3 & W4) & W23).
pose proof INV as (_ & _ & IDP & _).
unfold PMA.push_mi_spec, PMSAX.push_mi_spec in PMI. cbn [paa_esp_mi PMA.AAD AADDR_A] in PMI.
apply (call_push 0xab610 (PMSAX.cells_mi RSEGS ar) PMI false s sm e fx1 R1 M1 model1 LKc crc Ac 0xb1198 (PM.PS 9 0 0 0) BS1 B1
ltac:(apply pow_bnd_ra; [lia| reflexivity]) W2 W3 W4 B10).
+ unfold PMSAX.cells_mi. exists (S - 112), (S - 116), 9, 0.
split; [rewrite L5SAR.r11; exact B11|]. split; [rewrite L5K.rl12; exact B12|].
split; [apply sp_mod; [exists 8; reflexivity| lia| reflexivity]|]. split; [apply sp_mod; [exists 8; reflexivity| lia| reflexivity]|].
split; [exact AC1|]. split; [exact AC2|]. split; [exact AO1|]. split; [exact AO2|]. split; [exact BZ1|]. split; [exact BZ2|].
split; [exact C112|]. split; [exact C116|]. split; [lia|]. split; [lia| reflexivity].
+ unfold PM.pstate_ok. cbn [PM.ps_type PM.ps_mode PM.ps_len PM.ps_idx]. split; [lia|]. right. left. split; [unfold PM.mode_indef; right; left; reflexivity|]. unfold PM.MAX_ITEMS. lia.
+ reflexivity.
+ unfold PM.mode_bottom. cbn [PM.ps_mode]. lia.
+ unfold PM.mode_counted. cbn [PM.ps_mode]. lia.
+ unfold PM.MAX_DEPTH. lia.
+ intros fx4 R4 M4 model4 LK4 Aw4 s4 cr4 RP4 BSP4 SRC4 KPR4.
exact (tail_I s4 sm e fx4 R4 M4 model4 LK4 cr4 Aw4 BSP4 (mregs_keep R1 R4 MR1 RP4)).
Qed.
End Frame.
End Call.
End WithHeap.
End PMABO4.
