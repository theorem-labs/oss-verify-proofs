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
PmModelFactsA PmStepAB0 PmStep PmParStep PmParKit PmBSrcKit PmBParKit PmBReset1 PmBUarK PmBUar PmBUarKS PmBBaK PmBBaK2 PmBBaK3 Jb0_code_b2664_b2668 PmBBa1 PmBBaP1 PmBBaP2 PmBBaP3.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmBBa2 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBBa2.PMBBA2.WithHeap.Call.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBBaK.PMBBK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBBaK2.PMBBK2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0Ac"; "0Aw0"; "1bool"; "1false"; "1list"; "1nat"; "1option"; "1prod"; "1true"; "2and"; "2eq"; "2not"; "2or"; "3Z"; "0F"; "0FF"]; ["0HI"; "0K"; "0L"; "0LBX"; "0LK0"; "0LKc"; "4Model"; "5bvmap"; "0M0"; "0MV"; "0Mc"; "0R"; "0R'"; "0R0"; "6credit"; "6regs_preserved"]; ["7fframe"; "8SCFG"; "9mregs"; "9mregs0"; "9mregs0B1"; "9tregs"; "9tregs0"; ":U"; ":bst"; ":bst0"; ":oec"; ":op"; ":vfacts"; ";bsterr"; "<pst"; "<strm"]; ["=cfg"; ">FPState"; ">getr"; "?srealizes"; "@loaded_segments"; "0S"; "0SCFG_P"; "Aadd"; "Adiv"; "Ale"; "Alt"; "Aof_nat"; "Apow"; "Asub"; "0a"; "0ar"]; ["0cat"; "0cr0"; "0crc"; "0e"; "0e0"; "0fb"; "0fl"; "0fx"; "0hi"; "0i"; "0lo"; "0model0"; "0modelc"; "0s"; "0s0"; "0sm"]; ["0sm0"; "BZ_to_bv"; "Bbv"; "0str"; "0typed"; "0v"; "0x"]]).
Local Ltac lia := L5FastLia.plia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PMBBA2.
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
Local Abbreviation fin_any := (PMBBA1.fin_any L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE CMI SMI CMS SMS CMSU SMSU F fl LK2 M2 model2 G).
Definition mregs0 (R : bvmap 5 word) : Prop :=
getr R (reg 2) = Z_to_bv 64 (S - 160) /\ getr R (reg 8) = Z_to_bv 64 S /\ getr R (reg 9) = Z_to_bv 64 (S - 160) /\ getr R (reg 18) = Z_to_bv 64 F
/\ getr R (reg 19) = Z_to_bv 64 op /\ getr R (reg 20) = Z_to_bv 64 oec /\ getr R (reg 21) = Z_to_bv 64 65024
/\ getr R (reg 25) = Z_to_bv 64 F /\ getr R (reg 26) = Z_to_bv 64 (F / 8 + 2147450880) /\ getr R (reg 27) = Z_to_bv 64 2147450880
/\ getr R (reg 3) = getr R0 (reg 3) /\ getr R (reg 4) = getr R0 (reg 4).
Definition mregs (R : bvmap 5 word) : Prop := mregs0 R /\ getr R (reg 23) = Z_to_bv 64 (op + 24).
Definition tregs (R : bvmap 5 word) : Prop := mregs R /\ getr R (reg 22) = Z_to_bv 64 (F + 32) /\ getr R (reg 24) = Z_to_bv 64 1.
Lemma mregs0_keep : ltac2:(TCodec.tc2 tcn__PmBBa2 "A&Gy5'RByR0%211%5241&Q3r2%211&Or3%2214%612p021p061pQJ:1pQH;1").
Proof. intros R R'.
intros (X2 & X8 & X9 & X18 & X19 & X20 & X21 & X25 & X26 & X27 & X3 & X4) RP.
assert (K' : forall j, In j L5SAR.cs_all -> getr R' (reg j) = getr R (reg j)) by (intros j Hj; exact (L5SAR.cs_of_preserved R R' j RP Hj)).
repeat split; [rewrite K' by inl; assumption ..].
Qed.
Definition mregs0B1 (R : bvmap 5 word) : Prop :=
getr R (reg 2) = Z_to_bv 64 (S - 160) /\ getr R (reg 8) = Z_to_bv 64 S /\ getr R (reg 9) = Z_to_bv 64 (S - 160) /\ getr R (reg 18) = Z_to_bv 64 F
/\ getr R (reg 19) = Z_to_bv 64 op /\ getr R (reg 20) = Z_to_bv 64 oec /\ getr R (reg 21) = Z_to_bv 64 ov
/\ getr R (reg 25) = Z_to_bv 64 F /\ getr R (reg 26) = Z_to_bv 64 (F / 8 + 2147450880) /\ getr R (reg 27) = Z_to_bv 64 2147450880
/\ getr R (reg 3) = getr R0 (reg 3) /\ getr R (reg 4) = getr R0 (reg 4).
Lemma mregs0B1_keep : ltac2:(TCodec.tc2 tcn__PmBBa2 "A&Gy5'RByR0%211%5241&Q4r2%211&Or3%2214%612p021p061pQJ:1pQH;1").
Proof. intros R R'.
intros (X2 & X8 & X9 & X18 & X19 & X20 & X21 & X25 & X26 & X27 & X3 & X4) RP.
assert (K' : forall j, In j L5SAR.cs_all -> getr R' (reg j) = getr R (reg j)) by (intros j Hj; exact (L5SAR.cs_of_preserved R R' j RP Hj)).
repeat split; [rewrite K' by inl; assumption ..].
Qed.
Lemma mregs_keep : ltac2:(TCodec.tc2 tcn__PmBBa2 "A&Gy5'RByR0%211%5241&Q2r2%211&Or3%2214%612p021p061pQJ:1pQH;1").
Proof. intros R R'. intros (M & X23) RP. split; [exact (mregs0_keep R R' M RP)| rewrite (L5SAR.cs_of_preserved R R' 23 RP) by inl; exact X23]. Qed.
Lemma tregs_keep : ltac2:(TCodec.tc2 tcn__PmBBa2 "A&Gy5'RByR0%211%5241&Q5r2%211&Or3%2214%612p021p061pQJ:1pQH;1").
Proof. intros R R'.
intros (M & X22 & X24) RP. split; [exact (mregs_keep R R' M RP)|].
split; [rewrite (L5SAR.cs_of_preserved R R' 22 RP) by inl; exact X22| rewrite (L5SAR.cs_of_preserved R R' 24 RP) by inl; exact X24].
Qed.
Definition tregs0 (R : bvmap 5 word) : Prop := mregs R /\ getr R (reg 22) = Z_to_bv 64 (F + 32).
Lemma tregs0_keep : ltac2:(TCodec.tc2 tcn__PmBBa2 "A&Gy5'RByR0%211%5241&Q6r2%211&Or3%2214%612p021p061pQJ:1pQH;1").
Proof. intros R R'. intros (M & X22) RP. split; [exact (mregs_keep R R' M RP)| rewrite (L5SAR.cs_of_preserved R R' 22 RP) by inl; exact X22]. Qed.
Lemma tregs0_of : ltac2:(TCodec.tc2 tcn__PmBBa2 ">&Gy5'RByR0%211%5241&Q5r1%211&Q6r2%211p041pQH81").
Proof. intros R. intros (M & X22 & _). split; assumption. Qed.
Lemma UB : ltac2:(TCodec.tc2 tcn__PmBBa2 "A'5'9&QIz&Q7vMr1%3221%6251&QJ&QL+2+R0%3221%5271%>271pU>@1").
Proof. intros x. unfold PMBBK.U. pose proof (bv_unsigned_in_range 64 (getr R0 (reg x))) as B. change (bv_modulus 64) with (2 ^ 64) in B. exact B. Qed.
Lemma rng_or : ltac2:(TCodec.tc2 tcn__PmBBa2 "A'='<'9&QIr2r3%3221&QJr1%2241%8241&;%112%<231pTB>1pTF?1pSN@1").
Proof. intros a lo hi. destruct (L5SAR.rng_dec a lo hi) as [X|X]; [left| right]; exact X. Qed.
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
Lemma vf_rng : ltac2:(TCodec.tc2 tcn__PmBBa2 "QB'2'='RByR0%211'6y8%511%311p051&Q<vMvQEvR5v>vR6r3r2r1%9887654321'9&QI+Vb\P0&Q;%11;%4231+Soooooood0%6231%8231+SoomohPTV0%921B+TPPPPPPPP0%;2D1%=231%=2<D+Sooooooon0%?2F1%A231+TP0%B21H+SooooooooO%D2J1%F231%G261%H2;1%I2A1p0K1pQDQ61pU<Q?1pU:QA1").
Proof. intros typed v MV.
intros VF. unfold PMBBK.vfacts in VF.
destruct VF as (_ & _ & _ & _ & SR & _ & _ & OR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
& FRg & _ & _ & _ & _ & _ & _ & FLg & _). split; [exact OR|]. split; [exact SR|]. split; [exact FRg| exact FLg].
Qed.
Lemma op8_apart : ltac2:(TCodec.tc2 tcn__PmBBa2 "R?'2'='RByR0%211'6y8%511%311p051&Q<vMvQEvR5v>vR6r3r2r1%9887654321'9&QI&QG&Q;%11;+8%4221%6219&QJ+9%8261%32=1%<251&;&QM+S@%22H1%@21D+S8%52K1%<2G1%E241%911+V0%:2Q01%H21L+U0%=2Q31%D2O1%M241%A11%N2Q5Q2%N2Q6K%I2Q41%Q2231%F11&QH%12Q;Q0+QoooPP0%Q5221%Q721Q;+QoooPP8%Q8251%Q32Q>1%Q<241%Q011':%13R2QBQD%Q311%QA241%QB2?1%QC2E1%QD2N1p0Q91pTDR91p0QH1pQDR31pU<R<1pU:R>1").
Proof. intros typed v MV.
intros VF i Hi. unfold PMBBK.vfacts in VF.
destruct VF as (_ & _ & _ & _ & SR & _ & _ & OR & _ & OB & _ & _ & _ & _ & OS & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
& FRg & _ & _ & _ & FB & _ & _ & _ & _ & _ & _ & _ & _ & OF & OFl & _).
assert (D : F / 8 <= 17592186044408) by (apply Z.div_le_upper_bound; lia). assert (D0 : 0 <= F / 8) by (apply Z.div_pos; lia).
destruct OS as [X|X]; [lia|]. destruct OF as [Y|Y]; destruct OFl as [Z0|Z0]; destruct OB as [W|W]; (split; [lia|]); (split; [lia|]); (split; [lia|]); (split; [lia| lia]).
Qed.
Lemma mk_Z1 : ltac2:(TCodec.tc2 tcn__PmBBa2 "SG'Q>'Q?'2'QA&Gy5'RByR0%211%5241'6y8%611%311p061'F'4&Q0%211&N'7'=%2211%711&Q8vBvQOv@vMvHvR;vCv?vDv1vR1vQEvR5vR0vR>vRCvR@vR4v>(3r;r:r9r6r5r4r3r2%MLLKJIHGFEDCBA@?>=<;:987654321&Q2r8%211':&QB&RA&QKu1%211%42QJ1%62A1+fYn4%72QK1%:3QK31u:%911%;2R11%=2I1&Q:%11Q4%?2R31%B3R341u;%A11%C2R91%E2Q21%E2R9O%H3R921'9&QI+1%221Q5+R0%42Q71%6231'QC&QD&Q1vQF%211&Q@r>r=+en`Hr<%5694321QFvA%<4;821p0>1p0F1p0M1p0Q61p0QB1p0QF1pU<RG1p2RF1pT6RK1pQ<RM1pTJS11pQFS31pQHS91pT@S@1pT8SB1pU0SD1pTLSF1").
Proof using All. intros s sm e fx R Mc modelc LKc crc Ac v.
intros BS MR A1 A10 A11 Hv. pose proof MR as ((X2 & X8 & X9 & X18 & X19 & X20 & X21 & X25 & X26 & X27 & X3 & X4) & X23).
apply (call_mkec false s sm e fx R Mc modelc LKc crc Ac 0xb27c4 v BS A1 ltac:(split; [lia| reflexivity]) X2 X3 X4 A10 A11 Hv).
intros fx' R' M' model' LK' Aw' RP BSE.
pose proof BSE as (BI & RUN & EC & _ & HD & FSH & STEP & SD & CRL & CRK).
pose proof (mregs_keep R R' MR RP) as ((Y2 & Y8 & Y9 & Y18 & Y19 & Y20 & Y21 & Y25 & Y26 & Y27 & Y3 & Y4) & Y23).
pose proof (vpack false _ s sm true v _ M' model' LK' crc Aw' BI RUN EC HD FSH) as VF.
set (MV := mrestrict (ahid Aw' model') M') in *.
pose proof (PMBBAP3.abaZ1_conc fx' R' MV (fun j => match j with 2%nat => S | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 48%nat => fl
| 57%nat => U 1 | 58%nat => U 8 | 59%nat => U 9 | 60%nat => U 18 | 61%nat => U 19 | 62%nat => U 20 | 63%nat => U 21 | 64%nat => U 22
| 65%nat => U 23 | 66%nat => U 24 | 67%nat => U 25 | 68%nat => U 26 | 69%nat => U 27 | _ => 0 end)) as P.
cbn beta iota in P. feedV P VF.
destruct P as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & PR). decompose [and] PR. clear PR.
apply (fin_any s sm true 0 (fun _ => False) fx' fx9 R' 0xb27c4 R9 M9v M' model' LK' crc Aw' BI RUN ltac:(left; reflexivity)
(fun a X => match X with end) (fun a => or_intror (fun X => X)) MS9 MG9).
- intros a Ha N1 _ N3 N4 N5. apply FRZ9; [exact Ha| intros X; apply N1; lia| intros X; apply N3; lia| intros X; apply N4; lia| intros X; apply N5; lia].
- assumption.
- assumption.
- assumption.
- assumption.
- assumption.
- assumption.
- intros j Hj. repeat (destruct Hj as [<-|Hj]; [assumption|]). destruct Hj.
- rewrite (KS9 3%nat) by inl. exact Y3.
- rewrite (KS9 4%nat) by inl. exact Y4.
- exact STEP.
- intros _; reflexivity.
- left. split; [exists v; split; [exact Hv| exact EC]|]. split; reflexivity.
- exact CRK.
Qed.
Lemma mk_Z11 : ltac2:(TCodec.tc2 tcn__PmBBa2 "SG'Q>'Q?'2'QA&Gy5'RByR0%211%5241'6y8%611%311p061'F'4&Q0%211&N'7'=%2211%711&Q9vBvQOv@vMvHvR;vCv?vDv1vR1vQEvR5vR0vR>vRCvR@vR4v>(3r;r:r9r6r5r4r3r2%MLLKJIHGFEDCBA@?>=<;:987654321&Q4r8%211':&QB&RA&QKu1%211%42QJ1%62A1+fYlH%72QK1%:3QK31u:%911%;2R11%=2I1&Q:%11Q4%?2R31%B3R341u;%A11%C2R91%E2Q21%E2R9O%H3R921'9&QI+1%221Q5+R0%42Q71%6231'QC&QD&Q1vQF%211&Q@r>r=+en`Hr<%5694321QFvA%<4;821p0>1p0F1p0M1p0Q61p0QB1p0QF1pU<RG1p2RF1pT6RK1pQ<RM1pTJS11pQFS31pQHS91pT@S@1pT8SB1pU0SD1pTLSF1").
Proof using All. intros s sm e fx R Mc modelc LKc crc Ac v.
intros BS MR A1 A10 A11 Hv. pose proof MR as (X2 & X8 & X9 & X18 & X19 & X20 & X21 & X25 & X26 & X27 & X3 & X4).
apply (call_mkec0 false s sm e fx R Mc modelc LKc crc Ac 0xb2798 v BS A1 ltac:(split; [lia| reflexivity]) X2 X3 X4 A10 A11 Hv).
intros fx' R' M' model' LK' Aw' RP BSE.
pose proof BSE as (BI & RUN & EC & _ & HD & FSH & STEP & SD & CRL & CRK).
pose proof (mregs0B1_keep R R' MR RP) as (Y2 & Y8 & Y9 & Y18 & Y19 & Y20 & Y21 & Y25 & Y26 & Y27 & Y3 & Y4).
pose proof (vpack false _ s sm true v _ M' model' LK' crc Aw' BI RUN EC HD FSH) as VF.
set (MV := mrestrict (ahid Aw' model') M') in *.
pose proof (PMBBAP3.abaZ11_conc fx' R' MV (fun j => match j with 2%nat => S | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 48%nat => fl
| 57%nat => U 1 | 58%nat => U 8 | 59%nat => U 9 | 60%nat => U 18 | 61%nat => U 19 | 62%nat => U 20 | 63%nat => U 21 | 64%nat => U 22
| 65%nat => U 23 | 66%nat => U 24 | 67%nat => U 25 | 68%nat => U 26 | 69%nat => U 27 | _ => 0 end)) as P.
cbn beta iota in P. feedV P VF.
destruct P as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & PR). decompose [and] PR. clear PR.
apply (fin_any s sm true 0 (fun _ => False) fx' fx9 R' 0xb2798 R9 M9v M' model' LK' crc Aw' BI RUN ltac:(left; reflexivity)
(fun a X => match X with end) (fun a => or_intror (fun X => X)) MS9 MG9).
- intros a Ha N1 _ N3 N4 N5. apply FRZ9; [exact Ha| intros X; apply N1; lia| intros X; apply N3; lia| intros X; apply N4; lia| intros X; apply N5; lia].
- assumption.
- assumption.
- assumption.
- assumption.
- assumption.
- assumption.
- intros j Hj. repeat (destruct Hj as [<-|Hj]; [assumption|]). destruct Hj.
- rewrite (KS9 3%nat) by inl. exact Y3.
- rewrite (KS9 4%nat) by inl. exact Y4.
- exact STEP.
- intros _; reflexivity.
- left. split; [exists v; split; [exact Hv| exact EC]|]. split; reflexivity.
- exact CRK.
Qed.
Lemma mk_Zc : ltac2:(TCodec.tc2 tcn__PmBBa2 "SG'Q>'Q?'2'QA&Gy5'RByR0%211%5241'6y8%611%311p061'F'4&Q0%211&N'7'=%2211%711&Q8vBvQOv@vMvHvR;vCv?vDv1vR1vQEvR5vR0vR>vRCvR@vR4v>(3r;r:r9r6r5r4r3r2%MLLKJIHGFEDCBA@?>=<;:987654321&Q2r8%211':&QB&RA&QKu1%211%42QJ1%62A1+fXj<%72QK1%:3QK31u:%911%;2R11%=2I1&Q:%11Q4%?2R31%B3R341u;%A11%C2R91%E2Q21%E2R9O%H3R921'9&QI+1%221Q5+R0%42Q71%6231'QC&QD&Q1vQF%211&Q@r>r=+en`Hr<%5694321QFvA%<4;821p0>1p0F1p0M1p0Q61p0QB1p0QF1pU<RG1p2RF1pT6RK1pQ<RM1pTJS11pQFS31pQHS91pT@S@1pT8SB1pU0SD1pTLSF1").
Proof using All. intros s sm e fx R Mc modelc LKc crc Ac v.
intros BS MR A1 A10 A11 Hv. pose proof MR as ((X2 & X8 & X9 & X18 & X19 & X20 & X21 & X25 & X26 & X27 & X3 & X4) & X23).
apply (call_mkec false s sm e fx R Mc modelc LKc crc Ac 0xb234c v BS A1 ltac:(split; [lia| reflexivity]) X2 X3 X4 A10 A11 Hv).
intros fx' R' M' model' LK' Aw' RP BSE.
pose proof BSE as (BI & RUN & EC & _ & HD & FSH & STEP & SD & CRL & CRK).
pose proof (mregs_keep R R' MR RP) as ((Y2 & Y8 & Y9 & Y18 & Y19 & Y20 & Y21 & Y25 & Y26 & Y27 & Y3 & Y4) & Y23).
pose proof (vpack false _ s sm true v _ M' model' LK' crc Aw' BI RUN EC HD FSH) as VF.
set (MV := mrestrict (ahid Aw' model') M') in *.
pose proof (PMBBAP3.abaZc_conc fx' R' MV (fun j => match j with 2%nat => S | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 48%nat => fl
| 57%nat => U 1 | 58%nat => U 8 | 59%nat => U 9 | 60%nat => U 18 | 61%nat => U 19 | 62%nat => U 20 | 63%nat => U 21 | 64%nat => U 22
| 65%nat => U 23 | 66%nat => U 24 | 67%nat => U 25 | 68%nat => U 26 | 69%nat => U 27 | _ => 0 end)) as P.
cbn beta iota in P. feedV P VF.
destruct P as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & PR). decompose [and] PR. clear PR.
apply (fin_any s sm true 0 (fun _ => False) fx' fx9 R' 0xb234c R9 M9v M' model' LK' crc Aw' BI RUN ltac:(left; reflexivity)
(fun a X => match X with end) (fun a => or_intror (fun X => X)) MS9 MG9).
- intros a Ha N1 _ N3 N4 N5. apply FRZ9; [exact Ha| intros X; apply N1; lia| intros X; apply N3; lia| intros X; apply N4; lia| intros X; apply N5; lia].
- assumption.
- assumption.
- assumption.
- assumption.
- assumption.
- assumption.
- intros j Hj. repeat (destruct Hj as [<-|Hj]; [assumption|]). destruct Hj.
- rewrite (KS9 3%nat) by inl. exact Y3.
- rewrite (KS9 4%nat) by inl. exact Y4.
- exact STEP.
- intros _; reflexivity.
- left. split; [exists v; split; [exact Hv| exact EC]|]. split; reflexivity.
- exact CRK.
Qed.
Lemma mk_Zt : ltac2:(TCodec.tc2 tcn__PmBBa2 "SG'Q>'Q?'2'QA&Gy5'RByR0%211%5241'6y8%611%311p061'F'4&Q0%211&N'7'=%2211%711&Q8vBvQOv@vMvHvR;vCv?vDv1vR1vQEvR5vR0vR>vRCvR@vR4v>(8r;r:r9r6r5r4r3r2%MLLKJIHGFEDCBA@?>=<;:987654321&Q6r8%211':&QB&RA&QKu1%211%42QJ1%62A1+fYW<%72QK1%:3QK31u:%911%;2R11%=2I1&Q:%11Q4%?2R31%B3R341u;%A11%C2R91%E2Q21%E2R9O%H3R921'9&QI+1%221Q5+R0%42Q71%6231'QC&QD&Q1vQF%211&Q@r>r=+en`Hr<%5694321QFvA%<4;821p0>1p0F1p0M1p0Q61p0QB1p0QF1pU<RG1p2RF1pT6RK1pQ<RM1pTJS11pQFS31pQHS91pT@S@1pT8SB1pU0SD1pTLSF1").
Proof using All. intros s sm e fx R Mc modelc LKc crc Ac v.
intros BS MR A1 A10 A11 Hv. pose proof MR as (((X2 & X8 & X9 & X18 & X19 & X20 & X21 & X25 & X26 & X27 & X3 & X4) & X23) & X22).
apply (call_mkec true s sm e fx R Mc modelc LKc crc Ac 0xb24ec v BS A1 ltac:(split; [lia| reflexivity]) X2 X3 X4 A10 A11 Hv).
intros fx' R' M' model' LK' Aw' RP BSE.
pose proof BSE as (BI & RUN & EC & _ & HD & FSH & STEP & SD & CRL & CRK).
pose proof (tregs0_keep R R' MR RP) as (((Y2 & Y8 & Y9 & Y18 & Y19 & Y20 & Y21 & Y25 & Y26 & Y27 & Y3 & Y4) & Y23) & Y22).
pose proof (vpack true _ s sm true v _ M' model' LK' crc Aw' BI RUN EC HD FSH) as VF.
set (MV := mrestrict (ahid Aw' model') M') in *.
pose proof (PMBBAP2.abaZt_conc fx' R' MV (fun j => match j with 2%nat => S | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 48%nat => fl
| 57%nat => U 1 | 58%nat => U 8 | 59%nat => U 9 | 60%nat => U 18 | 61%nat => U 19 | 62%nat => U 20 | 63%nat => U 21 | 64%nat => U 22
| 65%nat => U 23 | 66%nat => U 24 | 67%nat => U 25 | 68%nat => U 26 | 69%nat => U 27 | _ => 0 end)) as P.
cbn beta iota in P. feedV P VF.
destruct P as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & PR). decompose [and] PR. clear PR.
apply (fin_any s sm true 0 (fun _ => False) fx' fx9 R' 0xb24ec R9 M9v M' model' LK' crc Aw' BI RUN ltac:(left; reflexivity)
(fun a X => match X with end) (fun a => or_intror (fun X => X)) MS9 MG9).
- intros a Ha N1 _ N3 N4 N5. apply FRZ9; [exact Ha| intros X; apply N1; lia| intros X; apply N3; lia| intros X; apply N4; lia| intros X; apply N5; lia].
- assumption.
- assumption.
- assumption.
- assumption.
- assumption.
- assumption.
- intros j Hj. repeat (destruct Hj as [<-|Hj]; [assumption|]). destruct Hj.
- rewrite (KS9 3%nat) by inl. exact Y3.
- rewrite (KS9 4%nat) by inl. exact Y4.
- exact STEP.
- intros _; reflexivity.
- left. split; [exists v; split; [exact Hv| exact EC]|]. split; reflexivity.
- exact CRK.
Qed.
Lemma mk_Zt13 : ltac2:(TCodec.tc2 tcn__PmBBa2 "SG'Q>'Q?'2'QA&Gy5'RByR0%211%5241'6y8%611%311p061'F'4&Q0%211&N'7'=%2211%711&Q8vBvQOv@vMvHvR;vCv?vDv1vR1vQEvR5vR0vR>vRCvR@vR4v>(8r;r:r9r6r5r4r3r2%MLLKJIHGFEDCBA@?>=<;:987654321&Q5r8%211':&QB&RA&QKu1%211%42QJ1%62A1+fXf@%72QK1%:3QK31u:%911%;2R11%=2I1&Q:%11Q4%?2R31%B3R341u;%A11%C2R91%E2Q21%E2R9O%H3R921'9&QI+1%221Q5+R0%42Q71%6231'QC&QD&Q1vQF%211&Q@r>r=+en`Hr<%5694321QFvA%<4;821p0>1p0F1p0M1p0Q61p0QB1p0QF1pU<RG1p2RF1pT6RK1pQ<RM1pTJS11pQFS31pQHS91pT@S@1pT8SB1pU0SD1pTLSF1").
Proof using All. intros s sm e fx R Mc modelc LKc crc Ac v.
intros BS MR A1 A10 A11 Hv. pose proof MR as (((X2 & X8 & X9 & X18 & X19 & X20 & X21 & X25 & X26 & X27 & X3 & X4) & X23) & X22 & X24).
apply (call_mkec true s sm e fx R Mc modelc LKc crc Ac 0xb22d0 v BS A1 ltac:(split; [lia| reflexivity]) X2 X3 X4 A10 A11 Hv).
intros fx' R' M' model' LK' Aw' RP BSE.
pose proof BSE as (BI & RUN & EC & _ & HD & FSH & STEP & SD & CRL & CRK).
pose proof (tregs_keep R R' MR RP) as (((Y2 & Y8 & Y9 & Y18 & Y19 & Y20 & Y21 & Y25 & Y26 & Y27 & Y3 & Y4) & Y23) & Y22 & Y24).
pose proof (vpack true _ s sm true v _ M' model' LK' crc Aw' BI RUN EC HD FSH) as VF.
set (MV := mrestrict (ahid Aw' model') M') in *.
pose proof (PMBBAP2.abaZt13_conc fx' R' MV (fun j => match j with 2%nat => S | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 48%nat => fl
| 57%nat => U 1 | 58%nat => U 8 | 59%nat => U 9 | 60%nat => U 18 | 61%nat => U 19 | 62%nat => U 20 | 63%nat => U 21 | 64%nat => U 22
| 65%nat => U 23 | 66%nat => U 24 | 67%nat => U 25 | 68%nat => U 26 | 69%nat => U 27 | _ => 0 end)) as P.
cbn beta iota in P. feedV P VF.
destruct P as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & PR). decompose [and] PR. clear PR.
apply (fin_any s sm true 0 (fun _ => False) fx' fx9 R' 0xb22d0 R9 M9v M' model' LK' crc Aw' BI RUN ltac:(left; reflexivity)
(fun a X => match X with end) (fun a => or_intror (fun X => X)) MS9 MG9).
- intros a Ha N1 _ N3 N4 N5. apply FRZ9; [exact Ha| intros X; apply N1; lia| intros X; apply N3; lia| intros X; apply N4; lia| intros X; apply N5; lia].
- assumption.
- assumption.
- assumption.
- assumption.
- assumption.
- assumption.
- intros j Hj. repeat (destruct Hj as [<-|Hj]; [assumption|]). destruct Hj.
- rewrite (KS9 3%nat) by inl. exact Y3.
- rewrite (KS9 4%nat) by inl. exact Y4.
- exact STEP.
- intros _; reflexivity.
- left. split; [exists v; split; [exact Hv| exact EC]|]. split; reflexivity.
- exact CRK.
Qed.
Ltac gle_tail typed conc BE s sm Mc modelc LKc crc Ac fx R pc :=
pose proof BE as (BI & RUN & (v & Hv & EC) & MO & HD & FSH & STEP & CRL & CRK & VSL);
pose proof (vpack typed _ s sm true v _ Mc modelc LKc crc Ac BI RUN EC HD FSH) as VF;
set (MV := mrestrict (ahid Ac modelc) Mc) in *;
assert (MO8 : L5.u8_at RSEGS MV (op + 8) 0);
[ pose proof BI as (HHc & _); pose proof RUN as (PA & _); pose proof PA as (_ & _ & _ & P8 & _); rewrite MO in P8;
pose proof (PMBPAR.op_vis L ar C HI LY HIok _ FF' LKc crc Ac Mc modelc fb _ s HHc (PMBUAR.frame_okA_push FF fb F 0 (S - 160 + 32) FOK) PA)
as ((O1 & _) & _ & _ & _ & _ & _ & OAV & _ & _);
apply (proj2 (L5A.u8_at_vis (ahid Ac modelc) Mc (op + 8) 0 (OAV (op + 8) 1 ltac:(unfold PMBBK.op; lia) ltac:(unfold PMBBK.op; lia)) ltac:(unfold PMBBK.op; lia) ltac:(unfold PMBBK.op; lia)));
exact P8 |];
pose proof (eq_sym (Z_to_bv_bv_unsigned 64 (getr R (reg 10)))) as A10;
pose proof (bv_unsigned_in_range 64 (getr R (reg 10))) as B10; change (bv_modulus 64) with (2 ^ 64) in B10;
assert (Hv' : 0 <= v < 2 ^ 64) by lia;
pose proof (conc fx R MV (fun j => match j with 2%nat => S | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 48%nat => fl | 49%nat => v
| 50%nat => bv_unsigned (getr R (reg 10))
| 57%nat => U 1 | 58%nat => U 8 | 59%nat => U 9 | 60%nat => U 18 | 61%nat => U 19 | 62%nat => U 20 | 63%nat => U 21 | 64%nat => U 22
| 65%nat => U 23 | 66%nat => U 24 | 67%nat => U 25 | 68%nat => U 26 | 69%nat => U 27 | _ => 0 end)) as P;
cbn beta iota in P; feedV P VF;
destruct P as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & PR); decompose [and] PR; clear PR;
apply (fin_any s sm true 0 (fun a => S - 112 <= a < S - 104) fx fx9 R pc R9 M9v Mc modelc LKc crc Ac BI RUN ltac:(left; reflexivity)
(fun a X => or_intror X) (fun a => rng_or a (S - 112) (S - 104)) MS9 MG9);
[ intros a Ha N1 N2 N3 N4 N5; apply FRZ9; [exact Ha| intros X; apply N2; lia| intros X; apply N3; lia| intros X; apply N4; lia| intros X; apply N5; lia]
| assumption
| pose proof (vf_rng typed v MV VF) as (Rop & _);
apply (L5C.u8_at_agree RSEGS MV M9v); [intros i Hi; destruct (op8_apart typed v MV VF i ltac:(lia)) as (Q1 & _ & Q3 & Q4 & Q5);
apply FRZ9; [lia| intros X; apply Q1; lia| intros X; apply Q3; lia| intros X; apply Q4; lia| intros X; apply Q5; lia]| lia| lia| exact MO8]
| assumption | assumption | assumption | assumption
| intros j Hj; repeat (destruct Hj as [<-|Hj]; [assumption|]); destruct Hj
| rewrite (KS9 3%nat) by inl; assumption
| rewrite (KS9 4%nat) by inl; assumption
| exact STEP
| intros _; reflexivity
| left; split; [exists v; split; [exact Hv| exact EC]|]; split; reflexivity
| exact CRK ].
Lemma gl_err_C : ltac2:(TCodec.tc2 tcn__PmBBa2 "R;'Q>'Q?'QA&Gy5'RByR0%211%5241'6y8%611%311p061'F'4&Q0%211&N'7'=%2211%711&Q=vBvQOv@vMvHvR;vCv?vDv1vR1vQEvR5vR>vRCvR@v>(3r9r8r5r4r3r2r1%JIIHGFEDCBA@?>=<;:987654321&Q2r7%211'QC&QD&Q1vQF%211&Q@+fXh8r6%367CB2:1vA%:49621p0<1p0@1p2Q<1pT6QA1pQ<QC1pTJQG1pQFQI1pQHQO1pT@R61pU0R81pTLR:1").
Proof using All. intros s sm fx R Mc modelc LKc crc Ac.
intros BE MR. pose proof MR as ((X2 & X8 & X9 & X18 & X19 & X20 & X21 & X25 & X26 & X27 & X3 & X4) & X23).
gle_tail false PMBBAP3.abaCe_conc BE s sm Mc modelc LKc crc Ac fx R 0xb2308.
Qed.
Lemma gl_err_T : ltac2:(TCodec.tc2 tcn__PmBBa2 "R;'Q>'Q?'QA&Gy5'RByR0%211%5241'6y8%611%311p061'F'4&Q0%211&N'7'=%2211%711&Q=vBvQOv@vMvHvR;vCv?vDv1vR1vQEvR5vR>vRCvR@v>(8r9r8r5r4r3r2r1%JIIHGFEDCBA@?>=<;:987654321&Q5r7%211'QC&QD&Q1vQF%211&Q@+fXd<r6%367CB2:1vA%:49621p0<1p0@1p2Q<1pT6QA1pQ<QC1pTJQG1pQFQI1pQHQO1pT@R61pU0R81pTLR:1").
Proof using All. intros s sm fx R Mc modelc LKc crc Ac.
intros BE MR. pose proof MR as (((X2 & X8 & X9 & X18 & X19 & X20 & X21 & X25 & X26 & X27 & X3 & X4) & X23) & X22 & X24).
gle_tail true PMBBAP2.abaTe_conc BE s sm Mc modelc LKc crc Ac fx R 0xb228c.
Qed.
End Frame.
End Call.
End WithHeap.
End PMBBA2.
