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
PmModelFactsA PmStepAB0 PmStep PmParStep PmParKit PmBSrcKit PmBParKit PmBReset1 PmBUarK PmBUar PmBUarKS PmBBoK PmBBoK2 PmBBoK3 Jb0_code_b2f4c_b2f50 PmBBo1 PmBBoP1 PmBBoP2 PmBBoP3 PmBBo2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmBBo3 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBBo3.PMBBO3.WithHeap.Call.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBBoK.PMBBOK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBBoK3.PMBBOK3."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmParKit.PMPK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0Ac"; "0Aw0"; "1bool"; "1false"; "1length"; "1list"; "1option"; "1prod"; "1true"; "2and"; "2eq"; "2not"; "2or"; "3Z"; "0F"; "0FF"]; ["0HI"; "0K"; "0L"; "0LBX"; "0LK0"; "0LKc"; "4Model"; "5bvmap"; "0M0"; "0Mc"; "0R"; "0R'"; "0R0"; "6mrestrict"; "7credit"; "7regs_preserved"]; ["8ahid"; "8fframe"; ":defined"; ":u64_at"; "9SCFG"; ";pregsI"; ";pregsT"; "<op"; "=bstp"; ">inv"; ">p_b"; ">p_stk"; ">pst"; ">pstate"; ">strm"; "?set_more"]; ["@cfg"; "AFPState"; "Agetr"; "Bsrealizes"; "Cloaded_segments"; "0S"; "0SCFG_P"; "Dadd"; "Dle"; "Dlt"; "Dmodulo"; "Dmul"; "Dof_nat"; "Dpow"; "Dsub"; "0a"]; ["0ar"; "0cat"; "0cr0"; "0crc"; "0e"; "0e0"; "0fb"; "0fx"; "0hi"; "0len"; "0lo"; "0model0"; "0modelc"; "0s"; "0s0"; "0sm"]; ["0sm0"; "EZ_to_bv"; "Ebv"; "0str"; "0typed"]]).
Local Ltac lia := L5FastLia.plia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PMBBO3.
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
Local Abbreviation SCR := PMBBOK.SCR.
Local Abbreviation BARR := PMBBOK.BARR.
Local Abbreviation op := (PMBBOK.op fb).
Local Abbreviation ois := (PMBBOK.ois fb).
Local Abbreviation ov := (PMBBOK.ov fb).
Local Abbreviation oec := (PMBBOK.oec fb).
Local Abbreviation WR := (PMBBOK.WR fb).
Local Abbreviation U := (PMBBOK.U R0).
Local Abbreviation ocell := (PMBBOK.ocell S).
Local Abbreviation own := (PMBBOK.own R0 S).
Local Abbreviation own_agree := (PMBBOK.own_agree R0 S).
Local Abbreviation sd := (PMBBOK.sd s0).
Local Abbreviation sdl := (PMBBOK.sdl s0).
Local Abbreviation spush := (PMBBOK.spush s0).
Local Abbreviation frame_geo := (PMBBOK.frame_geo fb).
Section Frame.
Variables (F fl : Z) (LK2 : list fframe) (M2 : word -> option byte) (model2 : Model).
Hypothesis G : PMBUK.gctx L ar HI LBX FF LK0 Aw0 S SCR (S - 160) (S - 104) S ocell own F fl 0 LK2 M2 model2 cr0 (PM.parser_own s0).
Local Abbreviation FF' := (PMBBOK.FF' FF S F).
Local Abbreviation binv' := (PMBBOK.binv' L ar HI R0 M0 model0 LBX FF LK0 Aw0 S fb F).
Local Abbreviation hdr := (PMBBOK.hdr S F).
Local Abbreviation fsh := (PMBBOK.fsh F).
Local Abbreviation bst := (PMBBOK.bst L ar HI R0 M0 model0 LBX FF LK0 Aw0 cr0 S fb cat s0 str sm0 e0 F).
Local Abbreviation bst0 := (PMBBOK.bst0 L ar HI R0 M0 model0 LBX FF LK0 Aw0 cr0 S fb cat s0 str sm0 e0 F).
Local Abbreviation bste := (PMBBOK.bste L ar HI R0 M0 model0 LBX FF LK0 Aw0 cr0 S fb s0 str sm0 F).
Local Abbreviation vfacts := (PMBBOK.vfacts R0 S fb F fl).
Local Abbreviation vpack := (PMBBOK.vpack L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE CMI SMI CMS SMS CMSU SMSU F fl LK2 M2 model2 G).
Local Abbreviation centry := (PMBBOK.centry L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE CMI SMI CMS SMS CMSU SMSU F fl LK2 M2 model2 G).
Local Abbreviation own_with_src := PMBBOK.own_with_src.
Local Abbreviation call_src := (PMBBOK.call_src L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE CMI SMI CMS SMS CMSU SMSU F fl LK2 M2 model2 G).
Local Abbreviation call_mkec := (PMBBOK.call_mkec L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE CMI SMI CMS SMS CMSU SMSU F fl LK2 M2 model2 G).
Local Abbreviation call_mkec0 := (PMBBOK.call_mkec0 L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE CMI SMI CMS SMS CMSU SMSU F fl LK2 M2 model2 G).
Local Abbreviation fsh_nc := (PMBBOK2.fsh_nc L ar C HI HIok R0 LBX FF LK0 Aw0 cr0 S s0 F fl LK2 M2 model2 G).
Local Abbreviation fsh_agree := (PMBBOK2.fsh_agree S F).
Local Abbreviation step_piece := (PMBBOK2.step_piece L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE CMI SMI CMS SMS CMSU SMSU F fl LK2 M2 model2 G).
Local Abbreviation wr_rng := (PMBBOK2.wr_rng fb).
Local Abbreviation bsterr := (PMBBOK2.bsterr L ar HI R0 M0 model0 LBX FF LK0 Aw0 cr0 S fb s0 str sm0 F).
Local Abbreviation call_gl := (PMBBOK2.call_gl L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE CMI SMI CMS SMS CMSU SMSU F fl LK2 M2 model2 G).
Local Abbreviation push_st := PMBBOK3.push_st.
Local Abbreviation aacc_sub := PMBBOK3.aacc_sub.
Local Abbreviation parser_push_updA := PMBBOK3.parser_push_updA.
Local Abbreviation stack_shape_push := PMBBOK3.stack_shape_push.
Local Abbreviation ri_swap12 := (PMBBOK3.ri_swap12 L ar C HI HIok).
Local Abbreviation stk_credit := (PMBBOK3.stk_credit L ar C LY).
Local Abbreviation bstp := (PMBBOK3.bstp L ar HI R0 M0 model0 LBX FF LK0 Aw0 cr0 S fb cat s0 str sm0 e0 F).
Local Abbreviation call_push := (PMBBOK3.call_push L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE CMI SMI CMS SMS CMSU SMSU F fl LK2 M2 model2 G).
Local Abbreviation vsl_vis := (PMBBOK3.vsl_vis L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE CMI SMI CMS SMS CMSU SMSU F fl LK2 M2 model2 G).
Local Abbreviation fin_any := (PMBBO1.fin_any L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb cat s0 str sm0 e0 HH0 AM0 K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT PEEK IGN SRD GLS MKE CMI SMI CMS SMS CMSU SMSU F fl LK2 M2 model2 G).
Local Abbreviation mregs0 := (PMBBO2.mregs0 R0 S fb F).
Local Abbreviation mregs := (PMBBO2.mregs R0 S fb F).
Local Abbreviation tregs := (PMBBO2.tregs R0 S fb F).
Local Abbreviation UB := (PMBBO2.UB R0).
Lemma rng_or : ltac2:(TCodec.tc2 tcn__PmBBo3 "A'='<'9&QHr2r3%3221&QIr1%2241%8241&;%112%<231pTB>1pTF?1pT0@1").
Proof. intros a lo hi. destruct (L5SAR.rng_dec a lo hi) as [X|X]; [left| right]; exact X. Qed.
Ltac vopen VF := unfold PMBBOK.vfacts, PMBBOK.hdr, PMBBOK.own, PMBBOK.fsh in VF; cbn iota in VF; decompose [and] VF; clear VF.
Ltac hx := match goal with |- ?G => match goal with H : G |- _ => exact H end end.
Ltac vfeed := first [ hx | (split; hx) | apply UB | (unfold PMBBOP1.aligned; hx) | (unfold PMBBOP2.aligned; hx) | (unfold PMBBOP3.aligned; hx) ].
Ltac vfeedV VF := first [ assumption | apply UB | unfold PMBBOP1.aligned; assumption | unfold PMBBOP2.aligned; assumption | unfold PMBBOP3.aligned; assumption
| let W := fresh "W" in pose proof VF as W; vopen W; vfeed ].
Ltac feedV P VF :=
let T := type of P in
let C := L5SAR.feed_concl T in
let Q := fresh "SC" in
assert (Q : C) by (let W := fresh "W" in pose proof VF as W; vopen W; apply P; clear P;
first [ vfeed | lazymatch goal with |- ?A => fail 1 "feedV: cannot prove premise" A end ]);
move Q after P; clear P; rename Q into P.
Lemma inv_more1 : ltac2:(TCodec.tc2 tcn__PmBBo3 ";'Q<&Q9r1%211&Q?r2+1%3221%711p061pTL:1").
Proof. intros s. intros (I1 & I2 & I3 & I4 & I5). unfold PM.inv, PMPK.set_more. cbn [PM.p_more PM.p_done PM.p_depth PM.p_stk PM.p_tb PM.p_tg]. split; [reflexivity|]. split; [exact I2|]. split; [exact I3|]. split; [exact I4| exact I5]. Qed.
Definition VT (x49 x50 : Z) (j : nat) : Z :=
match j with 2%nat => S | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 48%nat => fl | 49%nat => x49 | 50%nat => x50
| 57%nat => U 1 | 58%nat => U 8 | 59%nat => U 9 | 60%nat => U 18 | 61%nat => U 19 | 62%nat => U 20 | 63%nat => U 21 | 64%nat => U 22
| 65%nat => U 23 | 66%nat => U 24 | 67%nat => U 25 | 68%nat => U 26 | 69%nat => U 27 | _ => 0 end.
Definition VTj (x50 x53 x55 : Z) (j : nat) : Z := match j with 53%nat => x53 | 55%nat => x55 | _ => VT 0 x50 j end.
Definition pregs (R : bvmap 5 word) : Prop :=
getr R (reg 2) = Z_to_bv 64 (S - 160) /\ getr R (reg 8) = Z_to_bv 64 S /\ getr R (reg 9) = Z_to_bv 64 (S - 160) /\ getr R (reg 18) = Z_to_bv 64 F
/\ getr R (reg 19) = Z_to_bv 64 op /\ getr R (reg 20) = Z_to_bv 64 oec
/\ getr R (reg 25) = Z_to_bv 64 F /\ getr R (reg 26) = Z_to_bv 64 (F / 8 + 2147450880) /\ getr R (reg 27) = Z_to_bv 64 2147450880
/\ getr R (reg 3) = getr R0 (reg 3) /\ getr R (reg 4) = getr R0 (reg 4).
Definition pregsI (R : bvmap 5 word) : Prop := pregs R /\ getr R (reg 22) = Z_to_bv 64 (op + 368) /\ getr R (reg 23) = Z_to_bv 64 ((op + 368) / 8 + 2147450880).
Definition pregsT (R : bvmap 5 word) : Prop :=
pregs R /\ getr R (reg 22) = Z_to_bv 64 (F + 32) /\ getr R (reg 23) = Z_to_bv 64 (op + 368) /\ getr R (reg 24) = Z_to_bv 64 ((op + 368) / 8 + 2147450880).
Lemma pregsI_keep : ltac2:(TCodec.tc2 tcn__PmBBo3 "A&Gy5'RByR0%211%5241&Q5r2%211&Or3%2214%612p021p061pQH:1pQF;1").
Proof. intros R R'.
intros ((X2 & X8 & X9 & X18 & X19 & X20 & X25 & X26 & X27 & X3 & X4) & X22 & X23) RP.
assert (K' : forall j, In j L5SAR.cs_all -> getr R' (reg j) = getr R (reg j)) by (intros j Hj; exact (L5SAR.cs_of_preserved R R' j RP Hj)).
repeat split; [rewrite K' by inl; assumption ..].
Qed.
Lemma pregsT_keep : ltac2:(TCodec.tc2 tcn__PmBBo3 "A&Gy5'RByR0%211%5241&Q6r2%211&Or3%2214%612p021p061pQH:1pQF;1").
Proof. intros R R'.
intros ((X2 & X8 & X9 & X18 & X19 & X20 & X25 & X26 & X27 & X3 & X4) & X22 & X23 & X24) RP.
assert (K' : forall j, In j L5SAR.cs_all -> getr R' (reg j) = getr R (reg j)) by (intros j Hj; exact (L5SAR.cs_of_preserved R R' j RP Hj)).
repeat split; [rewrite K' by inl; assumption ..].
Qed.
Lemma vec_end : ltac2:(TCodec.tc2 tcn__PmBBo3 "S;'2'Q<'Q>'RByR0%211'6y8%511%311p051'F'5&Q1%211&N'7'=%2211%711&Q8vBvR0v@vLvHvR;vCv?vDv1vR2vQEvR6vR1vR>vRCvR@vR5v>r9r8r7r6r5r4r3r2r1%MLLKJIHGFEDCBA@?>=<;:987654321'9&Q3&QD&M&Q0%128;%321=&QG&Q7%11J+[@%4221&Q:%11G&QK+Q0&QL&4'Q=&Q;%11N%4231%611%9281%A2;1%H4GC>1&Q2+8%23FA1&QH+TP0%H21@%3218&QM+2+Q?%3221%82=1%Q6261':&QJ%12A>z%43R<21%Q<261%Q=2A1%Q>2E1p0Q@1p2R?1pT8RD1pQ<RF1pTJRJ1pQDRL1pT:S71pU0S61pTLS81pU:S:1").
Proof using All. intros typed s sm e Mc modelc LKc crc Ac.
intros BP. unfold PMBBOK.op. pose proof BP as (BI & RUN & EC & HD & FSH & STEP & E0' & INV' & PV & CRL & CRK & VSL).
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
pose proof INV' as (_ & _ & _ & (SL1 & _) & _).
pose proof (PM.pow2_pos (PM.p_k s) (proj1 Hk')) as P2.
set (n := Z.of_nat (length (PM.p_stk s))) in *.
assert (Hn1 : 1 <= n) by (unfold n; lia).
replace (PMSPA.o_p AD fb + 360 + 8) with (PMSPA.o_p AD fb + 368) in V8 by lia.
split; [apply (proj2 (L5A.u64_at_vis _ Mc (PMSPA.o_p AD fb + 368) _ (OAV (PMSPA.o_p AD fb + 368) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact V8|].
split; [apply (proj2 (L5A.defined_vis _ Mc (PMSPA.o_p AD fb + 368) 8 (OAV (PMSPA.o_p AD fb + 368) 8 ltac:(lia) ltac:(lia))));
apply (L5.defined_sub Mc (PMSPA.o_p AD fb) 384); [exact PDEF| lia| lia]|].
split; [lia|].
assert (Eb : PM.p_b s = 16 * (PM.p_b s / 16)) by (pose proof (Z.div_mod (PM.p_b s) 16 ltac:(lia)); lia).
rewrite Eb. replace (16 * (PM.p_b s / 16) + 32 * n) with ((2 * (PM.p_b s / 16) + 4 * n) * 8) by lia. apply Z_mod_mult.
Qed.
Ltac ok_tailj typed conc Wy WYin WYD VM NE UMV DMV BP s sm e Mc modelc LKc crc Ac fx R pc :=
pose proof BP as (BI & RUN & EC & HD & FSH & STEP & E0' & INV' & PV & CRL & CRK & VSL);
pose proof (vpack typed _ s sm e 0 cat Mc modelc LKc crc Ac BI RUN EC HD FSH) as VF;
pose proof (vsl_vis _ Mc modelc LKc crc Ac BI VSL) as VSLv;
pose proof (PMBBO2.vf_rng R0 S fb F fl typed 0 _ VF) as (Rop & RS & RF & Rfl);
set (MV := mrestrict (ahid Ac modelc) Mc) in *;
pose proof (conc fx R MV VM) as P; unfold VTj, VT in P;
cbn beta iota in P; feedV P VF;
destruct P as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & PR); decompose [and] PR; clear PR;
lazymatch goal with U9 : L5.u64_at RSEGS M9v (op + 368) ?x |- _ =>
let U9' := fresh "U9'" in
assert (U9' : L5.u64_at RSEGS M9v (op + 368) NE) by (replace NE with x by lia; exact U9);
assert (SAME : forall i, op + 368 <= i < op + 376 -> M9v (Z_to_bv 64 i) = MV (Z_to_bv 64 i))
by (intros i Hi; apply (PMBPQ.u64_same_agree RSEGS MV M9v (op + 368) NE); [lia| lia| exact UMV| exact U9'| exact DMV| exact (L5.defined_grows MV M9v _ _ MG9 DMV)| lia])
end;
apply (fin_any s sm e 1 Wy fx fx9 R pc R9 M9v Mc modelc LKc crc Ac BI RUN ltac:(right; reflexivity));
[ exact WYin | exact WYD | exact MS9 | exact MG9 | | assumption | assumption | assumption | assumption | assumption | assumption
| intros j Hj; repeat (destruct Hj as [<-|Hj]; [assumption|]); destruct Hj
| rewrite (KS9 3%nat) by inl; assumption
| rewrite (KS9 4%nat) by inl; assumption
| exact STEP
| exact E0'
| right; split; [exact EC|]; split; [exact (inv_more1 s INV')| exact PV]
| exact CRK ].
Ltac slv_tac BP SL :=
pose proof BP as (BI0 & _); pose proof G as G'; destruct G' as [Hk SPTg SLOg SHIg SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS];
pose proof (PMBUK.vis_facts L ar C HI LYa HIok M0 model0 LBX FF LK0 Aw0 S SCR (S - 160) (S - 104) S ocell own F fl 0 LK2 M2 model2 cr0 (PM.parser_own s0) G WR _ _ _ _ _ _ BI0)
as (_ & _ & _ & (_ & _ & _ & SV8 & _));
apply (proj2 (L5A.u64_at_vis _ _ (S - 112) _ (L5A.avis_sub _ (S - 160) (S - (S - 160)) (S - 112) 8 SV8 ltac:(lia) ltac:(lia)) ltac:(unfold SCR in *; lia) ltac:(unfold SCR in *; lia)));
exact SL.
Lemma tail_Ic : ltac2:(TCodec.tc2 tcn__PmBBo3 "S:'Q<'Q>'2'QA&Gy5'RByR0%211%5241'6y8%611%311p061'F'5&Q1%211&N'7'=%2211%711&Q8vBvR0v@vLvHvR;vCv?vDv1vR2vQEvR6vR1vR>vRCvR@vR5v>(3r:r9r8r5r4r3r2r1%MLLKJIHGFEDCBA@?>=<;:987654321&Q5r7%211':&QB&RA&QLuE%211%42QJ1%62A1&QN&QG&Q:r<%211&QK+Q0&4'Q=&Q;%117%4231%A11%8271%=2:1%?219%F2R:1%I3R:B1'QC&QD&Q4vQF%211&Q@+f[QL%266Q=Q<1Q;Q3vA%948521p0;1p0Q61p0Q:1p2R91pT8R>1pQ<R@1pTJRD1pQDRF1pQFRL1pT@S31pT:S51pU0S71pTLS91").
Proof using All. intros s sm e fx R Mc modelc LKc crc Ac.
intros BP PRG X21. pose proof PRG as ((X2 & X8 & X9 & X18 & X19 & X20 & X25 & X26 & X27 & X3 & X4) & X22 & X23).
destruct (vec_end false s sm e Mc modelc LKc crc Ac BP) as (UMV & DMV & NEr & NE8).
set (NE := PM.p_b s + 32 * Z.of_nat (length (PM.p_stk s))) in *.
assert (R53 : 4096 <= NE - 32 <= 140737488355296) by lia.
assert (A53 : (NE - 32) mod 8 = 0) by (rewrite Zminus_mod, NE8; reflexivity).
assert (B53 : 0 <= NE - 32 < 2 ^ 64) by lia.
ok_tailj false PMBBOP1.aboITc_conc (fun a : Z => False) (fun (a : Z) (X : False) => match X return (S - 192 <= a < S - 160) \/ (S - 112 <= a < S - 104) with end)
(fun a : Z => @or_intror False (~ False) (fun X => X)) (VTj 0 (NE - 32) 0) NE UMV DMV BP s sm e Mc modelc LKc crc Ac fx R 0xb2c3c.
intros a Ha N1 N2 N3 N4 N5. destruct (rng_or a (op + 368) (op + 376)) as [IN|OUT]; [exact (SAME a IN)|].
apply FRZ9; [exact Ha| intros X; apply OUT; lia| intros X; apply N1; lia| intros X; apply N3; lia| intros X; apply N4; lia| intros X; apply N5; lia].
Qed.
Lemma tail_Is : ltac2:(TCodec.tc2 tcn__PmBBo3 "S8'Q<'Q>'2'QA&Gy5'RByR0%211%5241'6y8%611%311p061'F'5&Q1%211&N'7'=%2211%711&Q8vBvR0v@vLvHvR;vCv?vDv1vR2vQEvR6vR1vR>vRCvR@vR5v>(3r:r9r8r5r4r3r2r1%MLLKJIHGFEDCBA@?>=<;:987654321&Q5r7%211':&QB&RA&QLu:%211%42QJ1%62A1&QG&Q:r<%211&QK+Q0&4'Q=&Q;%117%4231%@11%8271%=2:1%D2R81%G3R8@1'QC&QD&Q4vQF%211&Q@+f[T@%266Q;Q:1Q9Q1vA%948521p0;1p0Q41p0Q81p2R71pT8R<1pQ<R>1pTJRB1pQDRD1pQFRJ1pT@S11pT:S31pU0S51pTLS71").
Proof using All. intros s sm e fx R Mc modelc LKc crc Ac.
intros BP PRG X10. pose proof PRG as ((X2 & X8 & X9 & X18 & X19 & X20 & X25 & X26 & X27 & X3 & X4) & X22 & X23).
destruct (vec_end false s sm e Mc modelc LKc crc Ac BP) as (UMV & DMV & NEr & NE8).
set (NE := PM.p_b s + 32 * Z.of_nat (length (PM.p_stk s))) in *.
assert (A55 : NE mod 8 = 0) by exact NE8.
assert (B55 : 0 <= NE < 2 ^ 64) by lia. assert (R55 : 4128 <= NE <= 140737488355328) by lia.
assert (X21 : getr R (reg 21) = Z_to_bv 64 (bv_unsigned (getr R (reg 21)))) by (symmetry; apply Z_to_bv_bv_unsigned).
assert (B53 : 0 <= bv_unsigned (getr R (reg 21)) < 2 ^ 64) by apply bv_unsigned_in_range.
ok_tailj false PMBBOP1.aboITs_conc (fun a : Z => False) (fun (a : Z) (X : False) => match X return (S - 192 <= a < S - 160) \/ (S - 112 <= a < S - 104) with end)
(fun a : Z => @or_intror False (~ False) (fun X => X)) (VTj 0 (bv_unsigned (getr R (reg 21))) NE) NE UMV DMV BP s sm e Mc modelc LKc crc Ac fx R 0xb2c90.
intros a Ha N1 N2 N3 N4 N5. destruct (rng_or a (op + 368) (op + 376)) as [IN|OUT]; [exact (SAME a IN)|].
apply FRZ9; [exact Ha| intros X; apply OUT; lia| intros X; apply N1; lia| intros X; apply N3; lia| intros X; apply N4; lia| intros X; apply N5; lia].
Qed.
Lemma tail_Cc : ltac2:(TCodec.tc2 tcn__PmBBo3 "SI'Q<'Q>'2'QA&Gy5'RByR0%211%5241'6y8%611%311p061'F'5&Q1%211&N'7'=%2211%711&Q8vBvR0v@vLvHvR;vCv?vDv1vR2vQEvR6vR1vR>vRCvR@vR5v>(3r;r:r9r6r5r4r3r2%MLLKJIHGFEDCBA@?>=<;:987654321&Q5r8%211':&QB&RA&QLuE%211%42QJ1%62A1&QN&QG&Q:r=%211&QK+Q0&4'Q=&Q;%117%4231%A11%8271%=2:1%?219%F2R:1%I3R:B1'9&QHz%221Q4+`PPP0%42Q61%6231&Q3&QD+S@%L2QI1%443Q@1Q='QC&Q4vQF%211&Q@r<+f[\0%36;Q221QIQHvA%94=621p0;1p0A1p0I1p0QD1p0QH1pTDRI1p2RH1pT8RM1pQ<RO1pTJS31pQDS51pQFS;1pT@SB1pT:SD1pU0SF1pTLSH1").
Proof using All. intros s sm e fx R Mc modelc LKc crc Ac len.
intros BP PRG X21 HL SL. pose proof PRG as ((X2 & X8 & X9 & X18 & X19 & X20 & X25 & X26 & X27 & X3 & X4) & X22 & X23).
assert (SLv : L5.u64_at RSEGS (mrestrict (ahid Ac modelc) Mc) (S - 112) len) by (slv_tac BP SL).
assert (HLb : 0 <= len < 2 ^ 64) by lia.
destruct (vec_end false s sm e Mc modelc LKc crc Ac BP) as (UMV & DMV & NEr & NE8).
set (NE := PM.p_b s + 32 * Z.of_nat (length (PM.p_stk s))) in *.
assert (R53 : 4096 <= NE - 32 <= 140737488355296) by lia.
assert (A53 : (NE - 32) mod 8 = 0) by (rewrite Zminus_mod, NE8; reflexivity).
assert (B53 : 0 <= NE - 32 < 2 ^ 64) by lia.
ok_tailj false PMBBOP3.aboCTc_conc (fun a => S - 192 <= a < S - 160) (fun (a : Z) (X : S - 192 <= a < S - 160) => @or_introl _ (S - 112 <= a < S - 104) X)
(fun a => rng_or a (S - 192) (S - 160)) (VTj len (NE - 32) 0) NE UMV DMV BP s sm e Mc modelc LKc crc Ac fx R 0xb2d80.
intros a Ha N1 N2 N3 N4 N5. destruct (rng_or a (op + 368) (op + 376)) as [IN|OUT]; [exact (SAME a IN)|].
apply FRZ9; [exact Ha| intros X; apply OUT; lia| intros X; apply N1; lia| intros X; apply N2; lia| intros X; apply N3; lia| intros X; apply N4; lia| intros X; apply N5; lia].
Qed.
Lemma tail_Cs : ltac2:(TCodec.tc2 tcn__PmBBo3 "SH'Q<'Q>'2'QA&Gy5'RByR0%211%5241'6y8%611%311p061'F'5&Q1%211&N'7'=%2211%711&Q8vBvR0v@vLvHvR;vCv?vDv1vR2vQEvR6vR1vR>vRCvR@vR5v>(3r;r:r9r6r5r4r3r2%MLLKJIHGFEDCBA@?>=<;:987654321&Q5r8%211':&QB&RA&QLu:%211%42QJ1%62A1&QG&Q:r=%211&QK+Q0&4'Q=&Q;%117%4231%@11%8271%=2:1%D2R81%G3R8@1'9&QHz%221Q2+`PPP0%42Q41%6231&Q3&QD&QN+S@%22QH1%544Q?1Q<'QC&Q4vQF%211&Q@r<+f[`4%36<Q221QHQGvA%94>621p0;1p0B1p0J1p0QC1p0QG1pTDRH1p2RG1pT8RL1pQ<RN1pTJS21pQDS41pQFS:1pT@SA1pT:SC1pU0SE1pTLSG1").
Proof using All. intros s sm e fx R Mc modelc LKc crc Ac len.
intros BP PRG X10 HL SL. pose proof PRG as ((X2 & X8 & X9 & X18 & X19 & X20 & X25 & X26 & X27 & X3 & X4) & X22 & X23).
assert (SLv : L5.u64_at RSEGS (mrestrict (ahid Ac modelc) Mc) (S - 112) len) by (slv_tac BP SL).
assert (HLb : 0 <= len < 2 ^ 64) by lia.
destruct (vec_end false s sm e Mc modelc LKc crc Ac BP) as (UMV & DMV & NEr & NE8).
set (NE := PM.p_b s + 32 * Z.of_nat (length (PM.p_stk s))) in *.
assert (A55 : NE mod 8 = 0) by exact NE8.
assert (B55 : 0 <= NE < 2 ^ 64) by lia. assert (R55 : 4128 <= NE <= 140737488355328) by lia.
assert (X21 : getr R (reg 21) = Z_to_bv 64 (bv_unsigned (getr R (reg 21)))) by (symmetry; apply Z_to_bv_bv_unsigned).
assert (B53 : 0 <= bv_unsigned (getr R (reg 21)) < 2 ^ 64) by apply bv_unsigned_in_range.
ok_tailj false PMBBOP3.aboCTs_conc (fun a => S - 192 <= a < S - 160) (fun (a : Z) (X : S - 192 <= a < S - 160) => @or_introl _ (S - 112 <= a < S - 104) X)
(fun a => rng_or a (S - 192) (S - 160)) (VTj len (bv_unsigned (getr R (reg 21))) NE) NE UMV DMV BP s sm e Mc modelc LKc crc Ac fx R 0xb2e04.
intros a Ha N1 N2 N3 N4 N5. destruct (rng_or a (op + 368) (op + 376)) as [IN|OUT]; [exact (SAME a IN)|].
apply FRZ9; [exact Ha| intros X; apply OUT; lia| intros X; apply N1; lia| intros X; apply N2; lia| intros X; apply N3; lia| intros X; apply N4; lia| intros X; apply N5; lia].
Qed.
Lemma tail_Tc : ltac2:(TCodec.tc2 tcn__PmBBo3 "SI'Q<'Q>'2'QA&Gy5'RByR0%211%5241'6y8%611%311p061'F'5&Q1%211&N'7'=%2211%711&Q8vBvR0v@vLvHvR;vCv?vDv1vR2vQEvR6vR1vR>vRCvR@vR5v>(8r;r:r9r6r5r4r3r2%MLLKJIHGFEDCBA@?>=<;:987654321&Q6r8%211':&QB&RA&QLuE%211%42QJ1%62A1&QN&QG&Q:r=%211&QK+Q0&4'Q=&Q;%117%4231%A11%8271%=2:1%?219%F2R:1%I3R:B1'9&QHz%221Q4+`PPP0%42Q61%6231&Q3&QD+S@%L2QI1%443Q@1Q='QC&Q4vQF%211&Q@r<+f[_4%36;Q221QIQHvA%94=621p0;1p0A1p0I1p0QD1p0QH1pTDRI1p2RH1pT8RM1pQ<RO1pTJS31pQDS51pQFS;1pT@SB1pT:SD1pU0SF1pTLSH1").
Proof using All. intros s sm e fx R Mc modelc LKc crc Ac len.
intros BP PRG X21 HL SL. pose proof PRG as ((X2 & X8 & X9 & X18 & X19 & X20 & X25 & X26 & X27 & X3 & X4) & X22 & X23 & X24).
assert (SLv : L5.u64_at RSEGS (mrestrict (ahid Ac modelc) Mc) (S - 112) len) by (slv_tac BP SL).
assert (HLb : 0 <= len < 2 ^ 64) by lia.
destruct (vec_end true s sm e Mc modelc LKc crc Ac BP) as (UMV & DMV & NEr & NE8).
set (NE := PM.p_b s + 32 * Z.of_nat (length (PM.p_stk s))) in *.
assert (R53 : 4096 <= NE - 32 <= 140737488355296) by lia.
assert (A53 : (NE - 32) mod 8 = 0) by (rewrite Zminus_mod, NE8; reflexivity).
assert (B53 : 0 <= NE - 32 < 2 ^ 64) by lia.
ok_tailj true PMBBOP2.aboTTc_conc (fun a => S - 192 <= a < S - 160) (fun (a : Z) (X : S - 192 <= a < S - 160) => @or_introl _ (S - 112 <= a < S - 104) X)
(fun a => rng_or a (S - 192) (S - 160)) (VTj len (NE - 32) 0) NE UMV DMV BP s sm e Mc modelc LKc crc Ac fx R 0xb2de4.
intros a Ha N1 N2 N3 N4 N5. destruct (rng_or a (op + 368) (op + 376)) as [IN|OUT]; [exact (SAME a IN)|].
apply FRZ9; [exact Ha| intros X; apply OUT; lia| intros X; apply N1; lia| intros X; apply N2; lia| intros X; apply N3; lia| intros X; apply N4; lia| intros X; apply N5; lia].
Qed.
Lemma tail_Ts : ltac2:(TCodec.tc2 tcn__PmBBo3 "SH'Q<'Q>'2'QA&Gy5'RByR0%211%5241'6y8%611%311p061'F'5&Q1%211&N'7'=%2211%711&Q8vBvR0v@vLvHvR;vCv?vDv1vR2vQEvR6vR1vR>vRCvR@vR5v>(8r;r:r9r6r5r4r3r2%MLLKJIHGFEDCBA@?>=<;:987654321&Q6r8%211':&QB&RA&QLu:%211%42QJ1%62A1&QG&Q:r=%211&QK+Q0&4'Q=&Q;%117%4231%@11%8271%=2:1%D2R81%G3R8@1'9&QHz%221Q2+`PPP0%42Q41%6231&Q3&QD&QN+S@%22QH1%544Q?1Q<'QC&Q4vQF%211&Q@r<+f[k0%36<Q221QHQGvA%94>621p0;1p0B1p0J1p0QC1p0QG1pTDRH1p2RG1pT8RL1pQ<RN1pTJS21pQDS41pQFS:1pT@SA1pT:SC1pU0SE1pTLSG1").
Proof using All. intros s sm e fx R Mc modelc LKc crc Ac len.
intros BP PRG X10 HL SL. pose proof PRG as ((X2 & X8 & X9 & X18 & X19 & X20 & X25 & X26 & X27 & X3 & X4) & X22 & X23 & X24).
assert (SLv : L5.u64_at RSEGS (mrestrict (ahid Ac modelc) Mc) (S - 112) len) by (slv_tac BP SL).
assert (HLb : 0 <= len < 2 ^ 64) by lia.
destruct (vec_end true s sm e Mc modelc LKc crc Ac BP) as (UMV & DMV & NEr & NE8).
set (NE := PM.p_b s + 32 * Z.of_nat (length (PM.p_stk s))) in *.
assert (A55 : NE mod 8 = 0) by exact NE8.
assert (B55 : 0 <= NE < 2 ^ 64) by lia. assert (R55 : 4128 <= NE <= 140737488355328) by lia.
assert (X21 : getr R (reg 21) = Z_to_bv 64 (bv_unsigned (getr R (reg 21)))) by (symmetry; apply Z_to_bv_bv_unsigned).
assert (B53 : 0 <= bv_unsigned (getr R (reg 21)) < 2 ^ 64) by apply bv_unsigned_in_range.
ok_tailj true PMBBOP2.aboTTs_conc (fun a => S - 192 <= a < S - 160) (fun (a : Z) (X : S - 192 <= a < S - 160) => @or_introl _ (S - 112 <= a < S - 104) X)
(fun a => rng_or a (S - 192) (S - 160)) (VTj len (bv_unsigned (getr R (reg 21))) NE) NE UMV DMV BP s sm e Mc modelc LKc crc Ac fx R 0xb2f60.
intros a Ha N1 N2 N3 N4 N5. destruct (rng_or a (op + 368) (op + 376)) as [IN|OUT]; [exact (SAME a IN)|].
apply FRZ9; [exact Ha| intros X; apply OUT; lia| intros X; apply N1; lia| intros X; apply N2; lia| intros X; apply N3; lia| intros X; apply N4; lia| intros X; apply N5; lia].
Qed.
End Frame.
End Call.
End WithHeap.
End PMBBO3.
