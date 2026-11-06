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
PmModelFactsA PmStepA PmStep PmParStep PmParKit PmASrcKit PmAParKit PmAReset1 PmAUarK PmAUar PmAUarKS PmABaK PmABaK2 PmABaK3 Ja0_code_b0cfc_b0d00 PmABa1 PmABaP1 PmABaP2 PmABa2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmABa3 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmABa2.PMABA2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmABaK3.PMABK3."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmParKit.PMPK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0Ac"; "0Aw0"; "1bool"; "1false"; "1list"; "1option"; "1prod"; "1true"; "2and"; "2not"; "2or"; "3Z"; "0F"; "0FF"; "0HI"; "0K"]; ["0L"; "0LBX"; "0LK0"; "0LKc"; "4Model"; "5bvmap"; "0M0"; "0Mc"; "0R"; "0R0"; "6credit"; "7fframe"; "9u64_at"; "8SCFG"; ":mregs"; ":tregs"]; [";bstp"; "<inv"; "<pst"; "<strm"; "=set_more"; ">cfg"; "?FPState"; "@srealizes"; "Aloaded_segments"; "0S"; "0SCFG_P"; "Ble"; "Blt"; "Bsub"; "0a"; "0ar"]; ["0cat"; "0cr0"; "0crc"; "0e"; "0e0"; "0fb"; "0fx"; "0hi"; "0len"; "0lo"; "0model0"; "0modelc"; "0s"; "0s0"; "0sm"; "0sm0"]; ["Cbv"; "0str"]]).
Local Ltac lia := L5FastLia.plia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PMABA3.
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
Lemma rng_or : ltac2:(TCodec.tc2 tcn__PmABa3 "A';':'8&Q;r2r3%3221&Q<r1%2241%8241&9%112%<231pS@>1pSD?1pRN@1").
Proof. intros a lo hi. destruct (L5SAR.rng_dec a lo hi) as [X|X]; [left| right]; exact X. Qed.
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
Lemma inv_more1 : ltac2:(TCodec.tc2 tcn__PmABa3 ";'Q2&Q1r1%211&Q4r2+1%3221%711p061pSJ:1").
Proof. intros s. intros (I1 & I2 & I3 & I4 & I5). unfold PM.inv, PMPK.set_more. cbn [PM.p_more PM.p_done PM.p_depth PM.p_stk PM.p_tb PM.p_tg]. split; [reflexivity|]. split; [exact I2|]. split; [exact I3|]. split; [exact I4| exact I5]. Qed.
Definition VT (x49 x50 : Z) (j : nat) : Z :=
match j with 2%nat => S | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 48%nat => fl | 49%nat => x49 | 50%nat => x50
| 57%nat => U 1 | 58%nat => U 8 | 59%nat => U 9 | 60%nat => U 18 | 61%nat => U 19 | 62%nat => U 20 | 63%nat => U 21 | 64%nat => U 22
| 65%nat => U 23 | 66%nat => U 24 | 67%nat => U 25 | 68%nat => U 26 | 69%nat => U 27 | _ => 0 end.
Ltac ok_tail typed conc Wy WYin WYD x50 BP s sm e Mc modelc LKc crc Ac fx R pc :=
pose proof BP as (BI & RUN & EC & HD & FSH & STEP & E0' & INV' & PV & CRL & CRK);
pose proof (vpack typed _ s sm e 0 cat Mc modelc LKc crc Ac BI RUN EC HD FSH) as VF;
set (MV := mrestrict (ahid Ac modelc) Mc) in *;
pose proof (conc fx R MV (VT 0 x50)) as P; unfold VT in P;
cbn beta iota in P; feedV P VF;
destruct P as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & PR); decompose [and] PR; clear PR;
apply (fin_any s sm e 1 Wy fx fx9 R pc R9 M9v Mc modelc LKc crc Ac BI RUN ltac:(right; reflexivity));
[ exact WYin | exact WYD | exact MS9 | exact MG9 | | assumption | assumption | assumption | assumption | assumption | assumption
| intros j Hj; repeat (destruct Hj as [<-|Hj]; [assumption|]); destruct Hj
| rewrite (KS9 3%nat) by inl; assumption
| rewrite (KS9 4%nat) by inl; assumption
| exact STEP
| exact E0'
| right; split; [exact EC|]; split; [exact (inv_more1 s INV')| exact PV]
| exact CRK ].
Lemma tail_I : ltac2:(TCodec.tc2 tcn__PmABa3 "R@'Q2'Q3'2'Q6&Ey5'R0yR0%211%5241'5y8%611%311p061'D'4&K%211&J'6';%2211%711&Q0v@vQ?v>vIvFvQJvAv=vBv1vQAvQ9vQEvQ@vQMvR1vQOvQDv<(3r:r9r8r5r4r3r2r1%MLLKJIHGFEDCBA@?>=<;:987654321&Nr7%25LDC=1'Q7&Q8&MvQ:%211&Q5+fRi4r6%367CB2:1v?%:49621p0<1p0@1p2Q?1pS6QD1pQ8QF1pSHQJ1pQ@QL1pQBR21pS>R91pS8R;1pSNR=1pSJR?1").
Proof using All. intros s sm e fx R Mc modelc LKc crc Ac.
intros BP MR. pose proof MR as ((X2 & X8 & X9 & X18 & X19 & X20 & X21 & X25 & X26 & X27 & X3 & X4) & X23).
ok_tail false PMABAP1.abaIT_conc (fun a : Z => False) (fun (a : Z) (X : False) => match X return (S - 160 <= a < S - 128) \/ (S - 112 <= a < S - 104) with end)
(fun a : Z => @or_intror False (~ False) (fun X => X)) 0 BP s sm e Mc modelc LKc crc Ac fx R 0xb0b24.
intros a Ha N1 N2 N3 N4 N5. apply FRZ9; [exact Ha| intros X; apply N1; lia| intros X; apply N3; lia| intros X; apply N4; lia| intros X; apply N5; lia].
Qed.
Lemma tail_C : ltac2:(TCodec.tc2 tcn__PmABa3 "RO'Q2'Q3'2'Q6&Ey5'R0yR0%211%5241'5y8%611%311p061'D'4&K%211&J'6';%2211%711&Q0v@vQ?v>vIvFvQJvAv=vBv1vQAvQ9vQEvQ@vQMvR1vQOvQDv<(3r;r:r9r6r5r4r3r2%MLLKJIHGFEDCBA@?>=<;:987654321&Nr8%25LDC=1'8&Q;z%2219+`PPP0%42;1%6231&L&Q8&Q=+S@%22Q01%544F1C'Q7&MvQ:%211&Q5r<+fRm@%36<2Q01ONv?%94>621p0;1p0B1p0J1p0N1pSBQO1p2QN1pS6R31pQ8R51pSHR91pQ@R;1pQBRA1pS>RH1pS8RJ1pSNRL1pSJRN1").
Proof using All. intros s sm e fx R Mc modelc LKc crc Ac len.
intros BP MR HL SL. pose proof MR as ((X2 & X8 & X9 & X18 & X19 & X20 & X21 & X25 & X26 & X27 & X3 & X4) & X23).
assert (SLv : L5.u64_at RSEGS (mrestrict (ahid Ac modelc) Mc) (S - 112) len).
{ pose proof BP as (BI & _). pose proof G as G'. destruct G' as [Hk SPTg SLOg SHIg SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
pose proof (PMAUK.vis_facts L ar C HI LYa HIok M0 model0 LBX FF LK0 Aw0 S SCR (S - 128) (S - 104) S ocell own F fl 0 LK2 M2 model2 cr0 (PM.parser_own s0) G WR _ Mc modelc LKc crc Ac BI)
as (_ & _ & _ & (_ & _ & _ & SV8 & _)).
apply (proj2 (L5A.u64_at_vis _ Mc (S - 112) len (L5A.avis_sub _ (S - 128) (S - (S - 128)) (S - 112) 8 SV8 ltac:(lia) ltac:(lia)) ltac:(unfold SCR in *; lia) ltac:(unfold SCR in *; lia))).
exact SL. }
assert (HLb : 0 <= len < 2 ^ 64) by lia.
ok_tail false PMABAP1.abaCT_conc (fun a => S - 160 <= a < S - 128) (fun (a : Z) (X : S - 160 <= a < S - 128) => @or_introl _ (S - 112 <= a < S - 104) X)
(fun a => rng_or a (S - 160) (S - 128)) len BP s sm e Mc modelc LKc crc Ac fx R 0xb0bb0.
intros a Ha N1 N2 N3 N4 N5. apply FRZ9; [exact Ha| intros X; apply N1; lia| intros X; apply N2; lia| intros X; apply N3; lia| intros X; apply N4; lia| intros X; apply N5; lia].
Qed.
Lemma tail_T : ltac2:(TCodec.tc2 tcn__PmABa3 "RO'Q2'Q3'2'Q6&Ey5'R0yR0%211%5241'5y8%611%311p061'D'4&K%211&J'6';%2211%711&Q0v@vQ?v>vIvFvQJvAv=vBv1vQAvQ9vQEvQ@vQMvR1vQOvQDv<(7r;r:r9r6r5r4r3r2%MLLKJIHGFEDCBA@?>=<;:987654321&Or8%25LDC=1'8&Q;z%2219+`PPP0%42;1%6231&L&Q8&Q=+S@%22Q01%544F1C'Q7&MvQ:%211&Q5r<+fSXL%36<2Q01ONv?%94>621p0;1p0B1p0J1p0N1pSBQO1p2QN1pS6R31pQ8R51pSHR91pQ@R;1pQBRA1pS>RH1pS8RJ1pSNRL1pSJRN1").
Proof using All. intros s sm e fx R Mc modelc LKc crc Ac len.
intros BP MR HL SL. pose proof MR as (((X2 & X8 & X9 & X18 & X19 & X20 & X21 & X25 & X26 & X27 & X3 & X4) & X23) & X22 & X24).
assert (SLv : L5.u64_at RSEGS (mrestrict (ahid Ac modelc) Mc) (S - 112) len).
{ pose proof BP as (BI & _). pose proof G as G'. destruct G' as [Hk SPTg SLOg SHIg SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
pose proof (PMAUK.vis_facts L ar C HI LYa HIok M0 model0 LBX FF LK0 Aw0 S SCR (S - 128) (S - 104) S ocell own F fl 0 LK2 M2 model2 cr0 (PM.parser_own s0) G WR _ Mc modelc LKc crc Ac BI)
as (_ & _ & _ & (_ & _ & _ & SV8 & _)).
apply (proj2 (L5A.u64_at_vis _ Mc (S - 112) len (L5A.avis_sub _ (S - 128) (S - (S - 128)) (S - 112) 8 SV8 ltac:(lia) ltac:(lia)) ltac:(unfold SCR in *; lia) ltac:(unfold SCR in *; lia))).
exact SL. }
assert (HLb : 0 <= len < 2 ^ 64) by lia.
ok_tail true PMABAP2.abaTT_conc (fun a => S - 160 <= a < S - 128) (fun (a : Z) (X : S - 160 <= a < S - 128) => @or_introl _ (S - 112 <= a < S - 104) X)
(fun a => rng_or a (S - 160) (S - 128)) len BP s sm e Mc modelc LKc crc Ac fx R 0xb0d1c.
intros a Ha N1 N2 N3 N4 N5. apply FRZ9; [exact Ha| intros X; apply N1; lia| intros X; apply N2; lia| intros X; apply N3; lia| intros X; apply N4; lia| intros X; apply N5; lia].
Qed.
End Frame.
End Call.
End WithHeap.
End PMABA3.
