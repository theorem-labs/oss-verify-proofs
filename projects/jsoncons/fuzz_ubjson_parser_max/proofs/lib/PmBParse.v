(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith Zwf List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import HeapIfaceAJx PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA IcptIfaceAB0 LibIface
AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5CoreKit L5LazyA L5DefsAB0
L5CoreAB0 L5CoreSpecsAB0 L5StepARB0 L5CoreBRB0 L5ADetailHRB0 PmLayout PmLayoutA PmModel PmModelFacts PmStatics PmStaticsA PmSpecsA PmSpecsAX PmSpecsAb
PmModelFactsA PmStepAB0 PmStep PmParStep PmBSrcKit PmBParKit PmBUarK PmBUar PmParKit2 PmBParseD PmBParseE PmBParseK9
PmBParseA1 PmBParseA2 PmBParseA3 PmBParseA4 PmSpecsBX PmBParseA5.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmBParse () := ([""; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmParKit2.PMPK2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsAb.PMB."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsBX.PMBX."; "Stdlib.ZArith.BinInt.Z."], [["0HI"; "0L"; "1p_src"; "1p_stk"; "1pst"; "1stack_shape"; "1strm"; "1unread"; "2lp_mu"; "3end_array_spec"; "3end_object_spec"; "3ignore_spec"; "3make_ec_spec"; "3parse_spec"; "3peek_spec"; "3read_key_spec"]; ["3read_value_spec"; "3rtv_spec"; "4vec_clear_spec"; "0SCFG_P"; "5le"; "0ar"; "0s"; "0sm"]]).
Local Ltac lia := first [ L5FastLia.plia | Lia.lia ].
Module PMBLP.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Lemma lp_mu_nonneg : ltac2:(TCodec.tc2 tcn__PmBParse "G'4'6&5&3r2%211%411&Dz&7&2r3%211%4219%7261&8r4%2216%;2:1p051p0>1pQ@D1pQ>F1").
Proof. intros s sm. intros SH U. pose proof (PMPK2.lp_X_bound _ SH). unfold PMPK2.lp_mu. nia. Qed.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Theorem parse_ok : ltac2:(TCodec.tc2 tcn__PmBParse "Q1&AvCv1vEv0%544321&@%146543&?%148765&9%14:987&:%14<;:9&>%14>=<;&;%14@?>=&<%14BA@?&B%14DCBA&=%14FEDCp031p061p091p0<1p0?1p0B1p0E1p0H1p0K1").
Proof.
intros RTV RV RK EA EO PK IG MKE VCL.
unfold PMB.parse_spec, PMSPA.parse_spec.
intros fx R M model K LBX FF LK Aw cr sp r fb cat s str sm e HH AM K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT.
assert (CTX : PMBLPD.apctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat s str sm e).
{ split; [exact HH|]. split; [exact AM|]. split; [exact K0|]. split; [exact ENT|]. split; [exact FRM|]. split; [exact FRS|]. split; [exact FOK|].
split; [exact SP32|]. split; [exact ARGS|]. split; [exact RPRE|]. split; [exact INCS|]. split; [exact INV|]. split; [exact EC0|].
split; [exact UNR|]. split; [exact CRED| exact KONT]. }
unfold PMSPA.cfg. cbn [pa_parse PMB.AD ADDR_B].
apply (PMBLPE.parse_entry L ar C HI LY HIok IL ICok ILY fx R M model K LBX FF LK Aw cr sp r fb cat s str sm e CTX).
intros F fl LK2 M2 model2 G.
assert (LOOP : forall n, 0 <= n -> forall (fx1 : FPState) R1 M1 model1 LK1 Aw1 s1 sm1 e1 cr1,
PMBLPD.alinv L ar HI R M model LBX FF LK Aw cr sp fb cat s str sm e F R1 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 -> PMPK2.lp_mu s1 sm1 = n ->
srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx1 R1 0xad278 M1 model1) K).
{ intros n. pattern n. apply (well_founded_ind (Zwf_well_founded 0)). clear n.
intros n IHn Hn fx1 R1 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 LI EM.
assert (IH : forall (fx2 : FPState) R2 M2' model2' LK2' Aw2 s2 sm2 e2 cr2,
PMBLPD.alinv L ar HI R M model LBX FF LK Aw cr sp fb cat s str sm e F R2 M2' model2' LK2' Aw2 s2 sm2 e2 cr2 -> PMPK2.lp_mu s2 sm2 < PMPK2.lp_mu s1 sm1 ->
srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx2 R2 0xad278 M2' model2') K).
{ intros fx2 R2 M2' model2' LK2' Aw2 s2 sm2 e2 cr2 LI2 LT2.
pose proof LI2 as (_ & INV2 & _ & (_ & RPRE2 & _)).
pose proof INV2 as (_ & _ & _ & SH2 & _).
pose proof (lp_mu_nonneg s2 sm2 SH2 (PMBLPK9.unread_nonneg _ _ _ _ _ _ RPRE2)) as N2.
exact (IHn (PMPK2.lp_mu s2 sm2) ltac:(unfold Zwf; clear - LT2 EM N2; lia) N2 fx2 R2 M2' model2' LK2' Aw2 s2 sm2 e2 cr2 LI2 eq_refl). }
clear IHn.
pose proof LI as (_ & INV1 & _).
destruct s1 as [mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1].
pose proof INV1 as (_ & _ & _ & SH1 & _). cbn [PM.p_stk] in SH1.
destruct (exists_last (l := stk1) ltac:(intros E; rewrite E in SH1; destruct SH1 as (X & _); cbn in X; lia)) as (pre & top & Epre).
subst stk1. destruct top as [tm tl tt ti].
destruct (PMPK2.top_of_shape pre (PM.PS tm tl tt ti) SH1) as (TOK & _).
pose proof TOK as (_ & TM).
assert (MR : tm = 0 \/ tm = 1 \/ tm = 2 \/ tm = 3 \/ tm = 4 \/ tm = 5 \/ tm = 6 \/ tm = 7 \/ tm = 8 \/ tm = 9 \/ tm = 10).
{ clear - TM. unfold PM.mode_counted, PM.mode_indef, PM.mode_bottom in TM. cbn [PM.ps_mode] in TM. lia. }
assert (TLI : (PM.mode_counted tm -> 0 <= ti <= tl) /\ (PM.mode_indef tm -> 0 <= ti)).
{ clear - TOK. unfold PM.pstate_ok, PM.mode_counted, PM.mode_indef, PM.mode_bottom in *. cbn [PM.ps_mode PM.ps_len PM.ps_idx PM.ps_type] in TOK. lia. }
destruct MR as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]].
- exact (PMBLPA1.arm_H0 L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx1 R1 M1 model1 LK1 Aw1
mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre tl tt ti sm1 e1 cr1 RTV CTX G LI IH).
- exact (PMBLPA5.arm_H1 L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx1 R1 M1 model1 LK1 Aw1
mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre tl tt ti sm1 e1 cr1 VCL CTX G LI).
- destruct (Z_lt_le_dec ti tl) as [LT|GE].
+ exact (PMBLPA1.arm_H2a L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx1 R1 M1 model1 LK1 Aw1
mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre tl tt ti sm1 e1 cr1 RTV CTX G LI LT IH).
+ exact (PMBLPA2.arm_H2b L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx1 R1 M1 model1 LK1 Aw1
mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre tl tt ti sm1 e1 cr1 EA CTX G LI ltac:(destruct TLI as (X & _); specialize (X ltac:(unfold PM.mode_counted; clear; lia)); clear - X GE; lia) IH).
- exact (PMBLPA3.arm_H3 L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx1 R1 M1 model1 LK1 Aw1
mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre tl tt ti sm1 e1 cr1 PK IG EA RTV MKE CTX G LI IH).
- destruct (Z_lt_le_dec ti tl) as [LT|GE].
+ exact (PMBLPA1.arm_H4a L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx1 R1 M1 model1 LK1 Aw1
mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre tl tt ti sm1 e1 cr1 RV CTX G LI LT IH).
+ exact (PMBLPA2.arm_H4b L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx1 R1 M1 model1 LK1 Aw1
mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre tl tt ti sm1 e1 cr1 EA CTX G LI ltac:(destruct TLI as (X & _); specialize (X ltac:(unfold PM.mode_counted; clear; lia)); clear - X GE; lia) IH).
- destruct (Z_lt_le_dec ti tl) as [LT|GE].
+ exact (PMBLPA2.arm_H5a L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx1 R1 M1 model1 LK1 Aw1
mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre tl tt ti sm1 e1 cr1 RK CTX G LI LT IH).
+ exact (PMBLPA2.arm_H5b L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx1 R1 M1 model1 LK1 Aw1
mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre tl tt ti sm1 e1 cr1 EO CTX G LI ltac:(destruct TLI as (X & _); specialize (X ltac:(unfold PM.mode_counted; clear; lia)); clear - X GE; lia) IH).
- exact (PMBLPA1.arm_H6 L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx1 R1 M1 model1 LK1 Aw1
mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre tl tt ti sm1 e1 cr1 RTV CTX G LI IH).
- destruct (Z_lt_le_dec ti tl) as [LT|GE].
+ exact (PMBLPA2.arm_H7a L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx1 R1 M1 model1 LK1 Aw1
mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre tl tt ti sm1 e1 cr1 RK CTX G LI LT IH).
+ exact (PMBLPA2.arm_H7b L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx1 R1 M1 model1 LK1 Aw1
mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre tl tt ti sm1 e1 cr1 EO CTX G LI ltac:(destruct TLI as (X & _); specialize (X ltac:(unfold PM.mode_counted; clear; lia)); clear - X GE; lia) IH).
- exact (PMBLPA1.arm_H8 L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx1 R1 M1 model1 LK1 Aw1
mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre tl tt ti sm1 e1 cr1 RV CTX G LI IH).
- exact (PMBLPA4.arm_H9 L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx1 R1 M1 model1 LK1 Aw1
mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre tl tt ti sm1 e1 cr1 PK IG EO RK MKE CTX G LI IH).
- exact (PMBLPA1.arm_H10 L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx1 R1 M1 model1 LK1 Aw1
mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre tl tt ti sm1 e1 cr1 RTV CTX G LI IH). }
intros fx1 R1 M1 model1 LI.
pose proof LI as (_ & INV1 & _ & (_ & RPRE1 & _)). pose proof INV1 as (_ & _ & _ & SH1 & _).
exact (LOOP (PMPK2.lp_mu s sm) (lp_mu_nonneg s sm SH1 (PMBLPK9.unread_nonneg _ _ _ _ _ _ RPRE1)) fx1 R1 M1 model1 LK2 Aw s sm e cr LI eq_refl).
Qed.
End WithHeap.
End PMBLP.
