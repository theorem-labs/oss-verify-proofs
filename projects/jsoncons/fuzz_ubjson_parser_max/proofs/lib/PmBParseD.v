(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceAB0
L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsAB0 L5CoreAB0 L5StepARB0 PmLayout PmLayoutA PmModel PmStatics PmStaticsA HeapIfaceAJx PmSpecsA PmSpecsAX PmSpecsAb
PmStepAB0 PmBUarK PmParKit2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmBParseD () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBParseD.PMBLPD."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1option"; "2and"; "2eq"; "2or"; "3Z"; "0E"; "0F"; "4bvmap"; "0M"; "0M'"; "0M1"; "0M1'"; "0R"; "5lpG1"; "5lpG2"; "5lpG3"]; ["5lpG4"; "5lspill"; "5ocell"; "5own"; "6le"; "6lt"; "6pow"; "6sub"; "0a"; "0m"; "0oec"; "0op"; "0ov"; "7Z_to_bv"; "7bv"; "0x"]]).
Module PMBLPD.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition own (E : Z) (R : bvmap 5 word) (M : word -> option byte) : Prop :=
L5.u64_at RSEGS M (E - 8) (bv_unsigned (getr R (reg 1))) /\ L5.u64_at RSEGS M (E - 16) (bv_unsigned (getr R (reg 8)))
/\ L5.u64_at RSEGS M (E - 24) (bv_unsigned (getr R (reg 9))) /\ L5.u64_at RSEGS M (E - 32) (bv_unsigned (getr R (reg 18)))
/\ L5.u64_at RSEGS M (E - 40) (bv_unsigned (getr R (reg 19))) /\ L5.u64_at RSEGS M (E - 48) (bv_unsigned (getr R (reg 20)))
/\ L5.u64_at RSEGS M (E - 56) (bv_unsigned (getr R (reg 21))) /\ L5.u64_at RSEGS M (E - 64) (bv_unsigned (getr R (reg 22)))
/\ L5.u64_at RSEGS M (E - 72) (bv_unsigned (getr R (reg 23))) /\ L5.u64_at RSEGS M (E - 80) (bv_unsigned (getr R (reg 24)))
/\ L5.u64_at RSEGS M (E - 88) (bv_unsigned (getr R (reg 25))) /\ L5.u64_at RSEGS M (E - 96) (bv_unsigned (getr R (reg 26)))
/\ L5.u64_at RSEGS M (E - 104) (bv_unsigned (getr R (reg 27))).
Definition ocell (E : Z) (a : Z) : Prop := E - 104 <= a < E.
Lemma own_agree : ltac2:(TCodec.tc2 tcn__PmBParseD "QD'4&7y5'NyR0%211%5241'0y8%611%311p061pR072&Dz&Gr4+S8%3221%6251r5&F+2+R0%3221%<251&Cr6%2318<&Br8r1%3221'2&Mr2%22Q01%:11r7%113%73N31p091pQBQ:1%A3=5Gp021p0A1p0E1p0L1pHQ41pFQ61pJQ<1p<QC1").
Proof. intros E R M1 M1'.
intros H0 H1 (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13) AG. unfold own, ocell in *.
repeat split; (eapply L5C.u64_at_agree; [ | | | eassumption]; [intros j Hj; apply AG; lia | lia | lia]).
Qed.
Definition lspill (M : word -> option byte) (E F op ov oec : Z) : Prop :=
L5.u64_at RSEGS M (E - 264) (F + 32) /\ L5.u64_at RSEGS M (E - 256) 3 /\ L5.u64_at RSEGS M (E - 248) 1 /\ L5.u64_at RSEGS M (E - 240) 0
/\ L5.u64_at RSEGS M (E - 232) F /\ L5.u64_at RSEGS M (E - 224) ((op + 328) / 8 + 2147450880) /\ L5.u64_at RSEGS M (E - 216) (op + 328)
/\ L5.u64_at RSEGS M (E - 208) (ov / 8 + 2147450880) /\ L5.u64_at RSEGS M (E - 200) ((op + 360) / 8 + 2147450880)
/\ L5.u64_at RSEGS M (E - 192) (op + 360) /\ L5.u64_at RSEGS M (E - 184) F /\ L5.u64_at RSEGS M (E - 176) 65024
/\ L5.u64_at RSEGS M (E - 168) (op + 24) /\ L5.u64_at RSEGS M (E - 160) (oec / 8 + 2147450880) /\ L5.u64_at RSEGS M (E - 152) op
/\ L5.u64_at RSEGS M (E - 144) ov /\ L5.u64_at RSEGS M (E - 136) ((op + 9) / 8 + 2147450880) /\ L5.u64_at RSEGS M (E - 112) F.
Lemma lspill_agree : ltac2:(TCodec.tc2 tcn__PmBParseD "QO'NyR0%211'0y8%511%311p051pR062'4&Dz&Gr5+Y0%3221%6251r6&F+2+R0%3221%<251&Ar9r7r4r3%5643;?21'1%B26@r1%F221&E+S8%G2;1%3251%8251'2r;&Mr2%22Q91%411r<%113%83Q831p0:1pQBQ71r:r8%L62K1JQ2Q6p041p0I1p0Q01p0Q71pQFQ?1pQJQ@1pQHQA1p>QB1p<QC1pDQE1pBQG1").
Proof. intros M M' E F op ov oec.
intros H0 H1 (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14 & C15 & C16 & C17 & C18) AG. unfold lspill in *.
repeat split; (eapply L5C.u64_at_agree; [ | | | eassumption]; [intros j Hj; apply AG; lia | lia | lia]).
Qed.
Definition lregs (R R1 : bvmap 5 word) (E op oec F : Z) : Prop :=
getr R1 (reg 2) = Z_to_bv 64 (E - 288) /\ getr R1 (reg 8) = Z_to_bv 64 E /\ getr R1 (reg 9) = Z_to_bv 64 (E - 288)
/\ getr R1 (reg 18) = Z_to_bv 64 32 /\ getr R1 (reg 19) = Z_to_bv 64 oec /\ getr R1 (reg 20) = Z_to_bv 64 ((op + 8) / 8 + 2147450880)
/\ getr R1 (reg 21) = Z_to_bv 64 143148 /\ getr R1 (reg 22) = Z_to_bv 64 ((op + 368) / 8 + 2147450880) /\ getr R1 (reg 23) = Z_to_bv 64 (op + 8)
/\ getr R1 (reg 24) = Z_to_bv 64 (op + 9) /\ getr R1 (reg 25) = Z_to_bv 64 (op + 368) /\ getr R1 (reg 26) = Z_to_bv 64 (F / 8 + 2147450880)
/\ getr R1 (reg 27) = Z_to_bv 64 2147450880
/\ getr R1 (reg 3) = getr R (reg 3) /\ getr R1 (reg 4) = getr R (reg 4).
Definition top_mode (s : PM.pst) : Z := PM.ps_mode (last (PM.p_stk s) PM.ps_root).
Definition lpG1 (m : Z) : Prop := m = 0 \/ m = 1 \/ m = 6 \/ m = 8 \/ m = 10.
Definition lpG2 (m : Z) : Prop := m = 2 \/ m = 4.
Definition lpG3 (m : Z) : Prop := m = 5 \/ m = 7.
Definition lpG4 (m : Z) : Prop := m = 3 \/ m = 9.
Lemma lp_split : ltac2:(TCodec.tc2 tcn__PmBParseD "H'4'1&Dzr1%3221+:%5231%7231'3&=r2%211&>%113&?%115&@%117%:231%;261%<291p0>1pQDG1").
Proof. intros m. intros H. unfold lpG1, lpG2, lpG3, lpG4. lia. Qed.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (HI : asan_iface).
Definition apkont (K : TSet) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z))
(cr : credit) (sp r fb : Z) (s : PM.pst) (str : PM.vstr) (sm : PM.strm) (e : bool) : Prop :=
forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (s' : PM.pst) (sm' : PM.strm) (e' : bool) (cr' : credit),
regs_preserved R R' ->
PMSPA.parse_post RSEGS PMB.AD PMB.AAD M' fb s s' str sm sm' e e' ->
L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr 10) (PMSPA.W_run PMB.AD fb) M M' ->
PMSPA.credit_keep cr cr' (PMSPA.scA L (PM.pot_parser (PMSPA.HV L ar) s)) PMSPA.cr0 ->
model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (PM.parser_own s' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx' R' r M' model') K.
Definition apctx (K : TSet) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z))
(cr : credit) (sp r fb cat : Z) (s : PM.pst) (str : PM.vstr) (sm : PM.strm) (e : bool) : Prop :=
ri_inv HI (PM.parser_own s ++ LBX) FF LK cr Aw M (vml_of model) /\ L5CA.amodel_ok Aw model /\ K [] /\ PMSPA.entryA PMB.AD L ar R M sp r 10
/\ PMSPA.ffroomA 10 FF LK /\ PMSPA.ffrsA FF sp /\ PMSPA.frame_okA FF fb /\ sp mod 32 = 0 /\ PMSPA.args3 PMB.AD R fb s
/\ PMSPA.run_pre RSEGS PMB.AD PMB.AAD M fb s str sm e /\ incl (PM.vs_own str) LBX /\ PM.inv s /\ PMSPA.ec_at RSEGS M (PMSPA.o_ec PMB.AD fb) 0 cat
/\ PM.unread (PM.p_src s) sm < 2 ^ 26 /\ PMSPA.credit_le (PMSPA.scA L (PM.pot_parser (PMSPA.HV L ar) s)) cr
/\ apkont K R M model LBX FF LK Aw cr sp r fb s str sm e.
Definition aframe (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z))
(cr : credit) (sp : Z) (s : PM.pst) (F fl : Z) (LK2 : list fframe) (M2 : word -> option byte) (model2 : Model) : Prop :=
PMBUK.gctx L ar HI LBX FF LK Aw sp (PMSPA.pm_scr 10) (sp - 288) (sp - 104) sp (ocell sp) (own sp R) F fl 1 LK2 M2 model2 cr (PM.parser_own s).
Definition lmem (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z))
(cr : credit) (sp fb : Z) (s : PM.pst) (str : PM.vstr) (sm : PM.strm) (e : bool) (F : Z)
(M1 : word -> option byte) (model1 : Model) (LK1 : list fframe) (Aw1 : list (Z * Z)) (s1 : PM.pst) (sm1 : PM.strm) (e1 : bool) (cr1 : credit) : Prop :=
PMBUK.binv L ar HI M model LBX FF LK Aw sp (PMSPA.pm_scr 10) (sp - 288) (own sp R) F 1 (PMSPA.W_run PMB.AD fb) (PM.parser_own s1) M1 model1 LK1 cr1 Aw1
/\ PMSPA.run_pre RSEGS PMB.AD PMB.AAD M1 fb s1 str sm1 e1
/\ lspill M1 sp F (PMSPA.o_p PMB.AD fb) (PMSPA.o_v PMB.AD fb) (PMSPA.o_ec PMB.AD fb)
/\ PMSPA.src_step (PM.p_src s) (PM.p_src s1) sm sm1 /\ (e = true -> e1 = true)
/\ PMSPA.credit_keep cr cr1 (PMSPA.scA L (PM.pot_parser (PMSPA.HV L ar) s)) (PMSPA.scA L (PM.pot_parser (PMSPA.HV L ar) s1)).
Definition alinv (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z))
(cr : credit) (sp fb cat : Z) (s : PM.pst) (str : PM.vstr) (sm : PM.strm) (e : bool) (F : Z)
(R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (LK1 : list fframe) (Aw1 : list (Z * Z)) (s1 : PM.pst) (sm1 : PM.strm) (e1 : bool) (cr1 : credit) : Prop :=
lregs R R1 sp (PMSPA.o_p PMB.AD fb) (PMSPA.o_ec PMB.AD fb) F /\ PM.inv s1
/\ PMSPA.ec_at RSEGS M1 (PMSPA.o_ec PMB.AD fb) 0 cat
/\ lmem R M model LBX FF LK Aw cr sp fb s str sm e F M1 model1 LK1 Aw1 s1 sm1 e1 cr1.
Definition aiter_ok (G : Z -> Prop) : Prop :=
forall (K : TSet) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z))
(cr : credit) (sp r fb cat : Z) (s : PM.pst) (str : PM.vstr) (sm : PM.strm) (e : bool) (F fl : Z) (LK2 : list fframe) (M2 : word -> option byte) (model2 : Model),
apctx K R M model LBX FF LK Aw cr sp r fb cat s str sm e ->
aframe R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
forall (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (LK1 : list fframe) (Aw1 : list (Z * Z)) (s1 : PM.pst) (sm1 : PM.strm) (e1 : bool) (cr1 : credit),
alinv R M model LBX FF LK Aw cr sp fb cat s str sm e F R1 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 -> G (top_mode s1) ->
(forall (fx2 : FPState) (R2 : bvmap 5 word) (M2' : word -> option byte) (model2' : Model) (LK2' : list fframe) (Aw2 : list (Z * Z)) (s2 : PM.pst) (sm2 : PM.strm) (e2 : bool) (cr2 : credit),
alinv R M model LBX FF LK Aw cr sp fb cat s str sm e F R2 M2' model2' LK2' Aw2 s2 sm2 e2 cr2 -> PMPK2.lp_mu s2 sm2 < PMPK2.lp_mu s1 sm1 ->
srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx2 R2 0xad278 M2' model2') K) ->
srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx1 R1 0xad278 M1 model1) K.
End WithHeap.
End PMBLPD.
