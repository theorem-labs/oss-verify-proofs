(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import HeapIfaceAJx PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA IcptIfaceA LibIface
AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5CoreKit L5LazyA L5DefsA
L5CoreA L5CoreSpecsA L5StepAR L5CoreBR L5ADetailHR PmLayout PmLayoutA PmModel PmModelFacts PmStatics PmStaticsA PmSpecsA PmSpecsAX PmSpecsAa
PmModelFactsA PmStepA PmStep PmParStep PmASrcKit PmAParKit PmAUarK PmAUar PmParKit2 PmAReset1 PmAParseD PmAParseK.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmAParseK10 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmAParseD.PMALPD."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0Aw"; "0Aw1"; "0Aw2"; "1bool"; "1cons"; "1list"; "1option"; "1pair"; "1prod"; "2eq"; "3Z"; "0F"; "0FF"; "0HI"; "0K"; "0L"]; ["0LBX"; "0LK"; "0LK1"; "0LK2"; "0LK2'"; "4Model"; "5bvmap"; "0M"; "0M1"; "0M2"; "0M2'"; "0R"; "0R1"; "0R2"; "6credit"; "6regs_preserved"]; ["7fframe"; "9ra_ok"; "8SCFG"; ":aframe"; ":apctx"; ":lmem"; ";ADDR_A"; "<p_src"; "<pst"; "<srcst"; "<strm"; "<vstr"; "=cfg"; "=ec_at"; "=no_W"; "=o_ec"]; ["=o_src"; "=src_spec"; "=with_src"; ">FPState"; ">getr"; "?TSet"; "@srealizes"; "Aloaded_segments"; "0SCFG_P"; "Badd"; "Bof_nat"; "Bsub"; "0ar"; "0args"; "0c"; "0cat"]; ["0cr"; "0cr1"; "0e"; "0e1"; "0fb"; "0fl"; "0fx1"; "0fx2"; "0model"; "0model1"; "0model2"; "0model2'"; "0pc"; "0r"; "0res"; "0rr"]; ["0s"; "0s1"; "0sm"; "0sm1"; "0sm2"; "0sp"; "0src2"; "CZ_to_bv"; "Cbv"; "0str"; "0v"]]).
Local Ltac lia := first [ L5FastLia.plia | Lia.lia ].
Module PMALPK10.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.
Section S.
Local Abbreviation SECT := (ltac2:(TCodec.tc2 tcn__PmAParseK10 "WK&QE&Fy5'RHyR0%211%5241'6y8%611%311p061'E'5'8':%2211%411&Q0%611&N'Q8'Q;'Q:'3!p051p0<1p0=1p0B1p0H1p0<1'Q9p0:8p0;1p031p041p0J1p0Q01p0Q11'QC&QAvQH&QG&Q6v?vQLv=r@+4r?&Q>r>%<;;:987654321&Q4rQ7rQ6rQ5rQ4rQ3rQ2rQ1rQ0rOrNrMrLrKrJrIrHrG%BENKJIA@?>=<;:987654321&Q3rFrErDrC%5BQ1Q0OGFEDCBA@?;74321&Q5rQ8r=r<r;r:r9r8r7%9JQ;Q:Q98Q1Q0ONMLKJHFEDCBQ47654321'9&QD&RG&QJu1%211%42RM1%62Q@1%62RM:%93RM21&Q1%11>rBu2%;11%=2S61%?241&QK+X0%22QA1%B2S91%E3S951u3%D11%F2S?1%H2Q51rQ<%J213%L3S@31u4%K11%M2SF1%O2Q=1rQ=%Q1213%Q33SG31u:%Q211%Q42SM1%Q62QE1&Q@%12RFR8%Q82SO1%Q;3SO41(4%SH2SFSG(7+1%24SJSJR:1&QI%Q12RDQ0+Q0%3221%74SNSO51rQ;%;3:21rA%R=62R8R77RI1&Q=&Q?%12S9RM%35S;R<1R5R4&O%12RJR1&Q7%11RHr3r2%S27S0R7R632RJ1rQKrQJrQIrQHrQGrQFrQErQDrQCrQArQ?rQ>r6r5&QBr4%22S=1%S0JT2T1T0A@?>=<;:9876QEQLQ0RIRH541DS<S;rQB%M2T51%O5T7RM1S=S<'QF&Q2%11T;&Q<%16T<S5S4SDS3S2rQN%64T>421p081p0<1p0O1p0Q51pU:U71pU>TO1p6U?1pQ:U>1pTHUF1pQFUH1pQLUN1pT@TM1%@6TKT2T1T5T0SO%D4TLB1Q1p031p0QC1p0QH1p0R71p0R@1p0RH1p0S01p0S;1p0S>1p0SI1p0T41p0T;1p0TO1pSNV61pUFV71pU0V81pT4V41pT8V11pU8V31pU4V61p4V;1pQ6V:1pTDVB1pQBVD1pQJVJ1pT>UI1pTNUK1pSLV41pTJVE1pTFVI1pQDVK1pQ8VD1pT<VI1pHVJ1pT6VB1pU6VD1pUDVF1pU2VH1pT0VO1pT:W01pTLW11pU<W21pT2VN1p2W21pQ4W11pJW21pQ2W51pTBW;1pQ@W=1pQHWC1pNWJ1")) (only parsing).
Variable K : ltac:(sec_ty2 constr:(SECT) 0%nat 0%nat).
Variable R : ltac:(sec_ty2 constr:(SECT) 1%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SECT) 2%nat 0%nat).
Variable model : ltac:(sec_ty2 constr:(SECT) 3%nat 0%nat).
Variable LBX : ltac:(sec_ty2 constr:(SECT) 4%nat 0%nat).
Variable FF : ltac:(sec_ty2 constr:(SECT) 5%nat 0%nat).
Variable LK : ltac:(sec_ty2 constr:(SECT) 6%nat 0%nat).
Variable Aw : ltac:(sec_ty2 constr:(SECT) 7%nat 0%nat).
Variable cr : ltac:(sec_ty2 constr:(SECT) 8%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SECT) 9%nat 0%nat).
Variable r : ltac:(sec_ty2 constr:(SECT) 10%nat 0%nat).
Variable fb : ltac:(sec_ty2 constr:(SECT) 11%nat 0%nat).
Variable cat : ltac:(sec_ty2 constr:(SECT) 12%nat 0%nat).
Variable s : ltac:(sec_ty2 constr:(SECT) 13%nat 0%nat).
Variable str : ltac:(sec_ty2 constr:(SECT) 14%nat 0%nat).
Variable sm : ltac:(sec_ty2 constr:(SECT) 15%nat 0%nat).
Variable e : ltac:(sec_ty2 constr:(SECT) 16%nat 0%nat).
Variable F : ltac:(sec_ty2 constr:(SECT) 17%nat 0%nat).
Variable fl : ltac:(sec_ty2 constr:(SECT) 18%nat 0%nat).
Variable LK2 : ltac:(sec_ty2 constr:(SECT) 19%nat 0%nat).
Variable M2 : ltac:(sec_ty2 constr:(SECT) 20%nat 0%nat).
Variable model2 : ltac:(sec_ty2 constr:(SECT) 21%nat 0%nat).
Variables (pc : Z).
Variables (args : list fframe -> bvmap 5 word -> (word -> option byte) -> Z -> Z -> PM.pst -> Prop).
Variables (res : bvmap 5 word -> bvmap 5 word -> (word -> option byte) -> PM.srcst -> PM.srcst -> PM.strm -> PM.strm -> Prop).
Variables (fx1 : FPState).
Variable R1 : ltac:(sec_ty2 constr:(SECT) 26%nat 0%nat).
Variable M1 : ltac:(sec_ty2 constr:(SECT) 27%nat 0%nat).
Variable model1 : ltac:(sec_ty2 constr:(SECT) 28%nat 0%nat).
Variable LK1 : ltac:(sec_ty2 constr:(SECT) 29%nat 0%nat).
Variable Aw1 : ltac:(sec_ty2 constr:(SECT) 30%nat 0%nat).
Variable s1 : ltac:(sec_ty2 constr:(SECT) 31%nat 0%nat).
Variable sm1 : ltac:(sec_ty2 constr:(SECT) 32%nat 0%nat).
Variable e1 : ltac:(sec_ty2 constr:(SECT) 33%nat 0%nat).
Variable cr1 : ltac:(sec_ty2 constr:(SECT) 34%nat 0%nat).
Variables (rr v c : Z).
Lemma src_call : ltac:(sec_stmt2 constr:(SECT) 38%nat 0%nat).
Proof.
intros SRC CTX G LM G1 RA G2 G3 G4 G10 ARG EC1 KX.
pose proof (PMALPK.alp_callpre L ar C HI HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 4 CTX G LM ltac:(lia))
as (ASTKc & SZc & FRc & FSc & FOKc).
pose proof CTX as CTX0.
destruct CTX as (HH & AM & K0 & ENT & FRM & FRS & FOK & SP32 & ARGS & RPRE & INCS & INV & EC0 & UNR & CRED & KONT).
destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 10) with 32768 in *.
pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
pose proof FOK as ((rs & Hfb) & Fal).
pose proof LM as (BI & RP1 & LS1 & STEP1 & EE1 & CK1).
pose proof BI as (HH1 & AM1 & _ & _ & _ & ASTK1 & _).
set (FF' := (F, 1, sp - 256 + 32) :: FF) in *.
set (LB1 := PM.parser_own s1 ++ LBX) in *.
assert (FOK' : PMSPA.frame_okA FF' fb) by exact (PMAUAR.frame_okA_push FF fb F 1 (sp - 256 + 32) FOK).
destruct RP1 as (PA1 & IA1 & VIS1 & VREF1 & BASE1 & ERR1 & TB1).
pose proof (PMAPAR.op_vis L ar C HI LY HIok _ _ LK1 cr1 Aw1 M1 model1 fb _ s1 HH1 FOK' PA1) as ((O1 & O8 & ONSH) & Zop & Z32 & Z20 & OWR & OCE & OVIS & AOP & Eop).
pose proof (PMASK.iss_vis L ar C HI LY HIok _ _ LK1 cr1 Aw1 M1 model1 fb str sm1 sp 32768 HH1 FOK' IA1 ASTK1) as ((I1 & I8 & INSH) & Zis & IWR & ICE & IVIS & AOI & IOS).
set (op := PMSPA.o_p PMA.AD fb) in *. set (ov := PMSPA.o_v PMA.AD fb) in *. set (oec := PMSPA.o_ec PMA.AD fb) in *.
set (ois := PMSPA.o_is PMA.AD fb) in *.
assert (Eov : ov = fb + 432) by reflexivity. assert (Eoec : oec = fb + 992) by reflexivity. assert (Eois : ois = fb + 96) by reflexivity.
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH1) as (WB1 & WF1 & FSAPP & FSCEIL & _).
pose proof (WF1 _ (or_intror Hfb)) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 4) with 1024 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL, F1, F2.
pose proof G as G'. unfold PMALPD.aframe in G'.
destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
assert (AOF : forall a k0, fb + 32 <= a -> a + k0 <= fb + 1016 -> PMSPA.aobjA FF' a k0).
{ intros a k0 X1 X2. exists (fb, 4, rs). split; [right; exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 4) with 1024. clear - X1 X2; lia. }
set (qc := PM.sr_qc (PM.p_src s1)) in *.
assert (Iq : In (qc, PM.CHUNK) (PM.parser_own s1)) by (unfold PM.parser_own, PM.src_own; left; reflexivity).
assert (IqL : In (qc, PM.CHUNK) LB1) by (unfold LB1; apply in_or_app; left; exact Iq).
pose proof (WB1 _ IqL) as ((Bq0 & _ & _ & _ & Bq4 & Bq5) & _). cbn [fst snd] in Bq0, Bq4, Bq5. unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI, PM.CHUNK in Bq5, Bq4.
destruct Bq5 as (_ & Bq5 & _).
pose proof (PMASK.blk_img L ar C HI LY HIok _ _ _ _ _ _ _ _ _ HH1 IqL) as Bqi. unfold PM.CHUNK in Bqi.
unfold PMSPA.src_spec in SRC.
apply (SRC fx1 R1 M1 model1 K LBX FF' LK1 Aw1 cr1 (sp - 256) rr fb s1 str sm1 [] HH1 AM1 K0).
{ split; [exact G1|]. split; [exact RA|]. split; [exact G2|]. split; [exact (eq_trans G3 Rgp)|]. split; [exact (eq_trans G4 Rtp)|]. split; [exact ASTKc| exact SZc]. }
{ exact FRc. }
{ exact FSc. }
{ exact FOKc. }
{ exact G10. }
{ exact ARG. }
{ reflexivity. }
{ exact PA1. }
{ exact IA1. }
{ exact BASE1. }
{ exact INCS. }
intros fx2 R2 M2' model2' LK2' Aw2 src2 sm2 RP2 PA2 IA2 STEP2 RES2 HP2 MRT2 INCL2 INCA2 AM2 HH2.
change (PMSPA.pm_scr 4) with 20480 in HP2. rewrite app_nil_r in HP2.
pose proof STEP2 as (QC2 & _).
assert (EOWN : PM.parser_own (PMSPA.with_src s1 src2) = PM.parser_own s1)
by (unfold PMSPA.with_src, PM.parser_own, PM.src_own; cbn [PM.p_src PM.p_b PM.p_k PM.p_tb]; rewrite QC2; reflexivity).
set (Wc := PMSPA.W_src PMA.AD fb (PM.p_src s1)) in HP2.
assert (WcR : forall rr0 a, In rr0 Wc -> L5.in_rng rr0 a ->
(op + 280 <= a < op + 320) \/ (ois + 40 <= a < ois + 48) \/ (ois + 152 <= a < ois + 156) \/ (qc <= a < qc + 16384)).
{ intros rr0 a Hin Hr. unfold Wc, PMSPA.W_src, PMSPA.W_srcf, PMSPA.o_src, PMSPA.o_is, PMSPA.o_p in Hin. cbn [app pa_off_p pa_off_is PMA.AD ADDR_A] in Hin.
fold qc in Hin. unfold L5.in_rng in Hr. destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hr; unfold PM.CHUNK in Hr; clear - Hr Eop Eois;
[left|right;left|right;right;left|right;right;right]; lia. }
pose proof (L5SAR.ek_callee L ar LBX (PM.parser_own s1) FF' [] (sp - 256) 20480 (sp - 256) 20480 Wc Wc M1 M2' HP2 ltac:(clear; lia) ltac:(clear; lia) (fun a _ X => X)) as EK12.
assert (EK12' : L5SAR.ek L ar LB1 FF' (sp - 256) 20480 Wc M1 M2').
{ destruct HP2 as (P & _). intros a (Ha & Hc & Ho). apply P. split; [exact Ha|]. split; [exact Hc| exact Ho]. }
assert (WAPPc : PMKA.wapp Wc).
{ intros rr0 Hin. unfold Wc, PMSPA.W_src, PMSPA.W_srcf, PMSPA.o_src, PMSPA.o_is, PMSPA.o_p in Hin. cbn [app pa_off_p pa_off_is PMA.AD ADDR_A] in Hin.
fold qc in Hin. unfold BIGSHADOW_LO, BIGSHADOW_HI. destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd]; unfold PM.CHUNK.
- destruct ONSH as [Y|Y]; clear - Y Eop; lia.
- destruct INSH as [Y|Y]; clear - Y Eois; lia.
- destruct INSH as [Y|Y]; clear - Y Eois; lia.
- destruct Bq5 as [Y|Y]; clear - Y; lia. }
pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH1) as FRB1.
pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH1) as BRB1.
assert (OUTW : forall a n, fb + 32 <= a -> a + n <= fb + 1016 -> (a + n <= op + 280 \/ op + 320 <= a) -> (a + n <= ois + 40 \/ ois + 48 <= a) ->
(a + n <= ois + 152 \/ ois + 156 <= a) -> forall i, a <= i < a + n -> L5.outside Wc i).
{ intros a n X1 X2 X3 X4 X5 i Hi rr0 Hin Hr. destruct (WcR rr0 i Hin Hr) as [Y|[Y|[Y|Y]]]; [clear - Hi Y X3; lia| clear - Hi Y X4; lia| clear - Hi Y X5; lia|].
destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ qc 16384 a n HH1 IqL (AOF a n X1 X2)) as [Z|Z]; clear - Hi Y Z; lia. }
apply (KX fx2 R2 M2' model2' LK2' Aw2 src2 sm2 RP2 RES2).
2: { apply (PMKA.ec_keepA RSEGS L ar LB1 FF' (sp - 256) 20480 Wc M1 M2' EK12' WAPPc FRB1 _ v c (AOF oec 16 ltac:(clear - Eoec; lia) ltac:(clear - Eoec; lia))); [| exact EC1].
apply OUTW; clear - Eoec Eop Eois; lia. }
apply (PMALPK.alp_liftW L ar C HI HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 e1 cr1
M2' model2' LK2' Aw2 (PMSPA.with_src s1 src2) sm2 e1 cr1 (PM.parser_own s1) 20480 Wc CTX0 G LM ltac:(clear; lia) HP2).
- intros rr0 a Hin Hr. change (ff_bytes 1 / 8) with 16. unfold SB.
pose proof GFR as (GF1 & GF2 & _). assert (D1 : 0 <= F / 8) by (apply Z.div_pos; clear - GF1; lia).
assert (D2 : F / 8 <= 17592186044400) by (change (ff_bytes 1) with 128 in GF2; apply Z.div_le_upper_bound; clear - GF2; lia).
destruct (WcR rr0 a Hin Hr) as [X|[X|[X|X]]]; (split; [clear - X OCE ICE Bq4 GFCEIL SLO Eop Eois; lia|]).
+ destruct ONSH as [Y|Y]; clear - X Y D1 D2; lia.
+ destruct INSH as [Y|Y]; clear - X Y D1 D2; lia.
+ destruct INSH as [Y|Y]; clear - X Y D1 D2; lia.
+ destruct Bq5 as [Y|Y]; clear - X Y D1 D2; lia.
- intros a Hc Ho rr0 Hin Hr. destruct (WcR rr0 a Hin Hr) as [X|[X|[X|X]]].
+ apply (Ho (PMSPA.o_src PMA.AD fb + 256, 40)); [unfold PMSPA.W_run, PMSPA.W_srcf; right; left; reflexivity| unfold L5.in_rng, PMSPA.o_src; fold op; cbn [fst snd]; clear - X; lia].
+ apply (Ho (PMSPA.o_is PMA.AD fb + 40, 8)); [unfold PMSPA.W_run, PMSPA.W_srcf; right; right; left; reflexivity| unfold L5.in_rng; fold ois; cbn [fst snd]; clear - X; lia].
+ apply (Ho (PMSPA.o_is PMA.AD fb + 152, 4)); [unfold PMSPA.W_run, PMSPA.W_srcf; right; right; right; left; reflexivity| unfold L5.in_rng; fold ois; cbn [fst snd]; clear - X; lia].
+ assert (Iq0 : In (qc, PM.CHUNK) (PM.parser_own s)).
{ unfold qc. destruct STEP1 as (Q1 & _). rewrite Q1. unfold PM.parser_own, PM.src_own; left; reflexivity. }
exact (PMARS1.own_not_aclient L ar C HI HIok (PM.parser_own s) LBX FF LK cr Aw M _ qc 16384 a sp 32768 HH Iq0 X Hc).
- unfold PMSPA.run_pre. split; [exact PA2|]. split; [exact IA2|]. split; [| split; [| split; [| split]]].
+ apply (PMKA.visitor_keepA RSEGS PMA.AD L ar LB1 FF' (sp - 256) 20480 Wc M1 M2' EK12' WAPPc FRB1 _ (AOF ov 8 ltac:(clear - Eov; lia) ltac:(clear - Eov; lia))); [| exact VIS1].
apply OUTW; clear - Eov Eop Eois; lia.
+ apply (PMKA.u64_keepA RSEGS L ar LB1 FF' (sp - 256) 20480 Wc M1 M2' EK12' WAPPc FRB1 (op + 384) _ (AOF (op + 384) 8 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))); [| exact VREF1].
apply OUTW; clear - Eop Eois; lia.
+ apply (PMASK.base_keep L ar C LY LB1 FF' (sp - 256) 20480 Wc M1 M2' EK12'); [| exact BASE1].
intros a Ha rr0 Hin Hr. destruct (WcR rr0 a Hin Hr) as [X|[X|[X|X]]]; [clear - Ha X O1 Eop; lia| clear - Ha X I1; lia| clear - Ha X I1; lia| destruct Bqi as [Y|Y]; clear - Ha X Y; lia].
+ apply (PMKA.err_okA_keep RSEGS PMA.AD PMA.AAD L ar LB1 FF' (sp - 256) 20480 Wc M1 M2' EK12' e1 PMA.addrs_wf_A); [| exact ERR1].
intros a D. pose proof (PMASK.dep_img a D) as DI. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [clear - DI; lia|].
split; [exact (PMA.ly_static L C LY a D)|]. intros rr0 Hin Hr. destruct (WcR rr0 a Hin Hr) as [X|[X|[X|X]]];
[clear - DI X O1 Eop; lia| clear - DI X I1; lia| clear - DI X I1; lia| destruct Bqi as [Y|Y]; clear - DI X Y; lia].
+ exact TB1.
- exact STEP2.
- intros X; exact X.
- unfold PMSPA.credit_keep, PMSPA.with_src, PM.pot_parser. cbn [PM.p_k PM.p_tb PM.p_tg]. clear; lia.
- exact MRT2.
- exact INCL2.
- exact INCA2.
- exact AM2.
- rewrite EOWN. exact HH2.
Qed.
End S.
End WithHeap.
End PMALPK10.
