(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import HeapIfaceAJx PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA IcptIfaceAB0 LibIface
AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5CoreKit L5LazyA L5DefsAB0
L5CoreAB0 L5CoreSpecsAB0 L5StepARB0 L5CoreBRB0 L5ADetailHRB0 PmLayout PmLayoutA PmModel PmModelFacts PmStatics PmStaticsA PmSpecsA PmSpecsAX PmSpecsAb
PmModelFactsA PmStepAB0 PmStep PmFrame PmParKit PmParStep PmBSrcKit PmBParKit PmBUarK PmBUar PmParKit2 PmBReset1 PmSpecsBX PmBParseD PmBParseK PmBParseK4 PmBParseK5
PmBParseK11 PmBParseX PmBParseP1.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmBParseA5 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBParseD.PMBLPD."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsBX.PMBX."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "stdpp.bitvector.definitions."], [["0Aw"; "0Aw1"; "0Aw2"; "1app"; "1bool"; "1cons"; "1list"; "1nil"; "1option"; "1prod"; "2eq"; "3Z"; "0F"; "0FF"; "0HI"; "0K"]; ["0L"; "0LBX"; "0LK"; "0LK1"; "0LK2"; "0LK2'"; "4Model"; "5bvmap"; "0M"; "0M1"; "0M2"; "0M2'"; "0R"; "0R1"; "0R2"; "6credit"]; ["7fframe"; "8SCFG"; "9aframe"; "9alinv"; "9apctx"; "9lmem"; "9lregs"; ":ADDR_B"; ";PS"; ";PST"; ";pst"; ";pstate"; ";srcst"; ";strm"; ";vstr"; "<cfg"]; ["<ec_at"; "<o_ec"; "<o_p"; "=vec_clear_spec"; ">FPState"; "?TSet"; "@srealizes"; "Aloaded_segments"; "0SCFG_P"; "0ar"; "0cat"; "0cr"; "0cr1"; "0dn1"; "0dp1"; "0e"]; ["0e1"; "0fb"; "0fl"; "0fx1"; "0fx2"; "0mo1"; "0model"; "0model1"; "0model2"; "0model2'"; "0pre"; "0r"; "0s"; "0sm"; "0sm1"; "0sp"]; ["0src1"; "Bbv"; "0str"; "0tb1"; "0tg1"; "0ti"; "0tl"; "0tt"; "0vb1"; "0vk1"]]).
Local Ltac lia := first [ L5FastLia.plia | Lia.lia ].
Module PMBLPA5.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMB.ly_as0 L C LY.
Lemma acc_shrink : ltac2:(TCodec.tc2 tcn__PmBParseA5 "V1&QE&Gy5'RAyR0%211%5241'8y8%611%311p061'F'6'9';%2211%411&Q0%611&O'Q:'Q>'Q='4'QD'Q<&QCvQHv@vQIv>%544321&Q4rQ9rQ8rQ7rQ6rQ5rQ4rQ3rQ2rQ1rQ0rOrNrMrLrKrJrI%BEGFEDA@?>=<;:987654321&Q2rHrGrFrE%5BLKJGFEDCBA@?;74321&Q6rQ:rD&QB&Q7%221D&QA%123F%8676I31A&Q5rQ;rCrBrA(Q9r@r?r>r=r<r;r:r9(5'Q;(Q8+1zr8%443212(7%117%93831%C9BA@?>=<;1r7r6r5%LJR2R1R0KQ4QMQLQKQJQIQHQGQEQCQBQAQ@Q?Q3JIH4321&Q@&QG%Q22Q4QI%352Q;1>QI':%13RFOA%23RGQ0ArQErQ=%Q<2Q;Q5%Q:2Q<Q6%QA64=321R5rQFrQDrQCrQBrQArQ@rQ?rQ>rQ<r4r3r2%Q@9R8R7R6R3R2R1R0QLO%QFJRLRKRJ=B<;:98765QNRGRFRERDK4321QCQBQ@%QJ2QLB%K5JN1Q67'QF&Q1%11S2&Q?+ee\H%26Q0QAQ;1Q5Q4rQI%74Q2521p091p0<1p0K1p6SF1pQ<SE1pTDSM1pQHSO1pQNT51pT:SC1+edcH%?6Q=RNRM1RLRI%C4Q>A1Op041p0Q;1p0Q=1p0Q@1p0QE1p0RC1p0RM1p0S41p0SH1pSJT51pT2T21pTNT41pU@T=1pUDT>1pUBT?1pU:T@1pU8T:1pU2T71pSNTC1pSLTD1pT<TE1p4TD1pQ8TC1pT@TK1pQDTM1pQLU31pT8TA1pTBTO1pQFU11pQ:TJ1pT6TO1pJU01pT0TH1pTLTJ1pU6TL1pTJTN1pSFU51pT4U61pTHU71pU0U81pSHU41p2U81pQ6U71pLU81pQ4U;1pT>UA1pQBUC1pQJUI1pQ0V01").
Proof. intros K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx1 R1 M1 model1 LK1 Aw1 mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 tt sm1 e1 cr1.
intros ASH CTX G LR LM EC1 Emo Edn KX.
set (s1 := PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 [PM.PS 1 0 tt 0]) in *.
pose proof LR as LR0.
pose proof (PMBLPK.alp_callpre L ar C HI HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 0 CTX G LM ltac:(lia))
as (ASTKc & SZc & FRc & FSc & FOKc).
pose proof (PMBLPK.lfacts_of L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 0 cat CTX G LM EC1) as LF.
pose proof (PMBLPK.tfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 [] (PM.PS 1 0 tt 0) CTX G LM eq_refl) as (TF & PTv & PT1).
pose proof (PMBLPK4.hfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 CTX G LM) as (HM8 & HD9 & _).
cbn [s1 PM.p_b PM.p_more PM.p_done] in TF, PTv, PT1, HM8, HD9. rewrite Emo in HM8. rewrite Edn in HD9.
pose proof CTX as CTX0.
destruct CTX as (HH & AM & K0 & ENT & FRM & FRS & FOK & SP32 & ARGS & RPRE & INCS & INV & EC0 & UNR & CRED & KONT).
destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 10) with 32768 in *.
pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
pose proof FOK as ((rs & Hfb) & Fal).
pose proof LM as (BI & RP1 & LS1 & STEP1 & EE1 & CK1).
pose proof BI as (HH1 & AM1 & _).
set (FF' := (F, 1, sp - 288 + 32) :: FF) in *.
set (LB1 := PM.parser_own s1 ++ LBX) in *.
assert (FOK' : PMSPA.frame_okA FF' fb) by exact (PMBUAR.frame_okA_push FF fb F 1 (sp - 288 + 32) FOK).
destruct RP1 as (PA1 & IA1 & VIS1 & VREF1 & BASE1 & ERR1 & TB1).
pose proof (PMBPAR.op_vis L ar C HI LY HIok _ _ LK1 cr1 Aw1 M1 model1 fb _ s1 HH1 FOK' PA1) as ((O1 & O8 & ONSH) & Zop & Z32 & Z20 & OWR & OCE & OVIS & AOP & Eop).
set (op := PMSPA.o_p PMB.AD fb) in *. set (ov := PMSPA.o_v PMB.AD fb) in *. set (oec := PMSPA.o_ec PMB.AD fb) in *.
set (ois := PMSPA.o_is PMB.AD fb) in *.
assert (Eov : ov = fb + 432) by reflexivity. assert (Eoec : oec = fb + 992) by reflexivity. assert (Eois : ois = fb + 96) by reflexivity.
set (T := vb1 + 32 * Z.of_nat (length (@nil PM.pstate))) in *.
assert (ET : T = vb1) by (unfold T; cbn [length Z.of_nat]; clear; lia).
set (MV := mrestrict (ahid Aw1 model1) M1) in *.
pose proof PA1 as (_ & PD1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PC320 & _ & PVEC & _). cbn [s1 PM.p_b PM.p_k PM.p_stk] in PVEC.
pose proof PVEC as PVEC0. destruct PVEC as (VC0 & VC8 & VC16 & Hk & Hlen & Hal & DB & CB & AN & EL).
assert (V360 : L5.u64_at RSEGS MV (op + 360) T).
{ rewrite ET. apply (proj2 (L5A.u64_at_vis _ M1 (op + 360) vb1 (OVIS (op + 360) 8 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - O1; lia) ltac:(clear - O1; lia))). exact VC0. }
PMBLPK5.lf_open LF. PMBLPK5.lr_open LR.
pose proof PTv as (PT0 & _). cbn [PM.ps_mode] in PT0.
unfold PMBLPK.tfacts in TF. destruct TF as (TLO & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & T64).
cfeed P (PMBLPP1.blpH1_conc fx1 R1 MV (fun j => match j with 2%nat => sp | 34%nat => T | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 48%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PMBLPP1.aligned; assumption]).
destruct P as (fxa & Ra & Mav & MGa & _ & FRZa & MSa & KSa & ERA & E10 & _).
assert (LRa : PMBLPD.lregs R Ra sp op oec F) by (apply (PMBLPK4.lregs_ks R R1 Ra sp op oec F PMBLPP1.KS_blpH1 LR0 KSa); PMBLPK4.ksinc).
pose proof LRa as (X2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X3 & X4).
pose proof G as G'. unfold PMBLPD.aframe in G'.
destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
assert (AOF : forall a k0, fb + 32 <= a -> a + k0 <= fb + 1016 -> PMSPA.aobjA FF' a k0).
{ intros a k0 Y1 Y2. exists (fb, 4, rs). split; [right; exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 4) with 1024. clear - Y1 Y2; lia. }
unfold PMSPA.cfg.
apply (L5SAR.apiece L ar C HI LYa HIok LB1 FF' LK1 cr1 Aw1 M1 model1 fx1 fxa R1 0xad278 Ra 0xaaf04 Mav (fun a => False) K HH1 AM1 MSa MGa).
{ intros a Ha Nw. apply FRZa. exact Ha. }
{ intros a Ha Wa. destruct Wa. }
intros M1' model1' HH1' AM1' MRT1' HID1' VIS1' MGM1' FR1' VV1'.
assert (EQ1 : M1' = M1).
{ apply functional_extensionality. intros w. rewrite <- (Z_to_bv_bv_unsigned _ w). apply FR1'; [apply bv_unsigned_in_range| intros []]. }
subst M1'.
set (qc := PM.sr_qc src1) in *.
set (LBc := (qc, PM.CHUNK) :: (PM.vs_own tb1 ++ LBX)) in *.
assert (EPO : LB1 = (qc, PM.CHUNK) :: (vb1, 32 * 2 ^ vk1) :: (PM.vs_own tb1 ++ LBX)) by (unfold LB1, s1, PM.parser_own, PM.src_own, PM.vec_own; cbn; reflexivity).
assert (HHs : ri_inv HI (PM.vec_own vb1 vk1 ++ LBc) FF' LK1 cr1 Aw1 M1 (vml_of model1')).
{ rewrite EPO in HH1'. exact (PMBRS1.ri_swap12 L ar C HI HIok _ _ _ _ _ _ _ _ _ HH1'). }
assert (INCc : forall b, In b LBc -> In b LB1) by (intros b Hb; rewrite EPO; destruct Hb as [<-|Hb]; [left; reflexivity| right; right; exact Hb]).
pose proof (PMBSK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH1) as FRB1.
pose proof (PMBSK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH1) as BRB1.
assert (BRBc : forall b, In b LBc -> 0 <= fst b /\ fst b + snd b <= 2 ^ 47) by (intros b Hb; exact (BRB1 b (INCc b Hb))).
assert (EK01 : L5SAR.ek L ar LBc FF' (sp - 288) 12288 [(op + 368, 8)] M1 M1).
{ apply (L5SAR.ek_piece L ar LBc FF' (sp - 288) 12288 [(op + 368, 8)] M1 M1 (fun a => False) (fun a _ _ => eq_refl)). intros a Ha _ O X. destruct X. }
assert (WAPP1 : PMKB.wapp [(op + 368, 8)]).
{ apply PMKB.wapp_cons; [| apply PMKB.wapp_nil]. cbn [fst snd]. unfold BIGSHADOW_LO, BIGSHADOW_HI. destruct ONSH as [Y|Y]; [right| left]; clear - Y; lia. }
assert (OUT1 : forall a n, (a + n <= op + 368 \/ op + 376 <= a) -> forall i, a <= i < a + n -> L5.outside [(op + 368, 8)] i).
{ intros a n Y i Hi r0 [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - Hi Hr Y. lia. }
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH1) as (WB1 & _).
assert (Ivb : In (vb1, 32 * 2 ^ vk1) LB1) by (rewrite EPO; right; left; reflexivity).
destruct (WB1 _ Ivb) as ((Bb0 & _ & _ & _ & Bb4 & Bb5) & _). cbn [fst snd] in Bb0, Bb4, Bb5. unfold app_mem in Bb5.
pose proof (PM.pow2_pos vk1 ltac:(lia)) as P2k.
unfold PMBX.vec_clear_spec, PMSBX.vec_clear_spec_at in ASH.
apply (ASH fxa Ra M1 model1' K LBc FF' LK1 Aw1 cr1 (op + 360) vb1 vk1 [PM.PS 1 0 tt 0] (sp - 288) 0xad598 HHs AM1' K0).
{ split; [exact ERA|]. split; [split; [clear; lia| reflexivity]|]. split; [exact X2|]. split; [exact (eq_trans X3 Rgp)|]. split; [exact (eq_trans X4 Rtp)|].
change (PMSPA.pm_scr 0) with 12288 in *. change (12288 / 8) with 1536 in *.
split; [exact ASTKc|].
apply (PMKB.stksh_keepA L ar LBc FF' (sp - 288) 12288 [(op + 368, 8)] M1 M1 EK01 WAPP1 (sp - 288 - 12288) 1536); [clear - SLO SPT; lia| clear - SLO; lia| clear - SHI SPT; lia| | clear; lia| exact SZc].
apply PMKB.mod16_8'. replace (sp - 288 - 12288) with (sp + (-786) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
{ exact FSc. }
{ exact E10. }
{ apply AOF; clear - Eop; lia. }
{ replace (op + 360) with (op + 45 * 8) by (clear; lia). rewrite Z_mod_plus_full. exact O8. }
{ intros a Ha. apply PC320. clear - Ha; lia. }
{ exact PVEC0. }
intros fx2 R2 M2' model2' LK2' Aw2 RP2 VEC2 ACC2 HP2 MRT2 INCLK2 INCAw2 AM2 HH2.
change (PMSPA.pm_scr 0) with 12288 in HP2. replace (op + 360 + 8) with (op + 368) in HP2 by (clear; lia).
pose proof (PMBLPK4.lregs_pres R Ra R2 sp _ _ F LRa RP2) as LR2.
assert (HH2' : ri_inv HI (PM.parser_own s1 ++ LBX) FF' LK2' cr1 Aw2 M2' (vml_of model2')).
{ change (PM.parser_own s1 ++ LBX) with LB1. rewrite EPO. exact (PMBRS1.ri_swap12 L ar C HI HIok _ _ _ _ _ _ _ _ _ HH2). }
assert (EK12 : L5SAR.ek L ar LBc FF' (sp - 288) 12288 [(op + 368, 8)] M1 M2').
{ apply (L5SAR.ek_callee L ar LBc [] FF' [] (sp - 288) 12288 (sp - 288) 12288 _ _ M1 M2' HP2); [clear; lia| clear; lia| intros a _ O; exact O]. }
pose proof EK12 as EK02.
assert (PD2 : L5.defined M2' op 384).
{ intros i Hi. apply (proj2 (proj2 HP2)); [clear - Hi O1; lia| | apply PD1; exact Hi].
apply (L5SAR.fframe_client L ar LBc FF' (sp - 288) 12288 fb 4 rs); [right; exact Hfb| change (ff_bytes 4) with 1024; clear - Hi Eop; lia]. }
apply (KX fx2 R2 M2' model2' LK2' Aw2 LR2).
2: { apply (PMKB.ec_keepA RSEGS L ar LBc FF' (sp - 288) 12288 [(op + 368, 8)] M1 M2' EK02 WAPP1 FRB1 _ 0 cat (AOF oec 16 ltac:(clear - Eoec; lia) ltac:(clear - Eoec; lia))); [| exact EC1].
apply OUT1. clear - Eop Eoec; lia. }
split; [| split; [| split; [| split; [exact STEP1| split; [exact EE1| exact CK1]]]]].
-
assert (BI1' : PMBUK.binv L ar HI M model LBX FF LK Aw sp 32768 (sp - 288) (PMBLPD.own sp R) F 1 (PMSPA.W_run PMB.AD fb) (PM.parser_own s1) M1 model1' LK1 cr1 Aw1).
{ apply (PMBUK.binv_pieceW L ar HI M model LBX FF LK Aw sp 32768 (sp - 288) (sp - 104) sp (PMBLPD.ocell sp) (PMBLPD.own sp R) F fl 1 LK2 M2 model2 cr (PM.parser_own s) G
_ (PM.parser_own s1) M1 model1 LK1 cr1 Aw1 M1 model1' (fun a => False) BI HH1' AM1' MRT1' MGM1' (fun a _ _ => eq_refl)).
intros a []. }
assert (DFa : 0 <= F / 8 <= 17592186044400).
{ pose proof GFR as (GF1 & GF2 & _). change (ff_bytes 1) with 128 in GF2. split; [apply Z.div_pos; clear - GF1; lia| apply Z.div_le_upper_bound; clear - GF2; lia]. }
apply (PMBUK.binv_callee L ar C HI HIok M model LBX FF LK Aw sp 32768 (sp - 288) (sp - 104) sp (PMBLPD.ocell sp) (PMBLPD.own sp R) F fl 1 LK2 M2 model2 cr (PM.parser_own s) G
_ _ (PM.parser_own s1) ((qc, PM.CHUNK) :: PM.vs_own tb1) (PM.parser_own s1) M1 model1' LK1 cr1 Aw1 M2' model2' LK2' cr1 Aw2 12288 [(op + 368, 8)] BI1' HP2 HH2' AM2 MRT2 INCAw2 INCLK2);
[clear; lia| clear; lia| | | intros a X; exact X].
+ intros rr0 a Hr0 Hr. destruct Hr0 as [<-|[]]. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. unfold PMBLPD.ocell. change (ff_bytes 1 / 8) with 16. unfold SB.
split; [clear - Hr OCE SLO; lia| destruct ONSH as [Y|Y]; clear - Y Hr DFa; lia].
+ intros a _ O r0 [<-|[]] X. apply (O (PMSPA.o_vec PMB.AD fb, 24)); [unfold PMSPA.W_run; cbn [app]; do 5 right; left; reflexivity| unfold L5.in_rng, PMSPA.o_vec in *; fold op; cbn [fst snd] in *; clear - X; lia].
-
unfold PMSPA.run_pre. split; [| split; [| split; [| split; [| split; [| split]]]]].
+ assert (Iqc : In (qc, PM.CHUNK) LBc) by (left; reflexivity).
destruct (BRBc _ Iqc) as (Xq1 & Xq2). cbn [fst snd] in Xq1, Xq2.
apply (PMBLPK11.parser_vec_updA M1 M2' op ois s1 [] PA1 ltac:(clear - O1; lia) ltac:(clear - O1; lia)).
* apply (PMKB.agA_obj L ar _ FF' _ _ _ M1 M2' EK02 WAPP1 FRB1 op 360 (AOF op 360 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))). apply OUT1. clear; lia.
* exact (PMKB.agsh_obj L ar _ FF' _ _ _ M1 M2' EK02 WAPP1 FRB1 op 384 (AOF op 384 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))).
* exact PD2.
* exact VEC2.
* exact Xq1.
* unfold s1; cbn [PM.p_src]; fold qc. clear - Xq2; lia.
* apply (PMKB.agA_blk L ar _ FF' _ _ _ M1 M2' EK02 WAPP1 BRBc _ _ Iqc). intros i Hi.
destruct (PMBSK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ qc 16384 op 384 HH1 (INCc _ Iqc) AOP) as [Z|Z]; intros r0 [<-|[]] Hr; unfold L5.in_rng in Hr; cbn [fst snd] in Hr; unfold PM.CHUNK in *; clear - Z Hi Hr; lia.
* intros c0 n0 p0 E0. cbn [s1 PM.p_tb] in E0. assert (Ip : In (p0, c0) LBc) by (right; apply in_or_app; left; rewrite E0; left; reflexivity).
apply (PMKB.agA_blk L ar _ FF' _ _ _ M1 M2' EK02 WAPP1 BRBc _ _ Ip). intros i Hi.
destruct (PMBSK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ p0 c0 op 384 HH1 (INCc _ Ip) AOP) as [Z|Z]; intros r0 [<-|[]] Hr; unfold L5.in_rng in Hr; cbn [fst snd] in Hr; clear - Z Hi Hr; lia.
+ apply (PMKB.iss_keepA RSEGS PMB.AD L ar LBc FF' _ _ _ M1 M2' EK02 WAPP1 FRB1 BRBc ois str sm1 (AOF ois 272 ltac:(clear - Eois; lia) ltac:(clear - Eois; lia))); [| | | exact IA1].
* intros x Hx. right. apply in_or_app; right. apply INCS. exact Hx.
* apply OUT1. clear - Eop Eois; lia.
* intros c0 n0 p0 E0. unfold PMKB.blk_out. intros i Hi.
assert (Ip : In (p0, c0) LBX) by (apply INCS; rewrite E0; left; reflexivity).
destruct (PMBSK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ p0 c0 op 384 HH1 (in_or_app _ _ _ (or_intror Ip)) AOP) as [Z|Z]; intros r0 [<-|[]] Hr; unfold L5.in_rng in Hr; cbn [fst snd] in Hr; clear - Z Hi Hr; lia.
+ apply (PMKB.visitor_keepA RSEGS PMB.AD L ar LBc FF' _ _ _ M1 M2' EK02 WAPP1 FRB1 _ (AOF ov 8 ltac:(clear - Eov; lia) ltac:(clear - Eov; lia))); [| exact VIS1].
apply OUT1. clear - Eop Eov; lia.
+ apply (PMKB.u64_keepA RSEGS L ar LBc FF' _ _ _ M1 M2' EK02 WAPP1 FRB1 (op + 384) _ (AOF (op + 384) 8 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))); [| exact VREF1].
apply OUT1. clear; lia.
+ apply (PMBSK.base_keep L ar C LY LBc FF' _ _ _ M1 M2' EK02); [| exact BASE1]. intros a Ha rr0 [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - Ha Hr O1; lia.
+ apply (PMKB.err_okA_keep RSEGS PMB.AD PMB.AAD L ar LBc FF' _ _ _ M1 M2' EK02 e1 PMB.addrs_wf_A); [| exact ERR1].
intros a D. pose proof (PMBSK.dep_img a D) as DI. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [clear - DI; lia|].
split; [exact (PMB.ly_static L C LY a D)|]. intros rr0 [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - DI Hr O1; lia.
+ exact TB1.
-
apply (PMBLPD.lspill_agree M1 M2' sp F _ _ _ ltac:(clear - SLO SPT; lia) ltac:(clear - SHI SPT; lia) LS1).
intros a Ha. apply EK02. split; [clear - Ha SLO SHI SPT; lia|]. split.
+ apply (L5SAR.stack_client L ar LBc FF' (sp - 288) 12288 a); clear - Ha SLO SHI SPT; lia.
+ intros r0 [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - Ha Hr OCE SLO; lia.
Qed.
Lemma arm_H1 : ltac2:(TCodec.tc2 tcn__PmBParseA5 "TF&QE&Gy5'RAyR0%211%5241'8y8%611%311p061'F'6'9';%2211%411&Q0%611&O'Q:'Q>'Q='4'QD'Q<'Q;%?11&QCvQHv@vQIv>%544321&Q4rQ<rQ;rQ:rQ9rQ8rQ7rQ6rQ5rQ4rQ3rQ2rQ1rQ0rOrNrMrL%BEGFEDA@?>=<;:987654321&Q2rKrJrIrH%5BLKJGFEDCBA@?;74321&Q3rQ=rGrFrErDrC(Q9rBrAr@r?r>r=r<r;&3r:(5(Q8+1r9r8r7%544321(7%11QK%93QL31%<3QM;1%F9EDCBA@?>1r6r5r4%Q1LQNQMQLQ0QIQHQGQFQEQDQCQBQ@Q?Q>Q=Q<Q;Q:ONMLK4321'QF&QG&Q1%11R3&Q?+edcH%265Q;Q:1Q6Q5rQ?%847521p0:1p0Q=1p0QD1p0R81pSJRG1pT2RD1pTNRF1pU<RO1pU@S01pU>S11pTFRE1pUDS31pUBS41pU:S51pU8RO1pU2RL1pSNS81pSLS91pT<S:1p4S91pQ8S81pT@S@1pQDSB1pQLSH1pT8S61pTBSD1pQFSF1pQ:S?1pT6SD1pJSE1pT0S=1pTLS?1pU6SA1pTJSC1pSFSJ1pT4SK1pTHSL1pU0SM1pSHSI1p2SM1pQ6SL1pLSM1pQ4T01pT>T61pQBT81pQJT>1pQ0TE1").
Proof. intros K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx1 R1 M1 model1 LK1 Aw1 mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre tl tt ti sm1 e1 cr1.
intros ASH CTX G LI.
destruct LI as (LR & INV1 & EC1 & LM).
pose proof INV1 as (IM1 & ID1 & _ & SH1 & _). cbn [PM.p_more PM.p_done PM.p_stk] in IM1, ID1, SH1.
destruct (PMPK2.top_of_shape pre (PM.PS 1 tl tt ti) SH1) as (TOK & TPOS).
destruct TPOS as [(Ep & _)|(_ & NB)]; [| exfalso; apply NB; unfold PM.mode_bottom; cbn [PM.ps_mode]; right; reflexivity].
subst pre.
assert (Etl : tl = 0 /\ ti = 0) by (clear - TOK; unfold PM.pstate_ok, PM.mode_counted, PM.mode_indef, PM.mode_bottom in TOK; cbn [PM.ps_mode PM.ps_len PM.ps_idx PM.ps_type] in TOK; lia).
destruct Etl as (-> & ->).
change ([] ++ [PM.PS 1 0 tt 0]) with [PM.PS 1 0 tt 0] in LM.
apply (acc_shrink K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx1 R1 M1 model1 LK1 Aw1 mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 tt sm1 e1 cr1 ASH CTX G LR LM EC1 IM1 ID1).
intros fx2 R2 M2' model2' LK2' Aw2 LR2 LM2 EC2.
set (S0 := PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 []) in *.
pose proof (PMBLPK.lfacts_of L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M2' model2' LK2' Aw2 S0 sm1 e1 cr1 0 cat CTX G LM2 EC2) as LF.
pose proof (PMBLPK4.hfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M2' model2' LK2' Aw2 S0 sm1 e1 cr1 CTX G LM2) as (HM8 & HD9 & _).
cbn [S0 PM.p_more PM.p_done] in HM8, HD9. rewrite IM1 in HM8. rewrite ID1 in HD9.
pose proof LR2 as LR0.
set (op := PMSPA.o_p PMB.AD fb) in *. set (ov := PMSPA.o_v PMB.AD fb) in *. set (oec := PMSPA.o_ec PMB.AD fb) in *.
set (MV := mrestrict (ahid Aw2 model2') M2') in *.
PMBLPK5.lf_open LF. PMBLPK5.lr_open LR2.
cfeed P (PMBLPP1.blpH1b_conc fx2 R2 MV (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 48%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PMBLPP1.aligned; assumption]).
destruct P as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & _ & _ & _ & _ & DO3 & MO3).
apply (PMBLPK11.md_run L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M2' model2' LK2' Aw2 S0 sm1 e1 cr1 fx2 fx3 R2 R3 0xad598 0xad9a4 M3v 0 cat CTX G LM2 MS3 MG3 FRZ3 DO3 MO3 EC2).
intros M3 model3 LM3 EC3.
apply (PMBLPX.parse_exit L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx3 R3 M3 model3 LK2' Aw2
(PM.PST 0 1 (PM.p_depth S0) (PM.p_src S0) (PM.p_tb S0) (PM.p_tg S0) (PM.p_b S0) (PM.p_k S0) (PM.p_stk S0)) sm1 e1 cr1 0 cat CTX G); [| exact LM3| exact EC3].
apply (PMBLPK4.lregs_ks R R2 R3 sp op oec F PMBLPP1.KS_blpH1b LR0 KS3). PMBLPK4.ksinc.
Qed.
End WithHeap.
End PMBLPA5.
