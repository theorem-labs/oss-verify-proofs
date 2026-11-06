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
PmModelFactsA PmStepA PmStep PmFrame PmParKit PmParStep PmASrcKit PmAParKit PmAUarK PmAUar PmParKit2 PmAParseD PmAParseK PmAParseK4.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmAParseK7 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmAParseD.PMALPD."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayout."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmParKit.PMPK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsAa.PMA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0Aw"; "0Aw1"; "0Aw2"; "1app"; "1bool"; "1cons"; "1list"; "1nil"; "1option"; "1prod"; "1true"; "2and"; "2eq"; "2iff"; "2not"; "3Z"]; ["0F"; "0FF"; "0HI"; "0K"; "0L"; "0LBX"; "0LK"; "0LK1"; "0LK2"; "0LK2'"; "4Model"; "5bvmap"; "0M"; "0M'"; "0M1"; "0M1'"]; ["0M1v'"; "0M2"; "0M2'"; "0R"; "0R1"; "0R1'"; "0R2"; "6mrestrict"; "7msteps"; "8credit"; "8regs_preserved"; "9ahid"; "9fframe"; ";ra_ok"; ";u32_at"; ";u64_at"]; [";u8_at"; ":SCFG"; "<aframe"; "<apctx"; "<lmem"; "=pa_errcat_obj"; ">ADDR_A"; "?PS"; "?PST"; "?inv"; "?mode_bottom"; "?ps_mode"; "?pst"; "?pstate"; "?pstate_at"; "?pstate_ok"]; ["?srcst"; "?strm"; "?vstr"; "@set_more"; "Acfg"; "Aec_at"; "Ao_ec"; "Ao_p"; "Bmake_ec_spec"; "CFPState"; "Cgetr"; "Cmkst"; "Cseg_rom"; "DTSet"; "Esrealizes"; "Fmem_grows"]; ["Gloaded_segments"; "0SCFG_P"; "Hadd"; "Hle"; "Hlt"; "Hof_nat"; "Hpow"; "Hsub"; "0T"; "0a"; "0ar"; "0c"; "0cat"; "0cq"; "0cr"; "0cr1"]; ["0dn"; "0dp"; "0e"; "0e1"; "0fb"; "0fl"; "0fx"; "0fx'"; "0fx1"; "0fx2"; "0i"; "0i'"; "0l"; "0m"; "0m'"; "0mo"]; ["0model"; "0model1"; "0model1'"; "0model2"; "0model2'"; "0pc"; "0pc'"; "0pre"; "0r"; "0rr"; "0s"; "0s1"; "0sm"; "0sm1"; "0sp"; "0src"]; ["IZ_to_bv"; "Ibv"; "0str"; "0t"; "0tb"; "0tg"; "0top"; "0top'"; "0v"; "0vb"; "0vk"; "0vq"; "0x"]]).
Local Ltac lia := first [ L5FastLia.plia | Lia.lia ].
Module PMALPK7.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Lemma inv_set_top : ltac2:(TCodec.tc2 tcn__PmAParseK7 "QI'?'R0'R2'6'QM%211&QI(QHr;r:r9r8r7r6r5r4&3r3(5r2(7%11A%43B31%73C61%A9@?>=<;:91%C11&QO%118&=&QJ&QK%11@%311%31@%511%7231r>r=r<%E3Q3HB%H3Q4K1%Q29543Q1Q0ONM1%Q411p081p0A1p0D1pX@Q:1pX>Q;1pW@Q;1pXFQA1pXDQB1pX<QC1pX:QB1pX0QD1pV4QF1pV2QG1pW0QH1").
Proof. intros mo dn dp src tb tg vb vk pre top top'.
intros (I1 & I2 & I3 & I4 & I5) OK EB. unfold PM.inv in *. cbn [PM.p_more PM.p_done PM.p_depth PM.p_stk PM.p_tb PM.p_tg] in *.
split; [exact I1|]. split; [exact I2|]. split; [rewrite !length_app in *; cbn [length] in *; exact I3|].
split; [exact (PMPK2.stack_shape_set_top pre top top' I4 OK EB)| exact I5].
Qed.
Lemma pstate_mode_upd : ltac2:(TCodec.tc2 tcn__PmAParseK7 "R?'T1yR0%211'8y8%511%311p051pXJ62'?&QN&R@r8r6(QGr5r4r3r2%544321%:49871&RCzr7%3221&RB+Q0%22?1&RF+2+R0%3221%;251';r1%>2=1&RD%1236%5231&>r;%@21C%E21H+4%C231%92K1%=241%811'<r=&T0%12QBQ2%311r>%113%73QA31p091p0C1pUDQA1&Q>r:%24QBE1Q>r<r9%QB4QC1QDQ9%QG4QF3I1p051p091p0Q41p0Q=1p0QB1pVNQN1pVFQO1pX8R01pVJR11pVLR21pUBR31pQLR51pQJR71").
Proof. intros M M' T m l t i m'.
intros (P0 & P8 & P16 & P24) H0 H1 FR U. split; [exact U|]. cbn [PM.ps_len PM.ps_type PM.ps_idx] in *.
split; [apply (L5C.u64_at_agree RSEGS M M'); [intros j Hj; apply FR; lia|lia|lia| exact P8]|].
split; [apply (L5C.u8_at_agree RSEGS M M'); [intros j Hj; apply FR; lia|lia|lia| exact P16]|].
apply (L5C.u64_at_agree RSEGS M M'); [intros j Hj; apply FR; lia|lia|lia| exact P24].
Qed.
Lemma pstate_idx_upd : ltac2:(TCodec.tc2 tcn__PmAParseK7 "RA'T1yR0%211'8y8%511%311p051pXJ62'?&QN&R@r8r6(QGr5r4r3r2%544321%:49871&RCzr7%3221&RB+Q0%22?1&RF+2+R0%3221%;251';r1%>2=1&RD%1236%5231&>r;+H%A221%F21I+8%D231%:2L1%>241%911'<r=&T0%12QCQ3%311r>%113%73QB31p091p0D1pUDQB1&Q?r:%Q521E%34QDG1Q@r<r9%QD451QFQE%QI4QH3K1p051p0:1p0Q61p0Q?1p0QD1pVHR01pVFR11pX8R21pVJR31pVLR41pUBR51pQLR71pQJR91").
Proof. intros M M' T m l t i i'.
intros (P0 & P8 & P16 & P24) H0 H1 FR U. cbn [PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx] in *.
split; [apply (PMF.u32_at_agree RSEGS M M'); [intros j Hj; apply FR; lia|lia|lia| exact P0]|].
split; [apply (L5C.u64_at_agree RSEGS M M'); [intros j Hj; apply FR; lia|lia|lia| exact P8]|].
split; [apply (L5C.u8_at_agree RSEGS M M'); [intros j Hj; apply FR; lia|lia|lia| exact P16]| exact U].
Qed.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.
Lemma more0_run : ltac2:(TCodec.tc2 tcn__PmAParseK7 "VA&R=&Ky5'T1yR0%211%5241'8y8%611%311p061'J'6'9'?%2211%411&Q<%611&Q9'QL'R2'R1'4'R9&QCvRAvDvRJvBrQ7rQ6rQ5rQ4rQ3rQ2rQ1rQ0rOrNrMrLrKrJrIrHrG%FEEDCBA@?>=<;:987654321&QBrFrErDrC%5BJIHGFEDCBA@?;74321&QDrQ8rBrAr@r?r>r=r<%9JQ4Q3Q28Q1Q0ONMLKJHFEDCB;7654321'Q8&R@&R;r:&T0r8%22R31&Q7&Q;%12@E%321G&R<%11;%;5?:731r;r9r7%=2R>1r6%A554217%D3C71&R?%>2NQ3%@21Q5%3218';&RCzr1%3221&RD&RF+2+R0%3221%5271%;271&>&RB&R7&QF%221R7+8%5221r2%C221+1%9241%B241%H241%=11'<r3%QA2SB1%Q811%Q?2R6R:%QA31R<3%63S@31p081p0G1pUDS>1&Q@%G2FRK%I21E%34QOQA1Q5&R5&R6%12KS1%35R3RG1QEQOrQ@rQ?rQ>rQ=rQ<rQ;rQ:rQ9&R3%12S0QC%RIJSDSCSB:9876543RHS@S>S=S<S;S:Q3QCS3S21RNRMRL%>2Q8SB%@5R@M1RDRC'R>&QA%11SJ&R4r4%26RFS4RORM1Q3rQC%74RH521p091p0<1pW6TA1pR0TC1%96RMS6S4S2SCSB%=4RN;1Jp031p0M1p0Q21p0Q71p0R<1p0RA1p0S71p0SB1p0SI1pUHTK1pXBTL1pR2U11pW>TN1pW<TO1pR<U91pR:U:1pV@TH1pV>TI1pV0TO1pV8TL1pWLTN1pWHU11p4U61pQ@U51pW4U=1pQNU?1pW8U?1pR4UA1pQBU:1pV<U?1pQ2U@1pV6U81pWJU:1pX6U<1pWFU>1pUJUE1pV:UF1pWBUG1pWNUH1pUNUD1p2UH1pQ>UG1pQ4UH1pQ<UK1pW2V11pQJV31pR8V91pQ8V@1").
Proof. intros K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 fx fx' R1 R1' pc pc' M1v' v c.
intros CTX G LM MS MG FZ MO EC1 KX.
destruct CTX as (HH & AM & K0 & ENT & FRM & FRS & FOK & SP32 & ARGS & RPRE & INCS & INV & EC0 & UNR & CRED & KONT).
destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 10) with 32768 in *.
pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
pose proof FOK as ((rs & Hfb) & Fal).
destruct LM as (BI & RP1 & LS1 & STEP1 & EE1 & CK1).
pose proof BI as (HH1 & AM1 & MRT1 & INCA1 & INCL1 & ASTK1 & EK1 & DK1 & OWN1 & DSH1). change (PMSPA.pm_scr 10) with 32768 in *.
set (FF' := (F, 1, sp - 256 + 32) :: FF) in *.
set (LB1 := PM.parser_own s1 ++ LBX) in *.
assert (FOK' : PMSPA.frame_okA FF' fb) by exact (PMAUAR.frame_okA_push FF fb F 1 (sp - 256 + 32) FOK).
destruct RP1 as (PA1 & IA1 & VIS1 & VREF1 & BASE1 & ERR1 & TB1).
pose proof (PMAPAR.op_vis L ar C HI LY HIok _ _ LK1 cr1 Aw1 M1 model1 fb _ s1 HH1 FOK' PA1) as ((O1 & O8 & ONSH) & Zop & Z32 & Z20 & OWR & OCE & OVIS & AOP & Eop).
set (op := PMSPA.o_p PMA.AD fb) in *. set (ov := PMSPA.o_v PMA.AD fb) in *. set (oec := PMSPA.o_ec PMA.AD fb) in *.
set (ois := PMSPA.o_is PMA.AD fb) in *.
assert (Eov : ov = fb + 432) by reflexivity. assert (Eoec : oec = fb + 992) by reflexivity. assert (Eois : ois = fb + 96) by reflexivity.
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH1) as (WB1 & WF1 & FSAPP1 & FSCEIL1 & _).
pose proof (WF1 _ (or_intror Hfb)) as (FB1 & FB2 & _). cbn [ff_addr ff_class fst snd] in FB1, FB2. change (ff_bytes 4) with 1024 in *.
unfold app_mem, FS_BYTES in FSAPP1, FB2.
assert (AOF : forall a k0, fb + 32 <= a -> a + k0 <= fb + 1016 -> PMSPA.aobjA FF' a k0).
{ intros a k0 X1 X2. exists (fb, 4, rs). split; [right; exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 4) with 1024. clear - X1 X2; lia. }
pose proof G as G'. unfold PMALPD.aframe in G'.
destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
unfold PMSPA.cfg.
apply (L5SAR.apiece L ar C HI LYa HIok LB1 FF' LK1 cr1 Aw1 M1 model1 fx fx' R1 pc R1' pc' M1v' (fun a => op + 8 <= a < op + 9) K HH1 AM1 MS MG).
{ intros a Ha Nw. apply FZ; [exact Ha| intros X; apply Nw; clear - X; lia]. }
{ intros a Ha Wa. split.
- apply (L5SAR.fframe_client L ar LB1 FF' 0 0 fb 4 rs); [right; exact Hfb| change (ff_bytes 4) with 1024; clear - Wa Eop; lia].
- clear - Wa O1. lia. }
intros M1' model1' HH1' AM1' MRT1' HID1' VIS1' MGM1' FR1' VV1'.
assert (EKf : L5SAR.ek L ar LB1 FF' 0 0 [(op + 8, 1)] M1 M1').
{ apply (L5SAR.ek_piece L ar LB1 FF' 0 0 [(op + 8, 1)] M1 M1' (fun a => op + 8 <= a < op + 9) FR1').
intros a Ha _ O X. apply (O (op + 8, 1)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - X; lia]. }
assert (MO0f : L5.u8_at RSEGS M1' (op + 8) 0).
{ apply (proj1 (L5A.u8_at_vis (ahid Aw1 model1) M1' (op + 8) 0 (OVIS (op + 8) 1 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - O1; lia) ltac:(clear - O1; lia))).
rewrite VIS1'. exact MO. }
pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH1) as FRB1.
pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH1) as BRB1.
assert (OUT8 : forall a n, (a + n <= op + 8 \/ op + 9 <= a) -> forall i, a <= i < a + n -> L5.outside [(op + 8, 1)] i).
{ intros a n X3 i Hi rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - Hi Hr X3. lia. }
assert (OUTB8 : forall q m, In (q, m) LB1 -> forall i, q <= i < q + m -> L5.outside [(op + 8, 1)] i).
{ intros q m Hq i Hi rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr.
destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q m op 384 HH1 Hq AOP) as [Z|Z]; clear - Hi Hr Z; lia. }
assert (WAPP8 : PMKA.wapp [(op + 8, 1)]).
{ apply PMKA.wapp_cons; [| apply PMKA.wapp_nil]. cbn [fst snd]. unfold BIGSHADOW_LO, BIGSHADOW_HI. destruct ONSH as [Y|Y]; [right| left]; clear - Y; lia. }
assert (Ivb : In (PM.p_b s1, 32 * 2 ^ PM.p_k s1) LB1) by (apply in_or_app; left; unfold PM.parser_own, PM.vec_own; right; left; reflexivity).
assert (Iqc : In (PM.sr_qc (PM.p_src s1), PM.CHUNK) LB1) by (apply in_or_app; left; unfold PM.parser_own, PM.src_own; left; reflexivity).
apply (KX M1' model1').
2: { apply (PMKA.ec_keepA RSEGS L ar _ FF' 0 0 _ M1 M1' EKf WAPP8 FRB1 _ v c (AOF oec 16 ltac:(clear - Eoec; lia) ltac:(clear - Eoec; lia))); [| exact EC1].
apply OUT8. clear - Eop Eoec; lia. }
split; [| split; [| split; [| split; [exact STEP1| split; [exact EE1| exact CK1]]]]].
- apply (PMAUK.binv_pieceW L ar HI M model LBX FF LK Aw sp 32768 (sp - 256) (sp - 104) sp (PMALPD.ocell sp) (PMALPD.own sp R) F fl 1 LK2 M2 model2 cr (PM.parser_own s) G
_ (PM.parser_own s1) M1 model1 LK1 cr1 Aw1 M1' model1' (fun a => op + 8 <= a < op + 9) BI HH1' AM1' MRT1' MGM1' FR1').
intros a X. split.
+ unfold PMALPD.ocell. clear - X OCE SLO. lia.
+ right; right; right. intros O. apply (O (PMSPA.o_p PMA.AD fb + 8, 8)); [left; reflexivity| unfold L5.in_rng; fold op; cbn [fst snd]; clear - X; lia].
- unfold PMSPA.run_pre. split; [| split; [| split; [| split; [| split; [| split]]]]].
+ destruct (BRB1 _ Iqc) as (Xq1 & Xq2). destruct (BRB1 _ Ivb) as (Xb1 & Xb2). cbn [fst snd] in Xq1, Xq2, Xb1, Xb2.
apply (PMAPAR.parser_more_updA M1 M1' op ois s1 0 PA1).
* clear - O1; lia.
* clear - O1; lia.
* apply (PMKA.agA_obj L ar _ FF' 0 0 _ M1 M1' EKf WAPP8 FRB1 op 8 (AOF op 8 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))). apply OUT8. clear; lia.
* apply (PMKA.agA_obj L ar _ FF' 0 0 _ M1 M1' EKf WAPP8 FRB1 (op + 9) 375 (AOF (op + 9) 375 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))). apply OUT8. clear; lia.
* exact (PMKA.agsh_obj L ar _ FF' 0 0 _ M1 M1' EKf WAPP8 FRB1 op 384 (AOF op 384 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))).
* pose proof PA1 as (_ & PD1 & _). apply (L5.defined_grows M1 M1' _ _ MGM1' PD1).
* exact MO0f.
* left; reflexivity.
* exact Xq1.
* clear - Xq2; lia.
* apply (PMKA.agA_blk L ar _ FF' 0 0 _ M1 M1' EKf WAPP8 BRB1 _ _ Iqc). apply OUTB8. exact Iqc.
* exact Xb1.
* clear - Xb2; lia.
* apply (PMKA.agA_blk L ar _ FF' 0 0 _ M1 M1' EKf WAPP8 BRB1 _ _ Ivb). apply OUTB8. exact Ivb.
* intros c0 n0 p0 E0. assert (Ip : In (p0, c0) LB1) by (apply in_or_app; left; unfold PM.parser_own, PM.vs_own; rewrite E0; right; right; left; reflexivity).
apply (PMKA.agA_blk L ar _ FF' 0 0 _ M1 M1' EKf WAPP8 BRB1 _ _ Ip). apply OUTB8. exact Ip.
+ apply (PMKA.iss_keepA RSEGS PMA.AD L ar _ FF' 0 0 _ M1 M1' EKf WAPP8 FRB1 BRB1 ois str sm1 (AOF ois 272 ltac:(clear - Eois; lia) ltac:(clear - Eois; lia))); [| | | exact IA1].
* apply incl_appr. exact INCS.
* apply OUT8. clear - Eop Eois; lia.
* intros c0 n0 p0 E0. unfold PMKA.blk_out. apply (OUTB8 p0 c0). apply in_or_app; right. apply INCS. rewrite E0. left; reflexivity.
+ apply (PMKA.visitor_keepA RSEGS PMA.AD L ar _ FF' 0 0 _ M1 M1' EKf WAPP8 FRB1 _ (AOF ov 8 ltac:(clear - Eov; lia) ltac:(clear - Eov; lia))); [| exact VIS1].
apply OUT8. clear - Eop Eov; lia.
+ apply (PMKA.u64_keepA RSEGS L ar _ FF' 0 0 _ M1 M1' EKf WAPP8 FRB1 (op + 384) _ (AOF (op + 384) 8 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))); [| exact VREF1].
apply OUT8. clear; lia.
+ apply (PMASK.base_keep L ar C LY _ FF' 0 0 _ M1 M1' EKf); [| exact BASE1]. intros a Ha rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - Ha Hr O1; lia.
+ apply (PMKA.err_okA_keep RSEGS PMA.AD PMA.AAD L ar _ FF' 0 0 _ M1 M1' EKf e1 PMA.addrs_wf_A); [| exact ERR1].
intros a D. pose proof (PMASK.dep_img a D) as DI. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [clear - DI; lia|].
split; [exact (PMA.ly_static L C LY a D)|]. intros rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - DI Hr O1; lia.
+ exact TB1.
- apply (PMALPD.lspill_agree M1 M1' sp F _ _ _ ltac:(clear - SLO SPT; lia) ltac:(clear - SHI SPT; lia) LS1).
intros a Ha. apply FR1'; [clear - Ha SLO SHI SPT; lia| clear - Ha OCE SLO; lia].
Qed.
Lemma mkec_call : ltac2:(TCodec.tc2 tcn__PmAParseK7 "W2&R=&Ky5'T1yR0%211%5241'8y8%611%311p061'J'6'9'?%2211%411&Q<%611&Q9'QL'R2'R1'4'R9&R8vRAvDvRJvB%544321&QCrQ5rQ4rQ3rQ2rQ1rQ0rOrNrMrLrKrJrIrHrGrFrE%BEGFEDA@?>=<;:987654321&QBrDrCrBrA%5BLKJGFEDCBA@?;74321&QDrQ6r?r>r=r<r;r:r9r8%:JQ7Q6Q59Q2Q1Q0ONMLKIGFEDC87654321'<&R:&T0&REu1%211%42R81%62D1%62R8:%93R821&Q=%11>u2%:11%<2R@1%>2N1&RG+X0%22QA1%A2RC1%D3RC51u3%C11%E2RI1%G2Q81rQ:%I213%K3RJ31u4%J11%L2S01%N2QB1rQ;%Q0213%Q23S131u:%Q111%Q32S71%Q52QJ1&R6&QF%221R9%Q82S:1%Q;3S:51u;%Q:11%Q<2S@1%Q>2R41%Q>2S@QG%QA3S@21';&RC+1%221QM+R0%42QO1%6231&R5&R@%D2CRN%352RB1R4R3&Q:r5%22RM1rQGrQFrQErQDrQCrQBrQArQ@rQ?rQ=rQ9rQ8rQ7r4r3r2(:%RLJSISHSGA@?>=<;:98QAQH765C432S;S:1S8r6rQ>%Q=2Q<1&QE%11Q>%N5M53S=1'R>&QA%11T3&R4r7%26Q3S0ROSE1;rQJ%74Q5521p091p0@1p0Q31p6TF1pQDTE1pW:TM1pR6TO1pR>U51pVDTC1+ej[D%?6Q@T4T31T2T1%C4QAA1Q6p041p0QA1p0QF1p0QN1p0R51p0R?1p0RG1p0RO1p0S91p0S<1p0SG1p0T31p0T:1p0TN1pULU?1pXHU@1pXBUA1pWDUB1pV0U>1pV8U;1pWLU=1pWHU@1p4UE1pQ@UD1pW4UL1pQNUN1pR:V41pVBUB1pW8V01pR4V21pQBUK1pV<V01pQ2V11pV6UI1pWJUK1pX6UM1pWFUO1pUJV61pV:V71pWBV81pWNV91pUNV51p2V91pQ>V81pQ4V91pQ<V<1pW2VB1pQJVD1pR8VJ1pQ8W11").
Proof. intros K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx1 R1 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 rr v vq cq.
intros MKE CTX G LM G1 RA G2 G3 G4 G10 G11 Hv EC1 KX.
pose proof (PMALPK.alp_callpre L ar C HI HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 1 CTX G LM ltac:(lia))
as (ASTKc & SZc & FRc & FSc & FOKc).
pose proof CTX as CTX0.
destruct CTX as (HH & AM & K0 & ENT & FRM & FRS & FOK & SP32 & ARGS & RPRE & INCS & INV & EC0 & UNR & CRED & KONT).
destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 10) with 32768 in *.
pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
pose proof FOK as ((rs & Hfb) & Fal).
pose proof LM as (BI & RP1 & LS1 & STEP1 & EE1 & CK1).
pose proof BI as (HH1 & AM1 & _).
set (FF' := (F, 1, sp - 256 + 32) :: FF) in *.
set (LB1 := PM.parser_own s1 ++ LBX) in *.
assert (FOK' : PMSPA.frame_okA FF' fb) by exact (PMAUAR.frame_okA_push FF fb F 1 (sp - 256 + 32) FOK).
destruct RP1 as (PA1 & IA1 & VIS1 & VREF1 & BASE1 & ERR1 & TB1).
pose proof (PMAPAR.op_vis L ar C HI LY HIok _ _ LK1 cr1 Aw1 M1 model1 fb _ s1 HH1 FOK' PA1) as ((O1 & O8 & ONSH) & Zop & Z32 & Z20 & OWR & OCE & OVIS & AOP & Eop).
set (op := PMSPA.o_p PMA.AD fb) in *. set (ov := PMSPA.o_v PMA.AD fb) in *. set (oec := PMSPA.o_ec PMA.AD fb) in *.
set (ois := PMSPA.o_is PMA.AD fb) in *.
assert (Eov : ov = fb + 432) by reflexivity. assert (Eoec : oec = fb + 992) by reflexivity. assert (Eois : ois = fb + 96) by reflexivity.
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _).
pose proof (WF _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 4) with 1024 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL, F1, F2.
pose proof G as G'. unfold PMALPD.aframe in G'.
destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
assert (AOF : forall a k0, fb + 32 <= a -> a + k0 <= fb + 1016 -> PMSPA.aobjA FF' a k0).
{ intros a k0 X1 X2. exists (fb, 4, rs). split; [right; exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 4) with 1024. clear - X1 X2; lia. }
pose proof EC1 as (_ & _ & ECD1 & ECA1).
unfold PMA.make_ec_spec, PMSPA.make_ec_spec in MKE.
apply (MKE fx1 R1 M1 model1 K LB1 FF' LK1 Aw1 cr1 oec v (sp - 256) rr e1 HH1 AM1 K0).
{ split; [exact G1|]. split; [exact RA|]. split; [exact G2|]. split; [exact (eq_trans G3 Rgp)|]. split; [exact (eq_trans G4 Rtp)|]. split; [exact ASTKc| exact SZc]. }
{ exact FRc. }
{ exact FSc. }
{ exact G10. }
{ exact G11. }
{ exact Hv. }
{ apply AOF; clear - Eoec; lia. }
{ rewrite Eoec. pose proof (Z.div_mod fb 1024 ltac:(lia)) as Dm. rewrite Fal, Z.add_0_r in Dm. rewrite Dm.
replace (1024 * (fb / 1024) + 992) with ((128 * (fb / 1024) + 124) * 8) by (clear; lia). apply Z_mod_mult. }
{ exact ECD1. }
{ exact ECA1. }
{ exact BASE1. }
{ exact ERR1. }
intros fx2 R2 M2' model2' LK2' Aw2 RP2 EC2 ERR2 HP2 MRT2 INCL2 INCA2 AM2 HH2.
change (PMSPA.pm_scr 1) with 14336 in HP2.
set (Wc := (oec, 16) :: (if e1 then [] else PMSPA.err_W PMA.AD)) in HP2.
assert (WcR : forall rr0 a, In rr0 Wc -> L5.in_rng rr0 a -> (oec <= a < oec + 16) \/ (0x66d380 <= a < 0x68f0f4)).
{ intros rr0 a Hin Hr. unfold Wc in Hin. destruct Hin as [<-|Hin]; [left; exact Hr|]. right. destruct e1; [destruct Hin|].
unfold PMSPA.err_W in Hin. cbn [pa_errcat_guard pa_atexit PMA.AD ADDR_A] in Hin. unfold L5.in_rng in Hr.
destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; clear - Hr; lia. }
pose proof (L5SAR.ek_callee L ar LBX (PM.parser_own s1) FF' [] (sp - 256) 14336 (sp - 256) 14336 Wc Wc M1 M2' HP2 ltac:(clear; lia) ltac:(clear; lia) (fun a _ X => X)) as EK12.
assert (EK12' : L5SAR.ek L ar LB1 FF' (sp - 256) 14336 Wc M1 M2').
{ destruct HP2 as (P & _). intros a (Ha & Hc & Ho). apply P. split; [exact Ha|]. split; [exact Hc| exact Ho]. }
assert (WAPP2 : PMKA.wapp Wc).
{ intros rr0 Hin. unfold Wc in Hin. unfold BIGSHADOW_LO, BIGSHADOW_HI. destruct Hin as [<-|Hin]; cbn [fst snd].
- pose proof FSAPP as (FA0 & FA1 & FA2). unfold BIGSHADOW_LO, BIGSHADOW_HI in FA1. destruct FA1 as [Y|Y]; clear - Y F1 F2 Eoec; lia.
- destruct e1; [destruct Hin|]. unfold PMSPA.err_W in Hin. cbn [pa_errcat_guard pa_atexit PMA.AD ADDR_A] in Hin. destruct Hin as [<-|[<-|[]]]; cbn [fst snd]; clear; lia. }
pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH1) as FRB1.
pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH1) as BRB1.
assert (OUTW : forall a n, fb + 32 <= a -> a + n <= fb + 1016 -> (a + n <= oec \/ oec + 16 <= a) -> forall i, a <= i < a + n -> L5.outside Wc i).
{ intros a n X1 X2 X3 i Hi rr0 Hin Hr. destruct (WcR rr0 i Hin Hr) as [Y|Y]; [clear - Hi Y X3; lia| clear - Hi Y X1 Eop O1; lia]. }
assert (OUTBW : forall q m, In (q, m) LB1 -> forall i, q <= i < q + m -> L5.outside Wc i).
{ intros q m Hq i Hi rr0 Hin Hr. destruct (WcR rr0 i Hin Hr) as [Y|Y].
- destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q m oec 16 HH1 Hq (AOF oec 16 ltac:(clear - Eoec; lia) ltac:(clear - Eoec; lia))) as [Z|Z]; clear - Hi Y Z; lia.
- pose proof (PMASK.blk_img L ar C HI LY HIok _ _ _ _ _ _ _ q m HH1 Hq) as Z. destruct Z as [Z|Z]; clear - Hi Y Z; lia. }
apply (KX fx2 R2 M2' model2' LK2' Aw2 RP2); [| exact EC2].
apply (PMALPK.alp_liftW L ar C HI HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 e1 cr1
M2' model2' LK2' Aw2 s1 sm1 true cr1 (PM.parser_own s1) 14336 Wc CTX0 G LM ltac:(clear; lia) HP2).
- intros rr0 a Hin Hr. destruct (WcR rr0 a Hin Hr) as [X|X].
+ split; [clear - X F1 F2 FSCEIL SLO Eoec; lia|]. pose proof (Z.div_le_mono 6885376 F 8 ltac:(lia) ltac:(clear - GFR; lia)) as D8. change (6885376 / 8) with 860672 in D8.
unfold SB. unfold FS_BYTES in GFS2. change (ff_bytes 1) with 128 in GFS2. destruct FSAPP as (_ & [Y|Y] & _); unfold BIGSHADOW_LO, BIGSHADOW_HI in Y; clear - X Y F1 F2 D8 GFS2 GFR Eoec; lia.
+ split; [clear - X GFCEIL SLO GFR; lia|]. pose proof (Z.div_le_mono 6885376 F 8 ltac:(lia) ltac:(clear - GFR; lia)) as D8. change (6885376 / 8) with 860672 in D8.
unfold SB. clear - X D8; lia.
- intros a Hc Ho rr0 Hin Hr. destruct (WcR rr0 a Hin Hr) as [X|X].
+ apply (Ho (PMSPA.o_ec PMA.AD fb, 16)); [unfold PMSPA.W_run, PMSPA.W_srcf, PMSPA.err_W; cbn [app]; do 6 right; left; reflexivity| unfold L5.in_rng; fold oec; cbn [fst snd]; clear - X; lia].
+ unfold PMSPA.W_run, PMSPA.W_srcf, PMSPA.err_W in Ho. cbn [app pa_errcat_guard pa_atexit PMA.AD ADDR_A] in Ho.
unfold Wc, PMSPA.err_W in Hin. cbn [pa_errcat_guard pa_atexit PMA.AD ADDR_A] in Hin.
destruct Hin as [<-|Hin]; [unfold L5.in_rng in Hr; cbn [fst snd] in Hr; clear - Hr X Eoec O1 Eop; lia|].
destruct e1; [destruct Hin|]. destruct Hin as [<-|[<-|[]]].
* apply (Ho _ (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl))))))))); exact Hr.
* apply (Ho _ (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl)))))))))); exact Hr.
- unfold PMSPA.run_pre. split; [| split; [| split; [| split; [| split; [| split]]]]].
+ apply (PMKA.parser_keepA RSEGS PMA.AD L ar LB1 FF' (sp - 256) 14336 Wc M1 M2' EK12' WAPP2 FRB1 BRB1 _ _ _ AOP); [| | | | | exact PA1].
* apply incl_appl, incl_refl.
* apply OUTW; clear - Eop Eoec; lia.
* unfold PMKA.blk_out. apply (OUTBW (PM.sr_qc (PM.p_src s1)) 16384). apply in_or_app; left. unfold PM.parser_own, PM.src_own. left; reflexivity.
* unfold PMKA.blk_out. apply (OUTBW (PM.p_b s1) (32 * 2 ^ PM.p_k s1)). apply in_or_app; left. unfold PM.parser_own, PM.vec_own. right; left; reflexivity.
* intros c0 n0 p0 E0. unfold PMKA.blk_out. apply (OUTBW p0 c0). apply in_or_app; left. unfold PM.parser_own, PM.vs_own. rewrite E0. right; right; left; reflexivity.
+ apply (PMKA.iss_keepA RSEGS PMA.AD L ar LB1 FF' (sp - 256) 14336 Wc M1 M2' EK12' WAPP2 FRB1 BRB1 ois str sm1 (AOF ois 272 ltac:(clear - Eois; lia) ltac:(clear - Eois; lia))); [| | | exact IA1].
* apply incl_appr. exact INCS.
* apply OUTW; clear - Eois Eoec; lia.
* intros c0 n0 p0 E0. unfold PMKA.blk_out. apply (OUTBW p0 c0). apply in_or_app; right. apply INCS. rewrite E0. left; reflexivity.
+ apply (PMKA.visitor_keepA RSEGS PMA.AD L ar LB1 FF' (sp - 256) 14336 Wc M1 M2' EK12' WAPP2 FRB1 _ (AOF ov 8 ltac:(clear - Eov; lia) ltac:(clear - Eov; lia))); [| exact VIS1].
apply OUTW; clear - Eov Eoec; lia.
+ apply (PMKA.u64_keepA RSEGS L ar LB1 FF' (sp - 256) 14336 Wc M1 M2' EK12' WAPP2 FRB1 (op + 384) _ (AOF (op + 384) 8 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))); [| exact VREF1].
apply OUTW; clear - Eop Eoec; lia.
+ apply (PMAPAR.base_keepW L ar C LY LB1 FF' (sp - 256) 14336 Wc M1 M2' EK12'); [| | | | exact BASE1].
* intros a Ha rr0 Hin Hr. destruct (WcR rr0 a Hin Hr) as [X|X]; [clear - Ha X Eoec O1 Eop; lia|].
unfold Wc in Hin. destruct Hin as [<-|Hin]; [unfold L5.in_rng in Hr; cbn [fst snd] in Hr; clear - Hr Ha Eoec Eop O1; lia|]. destruct e1; [destruct Hin|].
unfold PMSPA.err_W in Hin. cbn [pa_errcat_guard pa_atexit PMA.AD ADDR_A] in Hin. unfold L5.in_rng in Hr.
destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; clear - Hr Ha; lia.
* intros a Ha rr0 Hin Hr. unfold Wc in Hin. destruct Hin as [<-|Hin]; [unfold L5.in_rng in Hr; cbn [fst snd] in Hr; clear - Hr Ha Eoec Eop O1; lia|]. destruct e1; [destruct Hin|].
unfold PMSPA.err_W in Hin. cbn [pa_errcat_guard pa_atexit PMA.AD ADDR_A] in Hin. unfold L5.in_rng in Hr.
destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; clear - Hr Ha; lia.
* intros rr0 Hin Hr. unfold Wc in Hin. destruct Hin as [<-|Hin]; [unfold L5.in_rng in Hr; cbn [fst snd] in Hr; clear - Hr Eoec Eop O1; lia|]. destruct e1; [destruct Hin|].
unfold PMSPA.err_W in Hin. cbn [pa_errcat_guard pa_atexit PMA.AD ADDR_A] in Hin. unfold L5.in_rng in Hr.
destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; clear - Hr; lia.
* intros a Ha rr0 Hin Hr. unfold Wc in Hin. destruct Hin as [<-|Hin]; [unfold L5.in_rng in Hr; cbn [fst snd] in Hr; clear - Hr Ha Eoec Eop O1; lia|]. destruct e1; [destruct Hin|].
unfold PMSPA.err_W in Hin. cbn [pa_errcat_guard pa_atexit PMA.AD ADDR_A] in Hin. unfold L5.in_rng in Hr.
destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; clear - Hr Ha; lia.
+ exact ERR2.
+ exact TB1.
- unfold PMSPA.src_step, PM.unread. split; [reflexivity|]. split; [reflexivity|]. split; [clear; lia|]. split; [intros X; exact X| clear; lia].
- intros _; reflexivity.
- unfold PMSPA.credit_keep. clear; lia.
- exact MRT2.
- exact INCL2.
- exact INCA2.
- exact AM2.
- exact HH2.
Qed.
End WithHeap.
End PMALPK7.
