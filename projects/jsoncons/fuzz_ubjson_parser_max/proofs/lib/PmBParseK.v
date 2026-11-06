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
PmModelFactsA PmStepAB0 PmStep PmParStep PmBSrcKit PmBParKit PmBUarK PmBUar PmParKit2 PmBReset1 PmBParseD.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmBParseK () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBParseD.PMBLPD."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBParseK.PMBLPK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBUarK.PMBUK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStepAB0.PMKB."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.L5CoreAB0.L5CA."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0Ac"; "0Aw"; "0Aw1"; "0Aw3"; "0BX"; "0BXa"; "1app"; "1bool"; "1cons"; "1length"; "1list"; "1nil"; "1option"; "1pair"; "1prod"; "1true"]; ["2and"; "2eq"; "2ex"; "2not"; "2or"; "3Z"; "0F"; "0FF"; "0HI"; "0K"; "0L"; "0LB"; "0LBX"; "0LK"; "0LK1"; "0LK2"]; ["0LK3"; "0LKc"; "4Model"; "5bvmap"; "0M"; "0M1"; "0M2"; "0M3"; "0Mc"; "0R"; "6mrestrict"; "7credit"; "8SB"; "8aclient"; "8ahid"; "8fframe"]; ["8model_rt"; "8ri_inv"; "8shadow_zero"; "8vml"; "8vml_of"; "9in_rng"; "9outside"; "9range"; ":aframe"; ":apctx"; ":lmem"; ":own"; ";lfacts"; ";tfacts"; "<binv"; "=AADDR_B"]; ["=ADDR_B"; ">p_b"; ">p_src"; ">p_stk"; ">parser_own"; ">pot_parser"; ">pst"; ">pstate"; ">pstate_at"; ">strm"; ">vstr"; "?HV"; "?W_run"; "?credit_keep"; "?ec_at"; "?ffroomA"]; ["?ffrsA"; "?frame_okA"; "?o_ec"; "?o_p"; "?o_v"; "?pm_scr"; "?run_pre"; "?scA"; "?src_step"; "@wapp"; "ATSet"; "Bmem_grows"; "Cahpres"; "Camodel_ok"; "Castk"; "Dloaded_segments"]; ["0SCFG_P"; "EIn"; "Eincl"; "Fadd"; "Fdiv"; "Fle"; "Flt"; "Fmul"; "Fof_nat"; "Fpow"; "Fsub"; "0V"; "0W"; "0Wc"; "0Wp"; "0a"]; ["0ar"; "0c"; "0cat"; "0cr"; "0cr1"; "0cr3"; "0crc"; "0e"; "0e1"; "0e3"; "0fb"; "0fl"; "0h"; "0m"; "0model"; "0model1"]; ["0model2"; "0model3"; "0modelc"; "0n"; "0pre"; "0q"; "0r"; "0rr"; "0s"; "0s1"; "0s3"; "0scr"; "0sm"; "0sm1"; "0sm3"; "0sp"]; ["GZ_to_bv"; "Gbv"; "0str"; "0top"; "0v"; "0x"; "0y"]]).
Local Ltac lia := first [ L5FastLia.plia | Lia.lia ].
Module PMBLPK.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Lemma iv_apart : ltac2:(TCodec.tc2 tcn__PmBParseK "Q7'E&S6zr3%3221r2%5241'@&S5r7r1%3221&S3r6%2251%>251%9251&C%:25=r5%8271%D2@1%?241%611p081pW0I1'D%C2=8r4%A2:1%F21E%5241p071p0K1p0N1pWLQ31pY>Q41pX8Q51pY<Q61").
Proof. intros x n y m.
intros Hn Hm H. destruct (Z_le_gt_dec (x + n) y) as [X|X]; [left; exact X|]. destruct (Z_le_gt_dec (y + m) x) as [Y|Y]; [right; exact Y|].
exfalso. apply (H (Z.max x y)); lia.
Qed.
Definition lfacts (MV : word -> option byte) (sp op ov oec F fl : Z) : Prop :=
L5.img_clear MV 65536 1269760 /\ L5.u64_at RSEGS MV 1296952 2147450880 /\ L5.u32_at RSEGS MV 1296960 1
/\ 140735332487456 <= sp <= 140737488355328 /\ sp mod 32 = 0 /\ L5.writable RSEGS MV (sp - 288) 288
/\ 6893568 <= op <= 140737488354944 /\ op mod 8 = 0 /\ (2147446784 + 17592186048512 <= op \/ op + 384 <= 2147446784)
/\ L5KA.zeros_at MV ((op / 8) + 2147450880) 3 /\ L5KA.zeros_at MV (((op + 32) / 8) + 2147450880) 44 /\ L5KA.zeros_at MV (((op + 20) / 8) + 2147450880) 1
/\ L5.writable RSEGS MV op 384 /\ ((sp - 288) + 288 <= op \/ op + 384 <= (sp - 288))
/\ 6893568 <= ov <= 140737488355320 /\ ov mod 8 = 0 /\ (2147446784 + 17592186048512 <= ov \/ ov + 8 <= 2147446784)
/\ L5KA.zeros_at MV ((ov / 8) + 2147450880) 1 /\ L5.writable RSEGS MV ov 8 /\ ((sp - 288) + 288 <= ov \/ ov + 8 <= (sp - 288))
/\ 6893568 <= oec <= 140737488355312 /\ oec mod 8 = 0 /\ (2147446784 + 17592186048512 <= oec \/ oec + 16 <= 2147446784)
/\ L5KA.zeros_at MV ((oec / 8) + 2147450880) 2 /\ L5.writable RSEGS MV oec 16 /\ ((sp - 288) + 288 <= oec \/ oec + 16 <= (sp - 288))
/\ L5.u64_at RSEGS MV ov 1238880 /\ L5KA.zeros_at MV 2147605740 16
/\ (op + 384 <= ov \/ ov + 8 <= op) /\ (oec + 16 <= ov \/ ov + 8 <= oec) /\ (op + 384 <= oec \/ oec + 16 <= op)
/\ 6893568 <= F <= 140737488355200 /\ F mod 32 = 0 /\ L5.defined MV F 128 /\ L5.writable RSEGS MV F 128
/\ (2147446784 + 17592186048512 <= F \/ F + 128 <= 2147446784) /\ L5.writable RSEGS MV ((F / 8) + 2147450880) 16
/\ L5.u64_at RSEGS MV (F + 120) fl /\ 4096 <= fl <= 140737488355327 /\ L5.writable RSEGS MV fl 1
/\ (2147446784 + 17592186048512 <= fl \/ fl + 1 <= 2147446784) /\ (F + 128 <= fl \/ fl + 1 <= F)
/\ ((sp - 288) + 288 <= F \/ F + 128 <= (sp - 288)) /\ ((sp - 288) + 288 <= fl \/ fl + 1 <= (sp - 288))
/\ (op + 384 <= F \/ F + 128 <= op) /\ (op + 384 <= fl \/ fl + 1 <= op)
/\ (((op / 8) + 2147450880) + 48 <= ((F / 8) + 2147450880) \/ ((F / 8) + 2147450880) + 16 <= ((op / 8) + 2147450880))
/\ (oec + 16 <= F \/ F + 128 <= oec) /\ (oec + 16 <= fl \/ fl + 1 <= oec)
/\ (((oec / 8) + 2147450880) + 2 <= ((F / 8) + 2147450880) \/ ((F / 8) + 2147450880) + 16 <= ((oec / 8) + 2147450880))
/\ (ov + 8 <= F \/ F + 128 <= ov) /\ (ov + 8 <= fl \/ fl + 1 <= ov)
/\ (((ov / 8) + 2147450880) + 1 <= ((F / 8) + 2147450880) \/ ((F / 8) + 2147450880) + 16 <= ((ov / 8) + 2147450880))
/\ (F + 128 <= 65536 \/ 65536 + 1204224 <= F)
/\ (((F / 8) + 2147450880) + 16 <= 2147605740 \/ 2147605740 + 16 <= ((F / 8) + 2147450880))
/\ PMBLPD.lspill MV sp F op ov oec
/\ 0 <= sp < 2 ^ 64 /\ 0 <= op < 2 ^ 64 /\ 0 <= ov < 2 ^ 64 /\ 0 <= oec < 2 ^ 64 /\ 0 <= F < 2 ^ 64 /\ 0 <= fl < 2 ^ 64.
Definition tfacts (MV : word -> option byte) (sp op ov oec F T : Z) : Prop :=
4096 <= T <= 140737488355264 /\ (T + 32 <= 65536 \/ 65536 + 6828032 <= T) /\ T mod 16 = 0 /\ L5.writable RSEGS MV T 32
/\ (2147446784 + 17592186048512 <= T \/ T + 32 <= 2147446784) /\ L5KA.zeros_at MV ((T / 8) + 2147450880) 4
/\ L5.u64_at RSEGS MV (op + 368) (T + 32)
/\ ((sp - 288) + 288 <= T \/ T + 32 <= (sp - 288)) /\ (op + 384 <= T \/ T + 32 <= op) /\ (oec + 16 <= T \/ T + 32 <= oec)
/\ (ov + 8 <= T \/ T + 32 <= ov) /\ (F + 128 <= T \/ T + 32 <= F)
/\ (((F / 8) + 2147450880) + 16 <= ((T / 8) + 2147450880) \/ ((T / 8) + 2147450880) + 4 <= ((F / 8) + 2147450880))
/\ 0 <= T < 2 ^ 64.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMB.ly_as0 L C LY.
Lemma lfacts_of : ltac2:(TCodec.tc2 tcn__PmBParseK "SF&RJ&Q3y5'TAyR0%211%5241'<y8%611%311p061'Q2':'>'E%2211%411&Q?%611&Q;'R6'R:'R9'7&QIvS0vJvS@vHrQ0rOrNrMrLrKrJrIrHrGrFrErDrCrBrAr@%FEEDCBA@?>=<;:987654321&QHr?r>r=r<%5BJIHGFEDCBA@?;74321&QJrQ1r;r:r9r8r7r6r5%9JQ4Q3Q28Q1Q0ONMLKJHFEDCB;7654321&R>&RO&RB&R0%221Nr4%655C281&QL&Q:&Q>%12BG%321I&RC%12:Q8&RD%12<Q:%>2=Q;%:76Q>421Q6Q5p0<1p0D1p0O1p0Q61pW4R71pY:R81pW:R41pWBR11pXLR31pXDR61p6R;1pQNR:1pX0RB1pR<RD1pX2RD1pR>RF1pR0R?1pWHRD1pQ>RE1pW@R=1pXJR?1pY6RA1pXBRC1pW6RJ1pWFRK1pX>RL1pY0RM1pW8RI1p4RM1pQLRL1pQ@RM1pQJS01pWNS61pR:S81pRDS>1pQDSE1").
Proof. intros K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 v c.
intros CTX G LM EC1.
destruct CTX as (HH & AM & K0 & ENT & FRM & FRS & FOK & SP32 & ARGS & RPRE & INCS & INV & EC0 & UNR & CRED & KONT).
destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 10) with 32768 in *.
pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
pose proof FOK as ((rs & Hfb) & Fal).
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _).
pose proof (WF _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 4) with 1024 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL, F1, F2.
destruct LM as (BI & RP1 & LS1 & STEP1 & EE1 & CK1).
pose proof G as G'. unfold PMBLPD.aframe in G'.
destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
change (ff_bytes 1) with 128 in *. change (128 / 8) with 16 in *.
pose proof BI as (HH1 & AM1 & MRT1 & INCA1 & INCL1 & ASTK1 & EK1 & DK1 & OWN1 & DSH1).
change (PMSPA.pm_scr 10) with 32768 in *.
set (FF' := (F, 1, sp - 288 + 32) :: FF) in *.
assert (FOK' : PMSPA.frame_okA FF' fb) by exact (PMBUAR.frame_okA_push FF fb F 1 (sp - 288 + 32) FOK).
destruct RP1 as (PA1 & IA1 & VIS1 & VREF1 & BASE1 & ERR1 & TB1).
pose proof (PMBPAR.op_vis L ar C HI LY HIok _ _ LK1 cr1 Aw1 M1 model1 fb _ s1 HH1 FOK' PA1) as ((O1 & O8 & ONSH) & Zop & Z32 & Z20 & OWR & OCE & OVIS & AOP & Eop).
pose proof (PMBPAR.ov_vis L ar C HI LY HIok _ _ LK1 cr1 Aw1 M1 model1 fb HH1 FOK' VIS1) as ((V1 & V8 & VNSH) & Zov & VWR & VCE & VVT & AOV & Eov).
pose proof (PMBPAR.oec_vis L ar C HI LY HIok _ _ LK1 cr1 Aw1 M1 model1 fb v c HH1 FOK' EC1) as ((E1 & E8 & ENSH) & Zoec & EWR & ECE & EV0 & AOE & Eoec).
pose proof (PMBSK.mach_vis L ar C HI LY HIok _ _ LK1 cr1 Aw1 M1 model1 HH1 BASE1) as (VM0 & VM1 & VM2).
pose proof (PMBSK.stk_vis L ar C HI LY HIok _ _ LK1 cr1 Aw1 M1 model1 sp 32768 288 HH1 ASTK1 ltac:(lia)) as (SL288 & SH288 & SWR).
pose proof (PMBSK.img_shz_vis L ar C HI LY IL ICok ILY _ _ LK1 cr1 Aw1 M1 model1 0x12e760 16 HH1 ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia)) as ZVT.
cbn in ZVT.
destruct (PMBUK.vis_facts L ar C HI LYa HIok M model LBX FF LK Aw sp 32768 (sp - 288) (sp - 104) sp (PMBLPD.ocell sp) (PMBLPD.own sp R) F fl 1 LK2 M2 model2 cr (PM.parser_own s) G
_ (PM.parser_own s1) M1 model1 LK1 cr1 Aw1 BI) as ((WS1 & _ & _ & _ & _) & OWNv & (FD1 & FW1 & FSW1 & FLC1 & FLW1) & (FLCc1 & FLV1 & VF1 & VS1 & VSH1)).
change (ff_bytes 1) with 128 in *. change (128 / 8) with 16 in *. replace (F + 128 - 8) with (F + 120) in FLC1 by (clear; lia).
set (op := PMSPA.o_p PMB.AD fb) in *. set (ov := PMSPA.o_v PMB.AD fb) in *. set (oec := PMSPA.o_ec PMB.AD fb) in *.
set (MV := mrestrict (ahid Aw1 model1) M1) in *.
pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ _ LK1 cr1 Aw1 M1 model1 HH1) as (_ & VISs & _).
assert (CLo : forall a, fb + 32 <= a < fb + 1016 -> aclient L ar LBX FF sp 32768 a).
{ intros a Ha. unfold aclient, aclient_g. do 3 right; left. exists (fb, 4, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd].
change (ff_bytes 4) with 1024. split; [clear - Ha; lia| intros Y; clear - Ha Y; lia]. }
assert (CLs : forall a, fb / 8 + SB <= a < fb / 8 + SB + 128 -> aclient L ar LBX FF sp 32768 a).
{ intros a Ha. unfold aclient, aclient_g. do 5 right; left. exists (fb, 4, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd].
change (ff_bytes 4) with 1024. unfold in_shadow_of, S. unfold SB in *.
assert (D1 : (fb + 1024 - 1) / 8 = fb / 8 + 127).
{ pose proof (Z.div_mod fb 1024 ltac:(lia)) as Dm. rewrite Fal, Z.add_0_r in Dm. rewrite Dm.
replace (1024 * (fb / 1024) + 1024 - 1) with (7 + (128 * (fb / 1024) + 127) * 8) by (clear; lia). rewrite Z.div_add by lia.
replace (1024 * (fb / 1024)) with ((128 * (fb / 1024)) * 8) by (clear; lia). rewrite Z.div_mul by lia. clear; lia. }
rewrite D1. clear - Ha. lia. }
assert (SHD : forall o k, o = fb + 8 * k -> o / 8 + SB = fb / 8 + SB + k).
{ intros o k ->. pose proof (Z.div_mod fb 1024 ltac:(lia)) as Dm. rewrite Fal, Z.add_0_r in Dm. rewrite Dm.
replace (1024 * (fb / 1024) + 8 * k) with ((128 * (fb / 1024) + k) * 8) by (clear; lia). rewrite Z.div_mul by lia.
replace (1024 * (fb / 1024)) with ((128 * (fb / 1024)) * 8) by (clear; lia). rewrite Z.div_mul by lia. clear; lia. }
assert (SHop : op / 8 + SB = fb / 8 + SB + 58) by (apply SHD; clear - Eop; lia).
assert (SHov : ov / 8 + SB = fb / 8 + SB + 54) by (apply SHD; clear - Eov; lia).
assert (SHoe : oec / 8 + SB = fb / 8 + SB + 124) by (apply SHD; clear - Eoec; lia).
assert (SF1 : S (F + 128 - 1) = F / 8 + SB + 15).
{ unfold S. destruct GF8 as (X1 & X2 & X3). rewrite X2. change (128 / 8) with 16. clear; lia. }
assert (NF : forall a, fb + 32 <= a < fb + 1016 -> ~ (F <= a < F + 128)).
{ intros a Ha X. apply (GNCF a); [left; exact X| exact (CLo a Ha)]. }
assert (NFS : forall a, fb / 8 + SB <= a < fb / 8 + SB + 128 -> ~ (F / 8 + SB <= a < F / 8 + SB + 16)).
{ intros a Ha X. apply (GNCF a); [right; unfold S at 1; rewrite SF1; clear - X; lia| exact (CLs a Ha)]. }
assert (NFL : forall a, fb + 32 <= a < fb + 1016 -> a <> fl).
{ intros a Ha X. subst a. apply GFLNC. apply L5SAR.aclient_cons. apply (L5SAR.aclient_00 L ar LBX FF sp 32768 fl). exact (CLo fl Ha). }
assert (ApF : op + 384 <= F \/ F + 128 <= op) by (apply iv_apart; [clear; lia| clear; lia| intros a Ha; apply NF; clear - Ha Eop; lia]).
assert (AvF : ov + 8 <= F \/ F + 128 <= ov) by (apply iv_apart; [clear; lia| clear; lia| intros a Ha; apply NF; clear - Ha Eov; lia]).
assert (DjF : oec + 16 <= F \/ F + 128 <= oec) by (apply iv_apart; [clear; lia| clear; lia| intros a Ha; apply NF; clear - Ha Eoec; lia]).
assert (ApFL : op + 384 <= fl \/ fl + 1 <= op).
{ destruct (Z_lt_le_dec fl op) as [X|X]; [right; clear - X; lia|]. destruct (Z_lt_le_dec fl (op + 384)) as [Y|Y]; [exfalso; apply (NFL fl); [clear - X Y Eop; lia| reflexivity]| left; exact Y]. }
assert (AvFL : ov + 8 <= fl \/ fl + 1 <= ov).
{ destruct (Z_lt_le_dec fl ov) as [X|X]; [right; clear - X; lia|]. destruct (Z_lt_le_dec fl (ov + 8)) as [Y|Y]; [exfalso; apply (NFL fl); [clear - X Y Eov; lia| reflexivity]| left; exact Y]. }
assert (DjFL : oec + 16 <= fl \/ fl + 1 <= oec).
{ destruct (Z_lt_le_dec fl oec) as [X|X]; [right; clear - X; lia|]. destruct (Z_lt_le_dec fl (oec + 16)) as [Y|Y]; [exfalso; apply (NFL fl); [clear - X Y Eoec; lia| reflexivity]| left; exact Y]. }
assert (ApS : ((op / 8) + 2147450880) + 48 <= ((F / 8) + 2147450880) \/ ((F / 8) + 2147450880) + 16 <= ((op / 8) + 2147450880)).
{ change 2147450880 with SB. apply iv_apart; [clear; lia| clear; lia| intros a Ha; apply NFS; clear - Ha SHop; lia]. }
assert (AvS : ((ov / 8) + 2147450880) + 1 <= ((F / 8) + 2147450880) \/ ((F / 8) + 2147450880) + 16 <= ((ov / 8) + 2147450880)).
{ change 2147450880 with SB. apply iv_apart; [clear; lia| clear; lia| intros a Ha; apply NFS; clear - Ha SHov; lia]. }
assert (AeS : ((oec / 8) + 2147450880) + 2 <= ((F / 8) + 2147450880) \/ ((F / 8) + 2147450880) + 16 <= ((oec / 8) + 2147450880)).
{ change 2147450880 with SB. apply iv_apart; [clear; lia| clear; lia| intros a Ha; apply NFS; clear - Ha SHoe; lia]. }
assert (SP32' : sp mod 32 = 0) by exact SP32.
assert (SVV : forall a v0, sp - 288 <= a -> a + 8 <= sp - 104 -> L5.u64_at RSEGS M1 a v0 -> L5.u64_at RSEGS MV a v0).
{ intros a v0 Ha1 Ha2 X. apply (proj2 (L5A.u64_at_vis _ M1 a v0 (VISs a 8 ltac:(clear - Ha1 SL288 SPT; lia) ltac:(clear - Ha2 SHI SPT; lia)) ltac:(clear - Ha1 SL288 SPT; lia) ltac:(clear - Ha2 SHI SPT; lia))). exact X. }
destruct LS1 as (L1 & L2 & L3 & L4 & L5' & L6 & L7 & L8 & L9 & L10 & L11 & L12 & L13 & L14 & L15 & L16 & L17 & L18).
unfold lfacts.
repeat (split; [first [assumption | (clear - SLO SHI SPT; lia) | (unfold SB in *; clear - GFR; lia) | (clear - OCE SL288; lia) | (clear - VCE SL288; lia) | (clear - ECE SL288; lia)
| (clear - Eop Eov; lia) | (clear - Eoec Eov; lia) | (clear - Eop Eoec; lia) | (clear - GFCEIL SL288; lia) | (clear - GFLR SL288; lia) | (clear - GFLR; lia)] |]).
split.
- unfold PMBLPD.lspill. repeat (split; [apply SVV; [clear; lia| clear; lia| assumption]|]). apply SVV; [clear; lia| clear; lia| assumption].
- clear - SLO SHI SPT O1 V1 E1 GFR GFLR. lia.
Qed.
Lemma alp_liftW : ltac2:(TCodec.tc2 tcn__PmBParseK "WM&RJ&Q3y5'TAyR0%211%5241'<y8%611%311p061'Q2':'>'E%2211%411&Q?%611&Q;'R6'R:'R9'7&QG%=11&QIvS0vJvS@vHrQ9rQ8rQ7rQ6rQ5rQ4rQ3rQ2rQ1rQ0rOrNrMrLrKrJrI%FEEDCBA@?>=<;:987654321&QHrHrGrFrE%5BJIHGFEDCBA@?;74321&QJrQ:rDrCrBrAr@r?r>%9JQ4Q3Q28Q1Q0ONMLKJHFEDCB;7654321'@&S5zr5%3221+nP0%5231%7231&RL&6r7%23QM1Q=(8%R12QOR0(=+1%24R3R3Q51&S3&S:+Y0%22QA1+Q0%5221%94R9R:71%<3;1QIr6%B9QOQN?261GQ8M&S1r2r8%33R721&QEr3%2215&C%A2R5@%Q3214&S6%126R8%Q7231%611&S4+8%22R51&Q<%L221%Q=21>+@%O231%<2A1%QB241%A11%QD2<1p0D1p0H1pW0S:1pX@S11&Q=rQ<rQ;+QPP0r1%57S3S243RN21&QF&R<&R0%221S1%421Q7r:%621Q5p031p091pW0SK1&RF&RO&QOr=r<%594=3RDS<R@S921&RH&R2%11RO%21RE%4421S0RE'A(?%23T0S31%33T1RJ2p021&R=&RG&R5&R;%12T2T1%321S@%52T41%523S5%72T61%94S?S431&Q@%12SJS@&S2%13TFSBSL%23TISMSC&RM%12SFSH&QA&R4%11SIrQD%S53U021%S14U2U2T?S0rQ?%RO21RN%S121RM%S54U5U641rQC%S93S821&QD%11T9%>8TK:3T7SOT6T;1rQHrQGrQFrQErQBrQArQ@rQ>%T;JU6U5U48765D=4321R7R6T:U3U2TETDTCT@T?T>T=T9p0:1p0J1p0M1p0O1p0Q21p0Q51p0Q@1p0QF1p0QL1p0R31p0RD1p0SC1p0T71p0T@1p0TK1p0U21pVLUJ1pXHV61p<V51pW<V31pWDV01pXNV21pXFV51p8V:1pR2V91pX4VA1pR@VC1pW:V;1pWBV81pXLV:1pXDV=1p6VB1pQNVA1pX0VI1pR<VK1pX2VK1pR>VM1pR0VF1pWHVK1pQ>VL1pW@VD1pXJVF1pY6VH1pXBVJ1pW6W11pWFW21pX>W31pY0W41pW8W01p4W41pQLW31pQ@W41pQJW71pWNW=1pR:W?1pRDWE1pQDWL1").
Proof. intros K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 M3 model3 LK3 Aw3 s3 sm3 e3 cr3 BXa scr Wc.
intros CTX G LM HS AH WAV WOUT RP3 STEP3 EE3 CK3 MRT3 INCL3 INCA3 AM3 HH3.
destruct CTX as (HH & AM & K0 & ENT & FRM & FRS & FOK & SP32 & ARGS & RPRE & INCS & INV & EC0 & UNR & CRED & KONT).
destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 10) with 32768 in *.
pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
destruct LM as (BI & RP1 & LS1 & STEP1 & EE1 & CK1).
split; [|split; [exact RP3| split; [| split; [| split; [| exact (PMBPAR.credit_keep_transA _ _ _ _ _ _ CK1 CK3)]]]]].
- apply (PMBUK.binv_callee L ar C HI HIok M model LBX FF LK Aw sp 32768 (sp - 288) (sp - 104) sp (PMBLPD.ocell sp) (PMBLPD.own sp R) F fl 1 LK2 M2 model2 cr (PM.parser_own s) G
_ _ (PM.parser_own s1) BXa (PM.parser_own s3) M1 model1 LK1 cr1 Aw1 M3 model3 LK3 cr3 Aw3 scr Wc BI AH HH3 AM3 MRT3 INCA3 INCL3);
[clear - HS; lia| clear - HS; lia| | exact WOUT| intros a X; exact X].
intros rr a Hin Hr. change (ff_bytes 1 / 8) with 16. unfold PMBLPD.ocell. destruct (WAV rr a Hin Hr) as (X1 & X2). split; [clear - X1; lia| exact X2].
- apply (PMBLPD.lspill_agree M1 M3 sp F _ _ _ ltac:(clear - SLO SPT; lia) ltac:(clear - SHI SPT; lia) LS1).
intros a Ha. destruct AH as (E & _). apply E. split; [clear - Ha SLO SHI SPT; lia|]. split.
+ apply (L5SAR.stack_client L ar (BXa ++ LBX) _ (sp - 288) scr a); clear - Ha SLO SHI SPT HS; lia.
+ intros rr Hin Hr. destruct (WAV rr a Hin Hr) as (X1 & _). apply X1. clear - Ha; lia.
- exact (PMBPAR.src_step_transA _ _ _ _ _ _ STEP1 STEP3).
- intros X. apply EE3, EE1, X.
Qed.
Lemma wapp_wrun : ltac2:(TCodec.tc2 tcn__PmBParseK "Q<':'>'E%2211%411&Q?%611&Q;'TAyR0%211'<y8%511%311p051&QC&QAvHr8r7r6r5r4r3r2%9887654321&RA%1293&RI&R<&R0%2218%411p061p091pWFQ21pVHE1pR:G1p4Q31pW8Q11pQLQ31pQ@Q41pQHQ71").
Proof. intros LB FF LK cr Aw M V fb.
intros HH ((rs & Hfb) & Fal).
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _).
pose proof (WF _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 4) with 1024 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL, F1, F2.
unfold PMSPA.W_run, PMSPA.W_srcf, PMSPA.err_W, PMSPA.o_src, PMSPA.o_is, PMSPA.o_tb, PMSPA.o_vec, PMSPA.o_ec, PMSPA.o_p.
cbn [app pa_off_p pa_off_is pa_off_ec pa_errcat_guard pa_atexit PMB.AD ADDR_B].
pose proof FSAPP as (FA0 & FA1 & FA2). unfold BIGSHADOW_LO, BIGSHADOW_HI in FA1.
repeat apply PMKB.wapp_cons; [..| apply PMKB.wapp_nil]; cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct FA1 as [FA1|FA1]; clear - FA0 FA1 FA2 F1 F2; lia.
Qed.
Lemma alp_callpre : ltac2:(TCodec.tc2 tcn__PmBParseK "T;&RJ&Q3y5'TAyR0%211%5241'<y8%611%311p061'Q2':'>'E%2211%411&Q?%611&Q;'R6'R:'R9'7&QIvS0vJvS@vHrOrNrMrLrKrJrIrHrGrFrErDrCrBrAr@r?%FEEDCBA@?>=<;:987654321&QHr>r=r<r;%5BJIHGFEDCBA@?;74321&QJrQ0r:r9r8r7r6r5r4%9JQ4Q3Q28Q1Q0ONMLKJHFEDCB;7654321'@&S5z%2215+9%4271%6231&RN&S:+Y0%22Q71&RE%11?%64QAK31&QB%7253&S4+8%2261%53Q141&R?(8%R82R6R7(=+1%24R:R:Q>1&S3+Q0%22B1%64R=R>41%9381QO%;3Q21Q;&R@%123G&RA%125QN%Q4231%Q5261%Q62C1%Q72J1p0Q21p0Q:1p0QE1p0QL1pWJRM1pW:RI1pWBRF1pXLRH1pXDRK1p6S01pQNRO1pX0S71pR<S91pX2S91pR>S;1pR0S41pWHS91pQ>S:1pW@S21pXJS41pY6S61pXBS81pW6S?1pWFS@1pX>SA1pY0SB1pW8S>1p4SB1pQLSA1pQ@SB1pQJSE1pWNSK1pR:SM1pRDT31pQDT:1").
Proof. intros K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 h.
intros CTX G LM Hh.
destruct CTX as (HH & AM & K0 & ENT & FRM & FRS & FOK & SP32 & ARGS & RPRE & INCS & INV & EC0 & UNR & CRED & KONT).
destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 10) with 32768 in *. change (32768 / 8) with 4096 in STKSH.
pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
destruct LM as (BI & RP1 & LS1 & STEP1 & EE1 & CK1).
pose proof BI as (HH1 & AM1 & MRT1 & INCA1 & INCL1 & ASTK1 & EK1 & DK1 & OWN1 & DSH1). change (PMSPA.pm_scr 10) with 32768 in *.
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH1) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDF1 & _).
pose proof (wapp_wrun _ _ _ _ _ _ _ fb HH FOK) as WAPPR.
assert (SCR : PMSPA.pm_scr h = 12288 + 2048 * h) by reflexivity.
assert (A32 : (sp - 288) mod 16 = 0).
{ replace (sp - 288) with (sp + (-18) * 16) by (clear; lia). rewrite Z_mod_plus_full.
apply Z.mod_divide in SP32; [|lia]. destruct SP32 as (q & Eq). rewrite Eq. replace (q * 32) with ((q * 2) * 16) by lia. apply Z.mod_mul. lia. }
split; [apply (L5SAR.astk_sub ar M1 M1 sp 32768 288 (PMSPA.pm_scr h) ASTK1 (fun _ X => X)); [clear; lia| rewrite SCR; clear - Hh; lia| rewrite SCR; clear - Hh; lia| exact A32]|].
split.
{ assert (M8a : (sp - 32768) mod 8 = 0) by (apply PMKB.mod16_8'; replace (sp - 32768) with (sp + (-2048) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact A16).
assert (M8b : (sp - 288 - PMSPA.pm_scr h) mod 8 = 0).
{ rewrite SCR. apply PMKB.mod16_8'. replace (sp - 288 - (12288 + 2048 * h)) with ((sp - 288) + (-(768 + 128 * h)) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A32. }
assert (DV : PMSPA.pm_scr h / 8 = 1536 + 256 * h) by (rewrite SCR; replace (12288 + 2048 * h) with ((1536 + 256 * h) * 8) by (clear; lia); apply Z.div_mul; lia).
rewrite DV. apply (PMKB.shadow_zero_sub M1 (sp - 32768) 4096); [exact M8a| exact M8b| rewrite SCR; clear - Hh; lia| rewrite SCR; clear - Hh; lia| clear - Hh; lia|].
apply (PMKB.stksh_keepA L ar LBX FF sp 32768 _ M M1 EK1 WAPPR (sp - 32768) 4096); [clear - SLO SPT; lia| clear - SLO; lia| clear - SHI SPT; lia| exact M8a| clear; lia| exact STKSH]. }
split; [apply (PMBUAR.ffroomA_push 10 h FF LK LK1 _ FRM INCL1 NDF1); clear - Hh; lia|].
split; [apply (PMBUAR.ffrsA_push FF sp (sp - 288) F 1 (sp - 288 + 32) FRS); clear; lia|].
exact (PMBUAR.frame_okA_push FF fb F 1 (sp - 288 + 32) FOK).
Qed.
Lemma binv_pieceB : ltac2:(TCodec.tc2 tcn__PmBParseK "U;&Q3y5'TAyR0%211%5241'<y8%611%311p061'Q2':'>'E%2211%411&Q?%611&Q;'R6&QG%:11!p0:1&QHvJvS@vHrIrHrGrFrErDrCrBrAr@r?r>r=r<r;%CBBA@?>=<;:987654321&QN&RE+:%211&S:+Y0%22?1&QKrJ%22B1+1r:r9r8r7r6r5%AFQ4Q3Q2Q1Q0ONMLJ>;8H7C654321&QA&6%13QBFQ3(8%QF2QDQE(=%14QGQGQ0>&S3%F2Q4E+Q0%3221%64QKQL51%9381Q<&QDr4%211%@8QC>4EDCB1&RM%12FD&Q@%12Q8G&RK%12Q<K'@&S5zr1%3221&S6&S9+2+R0%3221%5271%;271&Cr2%Q;11%311'A&T@r3%22S61%R011%R612%63S321p081p0=1pW0S11%QG1G'B&S1%Q?4S5S5@J%23S51RB%N2BQ8%Q@2CM%L2Q:1%Q2231%Q3251qWLS<1%:2S=1qX<S>1%<2S?1p0>1pW0SA1rQ0rOrNrMrLrK%RE2S9RDrQ1%RD2S;1%RLFS?S>S=987654S<RI31S:RBS5S4RNRAS1S0ROp0;1p0L1p0QG1p0QJ1p0QM1p0R01p0RB1p0S51pVNSJ1pX0T81pR<T:1p2T51pW>T31pR4T51pX6T=1pRBT?1p:T:1pVJT51pX2TA1pR>TC1pR0T<1pWHTA1pQ>TB1pXBT=1pY0TD1pW8T@1p4TD1pQLTC1pQ@TD1pQJTG1pWNTM1pR:TO1pRDU51").
Proof. intros R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 W BX Mc modelc LKc crc Ac M1 model1 Wp.
intros G (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10) HH1 AM1 RT1 MG FRM WPB.
pose proof G as G'. unfold PMBLPD.aframe in G'.
destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
change (PMSPA.pm_scr 10) with 32768 in *.
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ B1) as (WB & _).
unfold PMBUK.binv. split; [exact HH1|]. split; [exact AM1|]. split; [eapply L5LZ.model_rt_trans; [exact B3| exact RT1]|]. split; [exact B4|]. split; [exact B5|].
split; [eapply L5SAR.astk_grows; [exact B6| exact MG]|].
split.
{ eapply L5SAR.ek_trans; [exact B7|]. intros a (Ha & Hc & Ho). apply FRM; [exact Ha|]. intros X. destruct (WPB a X) as (q & m & Hq & Hqa).
apply (PMBRS1.own_not_aclient L ar C HI HIok BX LBX _ LKc crc Ac Mc _ q m a sp 32768 B1 Hq Hqa). apply L5SAR.aclient_cons. exact Hc. }
split; [eapply L5SAR.dk_trans; [exact B8| apply L5SAR.dk_grows; exact MG]|].
split.
{ apply (PMBLPD.own_agree sp R Mc M1 ltac:(clear - GSPC; lia) ltac:(clear - GSPC; lia) B9). intros a Ha. unfold PMBLPD.ocell in Ha.
apply FRM; [clear - Ha GSPC; lia|]. intros X. destruct (WPB a X) as (q & m & Hq & Hqa).
destruct (WB (q, m) (in_or_app _ _ _ (or_introl Hq))) as ((_ & _ & _ & _ & Q4 & _) & _). cbn [fst snd] in Q4. clear - Ha Hqa Q4 GSLO. lia. }
eapply L5.defined_grows; [exact MG| exact B10].
Qed.
Lemma tfacts_of : ltac2:(TCodec.tc2 tcn__PmBParseK "T@&RJ&Q3y5'TAyR0%211%5241'<y8%611%311p061'Q2':'>'E%2211%411&Q?%611&Q;'R6'R:'R9'7'R7%=11&QIvS0vJvS@vHrQ0rOrNrMrLrKrJrIrHrGrFrErDrCrBrAr@%FEEDCBA@?>=<;:987654321&QHr?r>r=r<%5BJIHGFEDCBA@?;74321&QJrQ1r;r:r9r8r7r6r5%9JQ4Q3Q28Q1Q0ONMLKJHFEDCB;7654321'A&R3%118&6(8r4(;%11Q@%43QA31%63QB;1%:3QB81'@&QM&Q:&Q>%12GL%321N&RC&R0%221Q>&RD%123Q@&RB%125QB&S3&R1%11Q1&S7+Q0&S8&9%12R8Q2%311%6251%:281%G7CR0@><QH1&R8&RO%241F4Q8%342QE5Q9%M221%N261p0Q01p0Q<1p0QG1p0QN1pY8RG1pX:RG1pW:RN1pWBRK1pXLRM1pXDS01p6S51pQNS41pX0S<1pR<S>1pX2S>1pR>S@1pR0S91pWHS>1pQ>S?1pW@S71pXJS91pY6S;1pXBS=1pW6SD1pWFSE1pX>SF1pY0SG1pW8SC1p4SG1pQLSF1pQ@SG1pQJSJ1pWNT01pR:T21pRDT81pQDT?1").
Proof. intros K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 pre top.
intros CTX G LM ES.
destruct CTX as (HH & AM & K0 & ENT & FRM & FRS & FOK & SP32 & ARGS & RPRE & INCS & INV & EC0 & UNR & CRED & KONT).
destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 10) with 32768 in *.
pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
pose proof FOK as ((rs & Hfb) & Fal).
destruct LM as (BI & RP1 & LS1 & STEP1 & EE1 & CK1).
pose proof G as G'. unfold PMBLPD.aframe in G'.
destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
change (ff_bytes 1) with 128 in *. change (128 / 8) with 16 in *.
pose proof BI as (HH1 & AM1 & MRT1 & INCA1 & INCL1 & ASTK1 & EK1 & DK1 & OWN1 & DSH1). change (PMSPA.pm_scr 10) with 32768 in *.
set (FF' := (F, 1, sp - 288 + 32) :: FF) in *.
assert (FOK' : PMSPA.frame_okA FF' fb) by exact (PMBUAR.frame_okA_push FF fb F 1 (sp - 288 + 32) FOK).
destruct RP1 as (PA1 & IA1 & VIS1 & VREF1 & BASE1 & ERR1 & TB1).
pose proof (PMBPAR.op_vis L ar C HI LY HIok _ _ LK1 cr1 Aw1 M1 model1 fb _ s1 HH1 FOK' PA1) as ((O1 & O8 & ONSH) & Zop & Z32 & Z20 & OWR & OCE & OVIS & AOP & Eop).
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH1) as (WB1 & WF1 & FSAPP1 & FSCEIL1 & _).
pose proof (WF1 _ (or_intror Hfb)) as (FB1 & FB2 & _). cbn [ff_addr ff_class fst snd] in FB1, FB2. change (ff_bytes 4) with 1024 in *.
pose proof (WF1 _ (or_introl eq_refl)) as (FF1 & FF2 & _). cbn [ff_addr ff_class fst snd] in FF1, FF2. change (ff_bytes 1) with 128 in *.
set (op := PMSPA.o_p PMB.AD fb) in *. set (ov := PMSPA.o_v PMB.AD fb) in *. set (oec := PMSPA.o_ec PMB.AD fb) in *.
assert (Eov : ov = fb + 432) by reflexivity. assert (Eoec : oec = fb + 992) by reflexivity.
destruct s1 as [mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1]. cbn [PM.p_stk PM.p_b PM.p_k] in *. subst stk1.
pose proof PA1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PVEC & _). cbn [PM.p_b PM.p_k PM.p_stk] in PVEC.
destruct PVEC as (VC0 & VC8 & VC16 & Hk & Hlen & Hal & DB & CB & AN & EL).
rewrite length_app in Hlen, VC8, CB, AN. cbn [length] in Hlen, VC8, CB, AN. rewrite Nat2Z.inj_add in Hlen, VC8, CB, AN. cbn [Z.of_nat Pos.of_succ_nat] in Hlen, VC8, CB, AN.
assert (VIN : In (vb1, 32 * 2 ^ vk1) (PM.parser_own (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [top])) ++ LBX)).
{ apply in_or_app. left. unfold PM.parser_own, PM.src_own, PM.vec_own. cbn. right. left. reflexivity. }
destruct (WB1 _ VIN) as ((B0 & BI0 & B16 & _ & B4 & BAPP) & _ & _ & _ & _ & BFA & _). cbn [fst snd] in B0, BI0, B16, B4, BAPP, BFA.
rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in BI0. unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in BAPP.
pose proof (PM.pow2_pos vk1 ltac:(lia)) as P2K.
set (T := vb1 + 32 * Z.of_nat (length pre)) in *.
assert (TB : vb1 <= T /\ T + 32 <= vb1 + 32 * 2 ^ vk1) by (unfold T; clear - Hlen; lia).
assert (TAL : T mod 16 = 0) by (unfold T; replace (vb1 + 32 * Z.of_nat (length pre)) with (vb1 + (Z.of_nat (length pre) * 2) * 16) by (clear; lia); rewrite Z.mod_add by lia; exact Hal).
pose proof (BFA (F, 1, sp - 288 + 32) (in_or_app FF' LK1 _ (or_introl (or_introl eq_refl)))) as Z1. cbn [ff_addr ff_class fst snd] in Z1. change (ff_bytes 1) with 128 in Z1.
pose proof (BFA (fb, 4, rs) (in_or_app FF' LK1 (fb, 4, rs) (or_introl (or_intror Hfb)))) as Z2. cbn [ff_addr ff_class fst snd] in Z2. change (ff_bytes 4) with 1024 in Z2.
all: pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ _ LK1 cr1 Aw1 M1 model1 HH1) as VP; cbv zeta in VP; destruct VP as (_ & _ & _ & _ & VB & _).
all: assert (TV : L5A.avis (ahid Aw1 model1) T 32) by (apply (VB vb1 (32 * 2 ^ vk1) T 32 VIN); clear - TB; lia).
all: assert (PT : PM.pstate_at RSEGS M1 T top) by (specialize (EL (length pre) ltac:(rewrite length_app; cbn; lia)); rewrite PMPK2.nth_app_at in EL; exact EL).
all: split; [| split; [| exact PT]].
all: try (destruct PT as (PT0 & PT8 & PT16 & PT24); split; [apply (proj2 (L5A.u32_at_vis _ M1 T _ ltac:(eapply L5A.avis_sub; [exact TV| lia| lia]) ltac:(lia) ltac:(lia))); exact PT0|];
split; [apply (proj2 (L5A.u64_at_vis _ M1 (T + 8) _ ltac:(eapply L5A.avis_sub; [exact TV| lia| lia]) ltac:(lia) ltac:(lia))); exact PT8|];
split; [apply (proj2 (L5A.u8_at_vis _ M1 (T + 16) _ ltac:(eapply L5A.avis_sub; [exact TV| lia| lia]) ltac:(lia) ltac:(lia))); exact PT16|];
apply (proj2 (L5A.u64_at_vis _ M1 (T + 24) _ ltac:(eapply L5A.avis_sub; [exact TV| lia| lia]) ltac:(lia) ltac:(lia))); exact PT24).
all: unfold tfacts.
all: split; [clear - B0 TB B4 SLO SHI SPT; lia|].
all: split; [clear - BI0 TB; lia|].
all: split; [exact TAL|].
all: split; [apply (proj2 (L5A.writable_vis _ M1 T 32 TV ltac:(lia) ltac:(lia))); apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M1 vb1 (32 * 2 ^ vk1)); [exact DB| lia| lia]| lia| lia]|].
all: split; [destruct BAPP as (_ & [X|X] & _); [right| left]; clear - X TB; lia|].
all: split; [change 2147450880 with SB; replace 4 with (32 / 8) by reflexivity;
apply (PMKB.blk_shadow_vis L ar C HI LYa HIok _ _ LK1 cr1 Aw1 M1 model1 vb1 (32 * 2 ^ vk1) T 32 HH1 VIN); [lia| lia| apply PMKB.mod16_8'; exact TAL| lia| reflexivity|];
intros a Ha; apply CB; clear - Ha TB Hlen; unfold T in *; lia|].
all: split; [apply (proj2 (L5A.u64_at_vis _ M1 (op + 368) _ ltac:(apply OVIS; lia) ltac:(lia) ltac:(lia))); replace (op + 368) with (op + 360 + 8) by (clear; lia);
replace (T + 32) with (vb1 + 32 * (Z.of_nat (length pre) + Z.of_nat 1)) by (unfold T; cbn; clear; lia); exact VC8|].
all: split; [clear - B4 TB SLO; lia|].
all: split; [clear - Z2 TB Eop; Lia.lia|]. all: split; [clear - Z2 TB Eoec; Lia.lia|]. all: split; [clear - Z2 TB Eov; Lia.lia|].
all: split; [clear - Z1 TB; Lia.lia|].
all: split; [|clear - B0 TB B4 SLO SHI SPT; lia].
all: assert (FS8 : F / 8 * 8 = F) by exact (proj1 GF8).
all: assert (TS8 : T / 8 * 8 = T) by (pose proof (Z.div_mod T 8 ltac:(lia)) as X; rewrite (PMKB.mod16_8' T TAL) in X; clear - X; lia).
all: clear - Z1 TB FS8 TS8; Lia.lia.
Qed.
End WithHeap.
End PMBLPK.
