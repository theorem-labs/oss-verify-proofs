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
PmModelFactsA PmStepA PmStep PmParStep PmParKit PmASrcKit PmAParKit PmAReset1 PmAUarK PmAUar PmARvK PmARvF PmARdValP7.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmARvS () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmARvK.PMARVK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayout."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmParKit.PMPK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0Ac"; "1bool"; "1list"; "1option"; "1prod"; "1true"; "2and"; "2eq"; "2not"; "2or"; "3Z"; "0E"; "0HI"; "0L"; "0LKc"; "4Model"]; ["5bvmap"; "0M1"; "0M1v"; "0Mc"; "0R1"; "0Rc"; "6mrestrict"; "7msteps"; "8credit"; "9ahid"; "9fframe"; ";u8_at"; ":SCFG"; "<mid"; "<op"; "<rvc"]; ["<rve"; "<rvst"; "<vF"; "<vK"; "<vcat"; "<vs0"; "<vsm0"; "=pa_errcat_obj"; ">ADDR_A"; "?inv"; "?pst"; "?strm"; "@set_more"; "Acfg"; "Aprog_value"; "BFPState"]; ["Bmkst"; "Bseg_rom"; "Csrealizes"; "Dmem_grows"; "Eloaded_segments"; "0SCFG_P"; "Fadd"; "Fdiv"; "Fle"; "Flt"; "Fpow"; "0Wp"; "0X"; "0a"; "0ar"; "0c"]; ["0crc"; "0e"; "0fx"; "0fx1"; "0m"; "0model1"; "0modelc"; "0pc"; "0pc1"; "0s"; "0sm"; "GZ_to_bv"; "Gbv"; "0v"]]).
Local Ltac lia := L5FastLia.plia.
Module PMARVS.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Section WithHeap.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMA.ly_as0 L C LY.
Lemma rv_step : ltac2:(TCodec.tc2 tcn__PmARvS "V:'Q0'OvQEv=vQNv<r1%6554321'Q?&@y5'R<yR0%211%5241':'3y8%711%311p071'?'2&J%211&H'4%12<<%611'Q:'Q;'1!p0B1&Q1rErBr@r?r>r=r<r;r:r9r8r7%=?Q<Q;Q:<;:987654321'G&QD&Q@rDrC&R;%12Q:B&F&I%12ADrA%4221&QA%11<%<5;:831r6r5%<2QE1r4%A5E4216%D3C61&QC%>2O<%@21Q3%3218'6&QHz%221R6&QI&QJ+2+R0%3221%52R<1%:271&8r2%Q811%311'7r3%Q52R>1%Q?11%Q42QHQIrF%Q73214%73R<41p091p0>1pSLRC1%QE1RM'9&QF&Q2rK%211+Q0%5221%Q121F+_H%8251%Q12I1%Q6241&QG+8%22:1+QoooPP0%?221%Q;21Q0%A22Q6%Q:2Q21%Q?231&N%11C%F21:%QB21Q7+9%I241%QB2Q:1%QG241%M291%N2C1p0Q01pSLSE1&KrJ%>11%Q321G%44RHRL1R:%QB3SKRLQO+1%QD3SMRN1%Q9231&MrL%221S7rOrHrG&Q<%12SBS;%SD?TCTBTA5S@R1T@43QI1S3S2SBRL%RO24R2%S121QO%R13T51SB'QB&L%11TJ&Q=%16S=SJS4SIRLR5&Q3rQ1%211%84SA641p0:1p0>1pT<T@1pQ4TB1rI%;6SGIR1Q21FrN%;11%A4SJ?31p061p0M1p0Q11p0Q61p0Q<1p0R?1p0S:1p0S?1p0T51pT:U61pSHTE1pQ6U31pTBU91pQ:U;1pT8UB1pT0U<1pTLU=1pT4TN1pTFU01pTDU21p2U41pT2U81pNU:1pT>U>1pQ8U@1pT@UF1pQ<UH1pT6UO1pSJV11pHV91").
Proof. intros E X fx Rc pc Mc modelc LKc crc Ac s sm e v c fx1 R1 pc1 M1v Wp m.
intros ST MS MG FZ WP MO Hm MID1 KC.
pose proof (PMARVK.c_AR L ar HI E X) as AR.
pose proof X as [_ XG XHH XK0 XRra XRA XRsp XRgp XRtp XASTK XSTKSH XFRM XFRS XFOK XSP32 XINCS XUNR XCRED XINV XKONT].
destruct ST as (BI & MID & RPRE & STEP & EE & CK & EC).
destruct E as [R r sp fb cat s0 str sm0 e0 LBX FF LK Aw cr model M K F fl LK2 M2 model2].
unfold PMARVK.rvar, PMARVK.op, PMARVK.oec, PMARVK.ov, PMARVK.mid, PMARVK.WR, PMARVK.SCR, PMARVK.kont in *.
cbn [PMARVK.vR PMARVK.vr PMARVK.vsp PMARVK.vfb PMARVK.vcat PMARVK.vs0 PMARVK.vstr PMARVK.vsm0 PMARVK.ve0 PMARVK.vLBX PMARVK.vFF PMARVK.vLK
PMARVK.vAw PMARVK.vcr PMARVK.vmodel PMARVK.vM PMARVK.vK PMARVK.vF PMARVK.vfl PMARVK.vLK2 PMARVK.vM2 PMARVK.vmodel2] in *.
set (op := PMSPA.o_p PMA.AD fb) in *. set (ov := PMSPA.o_v PMA.AD fb) in *. set (oec := PMSPA.o_ec PMA.AD fb) in *. set (ois := PMSPA.o_is PMA.AD fb) in *.
destruct AR as ((ARsp1 & ARsp2) & (ARop1 & ARop2 & ARop3 & ARop4) & (ARq1 & ARq2 & ARq3 & ARq4 & ARq5)
& (ARF1 & ARF2 & ARF3 & ARF4 & ARF5 & ARF6 & ARF7 & ARF8 & ARF9 & ARF10 & ARF11 & ARF12 & ARF13 & ARF14 & ARF15 & ARF16)
& (ARv1 & ARv2 & ARv3 & ARv4 & ARv5 & ARv6 & ARv7 & ARv8 & ARv9 & ARv10)).
pose proof XG as G'. destruct G' as [GHk GSPT GSLO GSHI GSPC GOCR GOWNAG GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
change (ff_bytes 3) with 512 in *. change (512 / 8) with 64 in *.
pose proof BI as (HHc & AMc & MRTc & INCAc & INCLc & ASTKc & EKc & DKc & OWNc & DEFc).
pose proof XFOK as ((rs & Hfb) & Fal).
assert (Eop : op = fb + 464) by reflexivity.
unfold PMSPA.cfg.
apply (L5SAR.apiece L ar C HI LYa HIok _ _ LKc crc Ac Mc modelc fx fx1 Rc pc R1 pc1 M1v Wp K HHc AMc MS MG FZ).
{ intros a Ha Wa. destruct (WP a Wa) as [Xa|[Xa|Xa]].
- split; [apply (L5SAR.fframe_client L ar _ ((F, 3, sp - 128 + 32) :: FF) 0 0 F 3 (sp - 128 + 32)); [left; reflexivity| change (ff_bytes 3) with 512; split; [clear - Xa; lia| clear - Xa; lia]]|].
clear - Xa ARF1; lia.
- split; [apply (L5SAR.fframe_shadow_client L ar _ ((F, 3, sp - 128 + 32) :: FF) 0 0 F 3 (sp - 128 + 32)); [left; reflexivity|];
change (ff_bytes 3) with 512; unfold in_shadow_of, S; rewrite (proj1 (proj2 GF8)); unfold SB; clear - Xa; lia|].
clear - Xa ARF1; lia.
- split; [apply (L5SAR.fframe_client L ar _ ((F, 3, sp - 128 + 32) :: FF) 0 0 fb 4 rs); [right; exact Hfb| change (ff_bytes 4) with 1024; split; [clear - Xa Eop; lia| clear - Xa Eop; lia]]|].
clear - Xa ARop1; lia. }
intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
apply KC; [| rewrite HID1; exact VIS1].
assert (EOWN : PM.parser_own (PMPK.set_more s m) = PM.parser_own s) by (destruct s; reflexivity).
assert (EKf : L5SAR.ek L ar (PM.parser_own s ++ LBX) FF 0 0 [(op + 8, 1)] Mc M1).
{ apply (PMAUAR.wfr_ek L ar C HI LY HIok LBX FF LK Aw sp 28672 (sp - 128) (sp - 104) sp (PMARVK.ocell sp) (PMARVK.own sp R) F fl 3 LK2 M2 model2 cr (PM.parser_own s0)
(PM.parser_own s ++ LBX) LKc crc Ac Mc M1 _ [(op + 8, 1)] (fun a => op + 8 <= a < op + 9) XG HHc).
- intros a Xa O. apply (O (op + 8, 1)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - Xa; lia].
- intros a Ha Nw. apply FR1; [exact Ha|]. intros Wa. apply Nw. unfold PMAUAR.Wfr. change (ff_bytes 3) with 512. change (512 / 8) with 64.
destruct (WP a Wa) as [Xa|[Xa|Xa]]; [left; left; left; clear - Xa; lia| left; left; right; unfold SB; clear - Xa; lia| right; exact Xa]. }
pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH1) as BRB1.
pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ XHH) as FRB.
pose proof RPRE as (PA & IA & VIS & VREF & BASE & ERR & TBOK).
pose proof (PMARVK.frame_okA' (PMARVK.RVE R r sp fb cat s0 str sm0 e0 LBX FF LK Aw cr model M K F fl LK2 M2 model2) XFOK) as FOK'.
cbn [PMARVK.FF' PMARVK.vF PMARVK.vsp PMARVK.vFF PMARVK.vfb] in FOK'.
pose proof (PMAPAR.op_vis L ar C HI LY HIok _ _ LKc crc Ac Mc modelc fb _ s HHc FOK' PA) as ((O1 & O8 & ONSH) & _ & _ & _ & _ & _ & OVIS & AOP & _).
assert (AOF : forall a n, fb + 32 <= a -> a + n <= fb + 1016 -> PMSPA.aobjA FF a n).
{ intros a n Xa1 Xa2. exists (fb, 4, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 4) with 1024. clear - Xa1 Xa2; lia. }
assert (AOP0 : PMSPA.aobjA FF op 384) by (apply AOF; clear - Eop; lia).
assert (Eois : ois = fb + 96) by reflexivity. assert (Eov : ov = fb + 432) by reflexivity. assert (Eoec : oec = fb + 992) by reflexivity.
assert (MO0f : L5.u8_at RSEGS M1 (op + 8) m).
{ apply (proj1 (L5A.u8_at_vis (ahid Ac modelc) M1 (op + 8) m (OVIS (op + 8) 1 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - O1; lia) ltac:(clear - O1; lia))).
rewrite VIS1. exact MO. }
assert (OUT8 : forall a n, (a + n <= op + 8 \/ op + 9 <= a) -> forall i, a <= i < a + n -> L5.outside [(op + 8, 1)] i).
{ intros a n X3 i Hi rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - Hi Hr X3. lia. }
assert (OUTB8 : forall q n, In (q, n) (PM.parser_own s ++ LBX) -> forall i, q <= i < q + n -> L5.outside [(op + 8, 1)] i).
{ intros q n Hq i Hi rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr.
destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q n op 384 HHc Hq (PMAUAR.aobjA_push FF op 384 _ AOP0)) as [Z|Z]; clear - Hi Hr Z; lia. }
assert (WAPP8 : PMKA.wapp [(op + 8, 1)]).
{ apply PMKA.wapp_cons; [| apply PMKA.wapp_nil]. cbn [fst snd]. unfold BIGSHADOW_LO, BIGSHADOW_HI. destruct ONSH as [Yn|Yn]; [right| left]; clear - Yn; lia. }
assert (Ivb : In (PM.p_b s, 32 * 2 ^ PM.p_k s) (PM.parser_own s ++ LBX)) by (apply in_or_app; left; unfold PM.parser_own, PM.vec_own; right; left; reflexivity).
assert (Iqc : In (PM.sr_qc (PM.p_src s), PM.CHUNK) (PM.parser_own s ++ LBX)) by (apply in_or_app; left; unfold PM.parser_own, PM.src_own; left; reflexivity).
unfold PMARVK.rvst. cbn [PMARVK.vR PMARVK.vr PMARVK.vsp PMARVK.vfb PMARVK.vcat PMARVK.vs0 PMARVK.vstr PMARVK.vsm0 PMARVK.ve0 PMARVK.vLBX PMARVK.vFF PMARVK.vLK
PMARVK.vAw PMARVK.vcr PMARVK.vmodel PMARVK.vM PMARVK.vK PMARVK.vF PMARVK.vfl PMARVK.vLK2 PMARVK.vM2 PMARVK.vmodel2].
unfold PMARVK.WR, PMARVK.SCR, PMARVK.oec. rewrite EOWN. fold oec.
split.
{ apply (PMAUK.binv_pieceW L ar HI M model LBX FF LK Aw sp 28672 (sp - 128) (sp - 104) sp (PMARVK.ocell sp) (PMARVK.own sp R) F fl 3 LK2 M2 model2 cr
(PM.parser_own s0) XG (PMSPA.W_run PMA.AD fb) (PM.parser_own s) Mc modelc LKc crc Ac M1 model1 Wp BI HH1 AM1 MRT1 MGM1 FR1).
intros a Wa. unfold PMARVK.ocell. change (ff_bytes 3) with 512. change (512 / 8) with 64.
destruct (WP a Wa) as [Xa|[Xa|Xa]].
- split; [clear - Xa ARF1 ARF7; lia| right; left; clear - Xa; lia].
- split; [clear - Xa ARF1 ARsp1; lia| right; right; left; unfold SB; clear - Xa; lia].
- split; [clear - Xa ARop1 ARop4; lia| right; right; right].
intros O. apply (O (PMSPA.o_p PMA.AD fb + 8, 8)); [left; reflexivity| unfold L5.in_rng; fold op; cbn [fst snd]; clear - Xa; lia]. }
split; [exact MID1|].
split.
{ unfold PMSPA.run_pre. fold op ois ov.
split; [|split; [|split; [|split; [|split; [|split]]]]].
- destruct (BRB1 _ Iqc) as (Xq1 & Xq2). destruct (BRB1 _ Ivb) as (Xb1 & Xb2). cbn [fst snd] in Xq1, Xq2, Xb1, Xb2.
apply (PMAPAR.parser_more_updA Mc M1 op ois s m PA).
+ clear - O1; lia.
+ clear - O1; lia.
+ apply (PMKA.agA_obj L ar _ FF 0 0 _ Mc M1 EKf WAPP8 FRB op 8 (AOF op 8 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))). apply OUT8. clear; lia.
+ apply (PMKA.agA_obj L ar _ FF 0 0 _ Mc M1 EKf WAPP8 FRB (op + 9) 375 (AOF (op + 9) 375 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))). apply OUT8. clear; lia.
+ exact (PMKA.agsh_obj L ar _ FF 0 0 _ Mc M1 EKf WAPP8 FRB op 384 AOP0).
+ pose proof PA as (_ & PD & _). apply (L5.defined_grows Mc M1 _ _ MGM1 PD).
+ exact MO0f.
+ exact Hm.
+ exact Xq1.
+ clear - Xq2; lia.
+ apply (PMKA.agA_blk L ar _ FF 0 0 _ Mc M1 EKf WAPP8 BRB1 _ _ Iqc). apply OUTB8. exact Iqc.
+ exact Xb1.
+ clear - Xb2; lia.
+ apply (PMKA.agA_blk L ar _ FF 0 0 _ Mc M1 EKf WAPP8 BRB1 _ _ Ivb). apply OUTB8. exact Ivb.
+ intros c0 n0 p0 E0. assert (Ip : In (p0, c0) (PM.parser_own s ++ LBX)) by (apply in_or_app; left; unfold PM.parser_own, PM.vs_own; rewrite E0; right; right; left; reflexivity).
apply (PMKA.agA_blk L ar _ FF 0 0 _ Mc M1 EKf WAPP8 BRB1 _ _ Ip). apply OUTB8. exact Ip.
- apply (PMKA.iss_keepA RSEGS PMA.AD L ar _ FF 0 0 _ Mc M1 EKf WAPP8 FRB BRB1 ois str sm (AOF ois 272 ltac:(clear - Eois; lia) ltac:(clear - Eois; lia))); [| | | exact IA].
+ apply incl_appr. exact XINCS.
+ apply OUT8. clear - Eop Eois; lia.
+ intros c0 n0 p0 E0. unfold PMKA.blk_out. apply (OUTB8 p0 c0). apply in_or_app; right. apply XINCS. rewrite E0. left; reflexivity.
- apply (PMKA.visitor_keepA RSEGS PMA.AD L ar _ FF 0 0 _ Mc M1 EKf WAPP8 FRB _ (AOF ov 8 ltac:(clear - Eov; lia) ltac:(clear - Eov; lia))); [| exact VIS].
apply OUT8. clear - Eop Eov; lia.
- apply (PMKA.u64_keepA RSEGS L ar _ FF 0 0 _ Mc M1 EKf WAPP8 FRB (op + 384) _ (AOF (op + 384) 8 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))); [| exact VREF].
apply OUT8. clear; lia.
- apply (PMASK.base_keep L ar C LY _ FF 0 0 _ Mc M1 EKf); [| exact BASE]. intros a Ha rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - Ha Hr O1; lia.
- apply (PMKA.err_okA_keep RSEGS PMA.AD PMA.AAD L ar _ FF 0 0 _ Mc M1 EKf e PMA.addrs_wf_A); [| exact ERR].
intros a D. pose proof (PMASK.dep_img a D) as DI. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [clear - DI; lia|].
split; [exact (PMA.ly_static L C LY a D)|]. intros rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - DI Hr O1; lia.
- unfold PMPK.set_more. cbn [PM.p_tb PM.p_tg]. exact TBOK. }
split; [unfold PMPK.set_more; cbn [PM.p_src]; exact STEP|].
split; [exact EE|].
split; [unfold PMSPA.credit_keep in *; unfold PMPK.set_more, PM.pot_parser in *; cbn [PM.p_k PM.p_tb PM.p_tg] in *; exact CK|].
apply (PMKA.ec_keepA RSEGS L ar _ FF 0 0 _ Mc M1 EKf WAPP8 FRB _ v c (AOF oec 16 ltac:(clear - Eoec; lia) ltac:(clear - Eoec; lia))); [| exact EC].
apply OUT8. clear - Eop Eoec; lia.
Qed.
Lemma rv_j0 : ltac2:(TCodec.tc2 tcn__PmARvS "RD'Q0'OvQEv=vQNv<r1%6554321'Q?&@y5'R<yR0%211%5241'3y8%611%311p061'?'2&J%211&H'4':%2211%711'Q:'Q;'1&Q1r<r9r8r7r6r5r4r3r2z&Q4%11;%=?Q:Q9Q8<;:987654Q731&Q9%118&Q>&Q5r>%211&Q6%113%643@1?'QB&QD&L%11QH&Q=r=+ehX@r;r:%5684O321&Q3r?%211%=4<:41p0?1p0G1p0J1pT4Q91pTFQ;1pTDQ=1p2Q?1pT2QD1pNQF1pT>QJ1pQ8QL1pQ<R21pT6R91pSJR;1pHRC1").
Proof. intros E X fx Rc Mc modelc LKc crc Ac s sm e.
intros ST INVs PRG.
PMARVK.rvfacts L ar C HI LY HIok E X ST.
pose proof (PMARVK.rvmore_of L ar C HI LY HIok E X _ _ _ _ _ _ _ _ _ _ _ ST) as MO.
pose proof INVs as (IM & _). rewrite IM in MO.
cfeed P (PMARVP7.arvJ0_conc fx Rc (mrestrict (ahid Ac modelc) Mc) (fun j => match j with 2%nat => PMARVK.vsp E | 36%nat => PMARVK.op E | 37%nat => PMARVK.ov E
| 38%nat => PMARVK.oec E | 47%nat => PMARVK.vF E | 48%nat => PMARVK.vfl E | _ => 0 end)) ltac:(PMARVK.rvsc).
destruct P as (fx1 & R1 & M1v & MG1 & _ & FZ1 & MS1 & KS1 & E1 & E10 & E11 & _).
apply (PMARVF.rv_fin L ar C HI LY HIok E X fx Rc 0xae110 Mc modelc LKc crc Ac s sm e 0 (PMARVK.vcat E) 1 fx1 R1 M1v ST MS1 MG1).
- intros a Ha N1 N2 N3. apply FZ1; [exact Ha| intros Y; apply N1; clear - Y; lia].
- apply (L5C.u8_at_agree RSEGS (mrestrict (ahid Ac modelc) Mc) M1v); [| clear - AO1; lia| clear - AO1; lia| exact MO].
intros i Hi. apply FZ1; [clear - Hi AO1; lia| clear - Hi AF9; lia].
- right; reflexivity.
- exact E1.
- exact E10.
- exact E11.
- apply (PMARVK.mid_keep E Rc R1); [pose proof ST as (_ & MD & _); exact MD| PMARVK.kks KS1].
- right. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact INVs| exact PRG].
Qed.
Lemma rv_je : ltac2:(TCodec.tc2 tcn__PmARvS "R@'Q0'OvQEv=vQNv<r1%6554321'Q?&@y5'R<yR0%211%5241'3y8%611%311p061'?'2&J%211&H'4':%2211%711'Q:'Q;&Q1r<r9r8r7r6r5r4r3r2(5&Q7&Q8%211%>?Q:Q9Q8=<;:987654Q71'6&QH+1%2219+R0%42;1%6231'QB&QD&L%11QF&Q=r;+ehX@r:%467M321L&Q3r>%211%<4;941p0>1p0F1pTLQ:1pTFQ71pTDQ91p2Q;1pT2Q@1pNQB1pT>QF1pQ8QH1pQ<QN1pT6R51pSJR71pHR?1").
Proof. intros E X fx Rc Mc modelc LKc crc Ac s sm v.
intros ST Hv.
PMARVK.rvfacts L ar C HI LY HIok E X ST.
cfeed P (PMARVP7.arvJe_conc fx Rc (mrestrict (ahid Ac modelc) Mc) (fun j => match j with 2%nat => PMARVK.vsp E | 36%nat => PMARVK.op E | 37%nat => PMARVK.ov E
| 38%nat => PMARVK.oec E | 47%nat => PMARVK.vF E | 48%nat => PMARVK.vfl E | 50%nat => v | _ => 0 end)) ltac:(first [PMARVK.rvsc | clear - Hv; lia]).
destruct P as (fx1 & R1 & M1v & MG1 & _ & FZ1 & MS1 & KS1 & E1 & E10 & E11 & _ & MO0 & _).
apply (PMARVF.rv_fin L ar C HI LY HIok E X fx Rc 0xae110 Mc modelc LKc crc Ac s sm true v (pa_errcat_obj PMA.AD) 0 fx1 R1 M1v ST MS1 MG1).
- intros a Ha N1 N2 N3. apply FZ1; [exact Ha| intros Y; apply N1; clear - Y; lia| intros Y; apply N3; clear - Y; lia].
- exact MO0.
- left; reflexivity.
- exact E1.
- exact E10.
- exact E11.
- apply (PMARVK.mid_keep E Rc R1); [pose proof ST as (_ & MD & _); exact MD| PMARVK.kks KS1].
- left. split; [exact Hv|]. split; [reflexivity|]. split; reflexivity.
Qed.
End WithHeap.
End SCFG_1.
End PMARVS.
