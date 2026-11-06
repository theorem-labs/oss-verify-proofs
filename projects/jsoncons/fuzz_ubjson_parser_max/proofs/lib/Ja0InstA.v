(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec HeapIface HeapIfaceA HeapIfaceANull IcptIfaceA LibIface LibIfaceAJ ArtRuns ArtBridge JatInv JatFsInv JatHandoffRi JatIfaceInst JatIfaceInstFree JatIfaceLayout
JatWrapSmallocI JatIcptInst Ja0DefsK Ja0Drv_defs Ja0DrvLib Ja0DrvRead Ja0MainPhaseA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import HeapIfaceAJx StrictOfJ JatIfaceInstAnn.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PmAImgGap JatIcptLawsGap.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Ja0InstA () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceAJx.HAJ."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.IcptIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0InstA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0MainPhaseA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatIfaceInst."], [["0BUDGET"; "1bool"; "1false"; "2eq"; "3Z"; "0EX"; "0IL"; "4SpuriousCfg"; "4sc_alloc"; "5ec_ann_pc"; "5ec_ann_scr"; "5ext_consts"; "6as0_icpt_layout"; "6icpt_layout"; "7ext_open_stmt"; "8dla_ok_stmt"]; ["8drv_consts_stmt"; "8ext_ok_stmt"; "8free_null_stmt"; "8gap_ok_stmt"; "8h4e_stmt"; "8icpt_ok_stmt"; "8inst_ok_stmt"; "9art_C"; "9art_L"; "0scfg"]]).
Local Ltac lia := L5FastLiaT.plia1.
Import ListNotations.
Open Scope Z_scope.
#[local] Existing Instance PropExec.fx0.
Theorem as0_h4e : ltac2:(TCodec.tc2 tcn__Ja0InstA "5'4&Dr1%211p241").
Proof. intros BUDGET MAPS0 RESV0 NOACC0 BASE rn gfs0 k0 K0 B0 A0 M V HT. exact (art_handoff_ri art_fsg art_fsinv MAPS0 RESV0 NOACC0 BASE BUDGET rn gfs0 k0 K0 B0 A0 M V HT). Qed.
Theorem as0_dla_ok : ltac2:(TCodec.tc2 tcn__Ja0InstA ">'7'='<r1%211&?r3&H&Gr2%544321p071p>;1pQD=1").
Proof.
intros scfg IL ILY ar HI sp0 HIok Hs. pose proof (aicl_memcpy IL ILY) as HM. constructor; try reflexivity; try exact HM; try exact Hs.
- cbn. lia.
- intros lo hi a Hin Ha. exact (art_L_client lo hi a Hin Ha).
- intros lo hi a Hin Ha. exact (art_L_w_not_ro lo hi a Hin Ha).
- exact art_L_ro_img.
Qed.
Section SE.
Local Abbreviation SEC_T_as0_drv_consts := (ltac2:(TCodec.tc2 tcn__Ja0InstA ";'='<r1%211&@&H&Gr2%43321p061p>:1")) (only parsing).
Variable IL : ltac:(sec_ty2 constr:(SEC_T_as0_drv_consts) 0%nat 0%nat).
Theorem as0_drv_consts : ltac:(sec_stmt2 constr:(SEC_T_as0_drv_consts) 1%nat 0%nat).
Proof.
intros ILY.
split; [exact ILY|]. split; [|split; [cbn; lia|split; [cbn; lia|split; [cbn; lia|split; [|split; [|split; [|split]]]]]]].
- intros c Hc. unfold RD_CELLS in Hc. cbn [In] in Hc. cbn.
repeat (destruct Hc as [<-|Hc]; [tauto|]). destruct Hc.
- intros c Hc. unfold Ja0DrvStdio.PR_CELLS in Hc. cbn [In] in Hc. cbn.
repeat (destruct Hc as [<-|Hc]; [tauto|]). destruct Hc.
- intros c Hc. unfold Ja0DrvStdio.EX_CELLS in Hc. cbn [In] in Hc. cbn.
repeat (destruct Hc as [<-|Hc]; [tauto|]). destruct Hc.
- intros c Hc. unfold Ja0DrvStdio.DG_CELLS in Hc. cbn [In] in Hc. cbn.
repeat (destruct Hc as [<-|Hc]; [tauto|]). destruct Hc.
- intros c Hc. unfold Ja0DrvStdio.DGS_CELLS in Hc. cbn [In] in Hc. cbn.
repeat (destruct Hc as [<-|Hc]; [tauto|]). destruct Hc.
- intros c Hc. cbn [In] in Hc. cbn.
repeat (destruct Hc as [<-|Hc]; [tauto|]). destruct Hc.
Qed.
End SE.
Theorem as0_inst_ok : ltac2:(TCodec.tc2 tcn__Ja0InstA "A'7'4'3'1&8r2%211(2%63521&Fr3&H&G%443218p061p2>1pQD@1").
Proof.
intros scfg BUDGET Halloc MAPS0 RESV0 NOACC0 BASE rn BS ROK Htp Hkey Htsd Hloff.
assert (SM : forall k, In k [0; 1; 2; 3; 4] -> astack_malloc_spec art_L (rn_ar rn) scfg (HIR BUDGET MAPS0 RESV0 NOACC0 BASE rn) k)
by exact (art_inst_smalloc MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg asegs_wx Htp).
split; [exact art_L_img_low|]. split.
- exact (art_inst_ok MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Halloc asegs_wx BS Htp Hkey Htsd Hloff
(art_inst_free MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Halloc asegs_wx BS Htp) SM).
- exact (art_inst_flag_in_fs MAPS0 RESV0 NOACC0 BASE BUDGET rn).
Qed.
Definition ext_open_stmt (scfg : SpuriousCfg) (BUDGET : Z) (EX : HAJ.ext_consts) : Prop :=
forall MAPS0 RESV0 NOACC0 BASE rn,
bridge_static ASEGS0 MAPS0 RESV0 NOACC0 (art_RES rn) (rn_HI rn) BUDGET JatInv.LENMAX JatInv.KMAX ->
art_run_ok rn -> rn_tp rn = 0x66ed80 -> rn_key rn = 0 -> rn_tsd rn = 0x690238 -> rn_loff rn = 0x10 ->
HAJ.cxa_atexit_spec art_L (rn_ar rn) scfg (HIR BUDGET MAPS0 RESV0 NOACC0 BASE rn) (HAJ.ec_cxa_pc EX) (HAJ.ec_cxa_scr EX) (HAJ.ec_atexit EX)
(HAJ.ec_f0 EX) (HAJ.ec_a0 EX) (HAJ.ec_f1 EX) (HAJ.ec_a1 EX) (HAJ.ec_atc EX) (HAJ.ec_nl EX).
Theorem as0_ext_ok : ltac2:(TCodec.tc2 tcn__Ja0InstA "M'7'4';'3&9r1%211+_\Y4%53721&:r2%211+RX0%:3<21&>r5r4r3%43321&Ar6&H%342167p051p0;1p0A1p<H1p2J1pQDL1").
Proof.
intros scfg BUDGET EX EPC ESCR OPEN MAPS0 RESV0 NOACC0 BASE rn BS ROK Htp Hkey Htsd Hloff.
pose proof (OPEN MAPS0 RESV0 NOACC0 BASE rn BS ROK Htp Hkey Htsd Hloff) as CXA.
apply HAJ.AEXT; [rewrite EPC, ESCR; exact (art_inst_annotate MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg asegs_wx Htp)|exact CXA| |].
- exact (art_inst_frame_ctr MAPS0 RESV0 NOACC0 BASE BUDGET rn Htp Hkey Htsd Hloff).
- exact (art_inst_free_null MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg asegs_wx Htp).
Qed.
Theorem as0_free_null : ltac2:(TCodec.tc2 tcn__Ja0InstA "9'7'4&Br2&Hr1%43321p261pQD81").
Proof.
intros scfg BUDGET MAPS0 RESV0 NOACC0 BASE rn _ _ Htp _ _ _.
exact (art_inst_free_null MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg asegs_wx Htp).
Qed.
Theorem as0_gap_ok : ltac2:(TCodec.tc2 tcn__Ja0InstA "5'4&Cr1%211p241").
Proof. intros BUDGET MAPS0 RESV0 NOACC0 BASE rn _ _ _ _ _ _. exact (art_law_img_gap MAPS0 RESV0 NOACC0 BASE BUDGET rn). Qed.
Theorem as0_icpt_ok : ltac2:(TCodec.tc2 tcn__Ja0InstA "?'7'='4'<r2%211&Er4&Hr3%443216p061p2:1p><1pQD>1").
Proof.
intros scfg IL BUDGET ILY MAPS0 RESV0 NOACC0 BASE rn _ _ Htp Hkey Htsd Hloff.
exact (art_icpt_ok scfg IL BUDGET asegs_wx ILY MAPS0 RESV0 NOACC0 BASE rn Htp Hkey Htsd Hloff).
Qed.
