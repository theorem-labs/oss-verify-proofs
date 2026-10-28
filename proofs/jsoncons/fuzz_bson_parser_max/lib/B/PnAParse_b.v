(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality Permutation Zwf.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound AsanPlanSoundSums SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5CoreKit L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5CoreSpecsA_b L5StepAR_b L5CoreBR_b L5ADetailHR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmParSpecs PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PnSpecsAa_b PnSpecsAX_b PnSpecsAXC_b
     PmModelFactsA_b PnStepA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PgSrc PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnLayout PnModel PnModelFacts PnStatics PnStaticsA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b PnRunAa_b PnASrcKit_b PmAUarK_b PmAUar_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnBrObj. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnBrObjA_b PnAParKit_b PnAReset1_b PnOwnerOkA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmCertKitG PmTxtKit2. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcKitA_b PnBrKitA_b PnAParseP_b PnAParseP2_b Ba0_code_ad390_ad394_b PnAParseK_b PnAParseA_b PnAParseB_b PnAParseC_b PnAParseD_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.


Module PNAPA.
Import L5A. Import L5CA. Import L5SAR. Import PNBKA. Import PNAPAK. Import PNAPAA. Import PNAPAB. Import PNAPAC. Import PNAPAD.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma pa_loop K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 :
  PNRAa.begin_document_spec L ar HI -> PNRAa.read_value_spec L ar HI -> PNRAa.read_e_name_spec L ar HI -> PNRAa.end_document_spec L ar HI -> PNRAa.end_array_spec L ar HI ->
  PNRAa.src_read_spec L ar HI -> PNRAa.make_ec_spec L ar HI -> PNSAXC.vec_clear_spec RSEGS PMA.AD L ar HI 0xab740 ->
  pa_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  pa_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  forall n, forall (fx1 : FPState) R1 (M1 : mem) model1 LK1 Aw1 s1 sm1 ax1 cr1,
    pa_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
    lregs R R1 sp fb F -> getr R1 (reg 17) = Z_to_bv 64 (fb + 464 + 8) -> spill M1 sp F (fb + 464) (fb + 432) (fb + 1024) -> ec_some M1 fb -> PNRA.binv s1 ->
    (PNM.b_more s1 = 1 -> PNRA.bb_room s1 sm1) ->
    (PNM.b_more s1 = 1 -> 0 <= PNRA.bmu s1 sm1 <= n) ->
    srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xae0cc M1 model1) K.
Proof.
  intros BD RV REN ED EA SR MKE ASH CTX G n. pattern n. apply (well_founded_ind (Zwf_well_founded 0)). clear n.
  intros n IHn fx1 R1 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 LM ER X17 SPL ECS INV1 BBR MU.
  pose proof (PNAPAA.mfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 CTX G LM) as (MOv & _ & _ & _ & _ & _ & _ & MO01 & _ & Q36 & Q34 & Q37).
  destruct MO01 as [MO0|MO1].
  - (* [comment removed for export] *)
    rewrite MO0 in MOv.
    pose proof (PNAPAK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 CTX G LM) as (PF & _).
    pose proof (PNAPAA.spill_vis L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 CTX G LM SPL) as SPv.
    set (MV1 := mrestrict (ahid Aw1 model1) M1) in *.
    pfx PF. spx SPv. pose proof ER as ER'. lrx ER'.
    pose proof (PNAPAP.apaHX_conc fx1 R1 MV1 (vmx R sp fb F fl 0 0 0 0 0 0 0 0)) as P.
    pfeed P.
    destruct P as (fx2 & R2 & M2v & MG2 & _ & FRZ2 & MS2 & KS2 & _).
    apply (PNAPAA.pa_piece_reg L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 fx1 fx2 R1 R2 0xae0cc 0xae510 M2v CTX G LM MS2 MG2 FRZ2).
    intros model2' LM2 HID2.
    apply (PNAPAA.pa_exit L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model2' LK1 Aw1 s1 sm1 ax1 cr1 fx2 R2 CTX G LM2); [lrk ER KS2| exact SPL| exact ECS].
  - (* [comment removed for export] *)
    pose proof (MU MO1) as MU1.
    assert (IH : PNAPAA.pa_IH L ar HI K R M model LBX FF LK Aw cr sp fb s str sm ax F (PNRA.bmu s1 sm1)).
    { unfold PNAPAA.pa_IH. intros fx2 R2 M2' model2' LK2' Aw2 s2 sm2 ax2 cr2 LM2 ER2 X172 SPL2 ECS2 INV2 BBR2 MU2.
      apply (IHn (PNRA.bmu s1 sm1 - 1) ltac:(unfold Zwf; clear - MU1; lia) fx2 R2 M2' model2' LK2' Aw2 s2 sm2 ax2 cr2 LM2 ER2 X172 SPL2 ECS2 INV2 BBR2).
      intros X. pose proof (MU2 X) as Y. clear - Y. lia. }
    pose proof INV1 as (_ & SH1).
    destruct (stack_top (PNM.b_stk s1) SH1) as (l & c & ES & OKc & _).
    pose proof OKc as (OKm & _).
    assert (CASES : PNM.bs_mode c = 0 \/ PNM.bs_mode c = 1 \/ PNM.bs_mode c = 2 \/ PNM.bs_mode c = 3 \/ PNM.bs_mode c = 4) by (clear - OKm; lia).
    destruct CASES as [Hm|[Hm|[Hm|[Hm|Hm]]]].
    + exact (PNAPAB.pa_mode0 L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 fx1 R1 l c BD CTX G IH LM ER X17 SPL ECS INV1 (BBR MO1) MO1 ES Hm).
    + exact (PNAPAB.pa_mode1 L ar C IL HI LY HIok ICok ILY K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 fx1 R1 l c ASH CTX G IH LM ER X17 SPL ECS INV1 MO1 ES Hm).
    + exact (PNAPAC.pa_doc L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 fx1 R1 l c SR MKE ED REN CTX G IH LM ER X17 SPL ECS INV1 (BBR MO1) MO1 ES Hm).
    + exact (PNAPAD.pa_arr L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 fx1 R1 l c SR MKE EA REN RV CTX G IH LM ER X17 SPL ECS INV1 (BBR MO1) MO1 ES Hm).
    + exact (PNAPAB.pa_mode4 L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 fx1 R1 l c RV CTX G IH LM ER X17 SPL ECS INV1 (BBR MO1) MO1 ES Hm).
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem parse_ok :
  PNRAa.begin_document_spec L ar HI -> PNRAa.read_value_spec L ar HI -> PNRAa.read_e_name_spec L ar HI -> PNRAa.end_document_spec L ar HI -> PNRAa.end_array_spec L ar HI ->
  PNRAa.src_read_spec L ar HI -> PNRAa.make_ec_spec L ar HI -> PNSAXC.vec_clear_spec RSEGS PMA.AD L ar HI 0xab740 -> PNRAa.parse_spec L ar HI.
Proof.
  intros BD RV REN ED EA SR MKE ASH. unfold PNRAa.parse_spec, PNRA.parse_spec.
  set (w := 0). assert (Hw : w = 0 \/ w = 1) by (left; reflexivity).
  intros fx R M model K LBX FF LK Aw cr sp r fb cat e s str sm ax HH AM K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC HE UNR BB0 CRED KONT.
  assert (CTX : pa_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w).
  { exact (conj Hw (conj HH (conj AM (conj K0 (conj ENT (conj FRM (conj FRS (conj FOK (conj SP32 (conj ARGS (conj RPRE (conj INCS (conj INV (conj EC (conj HE (conj UNR (conj CRED KONT))))))))))))))))). }
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 10) with 32768 in *. change (32768 / 8) with 4096 in STKSH.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof RAok as (Hr1 & Hr2).
  destruct ARGS as (A10 & A11 & A12).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11. rewrite L5K.rl12 in A12.
  pose proof RPRE as (PA & IA & VIS & VREF & OACC & BASE & ERR & GROW).
  pose proof FOK as ((rs & Hfb) & Fal).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _ & _ & _ & _ & _ & STOP & _).
  pose proof (WF _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 5) with 2048 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL, F1, F2.
  change (PNRA.o_p PMA.AD fb) with (fb + 464) in *. change (PNRA.o_ec PMA.AD fb) with (fb + 1024) in *.
  change (PNRA.o_v PMA.AD fb) with (fb + 432) in *. change (PNRA.o_is PMA.AD fb) with (fb + 96) in *.
  pose proof (PNAPAR.op_visB L ar C HI LY HIok _ FF LK cr Aw M model fb _ s HH FOK PA OACC) as ((O1 & O8 & ONSH) & Zop & OWR & OCE & OVIS & AOP).
  pose proof (PMASK.iss_vis L ar C HI LY HIok _ FF LK cr Aw M model fb str sm sp 32768 HH) as ISV.
  pose proof (PMASK.mach_vis L ar C HI LY HIok _ FF LK cr Aw M model HH BASE) as (VM0 & VM1 & VM2).
  pose proof (PMASK.stk_vis L ar C HI LY HIok _ FF LK cr Aw M model sp 32768 256 HH ASTK ltac:(lia)) as (SL160 & SH160 & SWR).
  set (op := fb + 464) in *. set (ov := fb + 432) in *. set (oec := fb + 1024) in *. set (ois := fb + 96) in *.
  set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK cr Aw M model HH) as (_ & VISs & _).
  LeanFeed.pfeed P (PNAPAP.apaA_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => op | 34%nat => ov | 36%nat => oec | _ => 0 end)) ltac:(first [assumption | unfold PNAPAP.aligned; assumption | clear - SL160 SHI SPT; lia | clear - O1; lia | unfold oec, ov, op in *; clear - O1; lia]).
  destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & T11 & T12 & T18 & T21 & T22 & T23 & T24 & T26
                 & SPEv & C104 & C96 & C88 & C80 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8 & C160).
  unfold PMSP.cfg. change (PNL.pn_parse PMA.AN) with 0xade6c.
  apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK cr Aw M model fx fx1 R 0xade6c R1 0x5dda0 M1v (fun a => sp - 256 <= a < sp - 256 + 256) K HH AM MS1 MG1).
  { intros a Ha N. apply FRZ1; [exact Ha| exact N]. }
  { intros a Ha Wa. split; [|intros X; clear - X Wa SL160 FSAPP FSCEIL; lia]. unfold aclientw, aclient_g. right; left. split; [clear - Wa SL160 SHI SPT; lia| intros X; clear - X; lia]. }
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1. change (mrestrict H M1 = M1v) in VIS1.
  set (LB := PNM.bparser_own s ++ LBX) in *.
  assert (INCX : incl LBX LB) by (unfold LB; apply incl_appr; apply incl_refl).
  assert (NCS0 : forall a, sp - 256 <= a < sp -> ~ aclient L ar LB FF sp 32768 a).
  { intros a Xa Hc. destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK cr Aw M _ sp 32768 a HH SPT Hc) as [Y|Y].
    - clear - Xa Y; lia.
    - clear - Xa Y SL160; lia. }
  assert (EK01f : L5SAR.ek L ar LB FF sp 32768 [] M M1).
  { apply (L5SAR.ek_piece L ar LB FF sp 32768 [] M M1 (fun a => sp - 256 <= a < sp - 256 + 256) FR1). intros a Ha Hc _ X. apply (NCS0 a); [clear - X; lia| exact Hc]. }
  assert (DK01f : L5SAR.dk L ar LB FF sp 32768 M M1) by (apply L5SAR.dk_grows; exact MGM1).
  pose proof (PMKA.ek_sublb L ar LB LBX FF sp 32768 [] M M1 INCX EK01f) as EK01.
  pose proof (PMKA.dk_sublb L ar LB LBX FF sp 32768 M M1 INCX DK01f) as DK01.
  (* [comment removed for export] *)
  assert (SV1 : forall a v, sp - 256 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v).
  { intros a v Ha1 Ha2 X. apply (proj1 (L5A.u64_at_vis H M1 a v (VISs a 8 ltac:(clear - Ha1 SL160 SPT; lia) ltac:(clear - Ha2 SHI SPT; lia)) ltac:(clear - Ha1 SL160 SPT; lia) ltac:(clear - Ha2 SHI SPT; lia))).
    rewrite VIS1. exact X. }
  assert (OWN1 : own sp R M1).
  { unfold own. repeat split; (apply SV1; [clear; lia| clear; lia| assumption]). }
  assert (SPE1 : L5.u64_at RSEGS M1 (sp - 160) oec) by (apply SV1; [clear; lia| clear; lia| exact SPEv]).
  clear C104 C96 C88 C80 C72 C64 C56 C48 C40 C32 C24 C16 C8 SV1.
  (* [comment removed for export] *)
  assert (FRk0 : ff_room 1 FF LK) by (apply (PMAUAR.ff_room_ofB PNRA.FCB 10 FF LK 1 FRM); [clear; lia| right; left; reflexivity]).
  change 0x5dda0 with (PMA.SM_PC 1).
  apply (PMAUAR.uar_sm L ar C HI LY HIok 1 LBX (PNM.bparser_own s) FF LK cr Aw sp 32768 (sp - 256) (sp - 104) sp (ocell sp) (own sp R)
           fx1 R1 M M1 model model1 K 0xadee4 ltac:(right; left; reflexivity) HH HH1 AM1 K0 ASTK MGM1 EK01 DK01).
  { rewrite L5K.rl2. exact T2. }
  { rewrite L5K.rl4. rewrite (KS1 4%nat) by inl. rewrite <- L5K.rl4. exact Rtp. }
  { rewrite L5K.rl1. exact T1. }
  { reflexivity. }
  { clear; lia. }
  { replace (sp - 256) with (sp + (-16) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  { clear; lia. } { clear; lia. } { clear; lia. } { clear; lia. }
  { intros a Ha. exact Ha. }
  { intros Ma Mb OW AG. apply (own_agree sp R Ma Mb ltac:(clear - SL160 SPT; lia) ltac:(clear - SHI SPT; lia) OW AG). }
  { exact FRk0. }
  { intros f Hf. specialize (FRS f Hf). clear - FRS; lia. }
  intros R2 M2 model2 F fl LK2 G G10 RP2 AM2 MRT2 ASTK2 EK02 DK02 EK12f DK12f AGF FW FSHW FSHZ FLC FLW FDEF VF VSH VFL APART.
  change (ff_bytes 1) with 128 in *. change (128 / 8) with 16 in *. change (128 - 8) with 120 in *.
  pose proof G as G'. destruct G' as [_ _ _ _ _ _ _ GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 1) with 128 in *.
  pose proof (L5SAR.ek_trans L ar LB FF sp 32768 [] M M1 M2 EK01f EK12f) as EK02f.
  pose proof (L5SAR.dk_trans L ar LB FF sp 32768 M M1 M2 DK01f DK12f) as DK02f.
  pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB.
  pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB.
  assert (HH2 : ri_inv HI LB ((F, 1, sp - 256 + 32) :: FF) LK2 cr Aw M2 (vml_of model2)) by exact GHH2.
  set (FF' := (F, 1, sp - 256 + 32) :: FF) in *.
  assert (FOK' : PNRA.frame_okB FF' fb). { split; [exists rs; right; exact Hfb| exact Fal]. }
  set (H2 := ahid Aw model2) in *. set (MV2 := mrestrict H2 M2) in *.
  pose proof (PMASK.stk_vis L ar C HI LY HIok _ _ LK2 cr Aw M2 model2 sp 32768 256 HH2 ASTK2 ltac:(lia)) as (_ & _ & SWR2).
  (* [comment removed for export] *)
  assert (R2c : forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R2 (reg j) = getr R1 (reg j)).
  { intros j Hj. apply (L5SAR.cs_of_preserved R1 R2 j RP2 Hj). }
  assert (B2R : getr R2 (reg 2) = Z_to_bv 64 (sp - 256)) by (rewrite (R2c 2%nat) by inl; exact T2).
  assert (B8R : getr R2 (reg 8) = Z_to_bv 64 sp) by (rewrite (R2c 8%nat) by inl; exact T8).
  assert (B9R : getr R2 (reg 9) = Z_to_bv 64 (sp - 256)) by (rewrite (R2c 9%nat) by inl; exact T9).
  assert (B22R : getr R2 (reg 22) = Z_to_bv 64 ov) by (rewrite (R2c 22%nat) by inl; exact T22).
  assert (B24R : getr R2 (reg 24) = Z_to_bv 64 op) by (rewrite (R2c 24%nat) by inl; exact T24).
  assert (B18R : getr R2 (reg 18) = Z_to_bv 64 2147450880) by (rewrite (R2c 18%nat) by inl; exact T18).
  assert (B10R : getr R2 (reg 10) = Z_to_bv 64 F) by (rewrite <- L5K.rl10; exact G10).
  assert (FLCv : L5.u64_at RSEGS MV2 (F + 120) fl) by (replace (F + 120) with (F + 128 - 8) by (clear; lia); exact FLC).
  assert (Q0 : 0 <= sp < 2 ^ 64 /\ 0 <= op < 2 ^ 64 /\ 0 <= ov < 2 ^ 64 /\ 0 <= F < 2 ^ 64 /\ 0 <= fl < 2 ^ 64)
    by (clear - SL160 SHI SPT O1 GFR GFLR; unfold ov, op in *; lia).
  destruct Q0 as (Q0a & Q0b & Q0d & Q0f & Q0g).
  assert (Q1 : 140735332487424 <= sp <= 140737488355328) by (clear - SL160 SHI SPT; lia).
  assert (Qop : 6905856 <= op <= 140737488354912) by (clear - O1; lia).
  assert (Q3 : 6905856 <= F <= 140737488355200) by (clear - GFR; lia).
  assert (Q4 : (sp - 256) + 256 <= F \/ F + 128 <= (sp - 256)) by (clear - GFCEIL SL160; lia).
  assert (Q5 : (sp - 256) + 256 <= fl \/ fl + 1 <= (sp - 256)) by (clear - GFLR SL160; lia).
  assert (Q7 : 4096 <= fl <= 140737488355327) by (clear - GFLR; lia).
  LeanFeed.pfeed P (PNAPAP.apaB0_conc fx1 R2 MV2 (fun j => match j with 2%nat => sp | 33%nat => op | 34%nat => ov | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNAPAP.aligned; assumption]).
  destruct P as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & Y10 & _ & _ & _ & _ & Y15 & Y16 & Y18 & Y23
                 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SH0 & _).
  set (W3 := fun a => (F <= a < F + 24) \/ (F / 8 + 2147450880 <= a < F / 8 + 2147450880 + 16)).
  apply (L5SAR.apiece L ar C HI LYa HIok LB FF' LK2 cr Aw M2 model2 fx1 fx3 R2 0xadee4 R3 0xadf94 M3v W3 K HH2 AM2 MS3 MG3).
  { intros a Ha Hn. apply FRZ3; [exact Ha| intros X; apply Hn; left; clear - X; lia| intros X; apply Hn; right; clear - X; lia]. }
  { intros a Ha Wa. split.
    - destruct Wa as [X|X].
      + apply (L5SAR.fframe_client L ar LB FF' 0 0 F 1 (sp - 256 + 32)); [left; reflexivity| change (ff_bytes 1) with 128; clear - X; lia].
      + apply (L5SAR.fframe_shadow_client L ar LB FF' 0 0 F 1 (sp - 256 + 32)); [left; reflexivity|]. change (ff_bytes 1) with 128.
        unfold in_shadow_of, S. rewrite (proj1 (proj2 GF8)). unfold SB. clear - X; lia.
    - destruct Wa as [X|X]; clear - X GFR SL160 SPT FSAPP FSCEIL; lia. }
  intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3. change (mrestrict H2 M3 = M3v) in VIS3.
  assert (EK23f : L5SAR.ek L ar LB FF sp 32768 [] M2 M3).
  { apply (L5SAR.ek_piece L ar LB FF sp 32768 [] M2 M3 W3 FR3). intros a Ha Hc _ X. destruct X as [X|X].
    - destruct (APART a 1 sp 32768 ltac:(intros i Hi; replace (a + i) with a by (clear - Hi; lia); exact Hc) ltac:(clear; lia)) as (Y & _). clear - X Y; lia.
    - destruct (APART a 1 sp 32768 ltac:(intros i Hi; replace (a + i) with a by (clear - Hi; lia); exact Hc) ltac:(clear; lia)) as (_ & Y & _). unfold SB in Y. clear - X Y; lia. }
  pose proof (L5SAR.ek_trans L ar LB FF sp 32768 [] M M2 M3 EK02f EK23f) as EK03f.
  assert (OWN3 : own sp R M3).
  { apply (own_agree sp R M1 M3 ltac:(clear - SL160 SPT; lia) ltac:(clear - SHI SPT; lia) OWN1). intros a Ha. unfold ocell in Ha.
    rewrite FR3; [apply AGF; clear - Ha; lia| clear - Ha SL160 SHI SPT; lia| intros [X|X]; clear - X Ha GFCEIL GFR SL160 SPT; unfold SB in *; lia]. }
  assert (SPE3 : L5.u64_at RSEGS M3 (sp - 160) oec).
  { apply (L5C.u64_at_agree RSEGS M1 M3); [| clear - SL160 SPT; lia| clear - SHI SPT; lia| exact SPE1]. intros a Ha.
    rewrite FR3; [apply AGF; clear - Ha; lia| clear - Ha SL160 SHI SPT; lia| intros [X|X]; clear - X Ha GFCEIL GFR SL160 SPT; unfold SB in *; lia]. }
  assert (WAPPR : PMKA.wapp (PNRA.W_brun PMA.AD PMA.AN fb)).
  { unfold PNRA.W_brun, PGS.W_srcfG, PNST.berr_W, PNST.cat_W, PNST.dec_W, PNRA.o_src, PNRA.o_is, PNRA.o_bb, PNRA.o_nb, PNRA.o_tb, PNRA.o_stk, PNRA.o_ec, PNRA.o_p, PMSP.o_p, PMSP.o_is, PMSP.o_ec.
    cbn [app pa_off_p pa_off_is pa_off_ec pa_errcat_guard pa_atexit PMA.AD ADDR_A PMA.AN NADDR_A PNL.pn_inf_guard PNL.pn_nan_guard PNL.pn_inf_obj PNL.pn_nan_obj].
    unfold PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK.
    pose proof FSAPP as (FA0 & FA1 & FA2). unfold BIGSHADOW_LO, BIGSHADOW_HI in FA1.
    repeat apply PMKA.wapp_cons; [..| apply PMKA.wapp_nil]; cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct FA1 as [FA1|FA1]; clear - FA0 FA1 FA2 F1 F2; lia. }
  set (WR := PNRA.W_brun PMA.AD PMA.AN fb) in *.
  assert (BI3 : PMAUK.binv L ar HI M model LBX FF LK Aw sp 32768 (sp - 256) (own sp R) F 1 WR (PNM.bparser_own s) M3 model3 LK2 cr Aw).
  { unfold PMAUK.binv. split; [exact HH3|]. split; [exact AM3|].
    split; [eapply L5LZ.model_rt_trans; [exact MRT1| eapply L5LZ.model_rt_trans; [exact MRT2| exact MRT3]]|].
    split; [apply incl_refl|]. split; [exact GLKI2|]. split; [exact (L5SAR.astk_grows ar M2 M3 sp 32768 ASTK2 MGM3)|].
    split; [apply (L5SAR.ek_W L ar LBX FF sp 32768 WR [] M M3 (PMKA.ek_sublb L ar LB LBX FF sp 32768 [] M M3 INCX EK03f)); intros a _ r0 []|].
    split; [apply (L5SAR.dk_trans L ar LBX FF sp 32768 M M2 M3 DK02); apply L5SAR.dk_grows; exact MGM3|].
    split; [exact OWN3|].
    change (ff_bytes 1 / 8) with 16. apply (L5.defined_grows M2 M3 _ _ MGM3).
    apply (proj1 (L5A.defined_vis H2 M2 (F / 8 + SB) 16 VSH)). intros i Hi. pose proof (FSHZ i Hi) as Z0. unfold MV2 in Z0. rewrite Z0. discriminate. }
  assert (R1c : forall j, In j [3; 4]%nat -> getr R1 (reg j) = getr R (reg j)).
  { intros j Hj. apply KS1. revert j Hj. apply (L5K.incl_b [3; 4]%nat). vm_compute. reflexivity. }
  (* [comment removed for export] *)
  assert (AOPp : PMSPA.aobjA FF op PNM.PSIZE) by (apply (PNAPAR.aobj_fbB FF fb op PNM.PSIZE FOK); unfold op, PNM.PSIZE; clear; lia).
  assert (PA3 : PNM.bparser_at RSEGS PMA.AD PMSPA.accA PMSPA.annA (pa_vp_parser PMA.AD) M3 op ois s).
  { apply (PNAPAR.bparser_keepA L ar C HI HIok LB FF LK cr Aw (vml_of model) [] sp 32768 M M3 op ois s HH EK03f PMKA.wapp_nil AOPp);
      [unfold LB; apply incl_appl; apply incl_refl| intros i _ r0 []| intros B m _ i _ r0 []| exact PA]. }
  assert (IA3 : PM.iss_at RSEGS PMA.AD PMSPA.accA M3 ois str sm).
  { apply (PMKA.iss_keepA RSEGS PMA.AD L ar LB FF sp 32768 [] M M3 EK03f PMKA.wapp_nil FRB BRB ois str sm); [| | intros i _ r0 []| intros c n p _ i _ r0 []| exact IA].
    - apply (PNAPAR.aobj_fbB FF fb ois 272 FOK); unfold ois; clear; lia.
    - unfold LB. apply incl_appr. exact INCS. }
  assert (EC3 : PMSPA.ec_at RSEGS M3 oec e cat).
  { apply (PMKA.ec_keepA RSEGS L ar LB FF sp 32768 [] M M3 EK03f PMKA.wapp_nil FRB oec e cat); [| intros i _ r0 []| exact EC].
    apply (PNAPAR.aobj_fbB FF fb oec 16 FOK); unfold oec; clear; lia. }
  assert (BASE3 : PMSTA.base_okA RSEGS PMA.AD M3) by (apply (PMASK.base_keep L ar C LY LB FF sp 32768 [] M M3 EK03f); [intros a _ r0 []| exact BASE]).
  assert (ERR3 : PNSTA.berr_okA RSEGS PMA.AD PMA.AAD PMA.AN M3 ax).
  { apply (PNSTA.berr_okA_frame RSEGS PMA.AD PMA.AAD PMA.AN PMA.addrs_wf_B M M3); [| exact ERR].
    intros a Ha D. apply EK03f. split; [exact Ha|]. split; [| intros r0 []]. unfold aclient, aclient_g. right; right; left.
    pose proof (depA_img a D). rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [lia| exact (PMA.ly_static L C LY a D)]. }
  assert (AV0 : avis H2 (F / 8 + 2147450880) 1) by (apply (L5A.avis_sub H2 (F / 8 + SB) 16); [exact VSH| unfold SB; clear; lia| unfold SB; clear; lia]).
  assert (R4a : 0 <= F / 8 + 2147450880) by (clear - Q3; lia).
  assert (R4b : F / 8 + 2147450880 + 1 <= 2 ^ 64) by (clear - Q3; pose proof (Z.div_le_upper_bound F 8 17592186044400 ltac:(lia) ltac:(lia)); lia).
  pose proof (L5A.u8_at_vis H2 M3 (F / 8 + 2147450880) 241 AV0 R4a R4b) as UV. rewrite VIS3 in UV.
  assert (U8c : L5.u8_at RSEGS M3 (F / 8 + 2147450880) 241) by (apply (proj1 UV); exact SH0). clear UV.
  (* [comment removed for export] *)
  assert (PRE3 : PNRA.brun_pre RSEGS PMA.AD PMA.AN PMA.AAD M3 fb s str sm ax).
  { refine (PNBKA.pre_after_call L ar LB FF sp 32768 [] M M3 fb s s str sm sm ax ax FRB EK03f PMKA.wapp_nil FOK _ RPRE PA3 IA3 GROW BASE3 ERR3). intros i _ rr []. }
  assert (LM3 : pa_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK2 Aw s sm ax cr).
  { unfold pa_mem. split; [exact BI3|]. split; [exact PRE3|]. split; [apply PNBKA.src_step_refl|]. split; [apply PNST.bax_le_refl|].
    split; [apply PNBKA.credit_keep_refl|]. split; [exact U8c| exact I]. }
  unfold op, ov, oec, ois in *. clear op ov oec ois.
  assert (R3gp : getr R3 (reg 3) = getr R (reg 3)) by (rewrite (KS3 3%nat) by inl; rewrite (R2c 3%nat) by inl; apply R1c; inl).
  assert (R3tp : getr R3 (reg 4) = getr R (reg 4)) by (rewrite (KS3 4%nat) by inl; rewrite (R2c 4%nat) by inl; apply R1c; inl).
  assert (X2 : getr R3 (reg 2) = Z_to_bv 64 (sp - 256)) by (rewrite (KS3 2%nat) by inl; exact B2R).
  assert (X8 : getr R3 (reg 8) = Z_to_bv 64 sp) by (rewrite (KS3 8%nat) by inl; exact B8R).
  assert (X9 : getr R3 (reg 9) = Z_to_bv 64 (sp - 256)) by (rewrite (KS3 9%nat) by inl; exact B9R).
  assert (X22 : getr R3 (reg 22) = Z_to_bv 64 (fb + 432)) by (rewrite (KS3 22%nat) by inl; exact B22R).
  assert (X24 : getr R3 (reg 24) = Z_to_bv 64 (fb + 464)) by (rewrite (KS3 24%nat) by inl; exact B24R).
  clear Q0a Q0b Q0d Q0f Q0g Q1 Qop Q3 Q4 Q5 Q7 FLCv.
  (* [comment removed for export] *)
  pose proof (PNAPAK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M3 model3 LK2 Aw s sm ax cr CTX G LM3) as (PF & _).
  pose proof (PNAPAA.mfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M3 model3 LK2 Aw s sm ax cr CTX G LM3) as (_ & DNv & _ & _ & _ & _ & SPTR & _ & _ & Q36 & Q34 & Q37).
  rewrite (proj1 INV) in DNv.
  pose proof (PNAPAA.ifacts_of L ar C IL HI LY HIok ICok ILY K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M3 model3 LK2 Aw s sm ax cr CTX G LM3)
    as (if1 & if2 & if3 & if4 & if5 & if6 & if7 & if8 & if9 & if10 & if11 & if12 & if13 & ST02).
  pose proof (PNAPAA.vfacts_of L ar C IL HI LY HIok ICok ILY K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M3 model3 LK2 Aw s sm ax cr CTX G LM3) as (vf1 & vf2 & vf3 & vf4 & vf5 & vf6 & vf7 & vf8 & _).
  set (MV3 := mrestrict (ahid Aw model3) M3) in *.
  pfx PF.
  set (W14 := fun a => (sp - 256 <= a < sp - 160) \/ (sp - 152 <= a < sp - 104)).
  assert (ENTRY : exists (fx4 : FPState) R4 (M4v : mem),
            mem_grows MV3 M4v /\ (forall i, 0 <= i < 2 ^ 64 -> ~ W14 i -> M4v (Z_to_bv 64 i) = MV3 (Z_to_bv 64 i))
            /\ msteps RSEGS (st fx3 R3 0xadf94 MV3) (st fx4 R4 0xae0cc M4v) /\ lregs R R4 sp fb F /\ getr R4 (reg 17) = Z_to_bv 64 (fb + 464 + 8)
            /\ L5.u64_at RSEGS M4v (sp - 136) ((fb + 464 + 8) / 8 + 2147450880) /\ L5.u64_at RSEGS M4v (sp - 144) ((fb + 464 + 9) / 8 + 2147450880)
            /\ L5.u64_at RSEGS M4v (sp - 152) (fb + 464 + 8) /\ L5.u64_at RSEGS M4v (sp - 168) (F + 32) /\ L5.u64_at RSEGS M4v (sp - 176) (fb + 464 + 16)
            /\ L5.u64_at RSEGS M4v (sp - 184) (F + 48) /\ L5.u64_at RSEGS M4v (sp - 192) (fb + 464) /\ L5.u64_at RSEGS M4v (sp - 200) ((fb + 464 + 392) / 8 + 2147450880)
            /\ L5.u64_at RSEGS M4v (sp - 208) (F / 8 + 2147450880) /\ L5.u64_at RSEGS M4v (sp - 216) ((fb + 432) / 8 + 2147450880)
            /\ L5.u64_at RSEGS M4v (sp - 224) F /\ L5.u64_at RSEGS M4v (sp - 232) F).
  { assert (FIN : forall R4,
              (forall x, In x PNAPAP.KS_apaS0 -> getr R4 (reg x) = getr R3 (reg x)) ->
              getr R4 (reg 19) = Z_to_bv 64 (fb + 464 + 392) -> getr R4 (reg 20) = Z_to_bv 64 40 -> getr R4 (reg 21) = Z_to_bv 64 143316 -> getr R4 (reg 22) = Z_to_bv 64 (fb + 432) ->
              getr R4 (reg 24) = Z_to_bv 64 (fb + 464 + 9) -> getr R4 (reg 25) = Z_to_bv 64 (fb + 464 + 400) -> getr R4 (reg 26) = Z_to_bv 64 (fb + 464) ->
              getr R4 (reg 27) = Z_to_bv 64 ((fb + 464 + 400) / 8 + 2147450880) -> lregs R R4 sp fb F).
    { intros R4 KS4 Z19 Z20 Z21 Z22 Z24 Z25 Z26 Z27.
      assert (K4 : forall k, In k [2; 3; 4; 8; 9; 18; 23]%nat -> getr R4 (reg k) = getr R3 (reg k)).
      { intros k Hk. apply KS4. revert k Hk. apply L5K.incl_b. vm_compute. reflexivity. }
      unfold lregs.
      split; [rewrite (K4 2%nat) by inl; exact X2|]. split; [rewrite (K4 3%nat) by inl; exact R3gp|]. split; [rewrite (K4 4%nat) by inl; exact R3tp|].
      split; [rewrite (K4 8%nat) by inl; exact X8|]. split; [rewrite (K4 9%nat) by inl; exact X9|]. split; [rewrite (K4 18%nat) by inl; exact Y18|].
      split; [exact Z19|]. split; [exact Z20|]. split; [exact Z21|]. split; [exact Z22|]. split; [rewrite (K4 23%nat) by inl; exact Y23|].
      split; [exact Z24|]. split; [exact Z25|]. split; [exact Z26| exact Z27]. }
    destruct ST02 as [ST|ST]; rewrite ST in if13.
    - pose proof (PNAPAP.apaS0_conc fx3 R3 MV3 (vmx R sp fb F fl 0 0 0 0 0 0 0 0)) as P.
      pfeed P.
      destruct P as (fx4 & R4 & M4v & MG4 & _ & FRZ4 & MS4 & KS4 & _ & _ & _ & _ & _ & _ & Z17 & Z19 & Z20 & Z21 & Z22 & Z24 & Z25 & Z26 & Z27 & CS).
      exists fx4, R4, M4v. split; [exact MG4|]. split; [intros i Hi N; apply FRZ4; [exact Hi| (intros X; apply N; unfold W14; clear - X; lia) ..]|].
      split; [exact MS4|]. split; [exact (FIN R4 KS4 Z19 Z20 Z21 Z22 Z24 Z25 Z26 Z27)|]. split; [exact Z17|].
      repeat match type of CS with _ /\ _ => let c := fresh "c" in destruct CS as [c CS] end. repeat split; assumption.
    - pose proof (PNAPAP.apaS2_conc fx3 R3 MV3 (vmx R sp fb F fl 0 0 0 0 0 0 0 0)) as P.
      pfeed P.
      destruct P as (fx4 & R4 & M4v & MG4 & _ & FRZ4 & MS4 & KS4 & _ & _ & _ & _ & _ & _ & Z17 & Z19 & Z20 & Z21 & Z22 & Z24 & Z25 & Z26 & Z27 & CS).
      exists fx4, R4, M4v. split; [exact MG4|]. split; [intros i Hi N; apply FRZ4; [exact Hi| (intros X; apply N; unfold W14; clear - X; lia) ..]|].
      split; [exact MS4|]. split; [exact (FIN R4 KS4 Z19 Z20 Z21 Z22 Z24 Z25 Z26 Z27)|]. split; [exact Z17|].
      repeat match type of CS with _ /\ _ => let c := fresh "c" in destruct CS as [c CS] end. repeat split; assumption. }
  destruct ENTRY as (fx4 & R4 & M4v & MG4 & FRW4 & MS4 & ER4 & X174 & c136 & c144 & c152 & c168 & c176 & c184 & c192 & c200 & c208 & c216 & c224 & c232).
  apply (PNAPAK.pa_piece_fr L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M3 model3 LK2 Aw s sm ax cr fx3 fx4 R3 R4 0xadf94 0xae0cc M4v W14 CTX G LM3 MS4 MG4 FRW4).
  { intros a Wa. unfold W14 in Wa. clear - Wa. lia. }
  intros M4 model4 LM4 HID4 VIS4 FR4 MGM4 ECK4.
  pose proof (PNAPAK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M4 model4 LK2 Aw s sm ax cr CTX G LM4) as (_ & _ & _ & _ & _ & _ & SVr4).
  rewrite HID4, VIS4 in SVr4.
  assert (SPL4 : spill M4 sp F (fb + 464) (fb + 432) (fb + 1024)).
  { unfold spill.
    split; [apply SVr4; [clear; lia| clear; lia| exact c136]|]. split; [apply SVr4; [clear; lia| clear; lia| exact c144]|]. split; [apply SVr4; [clear; lia| clear; lia| exact c152]|].
    split. { apply (L5C.u64_at_agree RSEGS M3 M4); [| clear - pf4; lia| clear - pf4; lia| exact SPE3]. intros j Hj. apply FR4; [clear - Hj pf4; lia| unfold W14; clear - Hj; lia]. }
    split; [apply SVr4; [clear; lia| clear; lia| exact c168]|]. split; [apply SVr4; [clear; lia| clear; lia| exact c176]|]. split; [apply SVr4; [clear; lia| clear; lia| exact c184]|].
    split; [apply SVr4; [clear; lia| clear; lia| exact c192]|]. split; [apply SVr4; [clear; lia| clear; lia| exact c200]|]. split; [apply SVr4; [clear; lia| clear; lia| exact c208]|].
    split; [apply SVr4; [clear; lia| clear; lia| exact c216]|]. split; [apply SVr4; [clear; lia| clear; lia| exact c224]|].
    apply SVr4; [clear; lia| clear; lia| exact c232]. }
  pose proof (PNAPAB.unread_le L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M4 model4 LK2 Aw s sm ax cr LM4) as (UN0 & _).
  pose proof (bflag_range (PNM.b_stk s)) as FR0.
  apply (pa_loop K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 BD RV REN ED EA SR MKE ASH CTX G (PNRA.bmu s sm) fx4 R4 M4 model4 LK2 Aw s sm ax cr LM4 ER4 X174 SPL4).
  - exists e, cat. split; [exact HE| exact (ECK4 _ _ EC3)].
  - exact INV.
  - intros _. exact BB0.
  - intros _. unfold PNRA.bmu. clear - UN0 FR0. lia.
Qed.
End WithHeap.
End PNAPA.
