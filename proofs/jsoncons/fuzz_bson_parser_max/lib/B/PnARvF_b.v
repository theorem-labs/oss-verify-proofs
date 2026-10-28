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
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5CoreKit L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5CoreSpecsA_b L5StepAR_b L5CoreBR_b L5ADetailHR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmParSpecs PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PnSpecsAa_b
     PmModelFactsA_b PnStepA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PgSrc PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnLayout PnModel PnModelFacts PnStatics PnStaticsA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b PnRunAa_b PnASrcKit_b PmAUarK_b PmAUar_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnBrObj. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnBrObjA_b PnAParKit_b PnAReset1_b PnOwnerOkA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmCertKitG. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnBrKitA_b PnARel3_b PnARvTP_b Ba0_code_b00a0_b00a4_b PnARvK_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNARVF.
Import L5A. Import L5CA. Import L5SAR. Import PNBKA. Import PNARVK.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMA.ly_as0 L C LY.
Let base_keepW := PNBKA.base_keepW L ar C LY.
Let berr_keep := PNBKA.berr_keep L ar C LY.
Let pre_after_call := PNBKA.pre_after_call L ar.
Let blk_ceil := PNBKA.blk_ceil L ar C HI HIok.

(* [comment removed for export] *)
Lemma rv_fin9 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 (fx5 fx9 : FPState) R5 R9 (pc5 mo : Z) (M9v : mem) :
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 ->
  msteps RSEGS (st fx5 R5 pc5 (mrestrict (ahid Aw5 model5) M5)) (st fx9 R9 0xb1578 M9v) ->
  mem_grows (mrestrict (ahid Aw5 model5) M5) M9v ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ PMAUK.WretX F fl 3 (fun a => fb + 472 <= a < fb + 473) a -> M9v (Z_to_bv 64 a) = mrestrict (ahid Aw5 model5) M5 (Z_to_bv 64 a)) ->
  L5.u8_at RSEGS M9v fl 0 -> L5.u8_at RSEGS M9v (fb + 472) mo -> (mo = 0 \/ mo = 1) ->
  getr R9 (reg 2) = Z_to_bv 64 sp ->
  (forall k, In k [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R9 (reg k) = Z_to_bv 64 (bv_unsigned (getr R (reg k)))) ->
  (forall k, In k [3; 4]%nat -> getr R9 (reg k) = getr R (reg k)) ->
  ( (exists v, 1 <= v <= 64 /\ PMSPA.ec_at RSEGS M5 (fb + 1024) v (pa_errcat_obj PMA.AD) /\ mo = 0 /\ PNST.bax_cat ax5 = true)
    \/ (PMSPA.ec_at RSEGS M5 (fb + 1024) e cat /\ PNRA.bprog_value R9 M5 s s5 sm sm5) ) ->
  PNRA.binv s5 -> (length (PNM.b_stk s) <= length (PNM.b_stk s5))%nat ->
  (PNRA.bb_room s sm -> mo = 1 -> PNRA.bb_room s5 sm5) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx5 R5 pc5 M5 model5) K.
Proof.
  intros CTX G LM MS9 MG9 FRZ9 FL0 MO9 Hmo Y2 YR Y34 POST INV5 LEN5 ROOM5.
  pose proof CTX as (Hw & HH & AM & K0 & ENT & FRM & FRS & FOK & SP32 & ARGS & RPRE & INCS & INV & EC0 & HE & UNR & CRED & KONT).
  destruct ENT as (Rra & RAok0 & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 8) with 28672 in *. change (28672 / 8) with 3584 in STKSH.
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof RAok0 as (Hr1 & Hr2).
  pose proof FOK as ((rs & Hfb) & Fal).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _).
  pose proof (WF _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 5) with 2048 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL, FSIMG, F1, F2.
  rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in FSIMG.
  assert (FBI : 6905856 <= fb) by (clear - F1 FSAPP FSIMG; lia).
  pose proof LM as (BI & RP1 & STEP1 & AXL1 & CK1 & SHC1 & EBB1).
  pose proof G as G'. unfold rv_frame in G'.
  destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 3) with 512 in *. change (512 / 8) with 64 in *.
  pose proof BI as (HH1 & AM1 & MRT1 & INCA1 & INCL1 & ASTK1 & EK1 & DK1 & OWN1 & DSH1).
  set (FF' := (F, 3, sp - 160 + 32) :: FF) in *.
  assert (FOK' : PNRA.frame_okB FF' fb). { split; [exists rs; right; exact Hfb| exact Fal]. }
  pose proof RP1 as (PA1 & IA1 & VIS1 & VREF1 & OACC1 & BASE1 & ERR1 & GR1).
  change (PNRA.o_p PMA.AD fb) with (fb + 464) in PA1, IA1, VIS1, VREF1, OACC1. change (PNRA.o_is PMA.AD fb) with (fb + 96) in PA1, IA1. change (PNRA.o_v PMA.AD fb) with (fb + 432) in VIS1, VREF1.
  change (PNM.PSIZE + 8) with 424 in OACC1.
  pose proof (PNAPAR.op_visB L ar C HI LY HIok _ FF' LK5 cr5 Aw5 M5 model5 fb _ s5 HH1 FOK' PA1 OACC1) as ((O1 & O8 & ONSH) & Zop & OWR & OCE & OVIS & AOP).
  set (op := fb + 464) in *. set (ois := fb + 96) in *.
  set (WR := PNRA.W_brun PMA.AD PMA.AN fb) in *.
  pose proof FSAPP as (FA0 & FA1 & FA2). unfold BIGSHADOW_LO, BIGSHADOW_HI in FA1.
  pose proof GFR as (GF1 & GF2 & _).
  set (H5 := ahid Aw5 model5) in *. set (MV5 := mrestrict H5 M5) in *.
  assert (R9ra : getr R9 (reg 1) = Z_to_bv 64 r) by (rewrite (YR 1%nat) by inl; rewrite Rra; rewrite L5.unsigned_lit by (clear - Hr1; lia); reflexivity).
  pose proof (PMK.ret_to RSEGS fx9 R9 M9v 0xb1578 W_b00a0 r F_b00a0 eq_refl D_b00a0 R9ra Hr1 Hr2) as MSr.
  set (Wx := fun a => fb + 472 <= a < fb + 473).
  apply (PMAUK.retire_coreW L ar C HI LYa HIok M model LBX FF LK Aw sp 28672 (sp - 160) (sp - 104) sp (ocell sp) (own sp R) F fl 3 LK2 M2 model2 cr (PNM.bparser_own s) G
           WR (PNM.bparser_own s5) M5 model5 LK5 cr5 Aw5 Wx fx5 fx9 R5 pc5 R9 r M9v K BI).
  { intros a X. unfold Wx in X. split.
    - apply (L5SAR.fframe_client L ar (PNM.bparser_own s5 ++ LBX) FF' 0 0 fb 5 rs); [right; exact Hfb| change (ff_bytes 5) with 2048; clear - X; lia].
    - intros O. apply (O (PNRA.o_p PMA.AD fb + 8, 8)); [unfold WR, PNRA.W_brun; left; reflexivity| unfold L5.in_rng, PNRA.o_p, PMSP.o_p; cbn [fst snd pa_off_p PMA.AD PnLayoutA_b.ADDR_A]; clear - X; lia]. }
  { intros a. unfold Wx. destruct (L5SAR.rng_dec a (fb + 472) (fb + 473)) as [X|X]; [left; exact X| right; exact X]. }
  { exact (msteps_trans _ _ _ _ MS9 MSr). }
  { exact MG9. }
  { exact FRZ9. }
  { exact FL0. }
  intros Mf modelf FZf MGf VISf AHf MRTf AMf HHf. change (mrestrict H5 Mf = M9v) in VISf.
  assert (EKf : L5SAR.ek L ar (PNM.bparser_own s5 ++ LBX) FF 0 0 [(fb + 472, 1)] M5 Mf).
  { apply (PMAUAR.wret_ek L ar C HI LY HIok LBX FF LK Aw sp 28672 (sp - 160) (sp - 104) sp (ocell sp) (own sp R) F fl 3 LK2 M2 model2 cr (PNM.bparser_own s)
             (PNM.bparser_own s5 ++ LBX) LK5 cr5 Aw5 M5 Mf _ [(fb + 472, 1)] Wx G HH1).
    - intros a X O. apply (O (fb + 472, 1)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; unfold Wx in X; clear - X; lia].
    - exact FZf. }
  pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB. pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH1) as BRB5.
  assert (MOf : L5.u8_at RSEGS Mf (op + 8) mo).
  { apply (proj1 (L5A.u8_at_vis H5 Mf (op + 8) mo (OVIS (op + 8) 1 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - O1; lia) ltac:(clear - O1; lia))). rewrite VISf. replace (op + 8) with (fb + 472) by (unfold op; clear; lia). exact MO9. }
  assert (WAPP8 : PMKA.wapp [(fb + 472, 1)]).
  { apply PMKA.wapp_cons; [| apply PMKA.wapp_nil]. cbn [fst snd]. unfold BIGSHADOW_LO, BIGSHADOW_HI. destruct FA1 as [Y|Y]; clear - Y F1 F2; lia. }
  assert (OUT8 : forall a n, (a + n <= op + 8 \/ op + 9 <= a) -> forall i, a <= i < a + n -> L5.outside [(fb + 472, 1)] i).
  { intros a n X3 i Hi rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. unfold op in X3. clear - Hi Hr X3. lia. }
  assert (OUTB8 : forall q m, In (q, m) (PNM.bparser_own s5 ++ LBX) -> forall i, q <= i < q + m -> L5.outside [(fb + 472, 1)] i).
  { intros q m Hq i Hi rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr.
    destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q m op 416 HH1 Hq (PMAUAR.aobjA_push FF op 416 _ (PNAPAR.aobj_fbB FF fb op 416 FOK ltac:(unfold op; clear; lia) ltac:(unfold op; clear; lia)))) as [Z0|Z0]; unfold op in Z0; clear - Hi Hr Z0; lia. }
  set (s9 := PNBO.set_more s5 mo).
  assert (EO9 : PNM.bparser_own s9 = PNM.bparser_own s5) by (unfold s9; destruct s5; reflexivity).
  assert (PA9 : PNM.bparser_at RSEGS PMA.AD PMSPA.accA PMSPA.annA (pa_vp_parser PMA.AD) Mf op ois s9).
  { apply (bparser_set_moreS M5 Mf (pa_vp_parser PMA.AD) op ois s5 mo ltac:(clear - O1; lia) ltac:(clear - O1; lia)); [| | | exact MOf| exact Hmo| exact PA1].
    - intros i Hi Hn. destruct (Z_lt_le_dec i (op + 8)) as [X|X].
      + refine (proj1 (PMKA.agA_obj L ar _ FF 0 0 _ M5 Mf EKf WAPP8 FRB op 8 _ _) i _); [| apply OUT8; clear; lia| clear - Hi X; lia].
        apply (PNAPAR.aobj_fbB FF fb op 8 FOK); unfold op; clear; lia.
      + refine (proj1 (PMKA.agA_obj L ar _ FF 0 0 _ M5 Mf EKf WAPP8 FRB (op + 9) 407 _ _) i _); [| apply OUT8; clear; lia| clear - Hi X Hn; lia].
        apply (PNAPAR.aobj_fbB FF fb (op + 9) 407 FOK); unfold op; clear; lia.
    - intros i Hi. refine (PMKA.agsh_obj L ar _ FF 0 0 _ M5 Mf EKf WAPP8 FRB op 416 _ i Hi). apply (PNAPAR.aobj_fbB FF fb op 416 FOK); unfold op; clear; lia.
    - intros q m Hq. assert (HqL : In (q, m) (PNM.bparser_own s5 ++ LBX)) by (apply in_or_app; left; exact Hq). destruct (BRB5 _ HqL) as (B0 & B1). cbn [fst snd] in B0, B1.
      split; [exact B0|]. split; [clear - B1; lia|]. apply (PMKA.agA_blk L ar _ FF 0 0 _ M5 Mf EKf WAPP8 BRB5 q m HqL). apply OUTB8. exact HqL. }
  assert (IA9 : PM.iss_at RSEGS PMA.AD PMSPA.accA Mf ois str sm5).
  { apply (PMKA.iss_keepA RSEGS PMA.AD L ar _ FF 0 0 _ M5 Mf EKf WAPP8 FRB BRB5 ois str sm5); [| | | | exact IA1].
    - apply (PNAPAR.aobj_fbB FF fb ois 272 FOK); unfold ois; clear; lia.
    - apply incl_appr. exact INCS.
    - apply OUT8. unfold ois, op; clear; lia.
    - intros c0 n0 p0 E0. unfold PMKA.blk_out. apply OUTB8. apply in_or_app; right. apply INCS. rewrite E0. left; reflexivity. }
  assert (BASE9 : PMSTA.base_okA RSEGS PMA.AD Mf).
  { apply (PMASK.base_keep L ar C LY _ FF 0 0 _ M5 Mf EKf); [| exact BASE1]. intros a Ha rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - Ha Hr FBI; lia. }
  assert (ERR9 : PNSTA.berr_okA RSEGS PMA.AD PMA.AAD PMA.AN Mf ax5).
  { apply (berr_keep _ FF 0 0 _ M5 Mf ax5 EKf); [| exact ERR1]. intros a Ha rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - Ha Hr FBI; lia. }
  assert (PRE9 : PNRA.brun_pre RSEGS PMA.AD PMA.AN PMA.AAD Mf fb s9 str sm5 ax5).
  { apply (pre_after_call _ FF 0 0 _ M5 Mf fb s5 s9 str sm5 sm5 ax5 ax5 FRB EKf WAPP8 FOK); [| exact RP1| exact PA9| exact IA9| unfold s9; exact GR1| exact BASE9| exact ERR9].
    intros i Hi. apply (OUT8 i 1); [unfold op; clear - Hi; lia| clear; lia]. }
  assert (ECf : forall v c, PMSPA.ec_at RSEGS M5 (fb + 1024) v c -> PMSPA.ec_at RSEGS Mf (fb + 1024) v c).
  { intros v c EC5. apply (PMKA.ec_keepA RSEGS L ar _ FF 0 0 _ M5 Mf EKf WAPP8 FRB (fb + 1024) v c); [| | exact EC5].
    - apply (PNAPAR.aobj_fbB FF fb (fb + 1024) 16 FOK); clear; lia.
    - apply OUT8. unfold op; clear; lia. }
  apply (KONT fx9 R9 Mf modelf LK5 Aw5 s9 sm5 ax5 cr5).
  - apply L5SAR.preserved_by_index. intros j Hj. unfold L5SAR.cs_all in Hj.
    repeat (destruct Hj as [<-|Hj]; [first [ rewrite Y2; exact (eq_sym Rsp) | rewrite (Y34 _) by inl; reflexivity | rewrite (YR _) by inl; apply Z_to_bv_bv_unsigned ] |]).
    destruct Hj.
  - unfold PNRA.brun_post. split; [exact PRE9|]. split; [unfold s9; cbn [PNBO.set_more PNM.b_src]; exact STEP1|]. split; [exact AXL1|].
    unfold PNRA.o_ec, PMSP.o_ec. cbn [pa_off_ec PMA.AD PnLayoutA_b.ADDR_A].
    split; [| unfold PNRA.bb_post, PNRA.bb_room, s9; cbn [PNBO.set_more PNM.b_bb PNM.b_more PNM.b_src]; exact ROOM5].
    destruct POST as [(v & Hv & EC5 & Hmo0 & CAT)|(EC5 & PROG)].
    + left. exists v. split; [exact Hv|]. split; [exact (ECf _ _ EC5)|]. split; [unfold s9; cbn [PNBO.set_more PNM.b_more]; exact Hmo0|]. split; [exact CAT|].
      split; [unfold s9; cbn [PNBO.set_more PNM.b_stk]; exact LEN5| unfold s9, PNRA.binv; cbn [PNBO.set_more PNM.b_done PNM.b_stk]; exact INV5].
    + right. split; [exact (ECf _ _ EC5)|]. split; [unfold s9, PNRA.binv; cbn [PNBO.set_more PNM.b_done PNM.b_stk]; exact INV5|].
      unfold s9, PNRA.bprog_value. unfold PNRA.bprog_value in PROG.
      unfold PNRA.bpush_rel, PNRA.btop_pos in *. cbn [PNBO.set_more PNM.b_stk PNM.b_src]. exact PROG.
  - exact AHf.
  - unfold s9, PNRA.pot_bparser. cbn [PNBO.set_more PNM.b_sk PNM.b_tb PNM.b_tg PNM.b_nb PNM.b_ng PNM.b_bb PNM.b_bg]. exact CK1.
  - exact MRTf.
  - exact INCL1.
  - exact INCA1.
  - exact AMf.
  - rewrite EO9. exact HHf.
Qed.


(* [comment removed for export] *)
Lemma rv_fin K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 (fx5 fx1 : FPState) R5 R1 (pc5 mo : Z) (M1v : mem) :
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 ->
  msteps RSEGS (st fx5 R5 pc5 (mrestrict (ahid Aw5 model5) M5)) (st fx1 R1 0x7b90c M1v) ->
  mem_grows (mrestrict (ahid Aw5 model5) M5) M1v ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (F <= a < F + 8) -> ~ (F / 8 + 2147450880 <= a < F / 8 + 2147450880 + 64) -> ~ (fb + 472 <= a < fb + 473) ->
     M1v (Z_to_bv 64 a) = mrestrict (ahid Aw5 model5) M5 (Z_to_bv 64 a)) ->
  L5.u8_at RSEGS M1v (fb + 472) mo -> (mo = 0 \/ mo = 1) ->
  getr R1 (reg 1) = Z_to_bv 64 0xb1440 -> getr R1 (reg 10) = Z_to_bv 64 (F / 8 + 2147450880) -> getr R1 (reg 11) = Z_to_bv 64 64 ->
  getr R1 (reg 2) = Z_to_bv 64 (sp - 160) -> getr R1 (reg 8) = Z_to_bv 64 sp -> getr R1 (reg 19) = Z_to_bv 64 F ->
  (forall k, In k [3; 4]%nat -> getr R1 (reg k) = getr R (reg k)) ->
  ( (exists v, 1 <= v <= 64 /\ PMSPA.ec_at RSEGS M5 (fb + 1024) v (pa_errcat_obj PMA.AD) /\ mo = 0 /\ PNST.bax_cat ax5 = true)
    \/ (PMSPA.ec_at RSEGS M5 (fb + 1024) e cat /\ PNRA.bprog_value R1 M5 s s5 sm sm5) ) ->
  PNRA.binv s5 -> (length (PNM.b_stk s) <= length (PNM.b_stk s5))%nat ->
  (PNRA.bb_room s sm -> mo = 1 -> PNRA.bb_room s5 sm5) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx5 R5 pc5 M5 model5) K.
Proof.
  intros CTX G LM MS1 MG1 FZ1 MO1 Hmo R1ra R1a0 R1a1 R1sp R1s0 R1s3 R134 POST INV5 LEN5 ROOM5.
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 CTX G LM)
    as (PF & OWNv & _).
  pose proof LM as (BI & _).
  destruct (PMAUK.vis_facts L ar C HI LYa HIok M model LBX FF LK Aw sp 28672 (sp - 160) (sp - 104) sp (ocell sp) (own sp R) F fl 3 LK2 M2 model2 cr (PNM.bparser_own s) G
              _ (PNM.bparser_own s5) M5 model5 LK5 cr5 Aw5 BI) as ((_ & IMGC0 & _ & _ & RMS0) & _).
  unfold pfacts in PF.
  destruct PF as (pI & pSB & pUAR & pSP & pSP32 & pSW & pOP & pOP8 & pOPN & PFZ).
  repeat (match type of PFZ with L5KA.zeros_at _ _ _ /\ _ => destruct PFZ as (_ & PFZ) end).
  destruct PFZ as (pOPD & pF & pF32 & pFD & pFW & pFN & pFSW & pFLC & pFL & pFLW & pFLN & pFFL & pFSP & pFLSP & pFOP & pFLOP & pFSOP & Q8 & Q9 & Q10 & pRs & pRo & pRF & pRfl).
  set (MV := mrestrict (ahid Aw5 model5) M5) in *.
  set (sh := F / 8 + 2147450880) in *.
  assert (SHR : 2148297872 <= sh /\ sh + 64 <= 17594333495296).
  { subst sh. clear - pF. assert (862208 <= F / 8) by (apply Z.div_le_lower_bound; lia).
    assert (F / 8 <= 17592186044352) by (apply Z.div_le_upper_bound; lia). lia. }
  (* [comment removed for export] *)
  assert (AG1 : forall a, 0 <= a < 2 ^ 64 -> (a < F \/ F + 8 <= a) -> (a < sh \/ sh + 64 <= a) -> (a < fb + 472 \/ fb + 473 <= a) -> M1v (Z_to_bv 64 a) = MV (Z_to_bv 64 a)).
  { intros a Ha X1 X2 X3. apply FZ1; [exact Ha| clear - X1; lia| subst sh; clear - X2; lia| clear - X3; lia]. }
  assert (AGI1 : forall i, 65536 <= i < 6905856 -> M1v (Z_to_bv 64 i) = MV (Z_to_bv 64 i)).
  { intros i Hi. apply AG1; [clear - Hi; lia| clear - Hi pF; lia| clear - Hi SHR; lia| clear - Hi pOP; lia]. }
  assert (IMGC1 : L5.img_clear M1v 1249280 1282048) by (intros i Hi; rewrite AGI1 by (clear - Hi; lia); apply IMGC0; exact Hi).
  assert (CSB1 : L5.u64_at RSEGS M1v 1309752 2147450880) by (eapply L5C.u64_at_agree; [intros i Hi; apply AGI1; clear - Hi; lia| clear; lia| clear; lia| exact pSB]).
  assert (CUAR1 : L5.u32_at RSEGS M1v 1309760 1) by (apply (PMF.u32_at_agree RSEGS MV M1v); [intros i Hi; apply AGI1; clear - Hi; lia| clear; lia| clear; lia| exact pUAR]).
  assert (RMS1 : L5.u64_at RSEGS M1v 1283280 1219844) by (eapply L5C.u64_at_agree; [intros i Hi; apply AGI1; clear - Hi; lia| clear; lia| clear; lia| exact RMS0]).
  assert (FSHW1 : L5.writable RSEGS M1v sh 64) by (eapply L5.writable_grows; [exact MG1| exact pFSW]).
  (* [comment removed for export] *)
  destruct (PNAREL.setshadow_f5_run fx1 R1 M1v sh 64 0xb1440 IMGC1 CSB1 CUAR1 RMS1 R1a0 R1a1 R1ra ltac:(reflexivity) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - SHR; lia) ltac:(clear - SHR; lia) FSHW1)
    as (fx2 & R3 & MS3 & KP3).
  set (M3v := wbytes M1v (Z_to_bv 64 sh) (repeat (Z_to_bv 8 245) (Z.to_nat 64))) in *.
  assert (MG3 : mem_grows M1v M3v) by (apply wbytes_grows).
  assert (AG3 : forall a, 0 <= a < 2 ^ 64 -> ~ (sh <= a < sh + 64) -> M3v (Z_to_bv 64 a) = M1v (Z_to_bv 64 a)).
  { intros a Ha Hn. subst M3v. apply AX2S.wbytes_out. rewrite repeat_length, L5.unsigned_lit by (clear - SHR; lia). clear - SHR; lia.
    rewrite repeat_length, !L5.unsigned_lit by (clear - SHR Ha; lia). clear - Hn. lia. }
  assert (AGM3 : forall a, 0 <= a < 2 ^ 64 -> (a < F \/ F + 8 <= a) -> (a < sh \/ sh + 64 <= a) -> (a < fb + 472 \/ fb + 473 <= a) -> M3v (Z_to_bv 64 a) = MV (Z_to_bv 64 a)).
  { intros a Ha X1 X2 X3. rewrite AG3; [apply AG1; assumption| exact Ha| clear - X2; lia]. }
  assert (MG13 : mem_grows MV M3v) by (intros x Hx; apply MG3; apply MG1; exact Hx).
  (* [comment removed for export] *)
  assert (WS3 : L5.writable RSEGS M3v (sp - 160) 160) by (eapply L5.writable_grows; [exact MG13| exact pSW]).
  assert (FD3 : L5.defined M3v F 512) by (eapply L5.defined_grows; [exact MG13| exact pFD]).
  assert (FW3 : L5.writable RSEGS M3v F 512) by (eapply L5.writable_grows; [exact MG13| exact pFW]).
  assert (FSW3 : L5.writable RSEGS M3v ((F / 8) + 2147450880) 64) by (eapply L5.writable_grows; [exact MG13| exact pFSW]).
  assert (FLC3 : L5.u64_at RSEGS M3v (F + 504) fl) by (eapply L5C.u64_at_agree; [intros i Hi; apply AGM3; clear - Hi pF pFN pFOP pOP SHR; subst sh; lia| clear - pF; lia| clear - pF; lia| exact pFLC]).
  assert (FLW3 : L5.writable RSEGS M3v fl 1) by (eapply L5.writable_grows; [exact MG13| exact pFLW]).
  assert (OWN3 : own sp R M3v).
  { apply (own_agree sp R MV M3v ltac:(clear - pSP; lia) ltac:(clear - pSP; lia) OWNv). intros a Ha. unfold ocell in Ha.
    apply AGM3; clear - Ha pSP pF pFSP pOP pOPD SHR; subst sh; lia. }
  pose proof OWN3 as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80 & S88 & S96 & S104).
  pose proof (bvu_rng (getr R (reg 1))) as B1. pose proof (bvu_rng (getr R (reg 8))) as B8. pose proof (bvu_rng (getr R (reg 9))) as B9.
  pose proof (bvu_rng (getr R (reg 18))) as B18. pose proof (bvu_rng (getr R (reg 19))) as B19. pose proof (bvu_rng (getr R (reg 20))) as B20.
  pose proof (bvu_rng (getr R (reg 21))) as B21. pose proof (bvu_rng (getr R (reg 22))) as B22. pose proof (bvu_rng (getr R (reg 23))) as B23.
  pose proof (bvu_rng (getr R (reg 24))) as B24. pose proof (bvu_rng (getr R (reg 25))) as B25. pose proof (bvu_rng (getr R (reg 26))) as B26.
  pose proof (bvu_rng (getr R (reg 27))) as B27.
  assert (KQ : forall k, In k [2; 3; 4; 8; 19]%nat -> getr R3 (reg k) = getr R1 (reg k)).
  { intros k Hk. apply KP3. revert k Hk. apply (L5K.incl_b [2; 3; 4; 8; 19]%nat PNAREL.KEPT). vm_compute. reflexivity. }
  assert (Y2 : getr R3 (reg 2) = Z_to_bv 64 (sp - 160)) by (rewrite KQ by inl; exact R1sp).
  assert (Y8 : getr R3 (reg 8) = Z_to_bv 64 sp) by (rewrite KQ by inl; exact R1s0).
  assert (Y19 : getr R3 (reg 19) = Z_to_bv 64 F) by (rewrite KQ by inl; exact R1s3).
  LeanFeed.pfeed P (PNARVTP.awvR2_conc fx2 R3 M3v (fun j => match j with 2%nat => sp | 50%nat => F | 51%nat => fl
      | 60%nat => bv_unsigned (getr R (reg 1)) | 61%nat => bv_unsigned (getr R (reg 8)) | 62%nat => bv_unsigned (getr R (reg 9))
      | 63%nat => bv_unsigned (getr R (reg 18)) | 64%nat => bv_unsigned (getr R (reg 19)) | 65%nat => bv_unsigned (getr R (reg 20))
      | 66%nat => bv_unsigned (getr R (reg 21)) | 67%nat => bv_unsigned (getr R (reg 22)) | 68%nat => bv_unsigned (getr R (reg 23))
      | 69%nat => bv_unsigned (getr R (reg 24)) | 70%nat => bv_unsigned (getr R (reg 25)) | 71%nat => bv_unsigned (getr R (reg 26))
      | 72%nat => bv_unsigned (getr R (reg 27)) | _ => 0 end)) ltac:(first [assumption | unfold PNARVTP.aligned; assumption | (clear; lia)]).
  destruct P as (fx4 & R4 & M4v & MG4 & _ & FRZ4 & MS4 & KS4 & E1 & E2 & E8 & E9 & E10 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27 & FL0).
  apply (rv_fin9 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 fx5 fx4 R5 R4 pc5 mo M4v CTX G LM).
  - eapply msteps_trans; [exact MS1|]. eapply msteps_trans; [exact MS3| exact MS4].
  - intros x Hx. apply MG4. apply MG13. exact Hx.
  - intros a Ha Nw. unfold PMAUK.WretX, PMAUK.Wret in Nw. change (ff_bytes 3) with 512 in Nw. change (512 / 8) with 64 in Nw.
    rewrite FRZ4; [| exact Ha| intros Xa; apply Nw; left; right; clear - Xa; lia].
    apply AGM3; [exact Ha| | subst sh; unfold SB in Nw; clear - Nw; lia| clear - Nw; lia].
    destruct (Z_lt_le_dec a F) as [Y|Y]; [left; exact Y| right]. destruct (Z_lt_le_dec a (F + 8)) as [Z0|Z0]; [exfalso; apply Nw; left; left; left; clear - Y Z0; lia| exact Z0].
  - exact FL0.
  - apply (L5C.u8_at_agree RSEGS M1v M4v); [| clear - pOP; lia| clear - pOP; lia| exact MO1].
    intros i Hi. rewrite FRZ4; [| clear - Hi pOP; lia| clear - Hi pFLOP; lia]. rewrite AG3; [reflexivity| clear - Hi pOP; lia| clear - Hi pOP pOPN SHR; subst sh; lia].
  - exact Hmo.
  - exact E2.
  - intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [assumption|]). destruct Hk.
  - intros k Hk. rewrite (KS4 k) by (revert k Hk; apply (L5K.incl_b [3; 4]%nat); vm_compute; reflexivity). rewrite KQ by (cbn [In] in Hk |- *; clear - Hk; tauto). exact (R134 k Hk).
  - destruct POST as [X|(X1 & X2)]; [left; exact X| right; split; [exact X1| exact X2]].
  - exact INV5.
  - exact LEN5.
  - exact ROOM5.
Qed.

End WithHeap.
End PNARVF.
