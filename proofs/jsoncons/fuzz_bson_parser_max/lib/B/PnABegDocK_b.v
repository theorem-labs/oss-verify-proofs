(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality Permutation.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5CoreKit L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5CoreSpecsA_b L5StepAR_b L5CoreBR_b L5ADetailHR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmParSpecs PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PnSpecsAa_b
     PmModelFactsA_b PnStepA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PgSrc PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnLayout PnModel PnModelFacts PnStatics PnStaticsA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b PnRunAa_b PnASrcKit_b PmAUarK_b PmAUar_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnBrObj. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnBrObjA_b PnAParKit_b PnAReset1_b PnOwnerOkA_b PnBrKitA_b PnABegDocP_b Ba0_code_ad9e4_ad9e8_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

From stdpp Require list_relations list_basics.

Module PNABDK.
Import L5A. Import L5CA. Import L5SAR. Import PNBKA.

(* [comment removed for export] *)
Definition spill (M : mem) (E F : Z) : Prop :=
  L5.u64_at RSEGS M (E - 128) F.
Lemma spill_agree M M' E F : 0 <= E - 128 -> E <= 2 ^ 64 ->
  spill M E F -> (forall a, E - 128 <= a < E - 104 -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> spill M' E F.
Proof.
  intros H0 H1 C1 AG. unfold spill in *.
  eapply L5C.u64_at_agree; [ | | | eassumption]; [intros j Hj; apply AG; lia | lia | lia].
Qed.

Lemma div8_add op o : op mod 8 = 0 -> 0 <= o -> (op + o) / 8 = op / 8 + o / 8.
Proof.
  intros H8 Ho. pose proof (Z.div_mod op 8 ltac:(lia)) as Dm. rewrite H8, Z.add_0_r in Dm. rewrite Dm at 1. rewrite Z.mul_comm. rewrite Z.div_add_l by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Definition pfacts (MV : mem) (sp op F fl : Z) : Prop :=
  L5.img_clear MV 65536 1282048 /\ L5.u64_at RSEGS MV 1309752 2147450880 /\ L5.u32_at RSEGS MV 1309760 1
  /\ 140735332487296 <= sp <= 140737488355328 /\ sp mod 32 = 0 /\ L5.writable RSEGS MV (sp - 160) 160
  /\ 6905856 <= op <= 140737488354912 /\ op mod 8 = 0 /\ (2147446784 + 17592186048512 <= op \/ op + 416 <= 2147446784)
  /\ L5KA.zeros_at MV ((op / 8) + 2147450880) 2 /\ L5KA.zeros_at MV (((op + 10) / 8) + 2147450880) 1 /\ L5KA.zeros_at MV (((op + 312) / 8) + 2147450880) 1 /\ L5KA.zeros_at MV (((op + 392) / 8) + 2147450880) 3
  /\ ((sp - 160) + 160 <= op \/ op + 416 <= (sp - 160))
  /\ 6905856 <= F <= 140737488355264 /\ F mod 32 = 0 /\ L5.defined MV F 64 /\ L5.writable RSEGS MV F 64
  /\ (2147446784 + 17592186048512 <= F \/ F + 64 <= 2147446784) /\ L5.writable RSEGS MV ((F / 8) + 2147450880) 8
  /\ L5.u64_at RSEGS MV (F + 56) fl /\ 4096 <= fl <= 140737488355327 /\ L5.writable RSEGS MV fl 1
  /\ (2147446784 + 17592186048512 <= fl \/ fl + 1 <= 2147446784) /\ (F + 64 <= fl \/ fl + 1 <= F)
  /\ ((sp - 160) + 160 <= F \/ F + 64 <= (sp - 160)) /\ ((sp - 160) + 160 <= fl \/ fl + 1 <= (sp - 160))
  /\ (op + 416 <= F \/ F + 64 <= op) /\ (op + 416 <= fl \/ fl + 1 <= op)
  /\ (((op / 8) + 2147450880) + 52 <= ((F / 8) + 2147450880) \/ ((F / 8) + 2147450880) + 8 <= ((op / 8) + 2147450880))
  /\ 0 <= sp < 2 ^ 64 /\ 0 <= op < 2 ^ 64 /\ 0 <= F < 2 ^ 64 /\ 0 <= fl < 2 ^ 64.


Section WithDefs.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (HI : asan_iface).

(* [comment removed for export] *)
Definition bd_kont (K : TSet) (R : bvmap 5 word) (M : mem) (model : Model) (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z))
           (cr : credit) (sp r fb cat e : Z) (s : PNM.bpst) (str : PM.vstr) (sm : PM.strm) (ax : PNST.bax) (w : Z) : Prop :=
  forall (fx' : FPState) (R' : bvmap 5 word) (M' : mem) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (s' : PNM.bpst) (sm' : PM.strm) (ax' : PNST.bax) (cr' : credit),
    regs_preserved R R' ->
    PNRA.brun_post RSEGS PMA.AD PMA.AN PMA.AAD false PNRA.bprog_value R' M' fb s s' str sm sm' ax ax' cat e ->
    ahpres L ar LBX FF sp 26624 (PNRA.W_brun PMA.AD PMA.AN fb) M M' ->
    PMSP.credit_keep cr cr' (pot L ar s) (pot L ar s') ->
    model_rt model model' -> incl LK' LK -> incl Aw Aw' -> amodel_ok Aw' model' -> ri_inv HI (PNM.bparser_own s' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
    srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K.

(* [comment removed for export] *)
Definition bd_ctx (K : TSet) (R : bvmap 5 word) (M : mem) (model : Model) (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z))
           (cr : credit) (sp r fb cat e : Z) (s : PNM.bpst) (str : PM.vstr) (sm : PM.strm) (ax : PNST.bax) (w : Z) : Prop :=
  (w = 0 \/ w = 1) /\ ri_inv HI (PNM.bparser_own s ++ LBX) FF LK cr Aw M (vml_of model) /\ amodel_ok Aw model /\ K [] /\ PMSPA.entryA PMA.AD L ar R M sp r 7
  /\ PGSA.ffroomB PNRA.FCB 7 FF LK /\ PMSPA.ffrsA FF sp /\ PNRA.frame_okB FF fb /\ sp mod 32 = 0 /\ PNRA.bargs3 PMA.AD R fb s sm
  /\ PNRA.brun_pre RSEGS PMA.AD PMA.AN PMA.AAD M fb s str sm ax /\ incl (PM.vs_own str) LBX /\ PNRA.binv s /\ PMSPA.ec_at RSEGS M (fb + 1024) e cat /\ 0 <= e <= 64
  /\ PM.unread (PNM.b_src s) sm < 2 ^ 26 /\ PMSP.credit_le (pot L ar s) cr
  /\ bd_kont K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w.

(* [comment removed for export] *)
Definition bd_frame (R : bvmap 5 word) (M : mem) (model : Model) (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z))
           (cr : credit) (sp : Z) (s : PNM.bpst) (F fl : Z) (LK2 : list fframe) (M2 : mem) (model2 : Model) : Prop :=
  PMAUK.gctx L ar HI LBX FF LK Aw sp 26624 (sp - 160) (sp - 104) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PNM.bparser_own s).

(* [comment removed for export] *)
Definition bd_mem (R : bvmap 5 word) (M : mem) (model : Model) (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z))
           (cr : credit) (sp fb : Z) (s : PNM.bpst) (str : PM.vstr) (sm : PM.strm) (ax : PNST.bax) (F : Z)
           (M1 : mem) (model1 : Model) (LK1 : list fframe) (Aw1 : list (Z * Z)) (s1 : PNM.bpst) (sm1 : PM.strm) (ax1 : PNST.bax) (cr1 : credit) : Prop :=
  PMAUK.binv L ar HI M model LBX FF LK Aw sp 26624 (sp - 160) (own sp R) F 0 (PNRA.W_brun PMA.AD PMA.AN fb) (PNM.bparser_own s1) M1 model1 LK1 cr1 Aw1
  /\ PNRA.brun_pre RSEGS PMA.AD PMA.AN PMA.AAD M1 fb s1 str sm1 ax1
  /\ PMSP.src_step (PNM.b_src s) (PNM.b_src s1) sm sm1 /\ PNST.bax_le ax ax1
  /\ PMSP.credit_keep cr cr1 (pot L ar s) (pot L ar s1)
  /\ L5.u8_at RSEGS M1 (F / 8 + 2147450880) 241
  /\ PNM.b_bb s1 = PNM.b_bb s.

End WithDefs.

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
Lemma pfacts_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 :
  bd_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  bd_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  bd_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
  pfacts (mrestrict (ahid Aw1 model1) M1) sp (fb + 464) F fl
  /\ own sp R (mrestrict (ahid Aw1 model1) M1)
  /\ (forall a v, sp - 160 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1 a v -> L5.u64_at RSEGS (mrestrict (ahid Aw1 model1) M1) a v)
  /\ (forall v, L5.u8_at RSEGS M1 (F + 32) v -> L5.u8_at RSEGS (mrestrict (ahid Aw1 model1) M1) (F + 32) v)
  /\ L5.writable RSEGS (mrestrict (ahid Aw1 model1) M1) (fb + 464) 424
  /\ (forall v, L5.u8_at RSEGS (mrestrict (ahid Aw1 model1) M1) (fb + 464 + 8) v <-> L5.u8_at RSEGS M1 (fb + 464 + 8) v)
  /\ (forall a v, sp - 160 <= a -> a + 8 <= sp -> L5.u64_at RSEGS (mrestrict (ahid Aw1 model1) M1) a v -> L5.u64_at RSEGS M1 a v).
Proof.
  intros CTX G LM.
  destruct CTX as (Hw & HH & AM & K0 & ENT & FRM & FRS & FOK & SP32 & ARGS & RPRE & INCS & INV & EC0 & HE & UNR & CRED & KONT).
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 7) with 26624 in *.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof FOK as ((rs & Hfb) & Fal).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _).
  pose proof (WF _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 5) with 2048 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL, F1, F2.
  destruct LM as (BI & RP1 & STEP1 & AXL1 & CK1 & SHC1 & EBB1).
  pose proof G as G'. unfold bd_frame in G'.
  destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 0) with 64 in *. change (64 / 8) with 8 in *.
  pose proof BI as (HH1 & AM1 & MRT1 & INCA1 & INCL1 & ASTK1 & EK1 & DK1 & OWN1 & DSH1).
  set (FF' := (F, 0, sp - 160 + 32) :: FF) in *.
  assert (FOK' : PNRA.frame_okB FF' fb). { split; [exists rs; right; exact Hfb| exact Fal]. }
  destruct RP1 as (PA1 & IA1 & VIS1 & VREF1 & OACC1 & BASE1 & ERR1 & GR1).
  change (PNRA.o_p PMA.AD fb) with (fb + 464) in *. change (PNRA.o_is PMA.AD fb) with (fb + 96) in *. change (PNRA.o_v PMA.AD fb) with (fb + 432) in *.
  change (PNM.PSIZE + 8) with 424 in OACC1.
  pose proof (PNAPAR.op_visB L ar C HI LY HIok _ FF' LK1 cr1 Aw1 M1 model1 fb _ s1 HH1 FOK' PA1 OACC1) as ((O1 & O8 & ONSH) & Zop & OWR & OCE & OVIS & AOP).
  pose proof (PMASK.mach_vis L ar C HI LY HIok _ FF' LK1 cr1 Aw1 M1 model1 HH1 BASE1) as (VM0 & VM1 & VM2).
  pose proof (PMASK.stk_vis L ar C HI LY HIok _ FF' LK1 cr1 Aw1 M1 model1 sp 26624 160 HH1 ASTK1 ltac:(lia)) as (SL160 & SH160 & SWR).
  destruct (PMAUK.vis_facts L ar C HI LYa HIok M model LBX FF LK Aw sp 26624 (sp - 160) (sp - 104) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PNM.bparser_own s) G
              _ (PNM.bparser_own s1) M1 model1 LK1 cr1 Aw1 BI) as ((WS1 & _ & _ & _ & _) & OWNv & (FD1 & FW1 & FSW1 & FLC1 & FLW1) & (FLCc1 & FLV1 & VF1 & VS1 & VSH1)).
  change (ff_bytes 0) with 64 in *. change (64 / 8) with 8 in *. replace (F + 64 - 8) with (F + 56) in FLC1 by (clear; lia).
  set (op := fb + 464) in *.
  set (MV := mrestrict (ahid Aw1 model1) M1) in *.
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ _ LK1 cr1 Aw1 M1 model1 HH1) as (_ & VISs & _).
  (* [comment removed for export] *)
  assert (CLo : forall a, fb + 32 <= a < fb + 2040 -> aclient L ar LBX FF sp 26624 a).
  { intros a Ha. unfold aclient, aclient_g. do 3 right; left. exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd].
    change (ff_bytes 5) with 2048. split; [clear - Ha; lia| intros Y; clear - Ha Y; lia]. }
  assert (CLs : forall a, fb / 8 + SB <= a < fb / 8 + SB + 256 -> aclient L ar LBX FF sp 26624 a).
  { intros a Ha. unfold aclient, aclient_g. do 5 right; left. exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd].
    change (ff_bytes 5) with 2048. unfold in_shadow_of, S. unfold SB in *.
    assert (D1 : (fb + 2048 - 1) / 8 = fb / 8 + 255).
    { pose proof (Z.div_mod fb 2048 ltac:(lia)) as Dm. rewrite Fal, Z.add_0_r in Dm. rewrite Dm.
      replace (2048 * (fb / 2048) + 2048 - 1) with (7 + (256 * (fb / 2048) + 255) * 8) by (clear; lia). rewrite Z.div_add by lia.
      replace (2048 * (fb / 2048)) with ((256 * (fb / 2048)) * 8) by (clear; lia). rewrite Z.div_mul by lia. clear; lia. }
    rewrite D1. clear - Ha. lia. }
  assert (SHop : op / 8 + SB = fb / 8 + SB + 58).
  { unfold op. pose proof (Z.div_mod fb 2048 ltac:(lia)) as Dm. rewrite Fal, Z.add_0_r in Dm. rewrite Dm.
    replace (2048 * (fb / 2048) + 464) with ((256 * (fb / 2048) + 58) * 8) by (clear; lia). rewrite Z.div_mul by lia.
    replace (2048 * (fb / 2048)) with ((256 * (fb / 2048)) * 8) by (clear; lia). rewrite Z.div_mul by lia. clear; lia. }
  assert (SF1 : S (F + 64 - 1) = F / 8 + SB + 7).
  { unfold S. destruct GF8 as (X1 & X2 & X3). rewrite X2. clear; lia. }
  assert (NF : forall a, fb + 32 <= a < fb + 2040 -> ~ (F <= a < F + 64)).
  { intros a Ha X. apply (GNCF a); [left; exact X| exact (CLo a Ha)]. }
  assert (NFS : forall a, fb / 8 + SB <= a < fb / 8 + SB + 256 -> ~ (F / 8 + SB <= a < F / 8 + SB + 8)).
  { intros a Ha X. apply (GNCF a); [right; unfold S at 1; rewrite SF1; clear - X; lia| exact (CLs a Ha)]. }
  assert (NFL : forall a, fb + 32 <= a < fb + 2040 -> a <> fl).
  { intros a Ha X. subst a. apply GFLNC. apply L5SAR.aclient_cons. apply (L5SAR.aclient_00 L ar LBX FF sp 26624 fl). exact (CLo fl Ha). }
  assert (ApF : op + 416 <= F \/ F + 64 <= op) by (apply iv_apart; [clear; lia| clear; lia| intros a Ha; apply NF; clear - Ha; unfold op in Ha; lia]).
  assert (ApFL : op + 416 <= fl \/ fl + 1 <= op).
  { destruct (Z_lt_le_dec fl op) as [X|X]; [right; clear - X; lia|]. destruct (Z_lt_le_dec fl (op + 416)) as [Y|Y]; [exfalso; apply (NFL fl); [clear - X Y; unfold op in X, Y; lia| reflexivity]| left; exact Y]. }
  assert (ApS : ((op / 8) + 2147450880) + 52 <= ((F / 8) + 2147450880) \/ ((F / 8) + 2147450880) + 8 <= ((op / 8) + 2147450880)).
  { change 2147450880 with SB. apply iv_apart; [clear; lia| clear; lia| intros a Ha; apply NFS; clear - Ha SHop; lia]. }
  (* [comment removed for export] *)
  assert (SVV : forall a v0, sp - 160 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1 a v0 -> L5.u64_at RSEGS MV a v0).
  { intros a v0 Ha1 Ha2 X. apply (proj2 (L5A.u64_at_vis _ M1 a v0 (VISs a 8 ltac:(clear - Ha1 SL160 SPT; lia) ltac:(clear - Ha2 SHI SPT; lia)) ltac:(clear - Ha1 SL160 SPT; lia) ltac:(clear - Ha2 SHI SPT; lia))). exact X. }
  assert (CV : forall v, L5.u8_at RSEGS M1 (F + 32) v -> L5.u8_at RSEGS MV (F + 32) v).
  { intros v X. apply (proj2 (L5A.u8_at_vis _ M1 (F + 32) v (L5A.avis_sub _ F 64 (F + 32) 1 VF1 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - GFR; lia) ltac:(clear - GFR; lia))). exact X. }
  assert (Zz0 : L5KA.zeros_at MV (op / 8 + 2147450880) 2). { intros i Hi. apply Zop. clear - Hi; lia. }
  assert (Zz1 : L5KA.zeros_at MV ((op + 10) / 8 + 2147450880) 1).
  { intros i Hi. replace ((op + 10) / 8 + 2147450880 + i) with (op / 8 + SB + (1 + i)) by (unfold SB; rewrite (div8_add op 10 O8 ltac:(clear; lia)); change (10 / 8) with 1; clear; lia).
    apply Zop. clear - Hi; lia. }
  assert (Zz2 : L5KA.zeros_at MV ((op + 312) / 8 + 2147450880) 1).
  { intros i Hi. replace ((op + 312) / 8 + 2147450880 + i) with (op / 8 + SB + (39 + i)) by (unfold SB; rewrite (div8_add op 312 O8 ltac:(clear; lia)); change (312 / 8) with 39; clear; lia).
    apply Zop. clear - Hi; lia. }
  assert (Zz3 : L5KA.zeros_at MV ((op + 392) / 8 + 2147450880) 3).
  { intros i Hi. replace ((op + 392) / 8 + 2147450880 + i) with (op / 8 + SB + (49 + i)) by (unfold SB; rewrite (div8_add op 392 O8 ltac:(clear; lia)); change (392 / 8) with 49; clear; lia).
    apply Zop. clear - Hi; lia. }
  assert (Z3 : L5KA.zeros_at MV ((op + 392) / 8 + 2147450880) 3).
  { intros i Hi. replace ((op + 392) / 8 + 2147450880 + i) with (op / 8 + SB + (49 + i)).
    - apply Zop. clear - Hi; lia.
    - unfold SB. replace (op + 392) with (op + 49 * 8) by (clear; lia). rewrite Z.div_add by (clear; lia). clear; lia. }
  assert (SVR : forall a v0, sp - 160 <= a -> a + 8 <= sp -> L5.u64_at RSEGS MV a v0 -> L5.u64_at RSEGS M1 a v0).
  { intros a v0 Ha1 Ha2 X. apply (proj1 (L5A.u64_at_vis _ M1 a v0 (VISs a 8 ltac:(clear - Ha1 SL160 SPT; lia) ltac:(clear - Ha2 SHI SPT; lia)) ltac:(clear - Ha1 SL160 SPT; lia) ltac:(clear - Ha2 SHI SPT; lia))). exact X. }
  split; [| split; [exact OWNv| split; [exact SVV| split; [exact CV| split; [exact OWR| split; [intros v; apply (L5A.u8_at_vis _ M1 (op + 8) v (OVIS (op + 8) 1 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - O1; lia) ltac:(clear - O1; lia))| exact SVR]]]]]].
  unfold pfacts. unfold SB in FSW1.
  split; [exact VM0|]. split; [exact VM1|]. split; [exact VM2|].
  split; [clear - SL160 SHI SPT; lia|]. split; [exact SP32|]. split; [exact SWR|].
  split; [clear - O1; lia|]. split; [exact O8|]. split; [clear - ONSH; lia|]. split; [exact Zz0|]. split; [exact Zz1|]. split; [exact Zz2|]. split; [exact Zz3|]. split; [clear - OCE SL160; lia|].
  split; [clear - GFR; lia|]. split; [exact GF32|]. split; [exact FD1|]. split; [exact FW1|]. split; [exact GFBIG|]. split; [exact FSW1|].
  split; [exact FLC1|]. split; [clear - GFLR; lia|]. split; [exact FLW1|]. split; [exact GFLBIG|]. split; [exact GFLA|].
  split; [clear - GFCEIL GSLO; lia|]. split; [clear - GFLR GSLO; lia|].
  split; [exact ApF|]. split; [exact ApFL|]. split; [exact ApS|].
  clear - SL160 SHI SPT O1 GFR GFLR. lia.
Qed.


(* [comment removed for export] *)
Lemma bd_call_mkec K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 (fx1 : FPState) R1 (ra v e1 c1 : Z) :
  PNRAa.make_ec_spec L ar HI ->
  bd_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  bd_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  bd_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
  PMSPA.ec_at RSEGS M1 (fb + 1024) e1 c1 ->
  getr R1 (reg 1) = Z_to_bv 64 ra -> L5.ra_ok ra -> getr R1 (reg 2) = Z_to_bv 64 (sp - 160) ->
  getr R1 (reg 3) = Z_to_bv 64 (pa_gp PMA.AD) -> getr R1 (reg 4) = Z_to_bv 64 (hl_tp L) ->
  getr R1 (reg 10) = Z_to_bv 64 (fb + 1024) -> getr R1 (reg 11) = Z_to_bv 64 v -> 1 <= v <= 64 ->
  (forall (fx2 : FPState) R2 (M3 : mem) model3 LK3 Aw3,
      regs_preserved R1 R2 -> PMSPA.ec_at RSEGS M3 (fb + 1024) v (pa_errcat_obj PMA.AD) ->
      bd_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK3 Aw3 s1 sm1 (PNST.bax_add_cat ax1) cr1 ->
      (forall a, sp - 128 <= a < sp - 104 -> M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx2 R2 ra M3 model3) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 (pa_make_ec PMA.AD) M1 model1) K.
Proof.
  intros MKE CTX G LM EC1 X1 RAok X2 X3 X4 X10 X11 Hv KR.
  pose proof CTX as (Hw & HH & AM & K0 & ENT & FRM & FRS & FOK & SP32 & ARGS & RPRE & INCS & INV & EC0 & HE & UNR & CRED & KONT).
  destruct ENT as (Rra & RAok0 & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 7) with 26624 in *. change (26624 / 8) with 3328 in STKSH.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof FOK as ((rs & Hfb) & Fal).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _).
  pose proof (WF _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 5) with 2048 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL, FSIMG, F1, F2.
  rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in FSIMG.
  assert (FBI : 6905856 <= fb) by (clear - F1 FSAPP FSIMG; lia).
  pose proof LM as (BI & RP1 & STEP1 & AXL1 & CK1 & SHC1 & EBB1).
  pose proof G as G'. unfold bd_frame in G'.
  destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 0) with 64 in *. change (64 / 8) with 8 in *.
  pose proof BI as (HH1 & AM1 & MRT1 & INCA1 & INCL1 & ASTK1 & EK1 & DK1 & OWN1 & DSH1).
  set (FF' := (F, 0, sp - 160 + 32) :: FF) in *.
  assert (FOK' : PNRA.frame_okB FF' fb). { split; [exists rs; right; exact Hfb| exact Fal]. }
  pose proof RP1 as (PA1 & IA1 & VIS1 & VREF1 & OACC1 & BASE1 & ERR1 & GR1).
  change (PNRA.o_p PMA.AD fb) with (fb + 464) in PA1, IA1, VIS1, VREF1, OACC1. change (PNRA.o_is PMA.AD fb) with (fb + 96) in PA1, IA1. change (PNRA.o_v PMA.AD fb) with (fb + 432) in VIS1, VREF1.
  change (PNM.PSIZE + 8) with 424 in OACC1.
  pose proof (PNAPAR.op_visB L ar C HI LY HIok _ FF' LK1 cr1 Aw1 M1 model1 fb _ s1 HH1 FOK' PA1 OACC1) as ((O1 & O8 & ONSH) & Zop & OWR & OCE & OVIS & AOP).
  set (op := fb + 464) in *. set (ois := fb + 96) in *. set (oec := fb + 1024) in *.
  set (WR := PNRA.W_brun PMA.AD PMA.AN fb) in *.
  pose proof FSAPP as (FA0 & FA1 & FA2). unfold BIGSHADOW_LO, BIGSHADOW_HI in FA1.
  assert (WAPPR : PMKA.wapp WR).
  { unfold WR, PNRA.W_brun, PGS.W_srcfG, PNST.berr_W, PNST.cat_W, PNST.dec_W, PNRA.o_src, PNRA.o_is, PNRA.o_bb, PNRA.o_nb, PNRA.o_tb, PNRA.o_stk, PNRA.o_ec, PNRA.o_p, PMSP.o_p, PMSP.o_is, PMSP.o_ec.
    cbn [app pa_off_p pa_off_is pa_off_ec pa_errcat_guard pa_atexit PMA.AD ADDR_A PMA.AN NADDR_A PNL.pn_inf_guard PNL.pn_nan_guard PNL.pn_inf_obj PNL.pn_nan_obj].
    unfold PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK.
    repeat apply PMKA.wapp_cons; [..| apply PMKA.wapp_nil]; cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct FA1 as [FA1|FA1]; clear - FA0 FA1 FA2 F1 F2; lia. }
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH1) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDF1 & _).
  pose proof EC1 as (_ & _ & ECD1 & ECA1).
  pose proof GFR as (GF1 & GF2 & _).
  assert (R4a : 0 <= F / 8 + 2147450880) by (clear - GF1; lia).
  assert (R4b : F / 8 + 2147450880 + 1 <= 2 ^ 64) by (clear - GF2; pose proof (Z.div_le_upper_bound F 8 17592186044408 ltac:(lia) ltac:(lia)); lia).
  assert (AOE : PMSPA.aobjA FF oec 16) by (apply (PNAPAR.aobj_fbB FF fb oec 16 FOK); unfold oec; clear; lia).
  unfold PNRAa.make_ec_spec, PNRA.make_ec_spec in MKE.
  apply (MKE fx1 R1 M1 model1 K (PNM.bparser_own s1 ++ LBX) FF' LK1 Aw1 cr1 oec v (sp - 160) ra ax1 HH1 AM1 K0).
  { unfold PMSPA.entryA. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact X1|]. split; [exact RAok|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|].
    change (PMSPA.pm_scr 1) with 14336. change (14336 / 8) with 1792.
    split; [apply (L5SAR.astk_sub ar M1 M1 sp 26624 160 14336 ASTK1 (mem_grows_refl M1)); [clear; lia| clear; lia| clear; lia| replace (sp - 160) with (sp + (-10) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact A16]|].
    apply (PMKA.shadow_zero_sub M1 (sp - 26624) 3328); [| | clear; lia| clear; lia| clear; lia|].
    - apply PMKA.mod16_8'. replace (sp - 26624) with (sp + (-1664) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16.
    - apply PMKA.mod16_8'. replace (sp - 160 - 14336) with (sp + (-906) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16.
    - apply (PMKA.stksh_keepA L ar LBX FF sp 26624 WR M M1 EK1 WAPPR (sp - 26624) 3328); [clear - SLO SPT; lia| clear - SLO; lia| clear - SHI SPT; lia| | clear; lia| exact STKSH].
      apply PMKA.mod16_8'. replace (sp - 26624) with (sp + (-1664) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  { apply (PMAUAR.ffroomB_push PNRA.FCB 7 1 FF LK LK1 _ FRM INCL1); [exact NDF1| clear; lia]. }
  { apply (PMAUAR.ffrsA_push FF sp (sp - 160) F 0 (sp - 160 + 32) FRS); clear; lia. }
  { rewrite L5K.rl10. exact X10. } { rewrite L5K.rl11. exact X11. } { exact Hv. }
  { apply PMAUAR.aobjA_push. exact AOE. }
  { unfold oec. pose proof (Z.div_mod fb 2048 ltac:(lia)) as Dm. rewrite Fal, Z.add_0_r in Dm. rewrite Dm.
    replace (2048 * (fb / 2048) + 1024) with ((256 * (fb / 2048) + 128) * 8) by (clear; lia). apply Z_mod_mult. }
  { exact ECD1. } { exact ECA1. } { exact BASE1. } { exact ERR1. }
  intros fx6 R6 M6 model6 LK6 Aw6 RP6 EC6 ERR6 HP6 MRT6 INCL6 INCA6 AM6 HH6.
  change (PMSPA.pm_scr 1) with 14336 in HP6.
  set (Wc6 := (oec, 16) :: (if PNST.bax_cat ax1 then [] else PNST.cat_W PMA.AD)) in HP6.
  assert (Wc6R : forall rr a, In rr Wc6 -> L5.in_rng rr a -> (oec <= a < oec + 16) \/ ((0x6722c0 <= a < 0x6722c2) \/ (0x693d50 <= a < 0x693f70))).
  { intros rr a Hin Hr. unfold Wc6 in Hin. destruct Hin as [<-|Hin]; [left; exact Hr|]. right. destruct (PNST.bax_cat ax1); [destruct Hin|].
    unfold PNST.cat_W in Hin. cbn [pa_errcat_guard pa_atexit PMA.AD ADDR_A] in Hin. unfold L5.in_rng in Hr.
    destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; clear - Hr; lia. }
  assert (DF1 : 0 <= F / 8) by (apply Z.div_pos; clear - GF1; lia).
  assert (DF2 : F / 8 <= 17592186044408) by (apply Z.div_le_upper_bound; clear - GF2; lia).
  assert (WAV : forall rr a, In rr Wc6 -> L5.in_rng rr a -> ~ (sp - 160 <= a < sp) /\ ~ (F / 8 + SB <= a < F / 8 + SB + 8)).
  { intros rr a Hin Hr. unfold SB. destruct (Wc6R rr a Hin Hr) as [X|X].
    - unfold oec in X. split; [clear - X GSLO F2 FSCEIL; lia| destruct FA1 as [Y|Y]; clear - X Y DF1 DF2 F1 F2; lia].
    - split; [clear - X GSLO GSHI GSPT; lia| clear - X DF1; lia]. }
  assert (WOUT : forall a, aclient L ar LBX FF sp 26624 a -> L5.outside WR a -> L5.outside Wc6 a).
  { intros a Hc Ho rr Hin Hr. destruct (Wc6R rr a Hin Hr) as [X|X].
    - apply (Ho (PNRA.o_ec PMA.AD fb, 16)); [unfold WR, PNRA.W_brun, PGS.W_srcfG; cbn [app]; do 8 right; left; reflexivity| unfold L5.in_rng, PNRA.o_ec, PMSP.o_ec; cbn [fst snd pa_off_ec PMA.AD PnLayoutA_b.ADDR_A]; unfold oec in X; clear - X; lia].
    - unfold Wc6 in Hin. destruct Hin as [<-|Hin]; [unfold L5.in_rng in Hr; cbn [fst snd] in Hr; unfold oec in Hr; clear - Hr X FBI; lia|].
      destruct (PNST.bax_cat ax1); [destruct Hin|]. unfold PNST.cat_W in Hin. destruct Hin as [<-|[<-|[]]].
      + apply (Ho (pa_errcat_guard PMA.AD, 2)); [unfold WR, PNRA.W_brun, PGS.W_srcfG, PNST.berr_W, PNST.cat_W; cbn [app]; do 9 right; left; reflexivity| exact Hr].
      + apply (Ho (pa_atexit PMA.AD, 544)); [unfold WR, PNRA.W_brun, PGS.W_srcfG, PNST.berr_W, PNST.cat_W; cbn [app]; do 10 right; left; reflexivity| exact Hr]. }
  assert (BI6 : PMAUK.binv L ar HI M model LBX FF LK Aw sp 26624 (sp - 160) (own sp R) F 0 WR (PNM.bparser_own s1) M6 model6 LK6 cr1 Aw6).
  { apply (PMAUK.binv_callee L ar C HI HIok M model LBX FF LK Aw sp 26624 (sp - 160) (sp - 104) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PNM.bparser_own s) G
             WR WR (PNM.bparser_own s1) (PNM.bparser_own s1) (PNM.bparser_own s1) M1 model1 LK1 cr1 Aw1 M6 model6 LK6 cr1 Aw6 14336 Wc6 BI HP6 HH6 AM6 MRT6 INCA6 INCL6);
      [clear; lia| clear; lia| intros rr a Hin Hr; destruct (WAV rr a Hin Hr) as (Y1 & Y2); split; [unfold ocell; clear - Y1; lia| exact Y2]| exact WOUT| intros a X; exact X]. }
  pose proof (L5SAR.ek_callee L ar (PNM.bparser_own s1 ++ LBX) [] FF [(F, 0, sp - 160 + 32)] sp 26624 (sp - 160) 14336 Wc6 Wc6 M1 M6 HP6 ltac:(clear; lia) ltac:(clear; lia) (fun a _ X => X)) as EK16.
  assert (WAPP6 : PMKA.wapp Wc6).
  { intros rr Hin. unfold BIGSHADOW_LO, BIGSHADOW_HI. unfold Wc6 in Hin. destruct Hin as [<-|Hin]; cbn [fst snd].
    - unfold oec. destruct FA1 as [Y|Y]; clear - Y F1 F2; lia.
    - destruct (PNST.bax_cat ax1); [destruct Hin|]. unfold PNST.cat_W in Hin. cbn [pa_errcat_guard pa_atexit PMA.AD ADDR_A] in Hin. destruct Hin as [<-|[<-|[]]]; cbn [fst snd]; clear; lia. }
  pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH1) as FRB1. pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH1) as BRB1.
  pose proof (proj1 HP6 : ek L ar (PNM.bparser_own s1 ++ LBX) FF' (sp - 160) 14336 Wc6 M1 M6) as EK6.
  assert (OUTB : forall q m, In (q, m) (PNM.bparser_own s1 ++ LBX) -> forall i, q <= i < q + m -> L5.outside Wc6 i).
  { intros q m Hq i Hi rr Hin Hr. destruct (Wc6R rr i Hin Hr) as [Y|Y].
    - destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q m oec 16 HH1 Hq (PMAUAR.aobjA_push FF oec 16 _ AOE)) as [Z0|Z0]; clear - Hi Y Z0; lia.
    - pose proof (PMASK.blk_img L ar C HI LY HIok _ _ _ _ _ _ _ q m HH1 Hq) as Z0. destruct Z0 as [Z0|Z0]; clear - Hi Y Z0; lia. }
  assert (OUTo : forall i, op <= i < op + 416 -> L5.outside Wc6 i).
  { intros i Hi rr Hin Hr. destruct (Wc6R rr i Hin Hr) as [Y|Y]; [unfold op in Hi; unfold oec in Y; clear - Hi Y; lia| unfold op in Hi; clear - Hi Y FBI; lia]. }
  assert (OUTi : forall i, ois <= i < ois + 272 -> L5.outside Wc6 i).
  { intros i Hi rr Hin Hr. destruct (Wc6R rr i Hin Hr) as [Y|Y]; [unfold ois in Hi; unfold oec in Y; clear - Hi Y; lia| unfold ois in Hi; clear - Hi Y FBI; lia]. }
  assert (PA6 : PNM.bparser_at RSEGS PMA.AD PMSPA.accA PMSPA.annA (pa_vp_parser PMA.AD) M6 op ois s1).
  { apply (PNAPAR.bparser_keepA L ar C HI HIok _ FF' LK1 cr1 Aw1 (vml_of model1) Wc6 (sp - 160) 14336 M1 M6 op ois s1 HH1 EK6 WAPP6); [| apply incl_appl; apply incl_refl| exact OUTo| | exact PA1].
    - apply PMAUAR.aobjA_push. apply (PNAPAR.aobj_fbB FF fb op PNM.PSIZE FOK); unfold op, PNM.PSIZE; clear; lia.
    - intros B m HB. unfold PMKA.blk_out. apply OUTB. apply in_or_app; left; exact HB. }
  assert (IA6 : PM.iss_at RSEGS PMA.AD PMSPA.accA M6 ois str sm1).
  { apply (PMKA.iss_keepA RSEGS PMA.AD L ar _ FF' (sp - 160) 14336 Wc6 M1 M6 EK6 WAPP6 FRB1 BRB1 ois str sm1); [| | exact OUTi| | exact IA1].
    - apply PMAUAR.aobjA_push. apply (PNAPAR.aobj_fbB FF fb ois 272 FOK); unfold ois; clear; lia.
    - apply incl_appr. exact INCS.
    - intros c0 n0 p0 E0. unfold PMKA.blk_out. apply OUTB. apply in_or_app; right. apply INCS. rewrite E0. left; reflexivity. }
  assert (BASE6 : PMSTA.base_okA RSEGS PMA.AD M6).
  { apply (base_keepW _ FF' (sp - 160) 14336 Wc6 M1 M6 EK6); [| | | | exact BASE1].
    - intros a Ha rr Hin Hr. destruct (Wc6R rr a Hin Hr) as [Y|Y]; [unfold oec in Y; clear - Ha Y FBI; lia| clear - Ha Y; lia].
    - intros a Ha rr Hin Hr. destruct (Wc6R rr a Hin Hr) as [Y|Y]; [unfold oec in Y; clear - Ha Y FBI; lia| clear - Ha Y; lia].
    - intros rr Hin Hr. destruct (Wc6R rr _ Hin Hr) as [Y|Y]; [unfold oec in Y; clear - Y FBI; lia| clear - Y; lia].
    - intros a Ha rr Hin Hr. destruct (Wc6R rr a Hin Hr) as [Y|Y]; [unfold oec in Y; clear - Ha Y FBI; lia| clear - Ha Y; lia]. }
  apply (KR fx6 R6 M6 model6 LK6 Aw6 RP6 EC6).
  - split; [exact BI6|].
    split. { apply (pre_after_call (PNM.bparser_own s1 ++ LBX) FF' (sp - 160) 14336 Wc6 M1 M6 fb s1 s1 str sm1 sm1 ax1 (PNST.bax_add_cat ax1) FRB1 EK6 WAPP6 FOK');
               [| exact RP1| exact PA6| exact IA6| exact GR1| exact BASE6| exact ERR6].
             intros i Hi rr Hin Hr. destruct (Wc6R rr i Hin Hr) as [Y|Y]; [unfold oec in Y; clear - Hi Y; lia| clear - Hi Y FBI; lia]. }
    split; [exact STEP1|]. split; [exact (PNST.bax_le_trans _ _ _ AXL1 (PNST.bax_le_cat ax1))|]. split; [exact CK1|].
    split; [| exact EBB1].
    apply (L5C.u8_at_agree RSEGS M1 M6); [| exact R4a| exact R4b| exact SHC1].
    intros j Hj. apply EK6. split; [clear - Hj R4a R4b; lia|]. split.
    + apply (L5SAR.fframe_shadow_client L ar _ FF' (sp - 160) 14336 F 0 (sp - 160 + 32)); [left; reflexivity|]. change (ff_bytes 0) with 64.
      unfold in_shadow_of, S. rewrite (proj1 (proj2 GF8)). unfold SB. clear - Hj; lia.
    + intros rr Hin Hr. destruct (WAV rr _ Hin Hr) as (_ & Y). apply Y. unfold SB. clear - Hj; lia.
  - intros a Ha. apply EK6. split; [clear - Ha GSLO GSHI GSPT; lia|]. split.
    + apply (L5SAR.stack_client L ar _ FF' (sp - 160) 14336 a); clear - Ha GSLO GSHI GSPT; lia.
    + intros rr Hin Hr. destruct (WAV rr a Hin Hr) as (Y & _). apply Y. clear - Ha; lia.
Qed.


(* [comment removed for export] *)
Lemma bd_fin K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 (fx5 fx9 : FPState) R5 R9 (pc5 mo : Z) (M9v : mem) :
  bd_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  bd_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  bd_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 ->
  msteps RSEGS (st fx5 R5 pc5 (mrestrict (ahid Aw5 model5) M5)) (st fx9 R9 0xaec80 M9v) ->
  mem_grows (mrestrict (ahid Aw5 model5) M5) M9v ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ PMAUK.WretX F fl 0 (fun a => fb + 472 <= a < fb + 473) a -> M9v (Z_to_bv 64 a) = mrestrict (ahid Aw5 model5) M5 (Z_to_bv 64 a)) ->
  L5.u8_at RSEGS M9v fl 0 -> L5.u8_at RSEGS M9v (fb + 472) mo -> (mo = 0 \/ mo = 1) ->
  getr R9 (reg 2) = Z_to_bv 64 sp ->
  (forall k, In k [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R9 (reg k) = Z_to_bv 64 (bv_unsigned (getr R (reg k)))) ->
  (forall k, In k [3; 4]%nat -> getr R9 (reg k) = getr R (reg k)) ->
  ( (exists v, 1 <= v <= 64 /\ PMSPA.ec_at RSEGS M5 (fb + 1024) v (pa_errcat_obj PMA.AD) /\ mo = 0 /\ PNST.bax_cat ax5 = true)
    \/ (PMSPA.ec_at RSEGS M5 (fb + 1024) e cat /\ PNRA.bprog_value R9 M5 s s5 sm sm5) ) ->
  PNRA.binv s5 -> (length (PNM.b_stk s) <= length (PNM.b_stk s5))%nat ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx5 R5 pc5 M5 model5) K.
Proof.
  intros CTX G LM MS9 MG9 FRZ9 FL0 MO9 Hmo Y2 YR Y34 POST INV5 LEN5.
  pose proof CTX as (Hw & HH & AM & K0 & ENT & FRM & FRS & FOK & SP32 & ARGS & RPRE & INCS & INV & EC0 & HE & UNR & CRED & KONT).
  destruct ENT as (Rra & RAok0 & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 7) with 26624 in *. change (26624 / 8) with 3328 in STKSH.
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof RAok0 as (Hr1 & Hr2).
  pose proof FOK as ((rs & Hfb) & Fal).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _).
  pose proof (WF _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 5) with 2048 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL, FSIMG, F1, F2.
  rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in FSIMG.
  assert (FBI : 6905856 <= fb) by (clear - F1 FSAPP FSIMG; lia).
  pose proof LM as (BI & RP1 & STEP1 & AXL1 & CK1 & SHC1 & EBB1).
  pose proof G as G'. unfold bd_frame in G'.
  destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 0) with 64 in *. change (64 / 8) with 8 in *.
  pose proof BI as (HH1 & AM1 & MRT1 & INCA1 & INCL1 & ASTK1 & EK1 & DK1 & OWN1 & DSH1).
  set (FF' := (F, 0, sp - 160 + 32) :: FF) in *.
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
  pose proof (PMK.ret_to RSEGS fx9 R9 M9v 0xaec80 W_ad9e4 r F_ad9e4 eq_refl D_ad9e4 R9ra Hr1 Hr2) as MSr.
  set (Wx := fun a => fb + 472 <= a < fb + 473).
  apply (PMAUK.retire_coreW L ar C HI LYa HIok M model LBX FF LK Aw sp 26624 (sp - 160) (sp - 104) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PNM.bparser_own s) G
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
  { apply (PMAUAR.wret_ek L ar C HI LY HIok LBX FF LK Aw sp 26624 (sp - 160) (sp - 104) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PNM.bparser_own s)
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
    split; [| unfold PNRA.bb_post, s9; cbn [PNBO.set_more PNM.b_bb]; exact EBB1].
    destruct POST as [(v & Hv & EC5 & Hmo0 & CAT)|(EC5 & PROG)].
    + left. exists v. split; [exact Hv|]. split; [exact (ECf _ _ EC5)|]. split; [unfold s9; cbn [PNBO.set_more PNM.b_more]; exact Hmo0|]. split; [exact CAT|].
      split; [unfold s9; cbn [PNBO.set_more PNM.b_stk]; exact LEN5| unfold s9, PNRA.binv; cbn [PNBO.set_more PNM.b_done PNM.b_stk]; exact INV5].
    + right. split; [exact (ECf _ _ EC5)|]. split; [unfold s9, PNRA.binv; cbn [PNBO.set_more PNM.b_done PNM.b_stk]; exact INV5|].
      unfold s9, PNRA.bprog_value. cbn [PNBO.set_more PNM.b_stk PNM.b_src PNM.b_nb PNM.b_tb]. unfold PNRA.bprog_value in PROG.
      unfold PNRA.btop_pos, PNRA.bcs_str in *. cbn [PNBO.set_more PNM.b_stk PNM.b_src PNM.b_nb PNM.b_tb]. exact PROG.
  - exact AHf.
  - unfold s9, PNRA.pot_bparser. cbn [PNBO.set_more PNM.b_sk PNM.b_tb PNM.b_tg PNM.b_nb PNM.b_ng PNM.b_bb PNM.b_bg]. exact CK1.
  - exact MRTf.
  - exact INCL1.
  - exact INCA1.
  - exact AMf.
  - rewrite EO9. exact HHf.
Qed.


(* [comment removed for export] *)
Lemma bd_piece_fr K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1
      (fx1 fx2 : FPState) R1 R2 (pc1 pc2 : Z) (M2v : mem) (W : Z -> Prop) :
  bd_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  bd_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  bd_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
  msteps RSEGS (st fx1 R1 pc1 (mrestrict (ahid Aw1 model1) M1)) (st fx2 R2 pc2 M2v) ->
  mem_grows (mrestrict (ahid Aw1 model1) M1) M2v ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ W a -> M2v (Z_to_bv 64 a) = mrestrict (ahid Aw1 model1) M1 (Z_to_bv 64 a)) ->
  (forall a, W a -> sp - 224 <= a < sp - 104) ->
  (forall (M3 : mem) model3,
      bd_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK1 Aw1 s1 sm1 ax1 cr1 ->
      ahid Aw1 model3 = ahid Aw1 model1 -> mrestrict (ahid Aw1 model1) M3 = M2v ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ W a -> M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> mem_grows M1 M3 ->
      (forall v c, PMSPA.ec_at RSEGS M1 (fb + 1024) v c -> PMSPA.ec_at RSEGS M3 (fb + 1024) v c) ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx2 R2 pc2 M3 model3) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 pc1 M1 model1) K.
Proof.
  intros CTX G LM MS MG FRZ WP KR.
  pose proof CTX as (Hw & HH & AM & K0 & ENT & FRM & FRS & FOK & SP32 & ARGS & RPRE & INCS & INV & EC0 & HE & UNR & CRED & KONT).
  destruct ENT as (Rra & RAok0 & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 7) with 26624 in *.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof FOK as ((rs & Hfb) & Fal).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _).
  pose proof (WF _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 5) with 2048 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL, FSIMG, F1, F2.
  rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in FSIMG.
  assert (FBI : 6905856 <= fb) by (clear - F1 FSAPP FSIMG; lia).
  pose proof LM as (BI & RP1 & STEP1 & AXL1 & CK1 & SHC1 & EBB1).
  pose proof G as G'. unfold bd_frame in G'.
  destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 0) with 64 in *. change (64 / 8) with 8 in *.
  pose proof BI as (HH1 & AM1 & MRT1 & INCA1 & INCL1 & ASTK1 & EK1 & DK1 & OWN1 & DSH1).
  set (FF' := (F, 0, sp - 160 + 32) :: FF) in *.
  assert (FOK' : PNRA.frame_okB FF' fb). { split; [exists rs; right; exact Hfb| exact Fal]. }
  pose proof RP1 as (PA1 & IA1 & VIS1 & VREF1 & OACC1 & BASE1 & ERR1 & GR1).
  change (PNRA.o_p PMA.AD fb) with (fb + 464) in PA1, IA1, VIS1, VREF1, OACC1. change (PNRA.o_is PMA.AD fb) with (fb + 96) in PA1, IA1. change (PNRA.o_v PMA.AD fb) with (fb + 432) in VIS1, VREF1.
  change (PNM.PSIZE + 8) with 424 in OACC1.
  pose proof GFR as (GF1 & GF2 & _).
  assert (R4a : 0 <= F / 8 + 2147450880) by (clear - GF1; lia).
  assert (R4b : F / 8 + 2147450880 + 1 <= 2 ^ 64) by (clear - GF2; pose proof (Z.div_le_upper_bound F 8 17592186044408 ltac:(lia) ltac:(lia)); lia).
  pose proof (PMASK.stk_vis L ar C HI LY HIok _ FF' LK1 cr1 Aw1 M1 model1 sp 26624 160 HH1 ASTK1 ltac:(lia)) as (SL160 & SH160 & SWR).
  set (H1 := ahid Aw1 model1) in *.
  apply (L5SAR.apiece L ar C HI LYa HIok _ FF' LK1 cr1 Aw1 M1 model1 fx1 fx2 R1 pc1 R2 pc2 M2v W K HH1 AM1 MS MG FRZ).
  { intros a Ha Wa. pose proof (WP a Wa) as X. split; [| clear - X GSLO GSHI GSPT FBI; lia].
    unfold aclientw, aclient_g. right; left. split; [clear - X GSLO GSHI GSPT; lia| intros Y; clear - Y; lia]. }
  intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MG3 FR3 VV3.
  assert (EK13 : L5SAR.ek L ar (PNM.bparser_own s1 ++ LBX) FF' (sp - 104) 120 [] M1 M3).
  { intros a (Ha & Hc & _). apply FR3; [exact Ha|]. intros Wa. pose proof (WP a Wa) as X.
    destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF' LK1 cr1 Aw1 M1 _ (sp - 104) 120 a HH1 GSPT Hc) as [Y|Y]; [clear - X Y; lia| clear - X Y GSLO; lia]. }
  pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH1) as FRB1. pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH1) as BRB1.
  assert (ECK : forall v c, PMSPA.ec_at RSEGS M1 (fb + 1024) v c -> PMSPA.ec_at RSEGS M3 (fb + 1024) v c).
  { intros v0 c0 E0. apply (PMKA.ec_keepA RSEGS L ar _ FF' (sp - 104) 120 [] M1 M3 EK13 PMKA.wapp_nil FRB1 (fb + 1024) v0 c0); [| intros i _ rr []| exact E0].
    apply PMAUAR.aobjA_push. apply (PNAPAR.aobj_fbB FF fb (fb + 1024) 16 FOK); clear; lia. }
  apply (KR M3 model3); [| exact HID3| exact VIS3| exact FR3| exact MG3| exact ECK].
  split.
  { pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
    unfold PMAUK.binv. split; [exact HH3|]. split; [exact AM3|]. split; [eapply L5LZ.model_rt_trans; [exact B3| exact MRT3]|].
    split; [exact B4|]. split; [exact B5|]. split; [eapply L5SAR.astk_grows; [exact B6| exact MG3]|].
    split. { eapply L5SAR.ek_trans; [exact B7|]. intros a (Ha & Hc & _). apply FR3; [exact Ha|]. intros Wa. pose proof (WP a Wa) as X.
             destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK cr Aw M _ sp 26624 a HH GSPT (L5SAR.aclient_appb L ar _ (PNM.bparser_own s) FF sp 26624 a Hc)) as [Y|Y];
               [clear - X Y; lia| clear - X Y GSLO; lia]. }
    split; [eapply L5SAR.dk_trans; [exact B8| apply L5SAR.dk_grows; exact MG3]|].
    split. { apply (GOWN M1 M3 B9). intros a Ha. apply FR3; [unfold ocell in Ha; clear - Ha GSPC GSHI GSPT; lia|]. intros Wa. pose proof (WP a Wa) as X. unfold ocell in Ha. clear - Ha X; lia. }
    eapply L5.defined_grows; [exact MG3| exact B10]. }
  split.
  { apply (pre_after_call (PNM.bparser_own s1 ++ LBX) FF' (sp - 104) 120 [] M1 M3 fb s1 s1 str sm1 sm1 ax1 ax1 FRB1 EK13 (PMKA.wapp_nil) FOK'); [intros i _ rr []| exact RP1| | | exact GR1| |].
    - apply (PNAPAR.bparser_keepA L ar C HI HIok _ FF' LK1 cr1 Aw1 (vml_of model1) [] (sp - 104) 120 M1 M3 _ _ s1 HH1 EK13 (PMKA.wapp_nil)); [| apply incl_appl; apply incl_refl| intros i _ rr []| intros B m _ i _ rr []| exact PA1].
      apply PMAUAR.aobjA_push. apply (PNAPAR.aobj_fbB FF fb (fb + 464) PNM.PSIZE FOK); unfold PNM.PSIZE; clear; lia.
    - apply (PMKA.iss_keepA RSEGS PMA.AD L ar _ FF' (sp - 104) 120 [] M1 M3 EK13 (PMKA.wapp_nil) FRB1 BRB1 (fb + 96) str sm1); [| apply incl_appr; exact INCS| intros i _ rr []| intros c0 n0 p0 _ i _ rr []| exact IA1].
      apply PMAUAR.aobjA_push. apply (PNAPAR.aobj_fbB FF fb (fb + 96) 272 FOK); clear; lia.
    - apply (PMASK.base_keep L ar C LY _ FF' (sp - 104) 120 [] M1 M3 EK13); [intros a _ rr []| exact BASE1].
    - apply (berr_keep _ FF' (sp - 104) 120 [] M1 M3 ax1 EK13); [intros a _ rr []| exact ERR1]. }
  split; [exact STEP1|]. split; [exact AXL1|]. split; [exact CK1|]. split; [| exact EBB1].
  apply (L5C.u8_at_agree RSEGS M1 M3); [| exact R4a| exact R4b| exact SHC1].
  intros j Hj. apply FR3; [clear - Hj R4a R4b; lia|]. intros Wj. pose proof (WP _ Wj) as X. clear - X Hj SL160 GSPT GF2.
  pose proof (Z.div_le_upper_bound F 8 17592186044408 ltac:(lia) ltac:(lia)). lia.
Qed.


(* [comment removed for export] *)
Lemma bd_call_read K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 (fx1 : FPState) R1 (ra off kk : Z) :
  PNRAa.src_read_spec L ar HI ->
  bd_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  bd_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  bd_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
  32 <= off -> off + kk <= 56 -> 1 <= kk <= 16 -> aacc M1 (F + off) kk ->
  getr R1 (reg 1) = Z_to_bv 64 ra -> L5.ra_ok ra -> getr R1 (reg 2) = Z_to_bv 64 (sp - 160) ->
  getr R1 (reg 3) = Z_to_bv 64 (pa_gp PMA.AD) -> getr R1 (reg 4) = Z_to_bv 64 (hl_tp L) ->
  getr R1 (reg 10) = Z_to_bv 64 (fb + 464 + 16) -> getr R1 (reg 11) = Z_to_bv 64 (F + off) -> getr R1 (reg 12) = Z_to_bv 64 kk ->
  (forall (fx2 : FPState) R2 (M3 : mem) model3 LK3 Aw3 src3 sm3 d,
      regs_preserved R1 R2 -> getr R2 (reg 10) = Z_to_bv 64 d -> 0 <= d <= kk ->
      PM.unread src3 sm3 = PM.unread (PNM.b_src s1) sm1 - d ->
      (1 <= PM.sr_rem (PNM.b_src s1) -> 1 <= d) -> (d = 0 -> PM.sr_rem src3 = 0 /\ PM.sm_st sm3 = 2) ->
      L5.defined M3 (F + off) d -> PM.sr_qc src3 = PM.sr_qc (PNM.b_src s1) ->
      bd_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK3 Aw3 (PNM.with_srcB s1 src3) sm3 ax1 cr1 ->
      (forall a, sp - 160 <= a < sp - 104 -> M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
      (forall v c, PMSPA.ec_at RSEGS M1 (fb + 1024) v c -> PMSPA.ec_at RSEGS M3 (fb + 1024) v c) ->
      (forall q m a, (In (q, m) (PNM.bparser_own s1) \/ (q = fb + 464 /\ m = 416)) -> q <= a < q + m ->
                     (M1 (Z_to_bv 64 a) <> None -> M3 (Z_to_bv 64 a) <> None) /\ M3 (Z_to_bv 64 (S a)) = M1 (Z_to_bv 64 (S a))) ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx2 R2 ra M3 model3) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 (pa_src_read PMA.AD) M1 model1) K.
Proof.
  intros SR CTX G LM Hoff Hok Hkk ACC X1 RAok X2 X3 X4 X10 X11 X12 KR.
  pose proof CTX as (Hw & HH & AM & K0 & ENT & FRM & FRS & FOK & SP32 & ARGS & RPRE & INCS & INV & EC0 & HE & UNR & CRED & KONT).
  destruct ENT as (Rra & RAok0 & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 7) with 26624 in *. change (26624 / 8) with 3328 in STKSH.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof FOK as ((rs & Hfb) & Fal).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _).
  pose proof (WF _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 5) with 2048 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL, FSIMG, F1, F2.
  rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in FSIMG.
  assert (FBI : 6905856 <= fb) by (clear - F1 FSAPP FSIMG; lia).
  pose proof LM as (BI & RP1 & STEP1 & AXL1 & CK1 & SHC1 & EBB1).
  pose proof G as G'. unfold bd_frame in G'.
  destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 0) with 64 in *. change (64 / 8) with 8 in *.
  pose proof BI as (HH1 & AM1 & MRT1 & INCA1 & INCL1 & ASTK1 & EK1 & DK1 & OWN1 & DSH1).
  set (FF' := (F, 0, sp - 160 + 32) :: FF) in *.
  assert (FOK' : PNRA.frame_okB FF' fb). { split; [exists rs; right; exact Hfb| exact Fal]. }
  pose proof RP1 as (PA1 & IA1 & VIS1 & VREF1 & OACC1 & BASE1 & ERR1 & GR1).
  change (PNRA.o_p PMA.AD fb) with (fb + 464) in PA1, IA1, VIS1, VREF1, OACC1. change (PNRA.o_is PMA.AD fb) with (fb + 96) in PA1, IA1. change (PNRA.o_v PMA.AD fb) with (fb + 432) in VIS1, VREF1.
  change (PNM.PSIZE + 8) with 424 in OACC1.
  pose proof (PNAPAR.op_visB L ar C HI LY HIok _ FF' LK1 cr1 Aw1 M1 model1 fb _ s1 HH1 FOK' PA1 OACC1) as ((O1 & O8 & ONSH) & Zop & OWR & OCE & OVIS & AOP).
  set (op := fb + 464) in *. set (ois := fb + 96) in *.
  set (WR := PNRA.W_brun PMA.AD PMA.AN fb) in *.
  assert (WAPPR : PMKA.wapp WR).
  { unfold WR, PNRA.W_brun, PGS.W_srcfG, PNST.berr_W, PNST.cat_W, PNST.dec_W, PNRA.o_src, PNRA.o_is, PNRA.o_bb, PNRA.o_nb, PNRA.o_tb, PNRA.o_stk, PNRA.o_ec, PNRA.o_p, PMSP.o_p, PMSP.o_is, PMSP.o_ec.
    cbn [app pa_off_p pa_off_is pa_off_ec pa_errcat_guard pa_atexit PMA.AD ADDR_A PMA.AN NADDR_A PNL.pn_inf_guard PNL.pn_nan_guard PNL.pn_inf_obj PNL.pn_nan_obj].
    unfold PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK.
    pose proof FSAPP as (FA0 & FA1 & FA2). unfold BIGSHADOW_LO, BIGSHADOW_HI in FA1.
    repeat apply PMKA.wapp_cons; [..| apply PMKA.wapp_nil]; cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct FA1 as [FA1|FA1]; clear - FA0 FA1 FA2 F1 F2; lia. }
  (* [comment removed for export] *)
  set (O := PNOKA.src_ownerA RSEGS PMA.AD (pa_vp_parser PMA.AD) op ois (fb + 32) (fb + 2040) s1).
  assert (OK : PGSA.owner_ok RSEGS PMA.AD L ar HI O).
  { apply (PNOKA.src_owner_ok RSEGS PMA.AD (pa_vp_parser PMA.AD) L ar HI op ois (fb + 32) (fb + 2040) s1 (HAJ.aior_wf _ _ _ _ _ HIok)).
    - change PNM.PSIZE with 416. unfold op, ois.
      assert (M8 : (fb + 464) mod 8 = 0 /\ (fb + 96) mod 8 = 0).
      { pose proof (Z.div_mod fb 2048 ltac:(lia)) as Dm. rewrite Fal, Z.add_0_r in Dm. split.
        - rewrite Dm. replace (2048 * (fb / 2048) + 464) with ((256 * (fb / 2048) + 58) * 8) by (clear; lia). apply Z_mod_mult.
        - rewrite Dm. replace (2048 * (fb / 2048) + 96) with ((256 * (fb / 2048) + 12) * 8) by (clear; lia). apply Z_mod_mult. }
      clear - M8 F1 F2 FSCEIL GSLO GSHI GSPT FBI. lia.
    - right. unfold op, ois. change PNM.PSIZE with 416. clear; lia. }
  unfold PNRAa.src_read_spec, PNRA.src_read_spec, PGSA.src_read_specG, PGSA.src_specG in SR.
  set (src1 := PNM.b_src s1) in *.
  set (LB1 := PM.src_own src1 ++ PNM.brest_own s1 ++ LBX).
  assert (ELB : PNM.bparser_own s1 ++ LBX = LB1) by (unfold LB1, PNM.bparser_own, src1; rewrite <- app_assoc; reflexivity).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH1) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDF1 & _).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ _ LK1 cr1 Aw1 M1 model1 HH1) as VP; cbv zeta in VP; destruct VP as (_ & _ & _ & VFS & _).
  assert (VSH : avis (ahid Aw1 model1) (F / 8 + SB) 8).
  { destruct (PMAUK.vis_facts L ar C HI LYa HIok M model LBX FF LK Aw sp 26624 (sp - 160) (sp - 104) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PNM.bparser_own s) G
              _ (PNM.bparser_own s1) M1 model1 LK1 cr1 Aw1 BI) as (_ & _ & _ & (_ & _ & _ & _ & X)). exact X. }
  assert (FV : avis (ahid Aw1 model1) F 64) by (apply VFS; [exact GFS1| exact GFS2]).
  assert (DEFc : L5.defined M1 (F + off) kk).
  { destruct (PMAUK.vis_facts L ar C HI LYa HIok M model LBX FF LK Aw sp 26624 (sp - 160) (sp - 104) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PNM.bparser_own s) G
              _ (PNM.bparser_own s1) M1 model1 LK1 cr1 Aw1 BI) as (_ & _ & (FD & _) & _).
    apply (L5.defined_sub M1 F 64); [| clear - Hoff; lia| clear - Hoff Hok Hkk; lia]. exact (proj1 (L5A.defined_vis _ M1 F 64 FV) FD). }
  pose proof GFR as (GF1 & GF2 & _).
  assert (R4a : 0 <= F / 8 + 2147450880) by (clear - GF1; lia).
  assert (R4b : F / 8 + 2147450880 + 1 <= 2 ^ 64) by (clear - GF2; pose proof (Z.div_le_upper_bound F 8 17592186044408 ltac:(lia) ltac:(lia)); lia).
  apply (SR O OK fx1 R1 M1 model1 K (PNM.brest_own s1) LBX FF' LK1 Aw1 cr1 (sp - 160) ra src1 str sm1 [(F + off, kk)]).
  { change (PM.src_own src1 ++ PNM.brest_own s1 ++ LBX) with LB1. rewrite <- ELB. exact HH1. }
  { exact AM1. } { exact K0. }
  { unfold PMSPA.entryA. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact X1|]. split; [exact RAok|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|].
    change (PMSPA.pm_scr 4) with 20480. change (20480 / 8) with 2560.
    split; [apply (L5SAR.astk_sub ar M1 M1 sp 26624 160 20480 ASTK1 (mem_grows_refl M1)); [clear; lia| clear; lia| clear; lia| replace (sp - 160) with (sp + (-10) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact A16]|].
    apply (PMKA.shadow_zero_sub M1 (sp - 26624) 3328); [| | clear; lia| clear; lia| clear; lia|].
    - apply PMKA.mod16_8'. replace (sp - 26624) with (sp + (-1664) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16.
    - apply PMKA.mod16_8'. replace (sp - 160 - 20480) with (sp + (-1290) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16.
    - apply (PMKA.stksh_keepA L ar LBX FF sp 26624 WR M M1 EK1 WAPPR (sp - 26624) 3328); [clear - SLO SPT; lia| clear - SLO; lia| clear - SHI SPT; lia| | clear; lia| exact STKSH].
      apply PMKA.mod16_8'. replace (sp - 26624) with (sp + (-1664) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  { apply (PMAUAR.ffroomB_push PNRA.FCB 7 4 FF LK LK1 _ FRM INCL1); [exact NDF1| clear; lia]. }
  { apply (PMAUAR.ffrsA_push FF sp (sp - 160) F 0 (sp - 160 + 32) FRS); clear; lia. }
  { unfold PGSA.ofr. cbn [O PNOKA.src_ownerA PGS.ow_lo PGS.ow_hi]. apply PMAUAR.aobjA_push. apply (PNAPAR.aobj_fbB FF fb (fb + 32) (fb + 2040 - (fb + 32)) FOK); clear; lia. }
  { rewrite L5K.rl10. cbn [O PNOKA.src_ownerA PGS.ow_os]. unfold PNM.OFF_SRC. exact X10. }
  { unfold PGSA.read_args. exists (F + off), kk. rewrite L5K.rl11, L5K.rl12. split; [exact X11|]. split; [exact X12|]. split; [unfold PM.CHUNK; clear - Hkk; lia|].
    unfold PGSA.dst_okG. left. cbn [O PNOKA.src_ownerA PGS.ow_lo PGS.ow_hi].
    split; [exists (F, 0, sp - 160 + 32); split; [left; reflexivity| cbn [ff_addr ff_class fst snd]; change (ff_bytes 0) with 64; clear - Hoff Hok Hkk; lia]|].
    split; [clear - Hkk; lia|]. split; [exact DEFc|].
    split; [exact ACC|].
    destruct (Z_lt_le_dec (F + off + kk) (fb + 32 + 1)) as [Y|Y]; [left; clear - Y; lia|]. destruct (Z_lt_le_dec (F + off) (fb + 2040)) as [Y'|Y']; [| right; clear - Y'; lia].
    exfalso. apply (GNCF (Z.max (F + off) (fb + 32))); [left; clear - Y Y' Hoff Hok Hkk; lia|]. unfold aclient, aclient_g; do 3 right; left; exists (fb, 5, rs); split; [exact Hfb|].
    cbn [ff_addr ff_class fst snd]; change (ff_bytes 5) with 2048; clear - Y Y' Hkk; lia. }
  { unfold PMPS.read_W. exists (F + off), kk. rewrite L5K.rl11, L5K.rl12. split; [exact X11|]. split; [exact X12|]. split; [clear - GF1 GF2 Hoff Hok Hkk; lia|]. split; [clear - Hkk; lia| reflexivity]. }
  { cbn [O PNOKA.src_ownerA PGS.ow_at]. split; [| reflexivity]. unfold src1. rewrite PNMF.with_srcB_id. exact PA1. }
  { cbn [O PNOKA.src_ownerA PGS.ow_ois]. exact IA1. }
  { exact BASE1. } { exact INCS. }
  intros fx4 R4 M4 model4 LK4 Aw4 src4 sm4 RP4 OW4 IA4 STEP4 RES4 HP4 MRT4 INCL4 INCA4 AM4 HH4.
  cbn [O PNOKA.src_ownerA PGS.ow_at PGS.ow_ois PGS.ow_os] in OW4, IA4, HP4. destruct OW4 as (PA4 & _).
  change (PMSPA.pm_scr 4) with 20480 in HP4. unfold PNM.OFF_SRC in HP4.
  assert (QC4 : PM.sr_qc src4 = PM.sr_qc src1) by (destruct STEP4 as (E4 & _); exact E4).
  change (PM.src_own src1 ++ PNM.brest_own s1 ++ LBX) with LB1 in HH4, HP4. rewrite <- ELB in HH4, HP4.
  pose proof (own_with_srcB s1 src4 QC4) as EOWN4.
  set (Wc := PGS.W_srcG (op + 16) ois src1 ++ [(F + off, kk)]) in HP4.
  (* [comment removed for export] *)
  assert (WcR : forall rr a, In rr Wc -> L5.in_rng rr a ->
            ((fb + 736 <= a < fb + 776) \/ (fb + 136 <= a < fb + 144) \/ (fb + 248 <= a < fb + 252)) \/ (PM.sr_qc src1 <= a < PM.sr_qc src1 + PM.CHUNK) \/ (F + off <= a < F + off + kk)).
  { intros rr a Hin Hr. unfold Wc, PGS.W_srcG, PGS.W_srcfG in Hin. unfold L5.in_rng in Hr.
    apply in_app_or in Hin. destruct Hin as [Hin|Hin].
    - destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hr; unfold op, ois in Hr; [left; left| left; right; left| left; right; right| right; left]; clear - Hr; lia.
    - destruct Hin as [<-|[]]. cbn [fst snd] in Hr. right; right. clear - Hr; lia. }
  assert (Iq : In (PM.sr_qc src1, PM.CHUNK) (PNM.bparser_own s1)) by (unfold PNM.bparser_own, PM.src_own, src1; left; reflexivity).
  pose proof (blk_ceil _ _ _ _ _ _ _ (PM.sr_qc src1) PM.CHUNK HH1 (in_or_app _ _ _ (or_introl Iq))) as (BqC & (_ & BqA & _)). unfold BIGSHADOW_LO, BIGSHADOW_HI, PM.CHUNK in BqA. unfold PM.CHUNK in BqC.
  pose proof (PMASK.blk_img L ar C HI LY HIok _ _ _ _ _ _ _ (PM.sr_qc src1) PM.CHUNK HH1 (in_or_app _ _ _ (or_introl Iq))) as BqI. unfold PM.CHUNK in BqI.
  pose proof FSAPP as (FA0 & FA1 & FA2). unfold BIGSHADOW_LO, BIGSHADOW_HI in FA1.
  assert (DF1 : 0 <= F / 8) by (apply Z.div_pos; clear - GF1; lia).
  assert (DF2 : F / 8 <= 17592186044408) by (apply Z.div_le_upper_bound; clear - GF2; lia).
  assert (WAV : forall rr a, In rr Wc -> L5.in_rng rr a -> ~ (sp - 160 <= a < sp) /\ ~ (F / 8 + SB <= a < F / 8 + SB + 8)).
  { intros rr a Hin Hr. unfold SB. destruct (WcR rr a Hin Hr) as [X|[X|X]].
    - split; [clear - X GSLO F2 FSCEIL; lia| destruct FA1 as [Y|Y]; clear - X Y DF1 DF2 F1 F2; lia].
    - split; [clear - X BqC GSLO; unfold PM.CHUNK in *; lia| clear - X BqA DF1 DF2; unfold PM.CHUNK in *; lia].
    - assert (DF3 : 8 * (F / 8) <= F) by (apply Z.mul_div_le; clear; lia).
      assert (DF4 : F < 8 * (F / 8) + 8) by (pose proof (Z.mod_pos_bound F 8 ltac:(clear; lia)) as Hm; pose proof (Z.div_mod F 8 ltac:(clear; lia)) as Hd; clear - Hm Hd; lia).
      split; [clear - X Hoff Hok Hkk GFCEIL GSLO; lia| clear - X Hoff Hok Hkk DF3 DF4 GF1 GF2 GFBIG; lia]. }
  assert (WOUT : forall a, aclient L ar LBX FF sp 26624 a -> L5.outside WR a -> L5.outside Wc a).
  { intros a Hc Ho rr Hin Hr. destruct (WcR rr a Hin Hr) as [[X|[X|X]]|[X|X]].
    - apply (Ho (PNRA.o_src PMA.AD fb + 256, 40)); [unfold WR, PNRA.W_brun, PGS.W_srcfG; cbn [app]; right; left; reflexivity| unfold L5.in_rng, PNRA.o_src, PNRA.o_p, PMSP.o_p, PNM.OFF_SRC; cbn [fst snd pa_off_p PMA.AD PnLayoutA_b.ADDR_A]; clear - X; lia].
    - apply (Ho (PNRA.o_is PMA.AD fb + 40, 8)); [unfold WR, PNRA.W_brun, PGS.W_srcfG; cbn [app]; right; right; left; reflexivity| unfold L5.in_rng, PNRA.o_is, PMSP.o_is; cbn [fst snd pa_off_is PMA.AD PnLayoutA_b.ADDR_A]; clear - X; lia].
    - apply (Ho (PNRA.o_is PMA.AD fb + 152, 4)); [unfold WR, PNRA.W_brun, PGS.W_srcfG; cbn [app]; right; right; right; left; reflexivity| unfold L5.in_rng, PNRA.o_is, PMSP.o_is; cbn [fst snd pa_off_is PMA.AD PnLayoutA_b.ADDR_A]; clear - X; lia].
    - exfalso. apply (PMARS1.own_not_aclient L ar C HI HIok (PNM.bparser_own s1) LBX FF' LK1 cr1 Aw1 M1 _ (PM.sr_qc src1) PM.CHUNK a sp 26624 HH1 Iq X). apply L5SAR.aclient_cons. exact Hc.
    - exfalso. apply (GNCF a); [left; clear - X Hoff Hok Hkk; lia| exact Hc]. }
  assert (BI4 : PMAUK.binv L ar HI M model LBX FF LK Aw sp 26624 (sp - 160) (own sp R) F 0 WR (PNM.bparser_own s1) M4 model4 LK4 cr1 Aw4).
  { apply (PMAUK.binv_callee L ar C HI HIok M model LBX FF LK Aw sp 26624 (sp - 160) (sp - 104) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PNM.bparser_own s) G
             WR WR (PNM.bparser_own s1) (PNM.bparser_own s1) (PNM.bparser_own s1) M1 model1 LK1 cr1 Aw1 M4 model4 LK4 cr1 Aw4 20480 Wc BI HP4 HH4 AM4 MRT4 INCA4 INCL4);
      [clear; lia| clear; lia| intros rr a Hin Hr; destruct (WAV rr a Hin Hr) as (Y1 & Y2); split; [unfold ocell; clear - Y1; lia| exact Y2]| exact WOUT| intros a X; exact X]. }
  pose proof (L5SAR.ek_callee L ar (PNM.bparser_own s1 ++ LBX) [] FF [(F, 0, sp - 160 + 32)] sp 26624 (sp - 160) 20480 Wc Wc M1 M4 HP4 ltac:(clear; lia) ltac:(clear; lia) (fun a _ X => X)) as EK14.
  assert (WAPPc : PMKA.wapp Wc).
  { intros rr Hin. unfold BIGSHADOW_LO, BIGSHADOW_HI. unfold Wc, PGS.W_srcG, PGS.W_srcfG in Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
    - destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd]; unfold op, ois, PM.CHUNK.
      + destruct FA1 as [Y|Y]; clear - Y F1 F2; lia.
      + destruct FA1 as [Y|Y]; clear - Y F1 F2; lia.
      + destruct FA1 as [Y|Y]; clear - Y F1 F2; lia.
      + clear - BqA; lia.
    - destruct Hin as [<-|[]]. cbn [fst snd]. clear - GFBIG Hoff Hok Hkk; lia. }
  destruct RES4 as (p' & k' & dd & Yp & Yk & Hp' & Hk' & Yd & Hdd & CONS & DEFd & RM1 & RM0).
  assert (Ek : k' = kk).
  { rewrite L5K.rl12 in Yk. rewrite X12 in Yk. apply (f_equal bv_unsigned) in Yk. unfold PM.CHUNK in Hk'. rewrite !L5.unsigned_lit in Yk by (clear - Hk' Hkk; lia). clear - Yk; lia. }
  assert (Ep : p' = F + off).
  { rewrite L5K.rl11 in Yp. rewrite X11 in Yp. apply (f_equal bv_unsigned) in Yp. rewrite !L5.unsigned_lit in Yp by (clear - Hp' GF1 GF2 Hoff Hok Hkk; lia). clear - Yp; lia. }
  subst k' p'. rewrite L5K.rl10 in Yd.
  apply (KR fx4 R4 M4 model4 LK4 Aw4 src4 sm4 dd RP4 Yd Hdd).
  - unfold PMSP.consumed in CONS. clear - CONS; lia.
  - exact RM1.
  - exact RM0.
  - exact DEFd.
  - exact QC4.
  - split; [rewrite EOWN4; exact BI4|].
    split. { apply (pre_after_call (PNM.bparser_own s1 ++ LBX) FF' (sp - 160) 20480 Wc M1 M4 fb s1 _ str sm1 sm4 ax1 ax1 (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH1) (proj1 HP4) WAPPc FOK');
               [| exact RP1| exact PA4| exact IA4| apply pre_with_srcB; exact GR1
                | apply (PMASK.base_keep L ar C LY _ FF' (sp - 160) 20480 Wc M1 M4 (proj1 HP4)); [| exact BASE1]
                | apply (berr_keep _ FF' (sp - 160) 20480 Wc M1 M4 ax1 (proj1 HP4)); [| exact ERR1]].
             2, 3: intros i Hi rr Hin Hr; destruct (WcR rr i Hin Hr) as [[X|[X|X]]|[X|X]]; [clear - Hi X FBI; lia| clear - Hi X FBI; lia| clear - Hi X FBI; lia| unfold PM.CHUNK in X; clear - Hi X BqI; lia| clear - Hi X GFR Hoff Hok Hkk; lia].
             pose proof (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ (PM.sr_qc src1) PM.CHUNK (fb + 432) 8 HH1 (in_or_app _ _ _ (or_introl Iq)) (PMAUAR.aobjA_push FF _ 8 _ (PNAPAR.aobj_fbB FF fb (fb + 432) 8 FOK ltac:(clear; lia) ltac:(clear; lia)))) as Bq1.
             pose proof (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ (PM.sr_qc src1) PM.CHUNK (fb + 880) 8 HH1 (in_or_app _ _ _ (or_introl Iq)) (PMAUAR.aobjA_push FF _ 8 _ (PNAPAR.aobj_fbB FF fb (fb + 880) 8 FOK ltac:(clear; lia) ltac:(clear; lia)))) as Bq2.
             unfold PM.CHUNK in Bq1, Bq2.
             intros i Hi rr Hin Hr. destruct (WcR rr i Hin Hr) as [[X|[X|X]]|[X|X]]; [clear - Hi X; lia| clear - Hi X; lia| clear - Hi X; lia| unfold PM.CHUNK in X; clear - Hi X Bq1 Bq2; lia| clear - Hi X GFR FBI GNCF Hfb Hoff Hok Hkk].
             (* [comment removed for export] *)
             destruct Hi as [Hi|Hi]; (apply (GNCF i); [left; clear - X Hoff Hok Hkk; lia|]; unfold aclient, aclient_g; do 3 right; left; exists (fb, 5, rs); split; [exact Hfb|];
               cbn [ff_addr ff_class fst snd]; change (ff_bytes 5) with 2048; lia). }
    split; [cbn [PNM.with_srcB PNM.b_src]; exact (src_step_trans _ _ _ _ _ _ STEP1 STEP4)|].
    split; [exact AXL1|]. split; [exact CK1|].
    split; [| cbn [PNM.with_srcB PNM.b_bb]; exact EBB1].
    (* [comment removed for export] *)
    apply (L5C.u8_at_agree RSEGS M1 M4); [| exact R4a| exact R4b| exact SHC1].
    intros j Hj. apply (proj1 HP4). split; [clear - Hj R4a R4b; lia|]. split.
    + apply (L5SAR.fframe_shadow_client L ar _ FF' (sp - 160) 20480 F 0 (sp - 160 + 32)); [left; reflexivity|]. change (ff_bytes 0) with 64.
      unfold in_shadow_of, S. rewrite (proj1 (proj2 GF8)). unfold SB. clear - Hj; lia.
    + intros rr Hin Hr. destruct (WAV rr _ Hin Hr) as (_ & Y). apply Y. unfold SB. clear - Hj; lia.
  - intros a Ha. apply (proj1 HP4). split; [clear - Ha GSLO GSHI GSPT; lia|]. split.
    + apply (L5SAR.stack_client L ar _ FF' (sp - 160) 20480 a); clear - Ha GSLO GSHI GSPT; lia.
    + intros rr Hin Hr. destruct (WAV rr a Hin Hr) as (Y & _). apply Y. clear - Ha; lia.
  - intros v0 c0 E0. apply (PMKA.ec_keepA RSEGS L ar _ FF' (sp - 160) 20480 Wc M1 M4 (proj1 HP4) WAPPc (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH1) (fb + 1024) v0 c0); [| | exact E0].
    + apply PMAUAR.aobjA_push. apply (PNAPAR.aobj_fbB FF fb (fb + 1024) 16 FOK); clear; lia.
    + intros i Hi rr Hin Hr. destruct (WcR rr i Hin Hr) as [[X|[X|X]]|[X|X]]; [clear - Hi X; lia| clear - Hi X; lia| clear - Hi X; lia| unfold PM.CHUNK in X | clear - Hi X GFR FBI GNCF Hfb Hoff Hok Hkk].
      * destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ (PM.sr_qc src1) PM.CHUNK (fb + 1024) 16 HH1 (in_or_app _ _ _ (or_introl Iq)) (PMAUAR.aobjA_push FF _ 16 _ (PNAPAR.aobj_fbB FF fb (fb + 1024) 16 FOK ltac:(clear; lia) ltac:(clear; lia)))) as [Z0|Z0]; unfold PM.CHUNK in Z0; clear - Hi X Z0; lia.
      * apply (GNCF i); [left; clear - X Hoff Hok Hkk; lia|]. unfold aclient, aclient_g; do 3 right; left; exists (fb, 5, rs); split; [exact Hfb|]; cbn [ff_addr ff_class fst snd]; change (ff_bytes 5) with 2048; lia.
  - intros q m a Hq Ha.
    assert (AR : 0 <= a < 2 ^ 47 /\ aclient L ar (PNM.bparser_own s1 ++ LBX) FF' (sp - 160) 20480 a /\ aclient L ar (PNM.bparser_own s1 ++ LBX) FF' (sp - 160) 20480 (S a)).
    { destruct Hq as [Hq|(Eq & Em)].
      - assert (HqL : In (q, m) (PNM.bparser_own s1 ++ LBX)) by (apply in_or_app; left; exact Hq).
        pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH1 _ HqL) as (B0 & B1). cbn [fst snd] in B0, B1.
        split; [clear - Ha B0 B1; lia|]. split; [apply (L5SAR.block_client L ar _ FF' (sp - 160) 20480 q m a HqL Ha)|].
        unfold aclient, aclient_g. do 6 right. exists (q, m). split; [exact HqL|]. cbn [fst snd]. unfold in_shadow_of. split; apply PMKA.S_mono; clear - Ha; lia.
      - subst q m. split; [clear - Ha O1; unfold op in *; lia|]. split.
        + apply (L5SAR.fframe_client L ar _ FF' (sp - 160) 20480 fb 5 rs); [right; exact Hfb| change (ff_bytes 5) with 2048; clear - Ha; lia].
        + apply (L5SAR.fframe_shadow_client L ar _ FF' (sp - 160) 20480 fb 5 rs); [right; exact Hfb|]. change (ff_bytes 5) with 2048. unfold in_shadow_of. split; apply PMKA.S_mono; clear - Ha; lia. }
    destruct AR as (Ar & C1 & C2).
    split.
    + intros D. exact (proj2 (proj2 HP4) a ltac:(clear - Ar; lia) C1 D).
    + apply (proj1 HP4). pose proof (PMKA.S_in_shadow a Ar) as S1. unfold BIGSHADOW_LO, BIGSHADOW_HI in S1. split; [clear - S1; lia|]. split; [exact C2|].
      intros rr Hin Hr. destruct (WcR rr _ Hin Hr) as [[X|[X|X]]|[X|X]].
      * destruct FA1 as [Y|Y]; clear - X Y S1 F1 F2; lia.
      * destruct FA1 as [Y|Y]; clear - X Y S1 F1 F2; lia.
      * destruct FA1 as [Y|Y]; clear - X Y S1 F1 F2; lia.
      * unfold PM.CHUNK in X. clear - X S1 BqA. lia.
      * clear - X S1 GFBIG Hoff Hok Hkk. lia.
Qed.

(* [comment removed for export] *)
Lemma set_more_id s : PNBO.set_more s (PNM.b_more s) = s.
Proof. destruct s; reflexivity. Qed.
Lemma bd_piece_sh K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1
      (fx1 fx2 : FPState) R1 R2 (pc1 pc2 : Z) (M2v : mem) (W : Z -> Prop) :
  bd_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  bd_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  bd_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
  msteps RSEGS (st fx1 R1 pc1 (mrestrict (ahid Aw1 model1) M1)) (st fx2 R2 pc2 M2v) ->
  mem_grows (mrestrict (ahid Aw1 model1) M1) M2v ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ W a -> M2v (Z_to_bv 64 a) = mrestrict (ahid Aw1 model1) M1 (Z_to_bv 64 a)) ->
  (forall a, W a -> F / 8 + 2147450880 + 5 <= a < F / 8 + 2147450880 + 8) ->
  (forall (M3 : mem) model3,
      bd_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK1 Aw1 s1 sm1 ax1 cr1 ->
      ahid Aw1 model3 = ahid Aw1 model1 -> mrestrict (ahid Aw1 model1) M3 = M2v ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ W a -> M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> mem_grows M1 M3 ->
      (forall v c, PMSPA.ec_at RSEGS M1 (fb + 1024) v c -> PMSPA.ec_at RSEGS M3 (fb + 1024) v c) ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx2 R2 pc2 M3 model3) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 pc1 M1 model1) K.
Proof.
  intros CTX G LM MS MG FRZ WP KR.
  pose proof CTX as (Hw & HH & AM & K0 & ENT & FRM & FRS & FOK & SP32 & ARGS & RPRE & INCS & INV & EC0 & HE & UNR & CRED & KONT).
  destruct ENT as (Rra & RAok0 & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 7) with 26624 in *.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof FOK as ((rs & Hfb) & Fal).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _).
  pose proof (WF _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 5) with 2048 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL, FSIMG, F1, F2.
  rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in FSIMG.
  assert (FBI : 6905856 <= fb) by (clear - F1 FSAPP FSIMG; lia).
  pose proof LM as (BI & RP1 & STEP1 & AXL1 & CK1 & SHC1 & EBB1).
  pose proof G as G'. unfold bd_frame in G'.
  destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 0) with 64 in *. change (64 / 8) with 8 in *.
  pose proof BI as (HH1 & AM1 & MRT1 & INCA1 & INCL1 & ASTK1 & EK1 & DK1 & OWN1 & DSH1).
  set (FF' := (F, 0, sp - 160 + 32) :: FF) in *.
  assert (FOK' : PNRA.frame_okB FF' fb). { split; [exists rs; right; exact Hfb| exact Fal]. }
  pose proof RP1 as (PA1 & IA1 & VIS1 & VREF1 & OACC1 & BASE1 & ERR1 & GR1).
  change (PNRA.o_p PMA.AD fb) with (fb + 464) in PA1, IA1, VIS1, VREF1, OACC1. change (PNRA.o_is PMA.AD fb) with (fb + 96) in PA1, IA1. change (PNRA.o_v PMA.AD fb) with (fb + 432) in VIS1, VREF1.
  change (PNM.PSIZE + 8) with 424 in OACC1.
  pose proof (PNAPAR.op_visB L ar C HI LY HIok _ FF' LK1 cr1 Aw1 M1 model1 fb _ s1 HH1 FOK' PA1 OACC1) as ((O1 & O8 & ONSH) & Zop & OWR & OCE & OVIS & AOP).
  set (op := fb + 464) in *. set (ois := fb + 96) in *.
  pose proof FSAPP as (FA0 & FA1 & FA2). unfold BIGSHADOW_LO, BIGSHADOW_HI in FA1.
  pose proof GFR as (GF1 & GF2 & _).
  assert (DF1 : 0 <= F / 8) by (apply Z.div_pos; clear - GF1; lia).
  assert (DF2 : F / 8 <= 17592186044408) by (apply Z.div_le_upper_bound; clear - GF2; lia).
  assert (R4a : 0 <= F / 8 + 2147450880) by (clear - DF1; lia).
  assert (R4b : F / 8 + 2147450880 + 1 <= 2 ^ 64) by (clear - DF2; lia).
  pose proof (PMASK.stk_vis L ar C HI LY HIok _ FF' LK1 cr1 Aw1 M1 model1 sp 26624 160 HH1 ASTK1 ltac:(lia)) as (SL160 & SH160 & SWR).
  set (H1 := ahid Aw1 model1) in *.
  apply (L5SAR.apiece L ar C HI LYa HIok _ FF' LK1 cr1 Aw1 M1 model1 fx1 fx2 R1 pc1 R2 pc2 M2v W K HH1 AM1 MS MG FRZ).
  { intros a Ha Wa. pose proof (WP a Wa) as X. split; [| clear - X DF1; lia].
    apply (L5SAR.fframe_shadow_client L ar _ FF' 0 0 F 0 (sp - 160 + 32)); [left; reflexivity|]. change (ff_bytes 0) with 64.
    unfold in_shadow_of, S. rewrite (proj1 (proj2 GF8)). unfold SB. clear - X; lia. }
  intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MG3 FR3 VV3.
  assert (EKf : L5SAR.ek L ar (PNM.bparser_own s1 ++ LBX) FF 0 0 [] M1 M3).
  { apply (PMAUAR.wret_ek L ar C HI LY HIok LBX FF LK Aw sp 26624 (sp - 160) (sp - 104) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PNM.bparser_own s)
             (PNM.bparser_own s1 ++ LBX) LK1 cr1 Aw1 M1 M3 _ [] (fun _ => False) G HH1).
    - intros a [].
    - intros a Ha N. apply FR3; [exact Ha|]. intros Wa. apply N. pose proof (WP a Wa) as X. unfold PMAUK.WretX, PMAUK.Wret. change (ff_bytes 0 / 8) with 8. unfold SB.
      left; left; right. clear - X; lia. }
  pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB. pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH1) as BRB1.
  assert (OUT0 : forall i, L5.outside [] i) by (intros i rr []).
  assert (MOf : L5.u8_at RSEGS M3 (op + 8) (PNM.b_more s1)).
  { pose proof PA1 as (_ & _ & _ & MORE1 & _). apply (L5C.u8_at_agree RSEGS M1 M3); [| clear - O1; lia| clear - O1; lia| exact MORE1].
    intros j Hj. apply FR3; [clear - Hj O1; lia|]. intros Wj. pose proof (WP _ Wj) as X. clear - X Hj DF1 DF2 O1 ONSH. lia. }
  assert (PA3 : PNM.bparser_at RSEGS PMA.AD PMSPA.accA PMSPA.annA (pa_vp_parser PMA.AD) M3 op ois s1).
  { rewrite <- (set_more_id s1).
    apply (bparser_set_moreS M1 M3 (pa_vp_parser PMA.AD) op ois s1 (PNM.b_more s1) ltac:(clear - O1; lia) ltac:(clear - O1; lia)); [| | | exact MOf| | exact PA1].
    - intros i Hi Hn. destruct (Z_lt_le_dec i (op + 8)) as [X|X].
      + refine (proj1 (PMKA.agA_obj L ar _ FF 0 0 _ M1 M3 EKf PMKA.wapp_nil FRB op 8 _ _) i _); [| intros j _; apply OUT0| clear - Hi X; lia].
        apply (PNAPAR.aobj_fbB FF fb op 8 FOK); unfold op; clear; lia.
      + refine (proj1 (PMKA.agA_obj L ar _ FF 0 0 _ M1 M3 EKf PMKA.wapp_nil FRB (op + 9) 407 _ _) i _); [| intros j _; apply OUT0| clear - Hi X Hn; lia].
        apply (PNAPAR.aobj_fbB FF fb (op + 9) 407 FOK); unfold op; clear; lia.
    - intros i Hi. refine (PMKA.agsh_obj L ar _ FF 0 0 _ M1 M3 EKf PMKA.wapp_nil FRB op 416 _ i Hi). apply (PNAPAR.aobj_fbB FF fb op 416 FOK); unfold op; clear; lia.
    - intros q m Hq. assert (HqL : In (q, m) (PNM.bparser_own s1 ++ LBX)) by (apply in_or_app; left; exact Hq). destruct (BRB1 _ HqL) as (B0 & B1). cbn [fst snd] in B0, B1.
      split; [exact B0|]. split; [clear - B1; lia|]. apply (PMKA.agA_blk L ar _ FF 0 0 _ M1 M3 EKf PMKA.wapp_nil BRB1 q m HqL). intros j _; apply OUT0.
    - pose proof PA1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MB & _). exact MB. }
  assert (IA3 : PM.iss_at RSEGS PMA.AD PMSPA.accA M3 ois str sm1).
  { apply (PMKA.iss_keepA RSEGS PMA.AD L ar _ FF 0 0 _ M1 M3 EKf PMKA.wapp_nil FRB BRB1 ois str sm1); [| | | | exact IA1].
    - apply (PNAPAR.aobj_fbB FF fb ois 272 FOK); unfold ois; clear; lia.
    - apply incl_appr. exact INCS.
    - intros j _; apply OUT0.
    - intros c0 n0 p0 E0. unfold PMKA.blk_out. intros j _; apply OUT0. }
  assert (BASE3 : PMSTA.base_okA RSEGS PMA.AD M3).
  { apply (PMASK.base_keep L ar C LY _ FF 0 0 _ M1 M3 EKf); [| exact BASE1]. intros a Ha rr []. }
  assert (ERR3 : PNSTA.berr_okA RSEGS PMA.AD PMA.AAD PMA.AN M3 ax1).
  { apply (berr_keep _ FF 0 0 _ M1 M3 ax1 EKf); [| exact ERR1]. intros a Ha rr []. }
  assert (ECK : forall v c, PMSPA.ec_at RSEGS M1 (fb + 1024) v c -> PMSPA.ec_at RSEGS M3 (fb + 1024) v c).
  { intros v0 c0 E0. apply (PMKA.ec_keepA RSEGS L ar _ FF 0 0 _ M1 M3 EKf PMKA.wapp_nil FRB (fb + 1024) v0 c0); [| intros j _; apply OUT0| exact E0].
    apply (PNAPAR.aobj_fbB FF fb (fb + 1024) 16 FOK); clear; lia. }
  apply (KR M3 model3); [| exact HID3| exact VIS3| exact FR3| exact MG3| exact ECK].
  split.
  { apply (PMAUK.binv_pieceW L ar HI M model LBX FF LK Aw sp 26624 (sp - 160) (sp - 104) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PNM.bparser_own s) G
             _ (PNM.bparser_own s1) M1 model1 LK1 cr1 Aw1 M3 model3 W BI HH3 AM3 MRT3 MG3 FR3).
    intros a Wa. pose proof (WP a Wa) as X. split; [unfold ocell; clear - X DF1 DF2 SL160 SHI SPT GSPT GSLO GSHI; lia| right; right; left; unfold SB; change (ff_bytes 0) with 64; change (64 / 8) with 8; clear - X; lia]. }
  split.
  { apply (pre_after_call _ FF 0 0 [] M1 M3 fb s1 s1 str sm1 sm1 ax1 ax1 FRB EKf PMKA.wapp_nil FOK); [intros i _ rr []| exact RP1| exact PA3| exact IA3| exact GR1| exact BASE3| exact ERR3]. }
  split; [exact STEP1|]. split; [exact AXL1|]. split; [exact CK1|]. split; [| exact EBB1].
  apply (L5C.u8_at_agree RSEGS M1 M3); [| exact R4a| exact R4b| exact SHC1].
  intros j Hj. apply FR3; [clear - Hj R4a R4b; lia|]. intros Wj. pose proof (WP _ Wj) as X. clear - X Hj. lia.
Qed.


End WithHeap.
End PNABDK.
