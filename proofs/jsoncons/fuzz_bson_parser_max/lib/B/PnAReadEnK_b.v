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
     PmModelFactsA_b PnStepA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PgSrc PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnLayout PnModel PnModelFacts PnStatics PnStaticsA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b PnRunAa_b PnASrcKit_b PmAUarK_b PmAUar_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnBrObj. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnBrObjA_b PnAParKit_b PnAReset1_b PnOwnerOkA_b PnBrKitA_b PnAReadEnP_b Ba0_code_ae2e8_ae2ec_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

From stdpp Require list_relations list_basics.

Module PNAENK.
Import L5A. Import L5CA. Import L5SAR. Import PNBKA.

(* [comment removed for export] *)
Definition spill (M : mem) (E F : Z) : Prop :=
  L5.u64_at RSEGS M (E - 112) F.
Lemma spill_agree M M' E F : 0 <= E - 128 -> E <= 2 ^ 64 ->
  spill M E F -> (forall a, E - 112 <= a < E - 104 -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> spill M' E F.
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
  /\ 140735332487296 <= sp <= 140737488355328 /\ sp mod 32 = 0 /\ L5.writable RSEGS MV (sp - 128) 128
  /\ 6905856 <= op <= 140737488354912 /\ op mod 8 = 0 /\ (2147446784 + 17592186048512 <= op \/ op + 416 <= 2147446784)
  /\ L5KA.zeros_at MV ((op / 8) + 2147450880) 2 /\ L5KA.zeros_at MV (((op + 10) / 8) + 2147450880) 1 /\ L5KA.zeros_at MV (((op + 344) / 8) + 2147450880) 3 /\ L5KA.zeros_at MV (((op + 345) / 8) + 2147450880) 1
  /\ ((sp - 128) + 128 <= op \/ op + 416 <= (sp - 128))
  /\ 6905856 <= F <= 140737488355264 /\ F mod 32 = 0 /\ L5.defined MV F 64 /\ L5.writable RSEGS MV F 64
  /\ (2147446784 + 17592186048512 <= F \/ F + 64 <= 2147446784) /\ L5.writable RSEGS MV ((F / 8) + 2147450880) 8
  /\ L5.u64_at RSEGS MV (F + 56) fl /\ 4096 <= fl <= 140737488355327 /\ L5.writable RSEGS MV fl 1
  /\ (2147446784 + 17592186048512 <= fl \/ fl + 1 <= 2147446784) /\ (F + 64 <= fl \/ fl + 1 <= F)
  /\ ((sp - 128) + 128 <= F \/ F + 64 <= (sp - 128)) /\ ((sp - 128) + 128 <= fl \/ fl + 1 <= (sp - 128))
  /\ (op + 416 <= F \/ F + 64 <= op) /\ (op + 416 <= fl \/ fl + 1 <= op)
  /\ (((op / 8) + 2147450880) + 52 <= ((F / 8) + 2147450880) \/ ((F / 8) + 2147450880) + 8 <= ((op / 8) + 2147450880))
  /\ 0 <= sp < 2 ^ 64 /\ 0 <= op < 2 ^ 64 /\ 0 <= F < 2 ^ 64 /\ 0 <= fl < 2 ^ 64.


Section WithDefs.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (HI : asan_iface).

(* [comment removed for export] *)
Definition en_kont (K : TSet) (R : bvmap 5 word) (M : mem) (model : Model) (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z))
           (cr : credit) (sp r fb cat e : Z) (s : PNM.bpst) (str : PM.vstr) (sm : PM.strm) (ax : PNST.bax) (w : Z) : Prop :=
  forall (fx' : FPState) (R' : bvmap 5 word) (M' : mem) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (s' : PNM.bpst) (sm' : PM.strm) (ax' : PNST.bax) (cr' : credit),
    regs_preserved R R' ->
    PNRA.brun_post RSEGS PMA.AD PMA.AN PMA.AAD false PNRA.bprog_name R' M' fb s s' str sm sm' ax ax' cat e ->
    ahpres L ar LBX FF sp 24576 (PNRA.W_brun PMA.AD PMA.AN fb) M M' ->
    PMSP.credit_keep cr cr' (pot L ar s) (pot L ar s') ->
    model_rt model model' -> incl LK' LK -> incl Aw Aw' -> amodel_ok Aw' model' -> ri_inv HI (PNM.bparser_own s' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
    srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K.

(* [comment removed for export] *)
Definition en_ctx (K : TSet) (R : bvmap 5 word) (M : mem) (model : Model) (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z))
           (cr : credit) (sp r fb cat e : Z) (s : PNM.bpst) (str : PM.vstr) (sm : PM.strm) (ax : PNST.bax) (w : Z) : Prop :=
  (w = 0 \/ w = 1) /\ ri_inv HI (PNM.bparser_own s ++ LBX) FF LK cr Aw M (vml_of model) /\ amodel_ok Aw model /\ K [] /\ PMSPA.entryA PMA.AD L ar R M sp r 6
  /\ PGSA.ffroomB PNRA.FCB 6 FF LK /\ PMSPA.ffrsA FF sp /\ PNRA.frame_okB FF fb /\ sp mod 32 = 0 /\ PNRA.bargs_en PMA.AD R fb s sm
  /\ PNRA.brun_pre RSEGS PMA.AD PMA.AN PMA.AAD M fb s str sm ax /\ incl (PM.vs_own str) LBX /\ PNRA.binv s /\ PMSPA.ec_at RSEGS M (fb + 1024) e cat /\ 0 <= e <= 64
  /\ PM.unread (PNM.b_src s) sm < 2 ^ 26 /\ PMSP.credit_le (pot L ar s) cr
  /\ en_kont K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w.

(* [comment removed for export] *)
Definition en_frame (R : bvmap 5 word) (M : mem) (model : Model) (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z))
           (cr : credit) (sp : Z) (s : PNM.bpst) (F fl : Z) (LK2 : list fframe) (M2 : mem) (model2 : Model) : Prop :=
  PMAUK.gctx L ar HI LBX FF LK Aw sp 24576 (sp - 128) (sp - 104) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PNM.bparser_own s).

(* [comment removed for export] *)
Definition en_mem (R : bvmap 5 word) (M : mem) (model : Model) (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z))
           (cr : credit) (sp fb : Z) (s : PNM.bpst) (str : PM.vstr) (sm : PM.strm) (ax : PNST.bax) (F : Z)
           (M1 : mem) (model1 : Model) (LK1 : list fframe) (Aw1 : list (Z * Z)) (s1 : PNM.bpst) (sm1 : PM.strm) (ax1 : PNST.bax) (cr1 : credit) : Prop :=
  PMAUK.binv L ar HI M model LBX FF LK Aw sp 24576 (sp - 128) (own sp R) F 0 (PNRA.W_brun PMA.AD PMA.AN fb) (PNM.bparser_own s1) M1 model1 LK1 cr1 Aw1
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
  en_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  en_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  en_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
  pfacts (mrestrict (ahid Aw1 model1) M1) sp (fb + 464) F fl
  /\ own sp R (mrestrict (ahid Aw1 model1) M1)
  /\ (forall a v, sp - 128 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1 a v -> L5.u64_at RSEGS (mrestrict (ahid Aw1 model1) M1) a v)
  /\ (forall v, L5.u8_at RSEGS M1 (F + 32) v -> L5.u8_at RSEGS (mrestrict (ahid Aw1 model1) M1) (F + 32) v)
  /\ L5.writable RSEGS (mrestrict (ahid Aw1 model1) M1) (fb + 464) 424
  /\ (forall v, L5.u8_at RSEGS (mrestrict (ahid Aw1 model1) M1) (fb + 464 + 8) v <-> L5.u8_at RSEGS M1 (fb + 464 + 8) v)
  /\ (forall a v, sp - 128 <= a -> a + 8 <= sp -> L5.u64_at RSEGS (mrestrict (ahid Aw1 model1) M1) a v -> L5.u64_at RSEGS M1 a v).
Proof.
  intros CTX G LM.
  destruct CTX as (Hw & HH & AM & K0 & ENT & FRM & FRS & FOK & SP32 & ARGS & RPRE & INCS & INV & EC0 & HE & UNR & CRED & KONT).
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 6) with 24576 in *.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof FOK as ((rs & Hfb) & Fal).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _).
  pose proof (WF _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 5) with 2048 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL, F1, F2.
  destruct LM as (BI & RP1 & STEP1 & AXL1 & CK1 & SHC1 & EBB1).
  pose proof G as G'. unfold en_frame in G'.
  destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 0) with 64 in *. change (64 / 8) with 8 in *.
  pose proof BI as (HH1 & AM1 & MRT1 & INCA1 & INCL1 & ASTK1 & EK1 & DK1 & OWN1 & DSH1).
  set (FF' := (F, 0, sp - 128 + 32) :: FF) in *.
  assert (FOK' : PNRA.frame_okB FF' fb). { split; [exists rs; right; exact Hfb| exact Fal]. }
  destruct RP1 as (PA1 & IA1 & VIS1 & VREF1 & OACC1 & BASE1 & ERR1 & GR1).
  change (PNRA.o_p PMA.AD fb) with (fb + 464) in *. change (PNRA.o_is PMA.AD fb) with (fb + 96) in *. change (PNRA.o_v PMA.AD fb) with (fb + 432) in *.
  change (PNM.PSIZE + 8) with 424 in OACC1.
  pose proof (PNAPAR.op_visB L ar C HI LY HIok _ FF' LK1 cr1 Aw1 M1 model1 fb _ s1 HH1 FOK' PA1 OACC1) as ((O1 & O8 & ONSH) & Zop & OWR & OCE & OVIS & AOP).
  pose proof (PMASK.mach_vis L ar C HI LY HIok _ FF' LK1 cr1 Aw1 M1 model1 HH1 BASE1) as (VM0 & VM1 & VM2).
  pose proof (PMASK.stk_vis L ar C HI LY HIok _ FF' LK1 cr1 Aw1 M1 model1 sp 24576 128 HH1 ASTK1 ltac:(lia)) as (SL160 & SH160 & SWR).
  destruct (PMAUK.vis_facts L ar C HI LYa HIok M model LBX FF LK Aw sp 24576 (sp - 128) (sp - 104) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PNM.bparser_own s) G
              _ (PNM.bparser_own s1) M1 model1 LK1 cr1 Aw1 BI) as ((WS1 & _ & _ & _ & _) & OWNv & (FD1 & FW1 & FSW1 & FLC1 & FLW1) & (FLCc1 & FLV1 & VF1 & VS1 & VSH1)).
  change (ff_bytes 0) with 64 in *. change (64 / 8) with 8 in *. replace (F + 64 - 8) with (F + 56) in FLC1 by (clear; lia).
  set (op := fb + 464) in *.
  set (MV := mrestrict (ahid Aw1 model1) M1) in *.
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ _ LK1 cr1 Aw1 M1 model1 HH1) as (_ & VISs & _).
  (* [comment removed for export] *)
  assert (CLo : forall a, fb + 32 <= a < fb + 2040 -> aclient L ar LBX FF sp 24576 a).
  { intros a Ha. unfold aclient, aclient_g. do 3 right; left. exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd].
    change (ff_bytes 5) with 2048. split; [clear - Ha; lia| intros Y; clear - Ha Y; lia]. }
  assert (CLs : forall a, fb / 8 + SB <= a < fb / 8 + SB + 256 -> aclient L ar LBX FF sp 24576 a).
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
  { intros a Ha X. subst a. apply GFLNC. apply L5SAR.aclient_cons. apply (L5SAR.aclient_00 L ar LBX FF sp 24576 fl). exact (CLo fl Ha). }
  assert (ApF : op + 416 <= F \/ F + 64 <= op) by (apply iv_apart; [clear; lia| clear; lia| intros a Ha; apply NF; clear - Ha; unfold op in Ha; lia]).
  assert (ApFL : op + 416 <= fl \/ fl + 1 <= op).
  { destruct (Z_lt_le_dec fl op) as [X|X]; [right; clear - X; lia|]. destruct (Z_lt_le_dec fl (op + 416)) as [Y|Y]; [exfalso; apply (NFL fl); [clear - X Y; unfold op in X, Y; lia| reflexivity]| left; exact Y]. }
  assert (ApS : ((op / 8) + 2147450880) + 52 <= ((F / 8) + 2147450880) \/ ((F / 8) + 2147450880) + 8 <= ((op / 8) + 2147450880)).
  { change 2147450880 with SB. apply iv_apart; [clear; lia| clear; lia| intros a Ha; apply NFS; clear - Ha SHop; lia]. }
  (* [comment removed for export] *)
  assert (SVV : forall a v0, sp - 128 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1 a v0 -> L5.u64_at RSEGS MV a v0).
  { intros a v0 Ha1 Ha2 X. apply (proj2 (L5A.u64_at_vis _ M1 a v0 (VISs a 8 ltac:(clear - Ha1 SL160 SPT; lia) ltac:(clear - Ha2 SHI SPT; lia)) ltac:(clear - Ha1 SL160 SPT; lia) ltac:(clear - Ha2 SHI SPT; lia))). exact X. }
  assert (CV : forall v, L5.u8_at RSEGS M1 (F + 32) v -> L5.u8_at RSEGS MV (F + 32) v).
  { intros v X. apply (proj2 (L5A.u8_at_vis _ M1 (F + 32) v (L5A.avis_sub _ F 64 (F + 32) 1 VF1 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - GFR; lia) ltac:(clear - GFR; lia))). exact X. }
  assert (Zz0 : L5KA.zeros_at MV (op / 8 + 2147450880) 2). { intros i Hi. apply Zop. clear - Hi; lia. }
  assert (Zz1 : L5KA.zeros_at MV ((op + 10) / 8 + 2147450880) 1).
  { intros i Hi. replace ((op + 10) / 8 + 2147450880 + i) with (op / 8 + SB + (1 + i)) by (unfold SB; rewrite (div8_add op 10 O8 ltac:(clear; lia)); change (10 / 8) with 1; clear; lia).
    apply Zop. clear - Hi; lia. }
  assert (Zz2 : L5KA.zeros_at MV ((op + 344) / 8 + 2147450880) 3).
  { intros i Hi. replace ((op + 344) / 8 + 2147450880 + i) with (op / 8 + SB + (43 + i)) by (unfold SB; rewrite (div8_add op 344 O8 ltac:(clear; lia)); change (344 / 8) with 43; clear; lia).
    apply Zop. clear - Hi; lia. }
  assert (Zz3 : L5KA.zeros_at MV ((op + 345) / 8 + 2147450880) 1).
  { intros i Hi. replace ((op + 345) / 8 + 2147450880 + i) with (op / 8 + SB + (43 + i)) by (unfold SB; rewrite (div8_add op 345 O8 ltac:(clear; lia)); change (345 / 8) with 43; clear; lia).
    apply Zop. clear - Hi; lia. }
  assert (Z3 : L5KA.zeros_at MV ((op + 392) / 8 + 2147450880) 3).
  { intros i Hi. replace ((op + 392) / 8 + 2147450880 + i) with (op / 8 + SB + (49 + i)).
    - apply Zop. clear - Hi; lia.
    - unfold SB. replace (op + 392) with (op + 49 * 8) by (clear; lia). rewrite Z.div_add by (clear; lia). clear; lia. }
  assert (SVR : forall a v0, sp - 128 <= a -> a + 8 <= sp -> L5.u64_at RSEGS MV a v0 -> L5.u64_at RSEGS M1 a v0).
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
Lemma en_call_mkec K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 (fx1 : FPState) R1 (ra v e1 c1 : Z) :
  PNRAa.make_ec_spec L ar HI ->
  en_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  en_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  en_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
  PMSPA.ec_at RSEGS M1 (fb + 1024) e1 c1 ->
  getr R1 (reg 1) = Z_to_bv 64 ra -> L5.ra_ok ra -> getr R1 (reg 2) = Z_to_bv 64 (sp - 128) ->
  getr R1 (reg 3) = Z_to_bv 64 (pa_gp PMA.AD) -> getr R1 (reg 4) = Z_to_bv 64 (hl_tp L) ->
  getr R1 (reg 10) = Z_to_bv 64 (fb + 1024) -> getr R1 (reg 11) = Z_to_bv 64 v -> 1 <= v <= 64 ->
  (forall (fx2 : FPState) R2 (M3 : mem) model3 LK3 Aw3,
      regs_preserved R1 R2 -> PMSPA.ec_at RSEGS M3 (fb + 1024) v (pa_errcat_obj PMA.AD) ->
      en_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK3 Aw3 s1 sm1 (PNST.bax_add_cat ax1) cr1 ->
      (forall a, sp - 128 <= a < sp - 104 -> M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx2 R2 ra M3 model3) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 (pa_make_ec PMA.AD) M1 model1) K.
Proof.
  intros MKE CTX G LM EC1 X1 RAok X2 X3 X4 X10 X11 Hv KR.
  pose proof CTX as (Hw & HH & AM & K0 & ENT & FRM & FRS & FOK & SP32 & ARGS & RPRE & INCS & INV & EC0 & HE & UNR & CRED & KONT).
  destruct ENT as (Rra & RAok0 & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 6) with 24576 in *. change (24576 / 8) with 3072 in STKSH.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof FOK as ((rs & Hfb) & Fal).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _).
  pose proof (WF _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 5) with 2048 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL, FSIMG, F1, F2.
  rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in FSIMG.
  assert (FBI : 6905856 <= fb) by (clear - F1 FSAPP FSIMG; lia).
  pose proof LM as (BI & RP1 & STEP1 & AXL1 & CK1 & SHC1 & EBB1).
  pose proof G as G'. unfold en_frame in G'.
  destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 0) with 64 in *. change (64 / 8) with 8 in *.
  pose proof BI as (HH1 & AM1 & MRT1 & INCA1 & INCL1 & ASTK1 & EK1 & DK1 & OWN1 & DSH1).
  set (FF' := (F, 0, sp - 128 + 32) :: FF) in *.
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
  apply (MKE fx1 R1 M1 model1 K (PNM.bparser_own s1 ++ LBX) FF' LK1 Aw1 cr1 oec v (sp - 128) ra ax1 HH1 AM1 K0).
  { unfold PMSPA.entryA. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact X1|]. split; [exact RAok|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|].
    change (PMSPA.pm_scr 1) with 14336. change (14336 / 8) with 1792.
    split; [apply (L5SAR.astk_sub ar M1 M1 sp 24576 128 14336 ASTK1 (mem_grows_refl M1)); [clear; lia| clear; lia| clear; lia| replace (sp - 128) with (sp + (-8) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact A16]|].
    apply (PMKA.shadow_zero_sub M1 (sp - 24576) 3072); [| | clear; lia| clear; lia| clear; lia|].
    - apply PMKA.mod16_8'. replace (sp - 24576) with (sp + (-1536) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16.
    - apply PMKA.mod16_8'. replace (sp - 128 - 14336) with (sp + (-904) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16.
    - apply (PMKA.stksh_keepA L ar LBX FF sp 24576 WR M M1 EK1 WAPPR (sp - 24576) 3072); [clear - SLO SPT; lia| clear - SLO; lia| clear - SHI SPT; lia| | clear; lia| exact STKSH].
      apply PMKA.mod16_8'. replace (sp - 24576) with (sp + (-1536) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  { apply (PMAUAR.ffroomB_push PNRA.FCB 6 1 FF LK LK1 _ FRM INCL1); [exact NDF1| clear; lia]. }
  { apply (PMAUAR.ffrsA_push FF sp (sp - 128) F 0 (sp - 128 + 32) FRS); clear; lia. }
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
  assert (WAV : forall rr a, In rr Wc6 -> L5.in_rng rr a -> ~ (sp - 128 <= a < sp) /\ ~ (F / 8 + SB <= a < F / 8 + SB + 8)).
  { intros rr a Hin Hr. unfold SB. destruct (Wc6R rr a Hin Hr) as [X|X].
    - unfold oec in X. split; [clear - X GSLO F2 FSCEIL; lia| destruct FA1 as [Y|Y]; clear - X Y DF1 DF2 F1 F2; lia].
    - split; [clear - X GSLO GSHI GSPT; lia| clear - X DF1; lia]. }
  assert (WOUT : forall a, aclient L ar LBX FF sp 24576 a -> L5.outside WR a -> L5.outside Wc6 a).
  { intros a Hc Ho rr Hin Hr. destruct (Wc6R rr a Hin Hr) as [X|X].
    - apply (Ho (PNRA.o_ec PMA.AD fb, 16)); [unfold WR, PNRA.W_brun, PGS.W_srcfG; cbn [app]; do 8 right; left; reflexivity| unfold L5.in_rng, PNRA.o_ec, PMSP.o_ec; cbn [fst snd pa_off_ec PMA.AD PnLayoutA_b.ADDR_A]; unfold oec in X; clear - X; lia].
    - unfold Wc6 in Hin. destruct Hin as [<-|Hin]; [unfold L5.in_rng in Hr; cbn [fst snd] in Hr; unfold oec in Hr; clear - Hr X FBI; lia|].
      destruct (PNST.bax_cat ax1); [destruct Hin|]. unfold PNST.cat_W in Hin. destruct Hin as [<-|[<-|[]]].
      + apply (Ho (pa_errcat_guard PMA.AD, 2)); [unfold WR, PNRA.W_brun, PGS.W_srcfG, PNST.berr_W, PNST.cat_W; cbn [app]; do 9 right; left; reflexivity| exact Hr].
      + apply (Ho (pa_atexit PMA.AD, 544)); [unfold WR, PNRA.W_brun, PGS.W_srcfG, PNST.berr_W, PNST.cat_W; cbn [app]; do 10 right; left; reflexivity| exact Hr]. }
  assert (BI6 : PMAUK.binv L ar HI M model LBX FF LK Aw sp 24576 (sp - 128) (own sp R) F 0 WR (PNM.bparser_own s1) M6 model6 LK6 cr1 Aw6).
  { apply (PMAUK.binv_callee L ar C HI HIok M model LBX FF LK Aw sp 24576 (sp - 128) (sp - 104) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PNM.bparser_own s) G
             WR WR (PNM.bparser_own s1) (PNM.bparser_own s1) (PNM.bparser_own s1) M1 model1 LK1 cr1 Aw1 M6 model6 LK6 cr1 Aw6 14336 Wc6 BI HP6 HH6 AM6 MRT6 INCA6 INCL6);
      [clear; lia| clear; lia| intros rr a Hin Hr; destruct (WAV rr a Hin Hr) as (Y1 & Y2); split; [unfold ocell; clear - Y1; lia| exact Y2]| exact WOUT| intros a X; exact X]. }
  pose proof (L5SAR.ek_callee L ar (PNM.bparser_own s1 ++ LBX) [] FF [(F, 0, sp - 128 + 32)] sp 24576 (sp - 128) 14336 Wc6 Wc6 M1 M6 HP6 ltac:(clear; lia) ltac:(clear; lia) (fun a _ X => X)) as EK16.
  assert (WAPP6 : PMKA.wapp Wc6).
  { intros rr Hin. unfold BIGSHADOW_LO, BIGSHADOW_HI. unfold Wc6 in Hin. destruct Hin as [<-|Hin]; cbn [fst snd].
    - unfold oec. destruct FA1 as [Y|Y]; clear - Y F1 F2; lia.
    - destruct (PNST.bax_cat ax1); [destruct Hin|]. unfold PNST.cat_W in Hin. cbn [pa_errcat_guard pa_atexit PMA.AD ADDR_A] in Hin. destruct Hin as [<-|[<-|[]]]; cbn [fst snd]; clear; lia. }
  pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH1) as FRB1. pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH1) as BRB1.
  pose proof (proj1 HP6 : ek L ar (PNM.bparser_own s1 ++ LBX) FF' (sp - 128) 14336 Wc6 M1 M6) as EK6.
  assert (OUTB : forall q m, In (q, m) (PNM.bparser_own s1 ++ LBX) -> forall i, q <= i < q + m -> L5.outside Wc6 i).
  { intros q m Hq i Hi rr Hin Hr. destruct (Wc6R rr i Hin Hr) as [Y|Y].
    - destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q m oec 16 HH1 Hq (PMAUAR.aobjA_push FF oec 16 _ AOE)) as [Z0|Z0]; clear - Hi Y Z0; lia.
    - pose proof (PMASK.blk_img L ar C HI LY HIok _ _ _ _ _ _ _ q m HH1 Hq) as Z0. destruct Z0 as [Z0|Z0]; clear - Hi Y Z0; lia. }
  assert (OUTo : forall i, op <= i < op + 416 -> L5.outside Wc6 i).
  { intros i Hi rr Hin Hr. destruct (Wc6R rr i Hin Hr) as [Y|Y]; [unfold op in Hi; unfold oec in Y; clear - Hi Y; lia| unfold op in Hi; clear - Hi Y FBI; lia]. }
  assert (OUTi : forall i, ois <= i < ois + 272 -> L5.outside Wc6 i).
  { intros i Hi rr Hin Hr. destruct (Wc6R rr i Hin Hr) as [Y|Y]; [unfold ois in Hi; unfold oec in Y; clear - Hi Y; lia| unfold ois in Hi; clear - Hi Y FBI; lia]. }
  assert (PA6 : PNM.bparser_at RSEGS PMA.AD PMSPA.accA PMSPA.annA (pa_vp_parser PMA.AD) M6 op ois s1).
  { apply (PNAPAR.bparser_keepA L ar C HI HIok _ FF' LK1 cr1 Aw1 (vml_of model1) Wc6 (sp - 128) 14336 M1 M6 op ois s1 HH1 EK6 WAPP6); [| apply incl_appl; apply incl_refl| exact OUTo| | exact PA1].
    - apply PMAUAR.aobjA_push. apply (PNAPAR.aobj_fbB FF fb op PNM.PSIZE FOK); unfold op, PNM.PSIZE; clear; lia.
    - intros B m HB. unfold PMKA.blk_out. apply OUTB. apply in_or_app; left; exact HB. }
  assert (IA6 : PM.iss_at RSEGS PMA.AD PMSPA.accA M6 ois str sm1).
  { apply (PMKA.iss_keepA RSEGS PMA.AD L ar _ FF' (sp - 128) 14336 Wc6 M1 M6 EK6 WAPP6 FRB1 BRB1 ois str sm1); [| | exact OUTi| | exact IA1].
    - apply PMAUAR.aobjA_push. apply (PNAPAR.aobj_fbB FF fb ois 272 FOK); unfold ois; clear; lia.
    - apply incl_appr. exact INCS.
    - intros c0 n0 p0 E0. unfold PMKA.blk_out. apply OUTB. apply in_or_app; right. apply INCS. rewrite E0. left; reflexivity. }
  assert (BASE6 : PMSTA.base_okA RSEGS PMA.AD M6).
  { apply (base_keepW _ FF' (sp - 128) 14336 Wc6 M1 M6 EK6); [| | | | exact BASE1].
    - intros a Ha rr Hin Hr. destruct (Wc6R rr a Hin Hr) as [Y|Y]; [unfold oec in Y; clear - Ha Y FBI; lia| clear - Ha Y; lia].
    - intros a Ha rr Hin Hr. destruct (Wc6R rr a Hin Hr) as [Y|Y]; [unfold oec in Y; clear - Ha Y FBI; lia| clear - Ha Y; lia].
    - intros rr Hin Hr. destruct (Wc6R rr _ Hin Hr) as [Y|Y]; [unfold oec in Y; clear - Y FBI; lia| clear - Y; lia].
    - intros a Ha rr Hin Hr. destruct (Wc6R rr a Hin Hr) as [Y|Y]; [unfold oec in Y; clear - Ha Y FBI; lia| clear - Ha Y; lia]. }
  apply (KR fx6 R6 M6 model6 LK6 Aw6 RP6 EC6).
  - split; [exact BI6|].
    split. { apply (pre_after_call (PNM.bparser_own s1 ++ LBX) FF' (sp - 128) 14336 Wc6 M1 M6 fb s1 s1 str sm1 sm1 ax1 (PNST.bax_add_cat ax1) FRB1 EK6 WAPP6 FOK');
               [| exact RP1| exact PA6| exact IA6| exact GR1| exact BASE6| exact ERR6].
             intros i Hi rr Hin Hr. destruct (Wc6R rr i Hin Hr) as [Y|Y]; [unfold oec in Y; clear - Hi Y; lia| clear - Hi Y FBI; lia]. }
    split; [exact STEP1|]. split; [exact (PNST.bax_le_trans _ _ _ AXL1 (PNST.bax_le_cat ax1))|]. split; [exact CK1|].
    split; [| exact EBB1].
    apply (L5C.u8_at_agree RSEGS M1 M6); [| exact R4a| exact R4b| exact SHC1].
    intros j Hj. apply EK6. split; [clear - Hj R4a R4b; lia|]. split.
    + apply (L5SAR.fframe_shadow_client L ar _ FF' (sp - 128) 14336 F 0 (sp - 128 + 32)); [left; reflexivity|]. change (ff_bytes 0) with 64.
      unfold in_shadow_of, S. rewrite (proj1 (proj2 GF8)). unfold SB. clear - Hj; lia.
    + intros rr Hin Hr. destruct (WAV rr _ Hin Hr) as (_ & Y). apply Y. unfold SB. clear - Hj; lia.
  - intros a Ha. apply EK6. split; [clear - Ha GSLO GSHI GSPT; lia|]. split.
    + apply (L5SAR.stack_client L ar _ FF' (sp - 128) 14336 a); clear - Ha GSLO GSHI GSPT; lia.
    + intros rr Hin Hr. destruct (WAV rr a Hin Hr) as (Y & _). apply Y. clear - Ha; lia.
Qed.


(* [comment removed for export] *)
Lemma en_fin K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 (fx5 fx9 : FPState) R5 R9 (pc5 mo : Z) (M9v : mem) :
  en_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  en_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  en_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 ->
  msteps RSEGS (st fx5 R5 pc5 (mrestrict (ahid Aw5 model5) M5)) (st fx9 R9 0xaf8f0 M9v) ->
  mem_grows (mrestrict (ahid Aw5 model5) M5) M9v ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ PMAUK.WretX F fl 0 (fun a => fb + 472 <= a < fb + 473) a -> M9v (Z_to_bv 64 a) = mrestrict (ahid Aw5 model5) M5 (Z_to_bv 64 a)) ->
  L5.u8_at RSEGS M9v fl 0 -> L5.u8_at RSEGS M9v (fb + 472) mo -> (mo = 0 \/ mo = 1) ->
  getr R9 (reg 2) = Z_to_bv 64 sp ->
  (forall k, In k [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R9 (reg k) = Z_to_bv 64 (bv_unsigned (getr R (reg k)))) ->
  (forall k, In k [3; 4]%nat -> getr R9 (reg k) = getr R (reg k)) ->
  ( (exists v, 1 <= v <= 64 /\ PMSPA.ec_at RSEGS M5 (fb + 1024) v (pa_errcat_obj PMA.AD) /\ mo = 0 /\ PNST.bax_cat ax5 = true)
    \/ (PMSPA.ec_at RSEGS M5 (fb + 1024) e cat /\ PNRA.bprog_name R9 M5 s s5 sm sm5) ) ->
  PNRA.binv s5 -> (length (PNM.b_stk s) <= length (PNM.b_stk s5))%nat ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx5 R5 pc5 M5 model5) K.
Proof.
  intros CTX G LM MS9 MG9 FRZ9 FL0 MO9 Hmo Y2 YR Y34 POST INV5 LEN5.
  pose proof CTX as (Hw & HH & AM & K0 & ENT & FRM & FRS & FOK & SP32 & ARGS & RPRE & INCS & INV & EC0 & HE & UNR & CRED & KONT).
  destruct ENT as (Rra & RAok0 & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 6) with 24576 in *. change (24576 / 8) with 3072 in STKSH.
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof RAok0 as (Hr1 & Hr2).
  pose proof FOK as ((rs & Hfb) & Fal).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _).
  pose proof (WF _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 5) with 2048 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL, FSIMG, F1, F2.
  rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in FSIMG.
  assert (FBI : 6905856 <= fb) by (clear - F1 FSAPP FSIMG; lia).
  pose proof LM as (BI & RP1 & STEP1 & AXL1 & CK1 & SHC1 & EBB1).
  pose proof G as G'. unfold en_frame in G'.
  destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 0) with 64 in *. change (64 / 8) with 8 in *.
  pose proof BI as (HH1 & AM1 & MRT1 & INCA1 & INCL1 & ASTK1 & EK1 & DK1 & OWN1 & DSH1).
  set (FF' := (F, 0, sp - 128 + 32) :: FF) in *.
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
  pose proof (PMK.ret_to RSEGS fx9 R9 M9v 0xaf8f0 W_ae2e8 r F_ae2e8 eq_refl D_ae2e8 R9ra Hr1 Hr2) as MSr.
  set (Wx := fun a => fb + 472 <= a < fb + 473).
  apply (PMAUK.retire_coreW L ar C HI LYa HIok M model LBX FF LK Aw sp 24576 (sp - 128) (sp - 104) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PNM.bparser_own s) G
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
  { apply (PMAUAR.wret_ek L ar C HI LY HIok LBX FF LK Aw sp 24576 (sp - 128) (sp - 104) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PNM.bparser_own s)
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
      unfold s9, PNRA.bprog_name. cbn [PNBO.set_more PNM.b_stk PNM.b_src PNM.b_nb PNM.b_tb]. unfold PNRA.bprog_name in PROG.
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
Lemma en_piece_fr K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1
      (fx1 fx2 : FPState) R1 R2 (pc1 pc2 : Z) (M2v : mem) (W : Z -> Prop) :
  en_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  en_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  en_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
  msteps RSEGS (st fx1 R1 pc1 (mrestrict (ahid Aw1 model1) M1)) (st fx2 R2 pc2 M2v) ->
  mem_grows (mrestrict (ahid Aw1 model1) M1) M2v ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ W a -> M2v (Z_to_bv 64 a) = mrestrict (ahid Aw1 model1) M1 (Z_to_bv 64 a)) ->
  (forall a, W a -> sp - 128 <= a < sp - 104) ->
  (forall (M3 : mem) model3,
      en_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK1 Aw1 s1 sm1 ax1 cr1 ->
      ahid Aw1 model3 = ahid Aw1 model1 -> mrestrict (ahid Aw1 model1) M3 = M2v ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ W a -> M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> mem_grows M1 M3 ->
      (forall v c, PMSPA.ec_at RSEGS M1 (fb + 1024) v c -> PMSPA.ec_at RSEGS M3 (fb + 1024) v c) ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx2 R2 pc2 M3 model3) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 pc1 M1 model1) K.
Proof.
  intros CTX G LM MS MG FRZ WP KR.
  pose proof CTX as (Hw & HH & AM & K0 & ENT & FRM & FRS & FOK & SP32 & ARGS & RPRE & INCS & INV & EC0 & HE & UNR & CRED & KONT).
  destruct ENT as (Rra & RAok0 & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 6) with 24576 in *.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof FOK as ((rs & Hfb) & Fal).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _).
  pose proof (WF _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 5) with 2048 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL, FSIMG, F1, F2.
  rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in FSIMG.
  assert (FBI : 6905856 <= fb) by (clear - F1 FSAPP FSIMG; lia).
  pose proof LM as (BI & RP1 & STEP1 & AXL1 & CK1 & SHC1 & EBB1).
  pose proof G as G'. unfold en_frame in G'.
  destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 0) with 64 in *. change (64 / 8) with 8 in *.
  pose proof BI as (HH1 & AM1 & MRT1 & INCA1 & INCL1 & ASTK1 & EK1 & DK1 & OWN1 & DSH1).
  set (FF' := (F, 0, sp - 128 + 32) :: FF) in *.
  assert (FOK' : PNRA.frame_okB FF' fb). { split; [exists rs; right; exact Hfb| exact Fal]. }
  pose proof RP1 as (PA1 & IA1 & VIS1 & VREF1 & OACC1 & BASE1 & ERR1 & GR1).
  change (PNRA.o_p PMA.AD fb) with (fb + 464) in PA1, IA1, VIS1, VREF1, OACC1. change (PNRA.o_is PMA.AD fb) with (fb + 96) in PA1, IA1. change (PNRA.o_v PMA.AD fb) with (fb + 432) in VIS1, VREF1.
  change (PNM.PSIZE + 8) with 424 in OACC1.
  pose proof GFR as (GF1 & GF2 & _).
  assert (R4a : 0 <= F / 8 + 2147450880) by (clear - GF1; lia).
  assert (R4b : F / 8 + 2147450880 + 1 <= 2 ^ 64) by (clear - GF2; pose proof (Z.div_le_upper_bound F 8 17592186044408 ltac:(lia) ltac:(lia)); lia).
  pose proof (PMASK.stk_vis L ar C HI LY HIok _ FF' LK1 cr1 Aw1 M1 model1 sp 24576 128 HH1 ASTK1 ltac:(lia)) as (SL160 & SH160 & SWR).
  set (H1 := ahid Aw1 model1) in *.
  apply (L5SAR.apiece L ar C HI LYa HIok _ FF' LK1 cr1 Aw1 M1 model1 fx1 fx2 R1 pc1 R2 pc2 M2v W K HH1 AM1 MS MG FRZ).
  { intros a Ha Wa. pose proof (WP a Wa) as X. split; [| clear - X GSLO GSHI GSPT FBI; lia].
    unfold aclientw, aclient_g. right; left. split; [clear - X GSLO GSHI GSPT; lia| intros Y; clear - Y; lia]. }
  intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MG3 FR3 VV3.
  assert (EK13 : L5SAR.ek L ar (PNM.bparser_own s1 ++ LBX) FF' (sp - 104) 24 [] M1 M3).
  { intros a (Ha & Hc & _). apply FR3; [exact Ha|]. intros Wa. pose proof (WP a Wa) as X.
    destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF' LK1 cr1 Aw1 M1 _ (sp - 104) 24 a HH1 GSPT Hc) as [Y|Y]; [clear - X Y; lia| clear - X Y GSLO; lia]. }
  pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH1) as FRB1. pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH1) as BRB1.
  assert (ECK : forall v c, PMSPA.ec_at RSEGS M1 (fb + 1024) v c -> PMSPA.ec_at RSEGS M3 (fb + 1024) v c).
  { intros v0 c0 E0. apply (PMKA.ec_keepA RSEGS L ar _ FF' (sp - 104) 24 [] M1 M3 EK13 PMKA.wapp_nil FRB1 (fb + 1024) v0 c0); [| intros i _ rr []| exact E0].
    apply PMAUAR.aobjA_push. apply (PNAPAR.aobj_fbB FF fb (fb + 1024) 16 FOK); clear; lia. }
  apply (KR M3 model3); [| exact HID3| exact VIS3| exact FR3| exact MG3| exact ECK].
  split.
  { apply (PMAUK.binv_pieceW L ar HI M model LBX FF LK Aw sp 24576 (sp - 128) (sp - 104) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PNM.bparser_own s) G
             _ (PNM.bparser_own s1) M1 model1 LK1 cr1 Aw1 M3 model3 W BI HH3 AM3 MRT3 MG3 FR3).
    intros a Wa. pose proof (WP a Wa) as X. split; [unfold ocell; clear - X; lia| left; clear - X; lia]. }
  split.
  { apply (pre_after_call (PNM.bparser_own s1 ++ LBX) FF' (sp - 104) 24 [] M1 M3 fb s1 s1 str sm1 sm1 ax1 ax1 FRB1 EK13 (PMKA.wapp_nil) FOK'); [intros i _ rr []| exact RP1| | | exact GR1| |].
    - apply (PNAPAR.bparser_keepA L ar C HI HIok _ FF' LK1 cr1 Aw1 (vml_of model1) [] (sp - 104) 24 M1 M3 _ _ s1 HH1 EK13 (PMKA.wapp_nil)); [| apply incl_appl; apply incl_refl| intros i _ rr []| intros B m _ i _ rr []| exact PA1].
      apply PMAUAR.aobjA_push. apply (PNAPAR.aobj_fbB FF fb (fb + 464) PNM.PSIZE FOK); unfold PNM.PSIZE; clear; lia.
    - apply (PMKA.iss_keepA RSEGS PMA.AD L ar _ FF' (sp - 104) 24 [] M1 M3 EK13 (PMKA.wapp_nil) FRB1 BRB1 (fb + 96) str sm1); [| apply incl_appr; exact INCS| intros i _ rr []| intros c0 n0 p0 _ i _ rr []| exact IA1].
      apply PMAUAR.aobjA_push. apply (PNAPAR.aobj_fbB FF fb (fb + 96) 272 FOK); clear; lia.
    - apply (PMASK.base_keep L ar C LY _ FF' (sp - 104) 24 [] M1 M3 EK13); [intros a _ rr []| exact BASE1].
    - apply (berr_keep _ FF' (sp - 104) 24 [] M1 M3 ax1 EK13); [intros a _ rr []| exact ERR1]. }
  split; [exact STEP1|]. split; [exact AXL1|]. split; [exact CK1|]. split; [| exact EBB1].
  apply (L5C.u8_at_agree RSEGS M1 M3); [| exact R4a| exact R4b| exact SHC1].
  intros j Hj. apply FR3; [clear - Hj R4a R4b; lia|]. intros Wj. pose proof (WP _ Wj) as X. clear - X Hj SL160 GSPT GF2.
  pose proof (Z.div_le_upper_bound F 8 17592186044408 ltac:(lia) ltac:(lia)). lia.
Qed.


(* [comment removed for export] *)
Lemma en_finF K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 (fx5 fx9 : FPState) R5 R9 (pc5 mo : Z) (M9v : mem) :
  en_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  en_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  en_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 ->
  msteps RSEGS (st fx5 R5 pc5 (mrestrict (ahid Aw5 model5) M5)) (st fx9 R9 0xaf8f0 M9v) ->
  mem_grows (mrestrict (ahid Aw5 model5) M5) M9v ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ PMAUK.WretX F fl 0 (fun a => fb + 472 <= a < fb + 473 \/ F + 32 <= a < F + 48) a -> M9v (Z_to_bv 64 a) = mrestrict (ahid Aw5 model5) M5 (Z_to_bv 64 a)) ->
  L5.u8_at RSEGS M9v fl 0 -> L5.u8_at RSEGS M9v (fb + 472) mo -> (mo = 0 \/ mo = 1) ->
  getr R9 (reg 2) = Z_to_bv 64 sp ->
  (forall k, In k [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R9 (reg k) = Z_to_bv 64 (bv_unsigned (getr R (reg k)))) ->
  (forall k, In k [3; 4]%nat -> getr R9 (reg k) = getr R (reg k)) ->
  ( (exists v, 1 <= v <= 64 /\ PMSPA.ec_at RSEGS M5 (fb + 1024) v (pa_errcat_obj PMA.AD) /\ mo = 0 /\ PNST.bax_cat ax5 = true)
    \/ (PMSPA.ec_at RSEGS M5 (fb + 1024) e cat /\ PNRA.bprog_name R9 M5 s s5 sm sm5) ) ->
  PNRA.binv s5 -> (length (PNM.b_stk s) <= length (PNM.b_stk s5))%nat ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx5 R5 pc5 M5 model5) K.
Proof.
  intros CTX G LM MS9 MG9 FRZ9 FL0 MO9 Hmo Y2 YR Y34 POST INV5 LEN5.
  pose proof CTX as (Hw & HH & AM & K0 & ENT & FRM & FRS & FOK & SP32 & ARGS & RPRE & INCS & INV & EC0 & HE & UNR & CRED & KONT).
  destruct ENT as (Rra & RAok0 & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 6) with 24576 in *. change (24576 / 8) with 3072 in STKSH.
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof RAok0 as (Hr1 & Hr2).
  pose proof FOK as ((rs & Hfb) & Fal).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _).
  pose proof (WF _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 5) with 2048 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL, FSIMG, F1, F2.
  rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in FSIMG.
  assert (FBI : 6905856 <= fb) by (clear - F1 FSAPP FSIMG; lia).
  pose proof LM as (BI & RP1 & STEP1 & AXL1 & CK1 & SHC1 & EBB1).
  pose proof G as G'. unfold en_frame in G'.
  destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 0) with 64 in *. change (64 / 8) with 8 in *.
  pose proof BI as (HH1 & AM1 & MRT1 & INCA1 & INCL1 & ASTK1 & EK1 & DK1 & OWN1 & DSH1).
  set (FF' := (F, 0, sp - 128 + 32) :: FF) in *.
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
  pose proof (PMK.ret_to RSEGS fx9 R9 M9v 0xaf8f0 W_ae2e8 r F_ae2e8 eq_refl D_ae2e8 R9ra Hr1 Hr2) as MSr.
  set (Wx := fun a => fb + 472 <= a < fb + 473 \/ F + 32 <= a < F + 48).
  set (WR' := WR ++ [(F + 32, 16)]).
  assert (CLh : forall a, fb + 32 <= a < fb + 2040 -> aclient L ar LBX FF sp 24576 a).
  { intros a Ha. unfold aclient, aclient_g. do 3 right; left. exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd].
    change (ff_bytes 5) with 2048. split; [clear - Ha; lia| intros Y; clear - Ha Y; lia]. }
  assert (HF : forall a, fb + 32 <= a < fb + 2040 -> ~ (F <= a < F + 64)).
  { intros a Ha X. apply (GNCF a); [left; exact X| exact (CLh a Ha)]. }
  assert (BI' : PMAUK.binv L ar HI M model LBX FF LK Aw sp 24576 (sp - 128) (own sp R) F 0 WR' (PNM.bparser_own s5) M5 model5 LK5 cr5 Aw5).
  { destruct BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10). unfold PMAUK.binv.
    split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|]. split; [exact B5|]. split; [exact B6|].
    split; [| split; [exact B8| split; [exact B9| exact B10]]].
    intros a (Ha & Hc & Ho). apply B7. split; [exact Ha|]. split; [exact Hc|]. intros rr Hin Hr. apply (Ho rr); [unfold WR'; apply in_or_app; left; exact Hin| exact Hr]. }
  apply (PMAUK.retire_coreW L ar C HI LYa HIok M model LBX FF LK Aw sp 24576 (sp - 128) (sp - 104) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PNM.bparser_own s) G
           WR' (PNM.bparser_own s5) M5 model5 LK5 cr5 Aw5 Wx fx5 fx9 R5 pc5 R9 r M9v K BI').
  { intros a X. unfold Wx in X. destruct X as [X|X]; split.
    - apply (L5SAR.fframe_client L ar (PNM.bparser_own s5 ++ LBX) FF' 0 0 fb 5 rs); [right; exact Hfb| change (ff_bytes 5) with 2048; clear - X; lia].
    - intros O. apply (O (PNRA.o_p PMA.AD fb + 8, 8)); [unfold WR', WR, PNRA.W_brun; apply in_or_app; left; left; reflexivity| unfold L5.in_rng, PNRA.o_p, PMSP.o_p; cbn [fst snd pa_off_p PMA.AD PnLayoutA_b.ADDR_A]; clear - X; lia].
    - apply (L5SAR.fframe_client L ar (PNM.bparser_own s5 ++ LBX) FF' 0 0 F 0 (sp - 128 + 32)); [left; reflexivity| change (ff_bytes 0) with 64; clear - X; lia].
    - intros O. apply (O (F + 32, 16)); [unfold WR'; apply in_or_app; right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - X; lia]. }
  { intros a. unfold Wx. destruct (L5SAR.rng_dec a (fb + 472) (fb + 473)) as [X|X]; [left; left; exact X|].
    destruct (L5SAR.rng_dec a (F + 32) (F + 48)) as [Y|Y]; [left; right; exact Y| right; intros [Z0|Z0]; [exact (X Z0)| exact (Y Z0)]]. }
  { exact (msteps_trans _ _ _ _ MS9 MSr). }
  { exact MG9. }
  { exact FRZ9. }
  { exact FL0. }
  intros Mf modelf FZf MGf VISf AHf' MRTf AMf HHf.
  assert (AHf : ahpres L ar LBX FF sp 24576 WR M Mf).
  { destruct AHf' as (E1 & E2 & E3). split; [| split; [exact E2| exact E3]].
    intros a (Ha & Hc & Ho). apply E1. split; [exact Ha|]. split; [exact Hc|]. intros rr Hin Hr. unfold WR' in Hin. apply in_app_or in Hin. destruct Hin as [Hin|[<-|[]]].
    - exact (Ho rr Hin Hr).
    - unfold L5.in_rng in Hr. cbn [fst snd] in Hr. apply (GNCF a); [left; clear - Hr; lia| exact Hc]. } change (mrestrict H5 Mf = M9v) in VISf.
  assert (EKf : L5SAR.ek L ar (PNM.bparser_own s5 ++ LBX) FF 0 0 [(fb + 472, 1); (F + 32, 16)] M5 Mf).
  { apply (PMAUAR.wret_ek L ar C HI LY HIok LBX FF LK Aw sp 24576 (sp - 128) (sp - 104) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PNM.bparser_own s)
             (PNM.bparser_own s5 ++ LBX) LK5 cr5 Aw5 M5 Mf _ [(fb + 472, 1); (F + 32, 16)] Wx G HH1).
    - intros a X O. unfold Wx in X. destruct X as [X|X]; [apply (O (fb + 472, 1)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - X; lia]| apply (O (F + 32, 16)); [right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - X; lia]].
    - exact FZf. }
  pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB. pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH1) as BRB5.
  assert (MOf : L5.u8_at RSEGS Mf (op + 8) mo).
  { apply (proj1 (L5A.u8_at_vis H5 Mf (op + 8) mo (OVIS (op + 8) 1 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - O1; lia) ltac:(clear - O1; lia))). rewrite VISf. replace (op + 8) with (fb + 472) by (unfold op; clear; lia). exact MO9. }
  assert (WAPP8 : PMKA.wapp [(fb + 472, 1); (F + 32, 16)]).
  { apply PMKA.wapp_cons; [| apply PMKA.wapp_cons; [| apply PMKA.wapp_nil]]; cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; [destruct FA1 as [Y|Y]; clear - Y F1 F2; lia| destruct GFBIG as [Y|Y]; clear - Y GF1 GF2; lia]. }
  assert (OUT8 : forall a n, fb + 32 <= a -> a + n <= fb + 2040 -> (a + n <= op + 8 \/ op + 9 <= a) -> forall i, a <= i < a + n -> L5.outside [(fb + 472, 1); (F + 32, 16)] i).
  { intros a n Xa Xb X3 i Hi rr [<-|[<-|[]]] Hr; unfold L5.in_rng in Hr; cbn [fst snd] in Hr; [unfold op in X3; clear - Hi Hr X3; lia| apply (HF i); [clear - Hi Xa Xb; lia| clear - Hr; lia]]. }
  assert (OUTB8 : forall q m, In (q, m) (PNM.bparser_own s5 ++ LBX) -> forall i, q <= i < q + m -> L5.outside [(fb + 472, 1); (F + 32, 16)] i).
  { intros q m Hq i Hi rr [<-|[<-|[]]] Hr; unfold L5.in_rng in Hr; cbn [fst snd] in Hr.
    2:{ pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH1) as (WB1 & _). destruct (WB1 _ Hq) as (_ & _ & _ & _ & _ & BFA & _).
        pose proof (BFA (F, 0, sp - 128 + 32) (in_or_app FF' LK5 _ (or_introl (or_introl eq_refl)))) as Z2. cbn [ff_addr ff_class fst snd] in Z2. change (ff_bytes 0) with 64 in Z2. clear - Hi Hr Z2; lia. }
    destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q m op 416 HH1 Hq (PMAUAR.aobjA_push FF op 416 _ (PNAPAR.aobj_fbB FF fb op 416 FOK ltac:(unfold op; clear; lia) ltac:(unfold op; clear; lia)))) as [Z0|Z0]; unfold op in Z0; clear - Hi Hr Z0; lia. }
  set (s9 := PNBO.set_more s5 mo).
  assert (EO9 : PNM.bparser_own s9 = PNM.bparser_own s5) by (unfold s9; destruct s5; reflexivity).
  assert (PA9 : PNM.bparser_at RSEGS PMA.AD PMSPA.accA PMSPA.annA (pa_vp_parser PMA.AD) Mf op ois s9).
  { apply (bparser_set_moreS M5 Mf (pa_vp_parser PMA.AD) op ois s5 mo ltac:(clear - O1; lia) ltac:(clear - O1; lia)); [| | | exact MOf| exact Hmo| exact PA1].
    - intros i Hi Hn. destruct (Z_lt_le_dec i (op + 8)) as [X|X].
      + refine (proj1 (PMKA.agA_obj L ar _ FF 0 0 _ M5 Mf EKf WAPP8 FRB op 8 _ _) i _); [| apply OUT8; unfold op; clear; lia| clear - Hi X; lia].
        apply (PNAPAR.aobj_fbB FF fb op 8 FOK); unfold op; clear; lia.
      + refine (proj1 (PMKA.agA_obj L ar _ FF 0 0 _ M5 Mf EKf WAPP8 FRB (op + 9) 407 _ _) i _); [| apply OUT8; unfold op; clear; lia| clear - Hi X Hn; lia].
        apply (PNAPAR.aobj_fbB FF fb (op + 9) 407 FOK); unfold op; clear; lia.
    - intros i Hi. refine (PMKA.agsh_obj L ar _ FF 0 0 _ M5 Mf EKf WAPP8 FRB op 416 _ i Hi). apply (PNAPAR.aobj_fbB FF fb op 416 FOK); unfold op; clear; lia.
    - intros q m Hq. assert (HqL : In (q, m) (PNM.bparser_own s5 ++ LBX)) by (apply in_or_app; left; exact Hq). destruct (BRB5 _ HqL) as (B0 & B1). cbn [fst snd] in B0, B1.
      split; [exact B0|]. split; [clear - B1; lia|]. apply (PMKA.agA_blk L ar _ FF 0 0 _ M5 Mf EKf WAPP8 BRB5 q m HqL). apply OUTB8. exact HqL. }
  assert (IA9 : PM.iss_at RSEGS PMA.AD PMSPA.accA Mf ois str sm5).
  { apply (PMKA.iss_keepA RSEGS PMA.AD L ar _ FF 0 0 _ M5 Mf EKf WAPP8 FRB BRB5 ois str sm5); [| | | | exact IA1].
    - apply (PNAPAR.aobj_fbB FF fb ois 272 FOK); unfold ois; clear; lia.
    - apply incl_appr. exact INCS.
    - apply OUT8; unfold ois, op; clear; lia.
    - intros c0 n0 p0 E0. unfold PMKA.blk_out. apply OUTB8. apply in_or_app; right. apply INCS. rewrite E0. left; reflexivity. }
  assert (BASE9 : PMSTA.base_okA RSEGS PMA.AD Mf).
  { apply (PMASK.base_keep L ar C LY _ FF 0 0 _ M5 Mf EKf); [| exact BASE1]. intros a Ha rr [<-|[<-|[]]] Hr; unfold L5.in_rng in Hr; cbn [fst snd] in Hr; [clear - Ha Hr FBI; lia| clear - Ha Hr GFR; lia]. }
  assert (ERR9 : PNSTA.berr_okA RSEGS PMA.AD PMA.AAD PMA.AN Mf ax5).
  { apply (berr_keep _ FF 0 0 _ M5 Mf ax5 EKf); [| exact ERR1]. intros a Ha rr [<-|[<-|[]]] Hr; unfold L5.in_rng in Hr; cbn [fst snd] in Hr; [clear - Ha Hr FBI; lia| clear - Ha Hr GFR; lia]. }
  assert (PRE9 : PNRA.brun_pre RSEGS PMA.AD PMA.AN PMA.AAD Mf fb s9 str sm5 ax5).
  { apply (pre_after_call _ FF 0 0 _ M5 Mf fb s5 s9 str sm5 sm5 ax5 ax5 FRB EKf WAPP8 FOK); [| exact RP1| exact PA9| exact IA9| unfold s9; exact GR1| exact BASE9| exact ERR9].
    intros i Hi. apply (OUT8 i 1); unfold op; clear - Hi; lia. }
  assert (ECf : forall v c, PMSPA.ec_at RSEGS M5 (fb + 1024) v c -> PMSPA.ec_at RSEGS Mf (fb + 1024) v c).
  { intros v c EC5. apply (PMKA.ec_keepA RSEGS L ar _ FF 0 0 _ M5 Mf EKf WAPP8 FRB (fb + 1024) v c); [| | exact EC5].
    - apply (PNAPAR.aobj_fbB FF fb (fb + 1024) 16 FOK); clear; lia.
    - apply OUT8; unfold op; clear; lia. }
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
      unfold s9, PNRA.bprog_name. cbn [PNBO.set_more PNM.b_stk PNM.b_src PNM.b_nb PNM.b_tb]. unfold PNRA.bprog_name in PROG.
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
Lemma en_call_cs K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 (fx1 : FPState) R1 (ra e1 c1 : Z) :
  PNRAa.read_cstring_spec L ar HI ->
  en_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  en_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  en_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
  PNRA.binv s1 -> PMSPA.ec_at RSEGS M1 (fb + 1024) e1 c1 -> 0 <= e1 <= 64 ->
  PM.unread (PNM.b_src s1) sm1 < 2 ^ 26 -> PM.vs_size (PNM.b_nb s1) + PM.unread (PNM.b_src s1) sm1 <= 2 ^ 26 ->
  getr R1 (reg 1) = Z_to_bv 64 ra -> L5.ra_ok ra -> getr R1 (reg 2) = Z_to_bv 64 (sp - 128) ->
  getr R1 (reg 3) = Z_to_bv 64 (pa_gp PMA.AD) -> getr R1 (reg 4) = Z_to_bv 64 (hl_tp L) ->
  getr R1 (reg 10) = Z_to_bv 64 (fb + 464) -> getr R1 (reg 11) = Z_to_bv 64 (fb + 464 + 344) -> getr R1 (reg 12) = Z_to_bv 64 (fb + 1024) ->
  (forall (fx2 : FPState) R2 (M3 : mem) model3 LK3 Aw3 s3 sm3 ax3 cr3,
      regs_preserved R1 R2 ->
      en_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 ->
      PMSP.src_step (PNM.b_src s1) (PNM.b_src s3) sm1 sm3 -> PNST.bax_le ax1 ax3 ->
      ( (exists v, 1 <= v <= 64 /\ PMSPA.ec_at RSEGS M3 (fb + 1024) v (pa_errcat_obj PMA.AD) /\ PNM.b_more s3 = 0 /\ PNST.bax_cat ax3 = true
                   /\ (length (PNM.b_stk s1) <= length (PNM.b_stk s3))%nat /\ PNRA.binv s3)
        \/ (PMSPA.ec_at RSEGS M3 (fb + 1024) e1 c1 /\ PNRA.binv s3 /\ PNRA.bprog_cs 0 R2 M3 s1 s3 sm1 sm3) ) ->
      (forall a, sp - 128 <= a < sp - 104 -> M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx2 R2 ra M3 model3) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 (PNL.pn_read_cstring PMA.AN) M1 model1) K.
Proof.
  intros RCS CTX G LM INV1 EC1 HE1 UN1 SZ1 X1 RAok X2 X3 X4 X10 X11 X12 KR.
  pose proof CTX as (Hw & HH & AM & K0 & ENT & FRM & FRS & FOK & SP32 & ARGS & RPRE & INCS & INV & EC0 & HE & UNR & CRED & KONT).
  destruct ENT as (Rra & RAok0 & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 6) with 24576 in *. change (24576 / 8) with 3072 in STKSH.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof FOK as ((rs & Hfb) & Fal).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _).
  pose proof (WF _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 5) with 2048 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL, FSIMG, F1, F2.
  rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in FSIMG.
  assert (FBI : 6905856 <= fb) by (clear - F1 FSAPP FSIMG; lia).
  pose proof LM as (BI & RP1 & STEP1 & AXL1 & CK1 & SHC1 & EBB1).
  pose proof G as G'. unfold en_frame in G'.
  destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 0) with 64 in *. change (64 / 8) with 8 in *.
  pose proof BI as (HH1 & AM1 & MRT1 & INCA1 & INCL1 & ASTK1 & EK1 & DK1 & OWN1 & DSH1).
  set (FF' := (F, 0, sp - 128 + 32) :: FF) in *.
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
  pose proof GFR as (GF1 & GF2 & GF3 & _).
  assert (R4a : 0 <= F / 8 + 2147450880) by (clear - GF1; pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)); lia).
  assert (R4b : F / 8 + 2147450880 + 1 <= 2 ^ 64) by (clear - GF2; pose proof (Z.div_le_upper_bound F 8 17592186044408 ltac:(lia) ltac:(lia)); lia).
  assert (DF1 : 0 <= F / 8) by (apply Z.div_pos; clear - GF1; lia).
  assert (DF2 : F / 8 <= 17592186044408) by (apply Z.div_le_upper_bound; clear - GF2; lia).
  assert (CRED1 : PMSP.credit_le (pot L ar s1) cr1).
  { revert CRED CK1. unfold PMSP.credit_le, PMSP.credit_keep. intros (A1 & A2) (B1 & B2). split; [clear - A1 B1; lia| clear - A2 B2; lia]. }
  assert (WRR : forall rr a, In rr WR -> L5.in_rng rr a -> (fb + 32 <= a < fb + 2040) \/ (65536 <= a < 6905856)).
  { intros rr a Hin Hr. unfold WR, PNRA.W_brun, PGS.W_srcfG, PNST.berr_W, PNST.cat_W, PNST.dec_W, PNRA.o_src, PNRA.o_is, PNRA.o_bb, PNRA.o_nb, PNRA.o_tb, PNRA.o_stk, PNRA.o_ec, PNRA.o_p, PMSP.o_p, PMSP.o_is, PMSP.o_ec in Hin.
    cbn [app pa_off_p pa_off_is pa_off_ec pa_errcat_guard pa_atexit PMA.AD ADDR_A PMA.AN NADDR_A PNL.pn_inf_guard PNL.pn_nan_guard PNL.pn_inf_obj PNL.pn_nan_obj] in Hin.
    unfold PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK in Hin. unfold L5.in_rng in Hr.
    repeat (destruct Hin as [<-|Hin]; [cbn [fst snd] in Hr; clear - Hr; lia|]). destruct Hin. }
  assert (WAV : forall rr a, In rr WR -> L5.in_rng rr a -> ~ (sp - 128 <= a < sp) /\ ~ (F / 8 + SB <= a < F / 8 + SB + 8)).
  { intros rr a Hin Hr. unfold SB. destruct (WRR rr a Hin Hr) as [X|X].
    - split; [clear - X GSLO F2 FSCEIL; lia| destruct FA1 as [Y|Y]; clear - X Y DF1 DF2 F1 F2; lia].
    - split; [clear - X GSLO GSHI GSPT; lia| clear - X DF1 GF3; pose proof (Z.div_le_lower_bound F 8 863232 ltac:(lia) ltac:(lia)); lia]. }
  unfold PNRAa.read_cstring_spec, PNRA.read_cstring_spec, PNRA.brun_spec in RCS.
  apply (RCS 0 (or_introl eq_refl) fx1 R1 M1 model1 K LBX FF' LK1 Aw1 cr1 (sp - 128) ra fb c1 e1 s1 str sm1 ax1 HH1 AM1 K0).
  { unfold PMSPA.entryA. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact X1|]. split; [exact RAok|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|].
    change (PMSPA.pm_scr 5) with 22528. change (22528 / 8) with 2816.
    split; [apply (L5SAR.astk_sub ar M1 M1 sp 24576 128 22528 ASTK1 (mem_grows_refl M1)); [clear; lia| clear; lia| clear; lia| replace (sp - 128) with (sp + (-8) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact A16]|].
    apply (PMKA.shadow_zero_sub M1 (sp - 24576) 3072); [| | clear; lia| clear; lia| clear; lia|].
    - apply PMKA.mod16_8'. replace (sp - 24576) with (sp + (-1536) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16.
    - apply PMKA.mod16_8'. replace (sp - 128 - 22528) with (sp + (-1416) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16.
    - apply (PMKA.stksh_keepA L ar LBX FF sp 24576 WR M M1 EK1 WAPPR (sp - 24576) 3072); [clear - SLO SPT; lia| clear - SLO; lia| clear - SHI SPT; lia| | clear; lia| exact STKSH].
      apply PMKA.mod16_8'. replace (sp - 24576) with (sp + (-1536) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  { apply (PMAUAR.ffroomB_push PNRA.FCB 6 5 FF LK LK1 _ FRM INCL1); [exact NDF1| clear; lia]. }
  { apply (PMAUAR.ffrsA_push FF sp (sp - 128) F 0 (sp - 128 + 32) FRS); clear; lia. }
  { exact FOK'. }
  { replace (sp - 128) with (sp + (-4) * 32) by (clear; lia). rewrite Z_mod_plus_full. exact SP32. }
  { unfold PNRA.bargs_cs, PNRA.bcs_off, PNRA.bcs_str, PNRA.o_p, PMSP.o_p, PNRA.o_ec, PMSP.o_ec. cbn [Z.eqb pa_off_p pa_off_ec PMA.AD PnLayoutA_b.ADDR_A]. unfold PNM.OFF_NB.
    rewrite L5K.rl10, L5K.rl11, L5K.rl12. split; [exact X10|]. split; [exact X11|]. split; [exact X12| exact SZ1]. }
  { exact RP1. } { exact INCS. } { exact INV1. } { exact EC1. } { exact HE1. } { exact UN1. } { exact CRED1. }
  intros fx6 R6 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 RP6 POST6 HP6 CK6 MRT6 INCL6 INCA6 AM6 HH6.
  change (PMSPA.pm_scr 5) with 22528 in HP6. fold WR in HP6.
  destruct POST6 as (PRE6 & STEP6 & AXL6 & RES6 & BB6). unfold PNRA.bb_post in BB6.
  change (PNRA.o_ec PMA.AD fb) with (fb + 1024) in RES6.
  assert (BI6 : PMAUK.binv L ar HI M model LBX FF LK Aw sp 24576 (sp - 128) (own sp R) F 0 WR (PNM.bparser_own s6) M6 model6 LK6 cr6 Aw6).
  { apply (PMAUK.binv_callee L ar C HI HIok M model LBX FF LK Aw sp 24576 (sp - 128) (sp - 104) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PNM.bparser_own s) G
             WR WR (PNM.bparser_own s1) [] (PNM.bparser_own s6) M1 model1 LK1 cr1 Aw1 M6 model6 LK6 cr6 Aw6 22528 WR BI HP6 HH6 AM6 MRT6 INCA6 INCL6);
      [clear; lia| clear; lia| intros rr a Hin Hr; destruct (WAV rr a Hin Hr) as (Y1 & Y2); split; [unfold ocell; clear - Y1; lia| exact Y2]| intros a _ X; exact X| intros a X; exact X]. }
  pose proof (proj1 HP6 : ek L ar LBX FF' (sp - 128) 22528 WR M1 M6) as EK6.
  apply (KR fx6 R6 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 RP6).
  - split; [exact BI6|]. split; [exact PRE6|].
    split; [exact (PNBKA.src_step_trans _ _ _ _ _ _ STEP1 STEP6)|]. split; [exact (PNST.bax_le_trans _ _ _ AXL1 AXL6)|].
    split; [exact (PNBKA.credit_keep_trans _ _ _ _ _ _ CK1 CK6)|].
    split; [| rewrite BB6; exact EBB1].
    apply (L5C.u8_at_agree RSEGS M1 M6); [| exact R4a| exact R4b| exact SHC1].
    intros j Hj. apply EK6. split; [clear - Hj R4a R4b; lia|]. split.
    + apply (L5SAR.fframe_shadow_client L ar _ FF' (sp - 128) 22528 F 0 (sp - 128 + 32)); [left; reflexivity|]. change (ff_bytes 0) with 64.
      unfold in_shadow_of, S. rewrite (proj1 (proj2 GF8)). unfold SB. clear - Hj; lia.
    + intros rr Hin Hr. destruct (WAV rr _ Hin Hr) as (_ & Y). apply Y. unfold SB. clear - Hj; lia.
  - exact STEP6.
  - exact AXL6.
  - exact RES6.
  - intros a Ha. apply EK6. split; [clear - Ha GSLO GSHI GSPT; lia|]. split.
    + apply (L5SAR.stack_client L ar _ FF' (sp - 128) 22528 a); clear - Ha GSLO GSHI GSPT; lia.
    + intros rr Hin Hr. destruct (WAV rr a Hin Hr) as (Y & _). apply Y. clear - Ha; lia.
Qed.


(* [comment removed for export] *)
Lemma en_call_val K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 (fx1 : FPState) R1 (ra p n : Z) :
  PMA.validate_spec L ar HI ->
  en_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  en_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  en_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
  getr R1 (reg 1) = Z_to_bv 64 ra -> L5.ra_ok ra -> getr R1 (reg 2) = Z_to_bv 64 (sp - 128) ->
  getr R1 (reg 3) = Z_to_bv 64 (pa_gp PMA.AD) -> getr R1 (reg 4) = Z_to_bv 64 (hl_tp L) ->
  getr R1 (reg 10) = Z_to_bv 64 p -> getr R1 (reg 11) = Z_to_bv 64 n ->
  0 <= n < 2 ^ 26 -> 0 <= p -> (n = 0 \/ 0 < p) -> p + n <= 2 ^ 47 ->
  L5.defined M1 p n -> aacc M1 p n ->
  (forall a, p <= a < p + n -> ahid Aw1 model1 (Z_to_bv 64 a) = false /\ ahid Aw1 model1 (Z_to_bv 64 (S a)) = false) ->
  (n = 0 \/ sp - 128 <= p \/ p + n <= sp - 128 - 12288) ->
  (forall (fx2 : FPState) R2 (M3 : mem) model3,
      regs_preserved R1 R2 ->
      en_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK1 Aw1 s1 sm1 ax1 cr1 ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 128 - 12288 <= a < sp - 128) -> M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
      (forall v c, PMSPA.ec_at RSEGS M1 (fb + 1024) v c -> PMSPA.ec_at RSEGS M3 (fb + 1024) v c) ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx2 R2 ra M3 model3) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 (pa_validate PMA.AD) M1 model1) K.
Proof.
  intros VAL CTX G LM X1 RAok X2 X3 X4 X10 X11 Hn Hp Hp0 Hp47 DEFp ACCp VISp LOCp KR.
  pose proof CTX as (Hw & HH & AM & K0 & ENT & FRM & FRS & FOK & SP32 & ARGS & RPRE & INCS & INV & EC0 & HE & UNR & CRED & KONT).
  destruct ENT as (Rra & RAok0 & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 6) with 24576 in *. change (24576 / 8) with 3072 in STKSH.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof FOK as ((rs & Hfb) & Fal).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _).
  pose proof (WF _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 5) with 2048 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL, FSIMG, F1, F2.
  rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in FSIMG.
  assert (FBI : 6905856 <= fb) by (clear - F1 FSAPP FSIMG; lia).
  pose proof LM as (BI & RP1 & STEP1 & AXL1 & CK1 & SHC1 & EBB1).
  pose proof G as G'. unfold en_frame in G'.
  destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 0) with 64 in *. change (64 / 8) with 8 in *.
  pose proof BI as (HH1 & AM1 & MRT1 & INCA1 & INCL1 & ASTK1 & EK1 & DK1 & OWN1 & DSH1).
  set (FF' := (F, 0, sp - 128 + 32) :: FF) in *.
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
  pose proof GFR as (GF1 & GF2 & GF3 & _).
  assert (R4a : 0 <= F / 8 + 2147450880) by (clear - GF1; pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)); lia).
  assert (R4b : F / 8 + 2147450880 + 1 <= 2 ^ 64) by (clear - GF2; pose proof (Z.div_le_upper_bound F 8 17592186044408 ltac:(lia) ltac:(lia)); lia).
  assert (ASTKv : L5CA.astk ar M1 (sp - 128) 12288).
  { apply (L5SAR.astk_sub ar M1 M1 sp 24576 128 12288 ASTK1 (mem_grows_refl M1)); [clear; lia| clear; lia| clear; lia|].
    replace (sp - 128) with (sp + (-8) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  unfold PMA.validate_spec, PMSPA.validate_spec, PMSPA.scan_spec in VAL.
  apply (VAL fx1 R1 M1 model1 K (PNM.bparser_own s1 ++ LBX) FF' LK1 Aw1 cr1 p n (sp - 128) ra HH1 AM1 K0).
  { unfold PMSPA.entryA. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact X1|]. split; [exact RAok|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|].
    change (PMSPA.pm_scr 0) with 12288. change (12288 / 8) with 1536.
    split; [exact ASTKv|].
    apply (PMKA.shadow_zero_sub M1 (sp - 24576) 3072); [| | clear; lia| clear; lia| clear; lia|].
    - apply PMKA.mod16_8'. replace (sp - 24576) with (sp + (-1536) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16.
    - apply PMKA.mod16_8'. replace (sp - 128 - 12288) with (sp + (-776) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16.
    - apply (PMKA.stksh_keepA L ar LBX FF sp 24576 WR M M1 EK1 WAPPR (sp - 24576) 3072); [clear - SLO SPT; lia| clear - SLO; lia| clear - SHI SPT; lia| | clear; lia| exact STKSH].
      apply PMKA.mod16_8'. replace (sp - 24576) with (sp + (-1536) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  { apply (PMAUAR.ffroomA_push 6 0 FF LK LK1 _ FRM INCL1); [exact NDF1| clear; lia]. }
  { apply (PMAUAR.ffrsA_push FF sp (sp - 128) F 0 (sp - 128 + 32) FRS); clear; lia. }
  { rewrite L5K.rl10. exact X10. } { rewrite L5K.rl11. exact X11. }
  { exact Hn. } { exact Hp. } { exact Hp0. } { exact Hp47. } { exact DEFp. } { exact ACCp. } { exact VISp. }
  { change (PMSPA.pm_scr 0) with 12288. exact LOCp. }
  { exact BASE1. }
  intros fx6 R6 M6 model6 RP6 FB6 MG6 MRT6 AM6 HH6.
  change (PMSPA.pm_scr 0) with 12288 in FB6.
  assert (AH6 : L5CA.ahpres L ar (PNM.bparser_own s1 ++ LBX) FF' (sp - 128) 12288 [] M1 M6).
  { apply (PMAUAR.ahpres_of_frame_but L ar C HI LY HIok (PNM.bparser_own s1 ++ LBX) FF' LK1 cr1 Aw1 M1 M6 (vml_of model1) (sp - 128) 12288 HH1);
      [clear - SPT; lia| clear - SLO; lia| clear; lia| exact FB6| exact MG6|].
    pose proof ASTKv as (_ & _ & _ & _ & X & _). exact X. }
  assert (BI6 : PMAUK.binv L ar HI M model LBX FF LK Aw sp 24576 (sp - 128) (own sp R) F 0 WR (PNM.bparser_own s1) M6 model6 LK1 cr1 Aw1).
  { apply (PMAUK.binv_callee L ar C HI HIok M model LBX FF LK Aw sp 24576 (sp - 128) (sp - 104) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PNM.bparser_own s) G
             WR WR (PNM.bparser_own s1) (PNM.bparser_own s1) (PNM.bparser_own s1) M1 model1 LK1 cr1 Aw1 M6 model6 LK1 cr1 Aw1 12288 [] BI AH6 HH6 AM6 MRT6 (incl_refl _) (incl_refl _));
      [clear; lia| clear; lia| intros rr a []| intros a _ _ rr []| intros a X; exact X]. }
  pose proof (proj1 AH6 : ek L ar (PNM.bparser_own s1 ++ LBX) FF' (sp - 128) 12288 [] M1 M6) as EK6.
  pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH1) as FRB1. pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH1) as BRB1.
  assert (FRA : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 128 - 12288 <= a < sp - 128) -> M6 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { intros a Ha Hn0. pose proof (FB6 (Z_to_bv 64 a)) as X. rewrite L5.unsigned_lit in X by exact Ha. apply X. intros rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. apply Hn0. clear - Hr; lia. }
  apply (KR fx6 R6 M6 model6 RP6); [| exact FRA|].
  2:{ intros v0 c0 E0. apply (PMKA.ec_keepA RSEGS L ar _ FF' (sp - 128) 12288 [] M1 M6 EK6 PMKA.wapp_nil FRB1 (fb + 1024) v0 c0); [| intros i _ rr []| exact E0].
      apply PMAUAR.aobjA_push. apply (PNAPAR.aobj_fbB FF fb (fb + 1024) 16 FOK); clear; lia. }
  split; [exact BI6|].
  split.
  { apply (pre_after_call (PNM.bparser_own s1 ++ LBX) FF' (sp - 128) 12288 [] M1 M6 fb s1 s1 str sm1 sm1 ax1 ax1 FRB1 EK6 (PMKA.wapp_nil) FOK'); [intros i _ rr []| exact RP1| | | exact GR1| |].
    - apply (PNAPAR.bparser_keepA L ar C HI HIok _ FF' LK1 cr1 Aw1 (vml_of model1) [] (sp - 128) 12288 M1 M6 _ _ s1 HH1 EK6 (PMKA.wapp_nil)); [| apply incl_appl; apply incl_refl| intros i _ rr []| intros B m _ i _ rr []| exact PA1].
      apply PMAUAR.aobjA_push. apply (PNAPAR.aobj_fbB FF fb (fb + 464) PNM.PSIZE FOK); unfold PNM.PSIZE; clear; lia.
    - apply (PMKA.iss_keepA RSEGS PMA.AD L ar _ FF' (sp - 128) 12288 [] M1 M6 EK6 (PMKA.wapp_nil) FRB1 BRB1 (fb + 96) str sm1); [| apply incl_appr; exact INCS| intros i _ rr []| intros c0 n0 p0 _ i _ rr []| exact IA1].
      apply PMAUAR.aobjA_push. apply (PNAPAR.aobj_fbB FF fb (fb + 96) 272 FOK); clear; lia.
    - apply (PMASK.base_keep L ar C LY _ FF' (sp - 128) 12288 [] M1 M6 EK6); [intros a _ rr []| exact BASE1].
    - apply (berr_keep _ FF' (sp - 128) 12288 [] M1 M6 ax1 EK6); [intros a _ rr []| exact ERR1]. }
  split; [exact STEP1|]. split; [exact AXL1|]. split; [exact CK1|]. split; [| exact EBB1].
  apply (L5C.u8_at_agree RSEGS M1 M6); [| exact R4a| exact R4b| exact SHC1].
  intros j Hj. apply FRA; [clear - Hj R4a R4b; lia|]. clear - Hj GSLO GSHI GSPT GF2 SLO. pose proof (Z.div_le_upper_bound F 8 17592186044408 ltac:(lia) ltac:(lia)). lia.
Qed.


Lemma in_elem_of (x : Z) (l : list Z) : In x l -> base.elem_of x l.
Proof. induction l as [|y l IH]; [intros []|]. intros [E|H]; [subst y; left| right; apply IH; exact H]. Qed.

(* [comment removed for export] *)
Lemma en_piece_nb K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1
      (fx1 fx2 : FPState) R1 R2 (pc1 pc2 : Z) (M2v : mem) (W : Z -> Prop) (x' : PM.vstr) :
  en_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  en_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  en_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
  msteps RSEGS (st fx1 R1 pc1 (mrestrict (ahid Aw1 model1) M1)) (st fx2 R2 pc2 M2v) ->
  mem_grows (mrestrict (ahid Aw1 model1) M1) M2v ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ W a -> M2v (Z_to_bv 64 a) = mrestrict (ahid Aw1 model1) M1 (Z_to_bv 64 a)) ->
  (forall a, W a -> (fb + 808 <= a < fb + 832) \/ (exists B m, In (B, m) (PM.vs_own (PNM.b_nb s1)) /\ B <= a < B + m) \/ (sp - 128 <= a < sp - 104)) ->
  PM.vs_own x' = PM.vs_own (PNM.b_nb s1) -> PM.tb_ok x' (PNM.b_ng s1) ->
  PM.pot_text (PMSPA.HV L ar) x' (PNM.b_ng s1) = PM.pot_text (PMSPA.HV L ar) (PNM.b_nb s1) (PNM.b_ng s1) ->
  (forall (M3 : mem), (forall a, 0 <= a < 2 ^ 64 -> ~ W a -> M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> mem_grows M1 M3 -> mrestrict (ahid Aw1 model1) M3 = M2v ->
                      PM.vstr_at RSEGS PMSPA.accA M3 (fb + 464 + 344) x') ->
  (forall (M3 : mem) model3,
      en_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK1 Aw1 (set_cs 0 s1 x' (PNM.b_ng s1)) sm1 ax1 cr1 ->
      ahid Aw1 model3 = ahid Aw1 model1 -> mrestrict (ahid Aw1 model1) M3 = M2v ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ W a -> M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> mem_grows M1 M3 ->
      (forall v c, PMSPA.ec_at RSEGS M1 (fb + 1024) v c -> PMSPA.ec_at RSEGS M3 (fb + 1024) v c) ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx2 R2 pc2 M3 model3) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 pc1 M1 model1) K.
Proof.
  intros CTX G LM MS MG FRZ WN EOWN TBOK POTE VS KR.
  pose proof CTX as (Hw & HH & AM & K0 & ENT & FRM & FRS & FOK & SP32 & ARGS & RPRE & INCS & INV & EC0 & HE & UNR & CRED & KONT).
  destruct ENT as (Rra & RAok0 & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 6) with 24576 in *.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof FOK as ((rs & Hfb) & Fal).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _).
  pose proof (WF _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 5) with 2048 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL, FSIMG, F1, F2.
  rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in FSIMG.
  assert (FBI : 6905856 <= fb) by (clear - F1 FSAPP FSIMG; lia).
  pose proof LM as (BI & RP1 & STEP1 & AXL1 & CK1 & SHC1 & EBB1).
  pose proof G as G'. unfold en_frame in G'.
  destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 0) with 64 in *. change (64 / 8) with 8 in *.
  pose proof BI as (HH1 & AM1 & MRT1 & INCA1 & INCL1 & ASTK1 & EK1 & DK1 & OWN1 & DSH1).
  set (FF' := (F, 0, sp - 128 + 32) :: FF) in *.
  assert (FOK' : PNRA.frame_okB FF' fb). { split; [exists rs; right; exact Hfb| exact Fal]. }
  pose proof RP1 as (PA1 & IA1 & VIS1 & VREF1 & OACC1 & BASE1 & ERR1 & GR1).
  change (PNRA.o_p PMA.AD fb) with (fb + 464) in PA1, IA1, VIS1, VREF1, OACC1. change (PNRA.o_is PMA.AD fb) with (fb + 96) in PA1, IA1. change (PNRA.o_v PMA.AD fb) with (fb + 432) in VIS1, VREF1.
  change (PNM.PSIZE + 8) with 424 in OACC1.
  pose proof GFR as (GF1 & GF2 & _).
  assert (R4a : 0 <= F / 8 + 2147450880) by (clear - GF1; lia).
  assert (R4b : F / 8 + 2147450880 + 1 <= 2 ^ 64) by (clear - GF2; pose proof (Z.div_le_upper_bound F 8 17592186044408 ltac:(lia) ltac:(lia)); lia).
  pose proof (PMASK.stk_vis L ar C HI LY HIok _ FF' LK1 cr1 Aw1 M1 model1 sp 24576 128 HH1 ASTK1 ltac:(lia)) as (SL160 & SH160 & SWR).
  set (H1 := ahid Aw1 model1) in *.
  set (op := fb + 464) in *. set (ois := fb + 96) in *.
  set (s3 := set_cs 0 s1 x' (PNM.b_ng s1)) in *.
  pose proof FSAPP as (FA0 & FA1 & FA2). unfold BIGSHADOW_LO, BIGSHADOW_HI in FA1.
  pose proof GFR as (_ & _ & GF3 & _).
  assert (AOP : PMSPA.aobjA FF' op 416) by (apply PMAUAR.aobjA_push; apply (PNAPAR.aobj_fbB FF fb op 416 FOK); unfold op; clear; lia).
  assert (OWNB : forall B m, In (B, m) (PM.vs_own (PNM.b_nb s1)) -> In (B, m) (PNM.bparser_own s1 ++ LBX)).
  { intros B m Hin. apply in_or_app; left. exact (PNBOA.PNM_own_nb s1 B m Hin). }
  assert (WB1 : forall B m a, In (B, m) (PM.vs_own (PNM.b_nb s1)) -> B <= a < B + m ->
                  (a + 1 <= op \/ op + 416 <= a) /\ ~ (65536 <= a < 6905856) /\ (a + 1 <= 2147446784 \/ 17594333495296 <= a) /\ 0 <= a < 2 ^ 47 /\ ~ (sp - 128 <= a < sp) /\ ~ (F <= a < F + 64)).
  { intros B m a Hin Ha. pose proof (OWNB B m Hin) as HinL.
    destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ B m op 416 HH1 HinL AOP) as [Z0|Z0].
    all: pose proof (blk_ceil _ _ _ _ _ _ _ _ _ HH1 HinL) as (BC & (BA0 & BAPP & BA2)); unfold BIGSHADOW_LO, BIGSHADOW_HI in BAPP.
    all: pose proof (PMASK.blk_img L ar C HI LY HIok _ _ _ _ _ _ _ B m HH1 HinL) as BIMG.
    all: pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH1) as (WBx & _); destruct (WBx _ HinL) as (_ & _ & _ & _ & _ & BFA & _).
    all: pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH1 _ HinL) as (Q0 & Q1); cbn [fst snd] in Q0, Q1.
    all: pose proof (BFA (fb, 5, rs) (in_or_app FF' LK1 (fb, 5, rs) (or_introl (or_intror Hfb)))) as Zf; cbn [ff_addr ff_class fst snd] in Zf; change (ff_bytes 5) with 2048 in Zf.
    all: pose proof (BFA (F, 0, sp - 128 + 32) (in_or_app FF' LK1 _ (or_introl (or_introl eq_refl)))) as ZF; cbn [ff_addr ff_class fst snd] in ZF; change (ff_bytes 0) with 64 in ZF.
    all: clear - Ha Z0 BC BA0 BAPP BA2 BIMG Q0 Q1 Zf ZF GSLO GSHI GSPT SLO SHI SPT; lia. }
  assert (WAPP : forall a, W a -> ~ (65536 <= a < 6905856) /\ (a + 1 <= 2147446784 \/ 17594333495296 <= a) /\ 0 <= a < 2 ^ 47 /\ ~ (sp - 104 <= a < sp) /\ ~ (F <= a < F + 64)).
  { intros a Wa. destruct (WN a Wa) as [X|[(B & m & Hin & X)|X]].
    3:{ split; [clear - X GSLO FSCEIL FSAPP; lia|]. split; [right; clear - X SL160 SHI SPT; lia|]. split; [clear - X GSLO GSHI GSPT; lia|]. split; [clear - X; lia|]. clear - X GFCEIL GSLO; lia. }
    - split; [clear - X FBI; lia|]. split; [destruct FA1 as [Y|Y]; clear - X Y F1 F2; lia|]. split; [clear - X F2 FSCEIL GSLO GSHI GSPT FBI; lia|].
      split; [clear - X GSLO F2 FSCEIL; lia|]. intros Y. apply (GNCF a); [left; exact Y|]. unfold aclient, aclient_g. do 3 right; left. exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd].
      change (ff_bytes 5) with 2048. split; [clear - X; lia| intros Y0; clear - X Y0; lia].
    - destruct (WB1 B m a Hin X) as (_ & Y1 & Y2 & Y3 & Y5 & Y6). split; [exact Y1|]. split; [exact Y2|]. split; [exact Y3|]. split; [clear - Y5; lia| exact Y6]. }
  assert (NSH : forall i, 0 <= i < 2 ^ 47 -> ~ W (i / 8 + 2147450880)).
  { intros i Hi Wa. destruct (WAPP _ Wa) as (_ & Y & _). pose proof (Z.div_pos i 8 ltac:(clear - Hi; lia) ltac:(clear; lia)) as D0.
    pose proof (Z.div_lt_upper_bound i 8 17592186044416 ltac:(clear; lia) ltac:(clear - Hi; lia)) as D1. clear - Y D0 D1. lia. }
  apply (L5SAR.apiece L ar C HI LYa HIok _ FF' LK1 cr1 Aw1 M1 model1 fx1 fx2 R1 pc1 R2 pc2 M2v W K HH1 AM1 MS MG FRZ).
  { intros a Ha Wa. destruct (WAPP a Wa) as (Y1 & _). split; [| exact Y1]. destruct (WN a Wa) as [X|[(B & m & Hin & X)|X]].
    3:{ unfold aclientw, aclient_g. right; left. split; [clear - X GSLO GSHI GSPT; lia| intros Y; clear - Y; lia]. }
    - unfold aclientw, aclient_g. do 3 right; left. exists (fb, 5, rs). split; [right; exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 5) with 2048. split; [clear - X; lia| intros Y; clear - X Y; lia].
    - unfold aclientw, aclient_g. left. exists (B, m). split; [exact (OWNB B m Hin)| cbn [fst snd]; exact X]. }
  intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MG3 FR3 VV3.
  pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH1) as FRB1. pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH1) as BRB1.
  assert (BRBx : forall b, In b LBX -> 0 <= fst b /\ fst b + snd b <= 2 ^ 47) by (intros b Hb; apply BRB1; apply in_or_app; right; exact Hb).
  set (Wl := [(fb + 808, 24)] : list L5.range).
  assert (NCWe : forall a, W a -> aclient L ar LBX FF' (sp - 104) 24 a -> fb + 808 <= a < fb + 832).
  { intros a Wa Hc. destruct (WN a Wa) as [X|[(B & m & Hin & X)|X]]; [exact X| |].
    - exfalso. exact (PMARS1.own_not_aclient L ar C HI HIok (PNM.bparser_own s1) LBX FF' LK1 cr1 Aw1 M1 _ B m a (sp - 104) 24 HH1 (PNBOA.PNM_own_nb s1 B m Hin) X Hc).
    - exfalso. pose proof (L5SAR.aclient_appb L ar LBX (PNM.bparser_own s1) FF' (sp - 104) 24 a Hc) as Hc'.
      destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF' LK1 cr1 Aw1 M1 _ (sp - 104) 24 a HH1 GSPT Hc') as [Y|Y]; [clear - X Y; lia| clear - X Y GSLO; lia]. }
  assert (NCWb : forall a, W a -> aclient L ar LBX FF sp 24576 a -> fb + 808 <= a < fb + 832).
  { intros a Wa Hc. destruct (WN a Wa) as [X|[(B & m & Hin & X)|X]]; [exact X| |].
    - exfalso. exact (PMARS1.own_not_aclient L ar C HI HIok (PNM.bparser_own s1) LBX FF' LK1 cr1 Aw1 M1 _ B m a sp 24576 HH1 (PNBOA.PNM_own_nb s1 B m Hin) X (L5SAR.aclient_cons L ar _ _ _ _ _ _ Hc)).
    - exfalso. apply (GNCS a); [clear - X; lia| exact Hc]. }
  assert (EK13 : L5SAR.ek L ar LBX FF' (sp - 104) 24 Wl M1 M3).
  { intros a (Ha & Hc & Ho). apply FR3; [exact Ha|]. intros Wa. pose proof (NCWe a Wa Hc) as X. apply (Ho (fb + 808, 24)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - X; lia]. }
  assert (WAPPl : PMKA.wapp Wl).
  { apply PMKA.wapp_cons; [| apply PMKA.wapp_nil]. cbn [fst snd]. unfold BIGSHADOW_LO, BIGSHADOW_HI. destruct FA1 as [Y|Y]; clear - Y F1 F2; lia. }
  assert (ECK : forall v c, PMSPA.ec_at RSEGS M1 (fb + 1024) v c -> PMSPA.ec_at RSEGS M3 (fb + 1024) v c).
  { intros v0 c0 E0. apply (PMKA.ec_keepA RSEGS L ar _ FF' (sp - 104) 24 Wl M1 M3 EK13 WAPPl FRB1 (fb + 1024) v0 c0); [| | exact E0].
    - apply PMAUAR.aobjA_push. apply (PNAPAR.aobj_fbB FF fb (fb + 1024) 16 FOK); clear; lia.
    - intros i Hi rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - Hi Hr; lia. }
  assert (EO3 : PNM.bparser_own s3 = PNM.bparser_own s1).
  { unfold s3, set_cs, PNBO.set_nb, PNM.bparser_own, PNM.brest_own. cbn [Z.eqb PNM.b_src PNM.b_sb PNM.b_sk PNM.b_bb PNM.b_nb PNM.b_tb]. rewrite EOWN. reflexivity. }
  assert (VS3 : PM.vstr_at RSEGS PMSPA.accA M3 (fb + 464 + 344) x') by (apply (VS M3 FR3 MG3); exact VIS3).
  apply (KR M3 model3); [| exact HID3| exact VIS3| exact FR3| exact MG3| exact ECK].
  split.
  { rewrite EO3. destruct BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10). unfold PMAUK.binv.
    split; [exact HH3|]. split; [exact AM3|]. split; [eapply L5LZ.model_rt_trans; [exact B3| exact MRT3]|]. split; [exact B4|]. split; [exact B5|].
    split; [eapply L5SAR.astk_grows; [exact B6| exact MG3]|].
    split. { eapply L5SAR.ek_trans; [exact B7|]. intros a (Ha & Hc & Ho). apply FR3; [exact Ha|]. intros Wa. pose proof (NCWb a Wa Hc) as X.
             apply (Ho (PNRA.o_nb PMA.AD fb, 24)); [unfold PNRA.W_brun, PGS.W_srcfG; cbn [app]; do 5 right; left; reflexivity| unfold L5.in_rng, PNRA.o_nb, PNRA.o_p, PMSP.o_p, PNM.OFF_NB; cbn [fst snd pa_off_p PMA.AD PnLayoutA_b.ADDR_A]; clear - X; lia]. }
    split; [eapply L5SAR.dk_trans; [exact B8| apply L5SAR.dk_grows; exact MG3]|].
    split. { apply (own_agree sp R M1 M3 ltac:(clear - GSPC; lia) ltac:(clear - GSPC; lia) B9). intros a Ha. unfold ocell in Ha. apply FR3; [clear - Ha GSPC; lia|]. intros Wa. destruct (WAPP a Wa) as (_ & _ & _ & Y & _). apply Y. clear - Ha; lia. }
    eapply L5.defined_grows; [exact MG3| exact B10]. }
  split.
  { apply (pre_after_call LBX FF' (sp - 104) 24 Wl M1 M3 fb s1 s3 str sm1 sm1 ax1 ax1 FRB1 EK13 WAPPl FOK'); [| exact RP1| | | | |].
    - intros i Hi rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - Hi Hr; lia.
    - apply (PNBKA.bparser_set_csS M1 M3 (pa_vp_parser PMA.AD) op ois s1 0 x' (PNM.b_ng s1) (or_introl eq_refl) ltac:(unfold op; clear - FBI; lia) ltac:(unfold op; clear - F2 FSCEIL GSLO GSHI GSPT FBI; lia)); [| | | exact VS3| exact PA1].
      + intros i Hi Hn. unfold PNBOA.snt. apply FR3; [unfold op in Hi; clear - Hi FBI F2 FSCEIL GSLO GSHI GSPT FBI; lia|]. intros Wa. destruct (WN i Wa) as [X|[(B & m & Hin & X)|X]]; [| | unfold op in Hi; clear - X Hi F2 FSCEIL GSLO; lia].
        * apply Hn. unfold PNRA.bcs_off, PNM.OFF_NB. cbn [Z.eqb]. unfold op. clear - X; lia.
        * destruct (WB1 B m i Hin X) as (Y & _). clear - Y Hi; lia.
      + intros i Hi. unfold PNBOA.sns, S, SB. apply FR3; [unfold op in Hi; pose proof (Z.div_pos i 8 ltac:(clear - Hi FBI; lia) ltac:(clear; lia)); pose proof (Z.div_lt_upper_bound i 8 17592186044416 ltac:(clear; lia) ltac:(clear - Hi F2 FSCEIL GSLO GSHI GSPT FBI; lia)); lia|].
        apply NSH. unfold op in Hi. clear - Hi FBI F2 FSCEIL GSLO GSHI GSPT FBI; lia.
      + intros B m HB. assert (HBL : In (B, m) (PNM.bparser_own s1 ++ LBX)) by (apply in_or_app; left; exact (incl_rest 0 s1 _ HB)).
        destruct (BRB1 _ HBL) as (B0 & B1'). cbn [fst snd] in B0, B1'. split; [exact B0|]. split; [clear - B1'; lia|].
        pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH1) as (WBx & _). destruct (WBx _ HBL) as ((_ & _ & _ & Bpos & _) & _). cbn [fst snd] in Bpos.
        split.
        * intros x Hx. apply FR3; [clear - Hx B0 B1'; lia|]. intros Wa. destruct (WN x Wa) as [X|[(B2 & m2 & Hin2 & X)|X]]; [| | pose proof (blk_ceil _ _ _ _ _ _ _ _ _ HH1 HBL) as (BCx & _); clear - X Hx BCx GSLO; lia].
          -- destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ B m op 416 HH1 HBL AOP) as [Z0|Z0]; unfold op in Z0; clear - Hx X Z0; lia.
          -- assert (NE : B <> B2).
             { pose proof (PMASK.lb_nodup L ar C HI HIok _ _ _ _ _ _ _ HH1) as ND. intros E. subst B2.
               pose proof (perm_cs 0 s1 LBX (or_introl eq_refl)) as PE. pose proof (ln_nodup_perm _ _ PE ND) as ND2. unfold PNRA.bcs_str in ND2. cbn [Z.eqb] in ND2.
               rewrite map_app in ND2. pose proof (proj1 (stdpp.list_relations.list.NoDup_app _ _) ND2) as (_ & ND3 & _). apply (ND3 B).
               - apply in_elem_of. apply (in_map fst _ (B, m2)). exact Hin2.
               - apply in_elem_of. rewrite map_app. apply in_or_app; left. apply (in_map fst _ (B, m)). exact HB. }
             destruct (PMASK.blk_apart L ar C HI HIok _ _ _ _ _ _ _ B m B2 m2 HH1 HBL (OWNB B2 m2 Hin2) NE) as [Z0|Z0]; clear - Hx X Z0; lia.
        * intros x Hx. unfold S, SB. apply FR3; [pose proof (Z.div_pos x 8 ltac:(clear - Hx B0; lia) ltac:(clear; lia)); pose proof (Z.div_lt_upper_bound x 8 17592186044416 ltac:(clear; lia) ltac:(clear - Hx B1'; lia)); lia|].
          apply NSH. clear - Hx B0 B1'; lia.
    - apply (PMKA.iss_keepA RSEGS PMA.AD L ar _ FF' (sp - 104) 24 Wl M1 M3 EK13 WAPPl FRB1 BRBx (fb + 96) str sm1); [| exact INCS| | | exact IA1].
      + apply PMAUAR.aobjA_push. apply (PNAPAR.aobj_fbB FF fb (fb + 96) 272 FOK); clear; lia.
      + intros i Hi rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - Hi Hr; lia.
      + intros c0 n0 p0 E0 i Hi rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr.
        assert (HqL : In (p0, c0) (PNM.bparser_own s1 ++ LBX)) by (apply in_or_app; right; apply INCS; rewrite E0; left; reflexivity).
        destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ p0 c0 op 416 HH1 HqL AOP) as [Z0|Z0]; unfold op in Z0; clear - Hi Hr Z0; lia.
    - unfold s3, set_cs, PNM.bgrow_ok, PNBO.set_nb. cbn [Z.eqb PNM.b_nb PNM.b_ng PNM.b_tb PNM.b_tg PNM.b_bb PNM.b_bg]. destruct GR1 as (_ & G2 & G3). split; [exact TBOK|]. split; [exact G2| exact G3].
    - apply (PMASK.base_keep L ar C LY _ FF' (sp - 104) 24 Wl M1 M3 EK13); [| exact BASE1]. intros a Ha rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - Ha Hr FBI; lia.
    - apply (berr_keep _ FF' (sp - 104) 24 Wl M1 M3 ax1 EK13); [| exact ERR1]. intros a Ha rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - Ha Hr FBI; lia. }
  split; [unfold s3, set_cs, PNBO.set_nb; cbn [Z.eqb PNM.b_src]; exact STEP1|]. split; [exact AXL1|].
  split. { revert CK1. unfold s3, set_cs, PNBO.set_nb, PNRA.pot_bparser. cbn [Z.eqb PNM.b_sk PNM.b_tb PNM.b_tg PNM.b_nb PNM.b_ng PNM.b_bb PNM.b_bg]. rewrite POTE. intros X; exact X. }
  split; [| unfold s3, set_cs, PNBO.set_nb; cbn [Z.eqb PNM.b_bb]; exact EBB1].
  apply (L5C.u8_at_agree RSEGS M1 M3); [| exact R4a| exact R4b| exact SHC1].
  intros j Hj. apply FR3; [clear - Hj R4a R4b; lia|]. intros Wj. destruct (WAPP j Wj) as (_ & Y & _). pose proof (Z.div_pos F 8 ltac:(clear - GFR; lia) ltac:(clear; lia)) as D0. pose proof (Z.div_lt_upper_bound F 8 17592186044416 ltac:(clear; lia) ltac:(clear - GFR; lia)) as D1. clear - Hj Y D0 D1. lia.
Qed.


(* [comment removed for export] *)
Lemma efacts_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 (v c : Z) :
  en_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  en_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  en_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
  PMSPA.ec_at RSEGS M1 (fb + 1024) v c ->
  6905856 <= fb + 1024 <= 140737488355312 /\ (fb + 1024) mod 8 = 0 /\ (2147446784 + 17592186048512 <= fb + 1024 \/ (fb + 1024) + 16 <= 2147446784)
  /\ L5KA.zeros_at (mrestrict (ahid Aw1 model1) M1) (((fb + 1024) / 8) + 2147450880) 2
  /\ ((sp - 128) + 128 <= fb + 1024 \/ (fb + 1024) + 16 <= (sp - 128)) /\ ((fb + 464) + 416 <= fb + 1024 \/ (fb + 1024) + 16 <= fb + 464)
  /\ (F + 64 <= fb + 1024 \/ (fb + 1024) + 16 <= F) /\ (fl + 1 <= fb + 1024 \/ (fb + 1024) + 16 <= fl)
  /\ L5.u32_at RSEGS (mrestrict (ahid Aw1 model1) M1) (fb + 1024) v /\ L5.writable RSEGS (mrestrict (ahid Aw1 model1) M1) (fb + 1024) 16.
Proof.
  intros CTX G LM EC1.
  pose proof CTX as (Hw & HH & AM & K0 & ENT & FRM & FRS & FOK & SP32 & ARGS & RPRE & INCS & INV & EC0 & HE & UNR & CRED & KONT).
  destruct ENT as (Rra & RAok0 & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 6) with 24576 in *.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof FOK as ((rs & Hfb) & Fal).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _).
  pose proof (WF _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 5) with 2048 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL, FSIMG, F1, F2.
  rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in FSIMG.
  assert (FBI : 6905856 <= fb) by (clear - F1 FSAPP FSIMG; lia).
  pose proof LM as (BI & RP1 & STEP1 & AXL1 & CK1 & SHC1 & EBB1).
  pose proof G as G'. unfold en_frame in G'.
  destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 0) with 64 in *. change (64 / 8) with 8 in *.
  pose proof BI as (HH1 & AM1 & MRT1 & INCA1 & INCL1 & ASTK1 & EK1 & DK1 & OWN1 & DSH1).
  set (FF' := (F, 0, sp - 128 + 32) :: FF) in *.
  assert (FOK' : PNRA.frame_okB FF' fb). { split; [exists rs; right; exact Hfb| exact Fal]. }
  pose proof RP1 as (PA1 & IA1 & VIS1 & VREF1 & OACC1 & BASE1 & ERR1 & GR1).
  change (PNRA.o_p PMA.AD fb) with (fb + 464) in PA1, IA1, VIS1, VREF1, OACC1. change (PNRA.o_is PMA.AD fb) with (fb + 96) in PA1, IA1. change (PNRA.o_v PMA.AD fb) with (fb + 432) in VIS1, VREF1.
  change (PNM.PSIZE + 8) with 424 in OACC1.
  pose proof GFR as (GF1 & GF2 & _).
  assert (R4a : 0 <= F / 8 + 2147450880) by (clear - GF1; lia).
  assert (R4b : F / 8 + 2147450880 + 1 <= 2 ^ 64) by (clear - GF2; pose proof (Z.div_le_upper_bound F 8 17592186044408 ltac:(lia) ltac:(lia)); lia).
  pose proof (PMASK.stk_vis L ar C HI LY HIok _ FF' LK1 cr1 Aw1 M1 model1 sp 24576 128 HH1 ASTK1 ltac:(lia)) as (SL160 & SH160 & SWR).
  set (H1 := ahid Aw1 model1) in *.
  pose proof (PNAPAR.oec_visB L ar C HI LY HIok _ FF' LK1 cr1 Aw1 M1 model1 fb v c HH1 FOK' EC1) as ((E1 & E8 & ENS) & EZ & EW & ECE & EU & _).
  assert (CLh : forall a, fb + 32 <= a < fb + 2040 -> aclient L ar LBX FF sp 24576 a).
  { intros a Ha. unfold aclient, aclient_g. do 3 right; left. exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd].
    change (ff_bytes 5) with 2048. split; [clear - Ha; lia| intros Y; clear - Ha Y; lia]. }
  split; [exact E1|]. split; [exact E8|]. split; [exact ENS|]. split; [exact EZ|].
  split; [clear - ECE GSLO; lia|]. split; [left; clear; lia|].
  split. { apply iv_apart; [clear; lia| clear; lia|]. intros a Ha X. apply (GNCF a); [left; exact Ha| apply CLh; clear - X; lia]. }
  split. { destruct (Z_lt_le_dec fl (fb + 1024)) as [X|X]; [left; clear - X; lia|]. destruct (Z_lt_le_dec fl (fb + 1024 + 16)) as [Y|Y]; [| right; clear - Y; lia].
           exfalso. apply GFLNC. apply L5SAR.aclient_cons. apply (L5SAR.aclient_00 L ar LBX FF sp 24576). apply CLh. clear - X Y; lia. }
  split; [exact EU| exact EW].
Qed.


End WithHeap.
End PNAENK.
