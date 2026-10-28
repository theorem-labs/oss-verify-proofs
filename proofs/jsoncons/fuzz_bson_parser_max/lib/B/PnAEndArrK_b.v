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
     PmModelFactsA_b PnStepA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PgSrc PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnLayout PnModel PnModelFacts PnStatics PnStaticsA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b PnRunAa_b PnASrcKit_b PmAUarK_b PmAUar_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnBrObj. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnBrObjA_b PnAParKit_b PnAReset1_b PnOwnerOkA_b PnBrKitA_b Ba0_code_b0c48_b0c4c_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

From stdpp Require list_relations list_basics.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnSpecsAX_b.

Module PNAEAK.
Import L5A. Import L5CA. Import L5SAR. Import PNBKA.

(* [comment removed for export] *)
Definition spill (M : mem) (E F oec : Z) : Prop :=
  L5.u64_at RSEGS M (E - 112) F /\ L5.u64_at RSEGS M (E - 136) oec /\ L5.u64_at RSEGS M (E - 144) F.
Lemma spill_agree M M' E F oec : 0 <= E - 160 -> E <= 2 ^ 64 ->
  spill M E F oec -> (forall a, E - 144 <= a < E - 104 -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> spill M' E F oec.
Proof.
  intros H0 H1 (C0 & C1 & C2) AG. unfold spill.
  repeat split; (eapply L5C.u64_at_agree; [ | | | eassumption]; [intros j Hj; apply AG; lia | lia | lia]).
Qed.

Lemma div8_add op o : op mod 8 = 0 -> 0 <= o -> (op + o) / 8 = op / 8 + o / 8.
Proof.
  intros H8 Ho. pose proof (Z.div_mod op 8 ltac:(lia)) as Dm. rewrite H8, Z.add_0_r in Dm. rewrite Dm at 1. rewrite Z.mul_comm. rewrite Z.div_add_l by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Definition pfacts (MV : mem) (sp op F fl : Z) : Prop :=
  L5.img_clear MV 65536 1282048 /\ L5.u64_at RSEGS MV 1309752 2147450880 /\ L5.u32_at RSEGS MV 1309760 1
  /\ 140735332487328 <= sp <= 140737488355328 /\ sp mod 32 = 0 /\ L5.writable RSEGS MV (sp - 160) 160
  /\ 6905856 <= op <= 140737488354912 /\ op mod 8 = 0 /\ (2147446784 + 17592186048512 <= op \/ op + 416 <= 2147446784)
  /\ L5KA.zeros_at MV ((op / 8) + 2147450880) 2 /\ L5KA.zeros_at MV (((op + 10) / 8) + 2147450880) 1 /\ L5KA.zeros_at MV (((op + 12) / 8) + 2147450880) 1 /\ L5KA.zeros_at MV (((op + 392) / 8) + 2147450880) 3
  /\ ((sp - 160) + 160 <= op \/ op + 416 <= (sp - 160))
  /\ 6905856 <= F <= 140737488355200 /\ F mod 32 = 0 /\ L5.defined MV F 128 /\ L5.writable RSEGS MV F 128
  /\ (2147446784 + 17592186048512 <= F \/ F + 128 <= 2147446784) /\ L5.writable RSEGS MV ((F / 8) + 2147450880) 16
  /\ L5.u64_at RSEGS MV (F + 120) fl /\ 4096 <= fl <= 140737488355327 /\ L5.writable RSEGS MV fl 1
  /\ (2147446784 + 17592186048512 <= fl \/ fl + 1 <= 2147446784) /\ (F + 128 <= fl \/ fl + 1 <= F)
  /\ ((sp - 160) + 160 <= F \/ F + 128 <= (sp - 160)) /\ ((sp - 160) + 160 <= fl \/ fl + 1 <= (sp - 160))
  /\ (op + 416 <= F \/ F + 128 <= op) /\ (op + 416 <= fl \/ fl + 1 <= op)
  /\ (((op / 8) + 2147450880) + 52 <= ((F / 8) + 2147450880) \/ ((F / 8) + 2147450880) + 16 <= ((op / 8) + 2147450880))
  /\ 0 <= sp < 2 ^ 64 /\ 0 <= op < 2 ^ 64 /\ 0 <= F < 2 ^ 64 /\ 0 <= fl < 2 ^ 64.


(* [comment removed for export] *)
Definition tfacts (MV : mem) (sp op F fl e pos : Z) : Prop :=
  L5.u64_at RSEGS MV (op + 400) e /\ 4136 <= e <= 140737488355328 /\ (65536 + 6840320 <= (e - 40) \/ (e - 40) + 40 <= 65536) /\ e mod 8 = 0
  /\ L5.u64_at RSEGS MV (e - 24) pos /\ L5.writable RSEGS MV (e - 24) 8
  /\ (2147446784 + 17592186048512 <= (e - 40) \/ (e - 40) + 40 <= 2147446784)
  /\ L5KA.zeros_at MV (((e - 24) / 8) + 2147450880) 1
  /\ ((sp - 160) + 160 <= (e - 40) \/ (e - 40) + 40 <= (sp - 160))
  /\ ((e - 40) + 40 <= op \/ op + 416 <= (e - 40)) /\ ((e - 40) + 40 <= F \/ F + 128 <= (e - 40)) /\ ((e - 40) + 40 <= fl \/ fl + 1 <= (e - 40))
  /\ 0 <= e < 2 ^ 64 /\ 0 <= pos < 2 ^ 64.


Section WithDefs.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (HI : asan_iface).

(* [comment removed for export] *)
Definition ed_kont (K : TSet) (R : bvmap 5 word) (M : mem) (model : Model) (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z))
           (cr : credit) (sp r fb cat e : Z) (s : PNM.bpst) (str : PM.vstr) (sm : PM.strm) (ax : PNST.bax) (w : Z) : Prop :=
  forall (fx' : FPState) (R' : bvmap 5 word) (M' : mem) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (s' : PNM.bpst) (sm' : PM.strm) (ax' : PNST.bax) (cr' : credit),
    regs_preserved R R' ->
    PNRA.brun_post RSEGS PMA.AD PMA.AN PMA.AAD false PNRA.bprog_pop R' M' fb s s' str sm sm' ax ax' cat e ->
    ahpres L ar LBX FF sp 18432 (PNRA.W_brun PMA.AD PMA.AN fb) M M' ->
    PMSP.credit_keep cr cr' (pot L ar s) (pot L ar s') ->
    model_rt model model' -> incl LK' LK -> incl Aw Aw' -> amodel_ok Aw' model' -> ri_inv HI (PNM.bparser_own s' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
    srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K.

(* [comment removed for export] *)
Definition ed_ctx (K : TSet) (R : bvmap 5 word) (M : mem) (model : Model) (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z))
           (cr : credit) (sp r fb cat e : Z) (s : PNM.bpst) (str : PM.vstr) (sm : PM.strm) (ax : PNST.bax) (w : Z) : Prop :=
  (w = 0 \/ w = 1) /\ ri_inv HI (PNM.bparser_own s ++ LBX) FF LK cr Aw M (vml_of model) /\ amodel_ok Aw model /\ K [] /\ PMSPA.entryA PMA.AD L ar R M sp r 3
  /\ PGSA.ffroomB PNRA.FCB 3 FF LK /\ PMSPA.ffrsA FF sp /\ PNRA.frame_okB FF fb /\ sp mod 32 = 0 /\ PNRA.bargs_end PMA.AD R fb s sm
  /\ PNRA.brun_pre RSEGS PMA.AD PMA.AN PMA.AAD M fb s str sm ax /\ incl (PM.vs_own str) LBX /\ PNRA.binv s /\ PMSPA.ec_at RSEGS M (fb + 1024) e cat /\ 0 <= e <= 64
  /\ PM.unread (PNM.b_src s) sm < 2 ^ 26 /\ PMSP.credit_le (pot L ar s) cr
  /\ ed_kont K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w.

(* [comment removed for export] *)
Definition ed_frame (R : bvmap 5 word) (M : mem) (model : Model) (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z))
           (cr : credit) (sp : Z) (s : PNM.bpst) (F fl : Z) (LK2 : list fframe) (M2 : mem) (model2 : Model) : Prop :=
  PMAUK.gctx L ar HI LBX FF LK Aw sp 18432 (sp - 160) (sp - 104) sp (ocell sp) (own sp R) F fl 1 LK2 M2 model2 cr (PNM.bparser_own s).

(* [comment removed for export] *)
Definition ed_mem (R : bvmap 5 word) (M : mem) (model : Model) (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z))
           (cr : credit) (sp fb : Z) (s : PNM.bpst) (str : PM.vstr) (sm : PM.strm) (ax : PNST.bax) (F : Z)
           (M1 : mem) (model1 : Model) (LK1 : list fframe) (Aw1 : list (Z * Z)) (s1 : PNM.bpst) (sm1 : PM.strm) (ax1 : PNST.bax) (cr1 : credit) : Prop :=
  PMAUK.binv L ar HI M model LBX FF LK Aw sp 18432 (sp - 160) (own sp R) F 1 (PNRA.W_brun PMA.AD PMA.AN fb) (PNM.bparser_own s1) M1 model1 LK1 cr1 Aw1
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
  ed_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  ed_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  ed_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
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
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 3) with 18432 in *.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof FOK as ((rs & Hfb) & Fal).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _).
  pose proof (WF _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 5) with 2048 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL, F1, F2.
  destruct LM as (BI & RP1 & STEP1 & AXL1 & CK1 & SHC1 & EBB1).
  pose proof G as G'. unfold ed_frame in G'.
  destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 1) with 128 in *. change (128 / 8) with 16 in *.
  pose proof BI as (HH1 & AM1 & MRT1 & INCA1 & INCL1 & ASTK1 & EK1 & DK1 & OWN1 & DSH1).
  set (FF' := (F, 1, sp - 160 + 32) :: FF) in *.
  assert (FOK' : PNRA.frame_okB FF' fb). { split; [exists rs; right; exact Hfb| exact Fal]. }
  destruct RP1 as (PA1 & IA1 & VIS1 & VREF1 & OACC1 & BASE1 & ERR1 & GR1).
  change (PNRA.o_p PMA.AD fb) with (fb + 464) in *. change (PNRA.o_is PMA.AD fb) with (fb + 96) in *. change (PNRA.o_v PMA.AD fb) with (fb + 432) in *.
  change (PNM.PSIZE + 8) with 424 in OACC1.
  pose proof (PNAPAR.op_visB L ar C HI LY HIok _ FF' LK1 cr1 Aw1 M1 model1 fb _ s1 HH1 FOK' PA1 OACC1) as ((O1 & O8 & ONSH) & Zop & OWR & OCE & OVIS & AOP).
  pose proof (PMASK.mach_vis L ar C HI LY HIok _ FF' LK1 cr1 Aw1 M1 model1 HH1 BASE1) as (VM0 & VM1 & VM2).
  pose proof (PMASK.stk_vis L ar C HI LY HIok _ FF' LK1 cr1 Aw1 M1 model1 sp 18432 160 HH1 ASTK1 ltac:(lia)) as (SL160 & SH160 & SWR).
  destruct (PMAUK.vis_facts L ar C HI LYa HIok M model LBX FF LK Aw sp 18432 (sp - 160) (sp - 104) sp (ocell sp) (own sp R) F fl 1 LK2 M2 model2 cr (PNM.bparser_own s) G
              _ (PNM.bparser_own s1) M1 model1 LK1 cr1 Aw1 BI) as ((WS1 & _ & _ & _ & _) & OWNv & (FD1 & FW1 & FSW1 & FLC1 & FLW1) & (FLCc1 & FLV1 & VF1 & VS1 & VSH1)).
  change (ff_bytes 1) with 128 in *. change (128 / 8) with 16 in *. replace (F + 128 - 8) with (F + 120) in FLC1 by (clear; lia).
  set (op := fb + 464) in *.
  set (MV := mrestrict (ahid Aw1 model1) M1) in *.
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ _ LK1 cr1 Aw1 M1 model1 HH1) as (_ & VISs & _).
  (* [comment removed for export] *)
  assert (CLo : forall a, fb + 32 <= a < fb + 2040 -> aclient L ar LBX FF sp 18432 a).
  { intros a Ha. unfold aclient, aclient_g. do 3 right; left. exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd].
    change (ff_bytes 5) with 2048. split; [clear - Ha; lia| intros Y; clear - Ha Y; lia]. }
  assert (CLs : forall a, fb / 8 + SB <= a < fb / 8 + SB + 256 -> aclient L ar LBX FF sp 18432 a).
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
  assert (SF1 : S (F + 128 - 1) = F / 8 + SB + 15).
  { unfold S. destruct GF8 as (X1 & X2 & X3). rewrite X2. clear; lia. }
  assert (NF : forall a, fb + 32 <= a < fb + 2040 -> ~ (F <= a < F + 128)).
  { intros a Ha X. apply (GNCF a); [left; exact X| exact (CLo a Ha)]. }
  assert (NFS : forall a, fb / 8 + SB <= a < fb / 8 + SB + 256 -> ~ (F / 8 + SB <= a < F / 8 + SB + 16)).
  { intros a Ha X. apply (GNCF a); [right; unfold S at 1; rewrite SF1; clear - X; lia| exact (CLs a Ha)]. }
  assert (NFL : forall a, fb + 32 <= a < fb + 2040 -> a <> fl).
  { intros a Ha X. subst a. apply GFLNC. apply L5SAR.aclient_cons. apply (L5SAR.aclient_00 L ar LBX FF sp 18432 fl). exact (CLo fl Ha). }
  assert (ApF : op + 416 <= F \/ F + 128 <= op) by (apply iv_apart; [clear; lia| clear; lia| intros a Ha; apply NF; clear - Ha; unfold op in Ha; lia]).
  assert (ApFL : op + 416 <= fl \/ fl + 1 <= op).
  { destruct (Z_lt_le_dec fl op) as [X|X]; [right; clear - X; lia|]. destruct (Z_lt_le_dec fl (op + 416)) as [Y|Y]; [exfalso; apply (NFL fl); [clear - X Y; unfold op in X, Y; lia| reflexivity]| left; exact Y]. }
  assert (ApS : ((op / 8) + 2147450880) + 52 <= ((F / 8) + 2147450880) \/ ((F / 8) + 2147450880) + 16 <= ((op / 8) + 2147450880)).
  { change 2147450880 with SB. apply iv_apart; [clear; lia| clear; lia| intros a Ha; apply NFS; clear - Ha SHop; lia]. }
  (* [comment removed for export] *)
  assert (SVV : forall a v0, sp - 160 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1 a v0 -> L5.u64_at RSEGS MV a v0).
  { intros a v0 Ha1 Ha2 X. apply (proj2 (L5A.u64_at_vis _ M1 a v0 (VISs a 8 ltac:(clear - Ha1 SL160 SPT; lia) ltac:(clear - Ha2 SHI SPT; lia)) ltac:(clear - Ha1 SL160 SPT; lia) ltac:(clear - Ha2 SHI SPT; lia))). exact X. }
  assert (CV : forall v, L5.u8_at RSEGS M1 (F + 32) v -> L5.u8_at RSEGS MV (F + 32) v).
  { intros v X. apply (proj2 (L5A.u8_at_vis _ M1 (F + 32) v (L5A.avis_sub _ F 128 (F + 32) 1 VF1 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - GFR; lia) ltac:(clear - GFR; lia))). exact X. }
  assert (Zz0 : L5KA.zeros_at MV (op / 8 + 2147450880) 2). { intros i Hi. apply Zop. clear - Hi; lia. }
  assert (Zz1 : L5KA.zeros_at MV ((op + 10) / 8 + 2147450880) 1).
  { intros i Hi. replace ((op + 10) / 8 + 2147450880 + i) with (op / 8 + SB + (1 + i)) by (unfold SB; rewrite (div8_add op 10 O8 ltac:(clear; lia)); change (10 / 8) with 1; clear; lia).
    apply Zop. clear - Hi; lia. }
  assert (Zz2 : L5KA.zeros_at MV ((op + 12) / 8 + 2147450880) 1).
  { intros i Hi. replace ((op + 12) / 8 + 2147450880 + i) with (op / 8 + SB + (1 + i)) by (unfold SB; rewrite (div8_add op 12 O8 ltac:(clear; lia)); change (12 / 8) with 1; clear; lia).
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

Lemma pstk176_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 :
  ed_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  ed_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  ed_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
  L5.writable RSEGS (mrestrict (ahid Aw1 model1) M1) (sp - 176) 176
  /\ ((sp - 176) + 176 <= fb + 464 \/ fb + 464 + 416 <= (sp - 176))
  /\ ((sp - 176) + 176 <= F \/ F + 128 <= (sp - 176))
  /\ ((sp - 176) + 176 <= fl \/ fl + 1 <= (sp - 176)).
Proof.
  intros CTX G LM.
  destruct CTX as (Hw & HH & AM & K0 & ENT & FRM & FRS & FOK & SP32 & ARGS & RPRE & INCS & INV & EC0 & HE & UNR & CRED & KONT).
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 3) with 18432 in *.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof FOK as ((rs & Hfb) & Fal).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _).
  pose proof (WF _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 5) with 2048 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL, F1, F2.
  destruct LM as (BI & RP1 & STEP1 & AXL1 & CK1 & SHC1 & EBB1).
  pose proof G as G'. unfold ed_frame in G'.
  destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 1) with 128 in *. change (128 / 8) with 16 in *.
  pose proof BI as (HH1 & AM1 & MRT1 & INCA1 & INCL1 & ASTK1 & EK1 & DK1 & OWN1 & DSH1).
  set (FF' := (F, 1, sp - 160 + 32) :: FF) in *.
  assert (FOK' : PNRA.frame_okB FF' fb). { split; [exists rs; right; exact Hfb| exact Fal]. }
  destruct RP1 as (PA1 & IA1 & VIS1 & VREF1 & OACC1 & BASE1 & ERR1 & GR1).
  change (PNRA.o_p PMA.AD fb) with (fb + 464) in *. change (PNRA.o_is PMA.AD fb) with (fb + 96) in *. change (PNRA.o_v PMA.AD fb) with (fb + 432) in *.
  change (PNM.PSIZE + 8) with 424 in OACC1.
  pose proof (PNAPAR.op_visB L ar C HI LY HIok _ FF' LK1 cr1 Aw1 M1 model1 fb _ s1 HH1 FOK' PA1 OACC1) as ((O1 & O8 & ONSH) & Zop & OWR & OCE & OVIS & AOP).
  pose proof (PMASK.mach_vis L ar C HI LY HIok _ FF' LK1 cr1 Aw1 M1 model1 HH1 BASE1) as (VM0 & VM1 & VM2).
  pose proof (PMASK.stk_vis L ar C HI LY HIok _ FF' LK1 cr1 Aw1 M1 model1 sp 18432 176 HH1 ASTK1 ltac:(lia)) as (SL176 & SH176 & SWR176).
  split; [exact SWR176|]. split; [clear - OCE SL176; lia|]. split; [clear - GFCEIL GSLO; lia|]. clear - GFLR GSLO. lia.
Qed.


(* [comment removed for export] *)
Lemma tfacts_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 pre top :
  ed_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  ed_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  ed_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
  PNRA.binv s1 -> PNM.b_stk s1 = pre ++ [top] ->
  tfacts (mrestrict (ahid Aw1 model1) M1) sp (fb + 464) F fl (PNM.b_sb s1 + 40 * Z.of_nat (length pre) + 40) (PNM.bs_pos top)
  /\ PNM.bstate_at RSEGS M1 (PNM.b_sb s1 + 40 * Z.of_nat (length pre)) top /\ PNM.bstate_ok top
  /\ In (PNM.b_sb s1, 40 * 2 ^ PNM.b_sk s1) (PNM.bparser_own s1)
  /\ PNM.b_sb s1 <= PNM.b_sb s1 + 40 * Z.of_nat (length pre) /\ PNM.b_sb s1 + 40 * Z.of_nat (length pre) + 40 <= PNM.b_sb s1 + 40 * 2 ^ PNM.b_sk s1
  /\ PNM.b_sb s1 + 40 * 2 ^ PNM.b_sk s1 <= ahl_ceil ar /\ 4096 <= PNM.b_sb s1.
Proof.
  intros CTX G LM INV1 ES.
  destruct CTX as (Hw & HH & AM & K0 & ENT & FRM & FRS & FOK & SP32 & ARGS & RPRE & INCS & INV & EC0 & HE & UNR & CRED & KONT).
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 3) with 18432 in *.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof FOK as ((rs & Hfb) & Fal).
  destruct LM as (BI & RP1 & STEP1 & AXL1 & CK1 & SHC1 & EBB1).
  pose proof G as G'. unfold ed_frame in G'.
  destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 1) with 128 in *. change (128 / 8) with 16 in *.
  pose proof BI as (HH1 & AM1 & MRT1 & INCA1 & INCL1 & ASTK1 & EK1 & DK1 & OWN1 & DSH1).
  set (FF' := (F, 1, sp - 160 + 32) :: FF) in *.
  assert (FOK' : PNRA.frame_okB FF' fb). { split; [exists rs; right; exact Hfb| exact Fal]. }
  destruct RP1 as (PA1 & IA1 & VIS1 & VREF1 & OACC1 & BASE1 & ERR1 & GR1).
  change (PNRA.o_p PMA.AD fb) with (fb + 464) in *. change (PNRA.o_is PMA.AD fb) with (fb + 96) in *. change (PNRA.o_v PMA.AD fb) with (fb + 432) in *.
  change (PNM.PSIZE + 8) with 424 in OACC1.
  pose proof (PNAPAR.op_visB L ar C HI LY HIok _ FF' LK1 cr1 Aw1 M1 model1 fb _ s1 HH1 FOK' PA1 OACC1) as ((O1 & O8 & ONSH) & Zop & OWR & OCE & OVIS & AOP).
  pose proof (PMASK.stk_vis L ar C HI LY HIok _ FF' LK1 cr1 Aw1 M1 model1 sp 18432 160 HH1 ASTK1 ltac:(lia)) as (SL160 & SH160 & SWR).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH1) as (WB1 & WF1 & FSAPP1 & FSCEIL1 & _).
  set (op := fb + 464) in *.
  destruct s1 as [mo1 dn1 src1 bb1 nb1 tb1 ng1 tg1 bg1 sb1 sk1 stk1]. cbn [PNM.b_stk PNM.b_sb PNM.b_sk] in *. subst stk1.
  pose proof PA1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PVEC & _). cbn [PNM.b_sb PNM.b_sk PNM.b_stk] in PVEC.
  destruct PVEC as (VC0 & VC8 & VC16 & Hk & Hlen & Hal & DB & CB & AN & EL).
  rewrite length_app in Hlen, VC8, CB, AN. cbn [length] in Hlen, VC8, CB, AN. rewrite Nat2Z.inj_add in Hlen, VC8, CB, AN. cbn [Z.of_nat Pos.of_succ_nat] in Hlen, VC8, CB, AN.
  change PNM.BSZ with 40 in *. change PNM.OFF_STK with 392 in *.
  assert (VIN : In (sb1, 40 * 2 ^ sk1) (PNM.bparser_own (PNM.BPST mo1 dn1 src1 bb1 nb1 tb1 ng1 tg1 bg1 sb1 sk1 (pre ++ [top])))).
  { unfold PNM.bparser_own, PNM.brest_own, PNM.bvec_own. cbn [PNM.b_src PNM.b_sb PNM.b_sk PNM.b_bb PNM.b_nb PNM.b_tb]. apply in_or_app. right. left. reflexivity. }
  assert (VINL : In (sb1, 40 * 2 ^ sk1) (PNM.bparser_own (PNM.BPST mo1 dn1 src1 bb1 nb1 tb1 ng1 tg1 bg1 sb1 sk1 (pre ++ [top])) ++ LBX)) by (apply in_or_app; left; exact VIN).
  destruct (WB1 _ VINL) as ((B0 & BI0 & B16 & _ & B4 & BAPP) & _ & _ & _ & _ & BFA & BFS). cbn [fst snd] in B0, BI0, B16, B4, BAPP, BFA, BFS.
  rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in BI0. unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in BAPP. unfold FS_BYTES in BFS.
  pose proof (PM.pow2_pos sk1 ltac:(lia)) as P2K.
  set (T := sb1 + 40 * Z.of_nat (length pre)) in *.
  assert (TB : sb1 <= T /\ T + 40 <= sb1 + 40 * 2 ^ sk1) by (unfold T; clear - Hlen; lia).
  assert (TAL : T mod 8 = 0).
  { unfold T. replace (sb1 + 40 * Z.of_nat (length pre)) with (sb1 + (Z.of_nat (length pre) * 5) * 8) by (clear; lia). rewrite Z.mod_add by lia. apply PMKA.mod16_8'. exact Hal. }
  pose proof (BFA (F, 1, sp - 160 + 32) (in_or_app FF' LK1 _ (or_introl (or_introl eq_refl)))) as Z1. cbn [ff_addr ff_class fst snd] in Z1. change (ff_bytes 1) with 128 in Z1.
  pose proof (BFA (fb, 5, rs) (in_or_app FF' LK1 (fb, 5, rs) (or_introl (or_intror Hfb)))) as Z2. cbn [ff_addr ff_class fst snd] in Z2. change (ff_bytes 5) with 2048 in Z2.
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ _ LK1 cr1 Aw1 M1 model1 HH1) as VP; cbv zeta in VP; destruct VP as (_ & _ & _ & VFS & VB & _).
  assert (TV : L5A.avis (ahid Aw1 model1) T 40) by (apply (VB sb1 (40 * 2 ^ sk1) T 40 VINL); clear - TB; lia).
  assert (PT : PNM.bstate_at RSEGS M1 T top) by (specialize (EL (length pre) ltac:(rewrite length_app; cbn; lia)); rewrite nth_middle in EL; exact EL).
  assert (OKt : PNM.bstate_ok top).
  { destruct INV1 as (_ & (_ & _ & _ & _ & OKS)). cbn [PNM.b_stk] in OKS. specialize (OKS (length pre) ltac:(rewrite length_app; cbn; lia)). rewrite nth_middle in OKS; exact OKS. }
  pose proof GFLP as GFLP'. unfold FS_BYTES in GFLP'.
  split; [| split; [exact PT| split; [exact OKt| split; [exact VIN| split; [clear - TB; lia| split; [clear - TB; lia| split; [clear - B4; lia| exact B0]]]]]]].
  destruct PT as (PT0 & PT8 & PT16 & PT24 & PT32). pose proof OKt as (_ & _ & POS & _).
  set (MV := mrestrict (ahid Aw1 model1) M1) in *.
  unfold tfacts. replace (T + 40 - 24) with (T + 16) by (clear; lia). replace (T + 40 - 40) with T by (clear; lia).
  split. { apply (proj2 (L5A.u64_at_vis _ M1 (op + 400) _ ltac:(apply OVIS; clear; lia) ltac:(clear - O1; lia) ltac:(clear - O1; lia))).
           replace (op + 400) with (op + 392 + 8) by (clear; lia). replace (T + 40) with (sb1 + 40 * (Z.of_nat (length pre) + 1)) by (unfold T; clear; lia). exact VC8. }
  split; [clear - B0 TB B4 GSLO GSHI GSPT; lia|].
  split; [clear - BI0 TB; lia|].
  split; [replace (T + 40) with (T + 5 * 8) by (clear; lia); rewrite Z_mod_plus_full; exact TAL|].
  split; [apply (proj2 (L5A.u64_at_vis _ M1 (T + 16) _ ltac:(eapply L5A.avis_sub; [exact TV| clear; lia| clear; lia]) ltac:(clear - B0 TB; lia) ltac:(clear - B4 TB GSLO GSHI GSPT; lia))); exact PT16|].
  split; [apply (proj2 (L5A.writable_vis _ M1 (T + 16) 8 ltac:(eapply L5A.avis_sub; [exact TV| clear; lia| clear; lia]) ltac:(clear - B0 TB; lia) ltac:(clear - B4 TB GSLO GSHI GSPT; lia)));
          apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M1 sb1 (40 * 2 ^ sk1)); [exact DB| clear - TB; lia| clear - TB; lia]| clear - B0 TB; lia| clear - B4 TB GSLO GSHI GSPT; lia]|].
  split; [destruct BAPP as (_ & [X|X] & _); [right| left]; clear - X TB; lia|].
  split. { change 2147450880 with SB. replace 1 with (8 / 8) by reflexivity.
           apply (PMKA.blk_shadow_vis L ar C HI LYa HIok _ _ LK1 cr1 Aw1 M1 model1 sb1 (40 * 2 ^ sk1) (T + 16) 8 HH1 VINL); [clear - TB; lia| clear - TB; lia| | clear; lia| reflexivity|].
           - replace (T + 16) with (T + 2 * 8) by (clear; lia). rewrite Z_mod_plus_full. exact TAL.
           - intros a Ha. apply CB. clear - Ha TB Hlen; unfold T in *; lia. }
  split; [clear - B4 TB GSLO; lia|].
  split; [clear - Z2 TB; unfold op; lia|].
  split; [clear - Z1 TB; lia|].
  split; [clear - BFS TB GFLP'; lia|].
  split; [clear - B0 TB B4 GSLO GSHI GSPT; lia| exact POS].
Qed.


(* [comment removed for export] *)
Lemma ed_call_mkec K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 (fx1 : FPState) R1 (ra v e1 c1 : Z) :
  PNRAa.make_ec_spec L ar HI ->
  ed_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  ed_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  ed_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
  PMSPA.ec_at RSEGS M1 (fb + 1024) e1 c1 ->
  getr R1 (reg 1) = Z_to_bv 64 ra -> L5.ra_ok ra -> getr R1 (reg 2) = Z_to_bv 64 (sp - 160) ->
  getr R1 (reg 3) = Z_to_bv 64 (pa_gp PMA.AD) -> getr R1 (reg 4) = Z_to_bv 64 (hl_tp L) ->
  getr R1 (reg 10) = Z_to_bv 64 (fb + 1024) -> getr R1 (reg 11) = Z_to_bv 64 v -> 1 <= v <= 64 ->
  (forall (fx2 : FPState) R2 (M3 : mem) model3 LK3 Aw3,
      regs_preserved R1 R2 -> PMSPA.ec_at RSEGS M3 (fb + 1024) v (pa_errcat_obj PMA.AD) ->
      ed_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK3 Aw3 s1 sm1 (PNST.bax_add_cat ax1) cr1 ->
      (forall a, sp - 160 <= a < sp - 104 -> M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx2 R2 ra M3 model3) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 (pa_make_ec PMA.AD) M1 model1) K.
Proof.
  intros MKE CTX G LM EC1 X1 RAok X2 X3 X4 X10 X11 Hv KR.
  pose proof CTX as (Hw & HH & AM & K0 & ENT & FRM & FRS & FOK & SP32 & ARGS & RPRE & INCS & INV & EC0 & HE & UNR & CRED & KONT).
  destruct ENT as (Rra & RAok0 & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 3) with 18432 in *. change (18432 / 8) with 2304 in STKSH.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof FOK as ((rs & Hfb) & Fal).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _).
  pose proof (WF _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 5) with 2048 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL, FSIMG, F1, F2.
  rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in FSIMG.
  assert (FBI : 6905856 <= fb) by (clear - F1 FSAPP FSIMG; lia).
  pose proof LM as (BI & RP1 & STEP1 & AXL1 & CK1 & SHC1 & EBB1).
  pose proof G as G'. unfold ed_frame in G'.
  destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 1) with 128 in *. change (128 / 8) with 16 in *.
  pose proof BI as (HH1 & AM1 & MRT1 & INCA1 & INCL1 & ASTK1 & EK1 & DK1 & OWN1 & DSH1).
  set (FF' := (F, 1, sp - 160 + 32) :: FF) in *.
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
  assert (R4b : F / 8 + 2147450880 + 1 <= 2 ^ 64) by (clear - GF2; pose proof (Z.div_le_upper_bound F 8 17592186044400 ltac:(lia) ltac:(lia)); lia).
  assert (AOE : PMSPA.aobjA FF oec 16) by (apply (PNAPAR.aobj_fbB FF fb oec 16 FOK); unfold oec; clear; lia).
  unfold PNRAa.make_ec_spec, PNRA.make_ec_spec in MKE.
  apply (MKE fx1 R1 M1 model1 K (PNM.bparser_own s1 ++ LBX) FF' LK1 Aw1 cr1 oec v (sp - 160) ra ax1 HH1 AM1 K0).
  { unfold PMSPA.entryA. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact X1|]. split; [exact RAok|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|].
    change (PMSPA.pm_scr 1) with 14336. change (14336 / 8) with 1792.
    split; [apply (L5SAR.astk_sub ar M1 M1 sp 18432 160 14336 ASTK1 (mem_grows_refl M1)); [clear; lia| clear; lia| clear; lia| replace (sp - 160) with (sp + (-10) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact A16]|].
    apply (PMKA.shadow_zero_sub M1 (sp - 18432) 2304); [| | clear; lia| clear; lia| clear; lia|].
    - apply PMKA.mod16_8'. replace (sp - 18432) with (sp + (-1152) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16.
    - apply PMKA.mod16_8'. replace (sp - 160 - 14336) with (sp + (-906) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16.
    - apply (PMKA.stksh_keepA L ar LBX FF sp 18432 WR M M1 EK1 WAPPR (sp - 18432) 2304); [clear - SLO SPT; lia| clear - SLO; lia| clear - SHI SPT; lia| | clear; lia| exact STKSH].
      apply PMKA.mod16_8'. replace (sp - 18432) with (sp + (-1152) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  { apply (PMAUAR.ffroomB_push PNRA.FCB 3 1 FF LK LK1 _ FRM INCL1); [exact NDF1| clear; lia]. }
  { apply (PMAUAR.ffrsA_push FF sp (sp - 160) F 1 (sp - 160 + 32) FRS); clear; lia. }
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
  assert (DF2 : F / 8 <= 17592186044400) by (apply Z.div_le_upper_bound; clear - GF2; lia).
  assert (WAV : forall rr a, In rr Wc6 -> L5.in_rng rr a -> ~ (sp - 160 <= a < sp) /\ ~ (F / 8 + SB <= a < F / 8 + SB + 16)).
  { intros rr a Hin Hr. unfold SB. destruct (Wc6R rr a Hin Hr) as [X|X].
    - unfold oec in X. split; [clear - X GSLO F2 FSCEIL; lia| destruct FA1 as [Y|Y]; clear - X Y DF1 DF2 F1 F2; lia].
    - split; [clear - X GSLO GSHI GSPT; lia| clear - X DF1; lia]. }
  assert (WOUT : forall a, aclient L ar LBX FF sp 18432 a -> L5.outside WR a -> L5.outside Wc6 a).
  { intros a Hc Ho rr Hin Hr. destruct (Wc6R rr a Hin Hr) as [X|X].
    - apply (Ho (PNRA.o_ec PMA.AD fb, 16)); [unfold WR, PNRA.W_brun, PGS.W_srcfG; cbn [app]; do 8 right; left; reflexivity| unfold L5.in_rng, PNRA.o_ec, PMSP.o_ec; cbn [fst snd pa_off_ec PMA.AD PnLayoutA_b.ADDR_A]; unfold oec in X; clear - X; lia].
    - unfold Wc6 in Hin. destruct Hin as [<-|Hin]; [unfold L5.in_rng in Hr; cbn [fst snd] in Hr; unfold oec in Hr; clear - Hr X FBI; lia|].
      destruct (PNST.bax_cat ax1); [destruct Hin|]. unfold PNST.cat_W in Hin. destruct Hin as [<-|[<-|[]]].
      + apply (Ho (pa_errcat_guard PMA.AD, 2)); [unfold WR, PNRA.W_brun, PGS.W_srcfG, PNST.berr_W, PNST.cat_W; cbn [app]; do 9 right; left; reflexivity| exact Hr].
      + apply (Ho (pa_atexit PMA.AD, 544)); [unfold WR, PNRA.W_brun, PGS.W_srcfG, PNST.berr_W, PNST.cat_W; cbn [app]; do 10 right; left; reflexivity| exact Hr]. }
  assert (BI6 : PMAUK.binv L ar HI M model LBX FF LK Aw sp 18432 (sp - 160) (own sp R) F 1 WR (PNM.bparser_own s1) M6 model6 LK6 cr1 Aw6).
  { apply (PMAUK.binv_callee L ar C HI HIok M model LBX FF LK Aw sp 18432 (sp - 160) (sp - 104) sp (ocell sp) (own sp R) F fl 1 LK2 M2 model2 cr (PNM.bparser_own s) G
             WR WR (PNM.bparser_own s1) (PNM.bparser_own s1) (PNM.bparser_own s1) M1 model1 LK1 cr1 Aw1 M6 model6 LK6 cr1 Aw6 14336 Wc6 BI HP6 HH6 AM6 MRT6 INCA6 INCL6);
      [clear; lia| clear; lia| intros rr a Hin Hr; destruct (WAV rr a Hin Hr) as (Y1 & Y2); split; [unfold ocell; clear - Y1; lia| exact Y2]| exact WOUT| intros a X; exact X]. }
  pose proof (L5SAR.ek_callee L ar (PNM.bparser_own s1 ++ LBX) [] FF [(F, 1, sp - 160 + 32)] sp 18432 (sp - 160) 14336 Wc6 Wc6 M1 M6 HP6 ltac:(clear; lia) ltac:(clear; lia) (fun a _ X => X)) as EK16.
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
    + apply (L5SAR.fframe_shadow_client L ar _ FF' (sp - 160) 14336 F 1 (sp - 160 + 32)); [left; reflexivity|]. change (ff_bytes 1) with 128.
      unfold in_shadow_of, S. rewrite (proj1 (proj2 GF8)). unfold SB. clear - Hj; lia.
    + intros rr Hin Hr. destruct (WAV rr _ Hin Hr) as (_ & Y). apply Y. unfold SB. clear - Hj; lia.
  - intros a Ha. apply EK6. split; [clear - Ha GSLO GSHI GSPT; lia|]. split.
    + apply (L5SAR.stack_client L ar _ FF' (sp - 160) 14336 a); clear - Ha GSLO GSHI GSPT; lia.
    + intros rr Hin Hr. destruct (WAV rr a Hin Hr) as (Y & _). apply Y. clear - Ha; lia.
Qed.


(* [comment removed for export] *)
Lemma ed_fin K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 (fx5 fx9 : FPState) R5 R9 (pc5 mo : Z) (M9v : mem) :
  ed_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  ed_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  ed_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 ->
  msteps RSEGS (st fx5 R5 pc5 (mrestrict (ahid Aw5 model5) M5)) (st fx9 R9 0xb2038 M9v) ->
  mem_grows (mrestrict (ahid Aw5 model5) M5) M9v ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ PMAUK.WretX F fl 1 (fun a => fb + 472 <= a < fb + 473) a -> M9v (Z_to_bv 64 a) = mrestrict (ahid Aw5 model5) M5 (Z_to_bv 64 a)) ->
  L5.u8_at RSEGS M9v fl 0 -> L5.u8_at RSEGS M9v (fb + 472) mo -> (mo = 0 \/ mo = 1) ->
  getr R9 (reg 2) = Z_to_bv 64 sp ->
  (forall k, In k [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R9 (reg k) = Z_to_bv 64 (bv_unsigned (getr R (reg k)))) ->
  (forall k, In k [3; 4]%nat -> getr R9 (reg k) = getr R (reg k)) ->
  ( (exists v, 1 <= v <= 64 /\ PMSPA.ec_at RSEGS M5 (fb + 1024) v (pa_errcat_obj PMA.AD) /\ mo = 0 /\ PNST.bax_cat ax5 = true /\ (length (PNM.b_stk s) <= length (PNM.b_stk s5))%nat)
    \/ (PMSPA.ec_at RSEGS M5 (fb + 1024) e cat /\ PNRA.bprog_pop R9 M5 s s5 sm sm5) ) ->
  PNRA.binv s5 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx5 R5 pc5 M5 model5) K.
Proof.
  intros CTX G LM MS9 MG9 FRZ9 FL0 MO9 Hmo Y2 YR Y34 POST INV5.
  pose proof CTX as (Hw & HH & AM & K0 & ENT & FRM & FRS & FOK & SP32 & ARGS & RPRE & INCS & INV & EC0 & HE & UNR & CRED & KONT).
  destruct ENT as (Rra & RAok0 & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 3) with 18432 in *. change (18432 / 8) with 2304 in STKSH.
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof RAok0 as (Hr1 & Hr2).
  pose proof FOK as ((rs & Hfb) & Fal).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _).
  pose proof (WF _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 5) with 2048 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL, FSIMG, F1, F2.
  rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in FSIMG.
  assert (FBI : 6905856 <= fb) by (clear - F1 FSAPP FSIMG; lia).
  pose proof LM as (BI & RP1 & STEP1 & AXL1 & CK1 & SHC1 & EBB1).
  pose proof G as G'. unfold ed_frame in G'.
  destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 1) with 128 in *. change (128 / 8) with 16 in *.
  pose proof BI as (HH1 & AM1 & MRT1 & INCA1 & INCL1 & ASTK1 & EK1 & DK1 & OWN1 & DSH1).
  set (FF' := (F, 1, sp - 160 + 32) :: FF) in *.
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
  pose proof (PMK.ret_to RSEGS fx9 R9 M9v 0xb2038 W_b0c48 r F_b0c48 eq_refl D_b0c48 R9ra Hr1 Hr2) as MSr.
  set (Wx := fun a => fb + 472 <= a < fb + 473).
  apply (PMAUK.retire_coreW L ar C HI LYa HIok M model LBX FF LK Aw sp 18432 (sp - 160) (sp - 104) sp (ocell sp) (own sp R) F fl 1 LK2 M2 model2 cr (PNM.bparser_own s) G
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
  { apply (PMAUAR.wret_ek L ar C HI LY HIok LBX FF LK Aw sp 18432 (sp - 160) (sp - 104) sp (ocell sp) (own sp R) F fl 1 LK2 M2 model2 cr (PNM.bparser_own s)
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
    destruct POST as [(v & Hv & EC5 & Hmo0 & CAT & LEN5)|(EC5 & PROG)].
    + left. exists v. split; [exact Hv|]. split; [exact (ECf _ _ EC5)|]. split; [unfold s9; cbn [PNBO.set_more PNM.b_more]; exact Hmo0|]. split; [exact CAT|].
      split; [unfold s9; cbn [PNBO.set_more PNM.b_stk]; exact LEN5| unfold s9, PNRA.binv; cbn [PNBO.set_more PNM.b_done PNM.b_stk]; exact INV5].
    + right. split; [exact (ECf _ _ EC5)|]. split; [unfold s9, PNRA.binv; cbn [PNBO.set_more PNM.b_done PNM.b_stk]; exact INV5|].
      unfold s9, PNRA.bprog_pop. cbn [PNBO.set_more PNM.b_stk PNM.b_src PNM.b_nb PNM.b_tb]. unfold PNRA.bprog_pop in PROG.
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
Lemma ed_piece_fr K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1
      (fx1 fx2 : FPState) R1 R2 (pc1 pc2 : Z) (M2v : mem) (W : Z -> Prop) :
  ed_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  ed_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  ed_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
  msteps RSEGS (st fx1 R1 pc1 (mrestrict (ahid Aw1 model1) M1)) (st fx2 R2 pc2 M2v) ->
  mem_grows (mrestrict (ahid Aw1 model1) M1) M2v ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ W a -> M2v (Z_to_bv 64 a) = mrestrict (ahid Aw1 model1) M1 (Z_to_bv 64 a)) ->
  (forall a, W a -> sp - 160 <= a < sp - 104) ->
  (forall (M3 : mem) model3,
      ed_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK1 Aw1 s1 sm1 ax1 cr1 ->
      ahid Aw1 model3 = ahid Aw1 model1 -> mrestrict (ahid Aw1 model1) M3 = M2v ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ W a -> M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> mem_grows M1 M3 ->
      (forall v c, PMSPA.ec_at RSEGS M1 (fb + 1024) v c -> PMSPA.ec_at RSEGS M3 (fb + 1024) v c) ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx2 R2 pc2 M3 model3) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 pc1 M1 model1) K.
Proof.
  intros CTX G LM MS MG FRZ WP KR.
  pose proof CTX as (Hw & HH & AM & K0 & ENT & FRM & FRS & FOK & SP32 & ARGS & RPRE & INCS & INV & EC0 & HE & UNR & CRED & KONT).
  destruct ENT as (Rra & RAok0 & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 3) with 18432 in *.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof FOK as ((rs & Hfb) & Fal).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _).
  pose proof (WF _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 5) with 2048 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL, FSIMG, F1, F2.
  rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in FSIMG.
  assert (FBI : 6905856 <= fb) by (clear - F1 FSAPP FSIMG; lia).
  pose proof LM as (BI & RP1 & STEP1 & AXL1 & CK1 & SHC1 & EBB1).
  pose proof G as G'. unfold ed_frame in G'.
  destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 1) with 128 in *. change (128 / 8) with 16 in *.
  pose proof BI as (HH1 & AM1 & MRT1 & INCA1 & INCL1 & ASTK1 & EK1 & DK1 & OWN1 & DSH1).
  set (FF' := (F, 1, sp - 160 + 32) :: FF) in *.
  assert (FOK' : PNRA.frame_okB FF' fb). { split; [exists rs; right; exact Hfb| exact Fal]. }
  pose proof RP1 as (PA1 & IA1 & VIS1 & VREF1 & OACC1 & BASE1 & ERR1 & GR1).
  change (PNRA.o_p PMA.AD fb) with (fb + 464) in PA1, IA1, VIS1, VREF1, OACC1. change (PNRA.o_is PMA.AD fb) with (fb + 96) in PA1, IA1. change (PNRA.o_v PMA.AD fb) with (fb + 432) in VIS1, VREF1.
  change (PNM.PSIZE + 8) with 424 in OACC1.
  pose proof GFR as (GF1 & GF2 & _).
  assert (R4a : 0 <= F / 8 + 2147450880) by (clear - GF1; lia).
  assert (R4b : F / 8 + 2147450880 + 1 <= 2 ^ 64) by (clear - GF2; pose proof (Z.div_le_upper_bound F 8 17592186044400 ltac:(lia) ltac:(lia)); lia).
  pose proof (PMASK.stk_vis L ar C HI LY HIok _ FF' LK1 cr1 Aw1 M1 model1 sp 18432 160 HH1 ASTK1 ltac:(lia)) as (SL160 & SH160 & SWR).
  set (H1 := ahid Aw1 model1) in *.
  apply (L5SAR.apiece L ar C HI LYa HIok _ FF' LK1 cr1 Aw1 M1 model1 fx1 fx2 R1 pc1 R2 pc2 M2v W K HH1 AM1 MS MG FRZ).
  { intros a Ha Wa. pose proof (WP a Wa) as X. split; [| clear - X GSLO GSHI GSPT FBI; lia].
    unfold aclientw, aclient_g. right; left. split; [clear - X GSLO GSHI GSPT; lia| intros Y; clear - Y; lia]. }
  intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MG3 FR3 VV3.
  assert (EK13 : L5SAR.ek L ar (PNM.bparser_own s1 ++ LBX) FF' (sp - 104) 56 [] M1 M3).
  { intros a (Ha & Hc & _). apply FR3; [exact Ha|]. intros Wa. pose proof (WP a Wa) as X.
    destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF' LK1 cr1 Aw1 M1 _ (sp - 104) 56 a HH1 GSPT Hc) as [Y|Y]; [clear - X Y; lia| clear - X Y GSLO; lia]. }
  pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH1) as FRB1. pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH1) as BRB1.
  assert (ECK : forall v c, PMSPA.ec_at RSEGS M1 (fb + 1024) v c -> PMSPA.ec_at RSEGS M3 (fb + 1024) v c).
  { intros v0 c0 E0. apply (PMKA.ec_keepA RSEGS L ar _ FF' (sp - 104) 56 [] M1 M3 EK13 PMKA.wapp_nil FRB1 (fb + 1024) v0 c0); [| intros i _ rr []| exact E0].
    apply PMAUAR.aobjA_push. apply (PNAPAR.aobj_fbB FF fb (fb + 1024) 16 FOK); clear; lia. }
  apply (KR M3 model3); [| exact HID3| exact VIS3| exact FR3| exact MG3| exact ECK].
  split.
  { apply (PMAUK.binv_pieceW L ar HI M model LBX FF LK Aw sp 18432 (sp - 160) (sp - 104) sp (ocell sp) (own sp R) F fl 1 LK2 M2 model2 cr (PNM.bparser_own s) G
             _ (PNM.bparser_own s1) M1 model1 LK1 cr1 Aw1 M3 model3 W BI HH3 AM3 MRT3 MG3 FR3).
    intros a Wa. pose proof (WP a Wa) as X. split; [unfold ocell; clear - X; lia| left; clear - X; lia]. }
  split.
  { apply (pre_after_call (PNM.bparser_own s1 ++ LBX) FF' (sp - 104) 56 [] M1 M3 fb s1 s1 str sm1 sm1 ax1 ax1 FRB1 EK13 (PMKA.wapp_nil) FOK'); [intros i _ rr []| exact RP1| | | exact GR1| |].
    - apply (PNAPAR.bparser_keepA L ar C HI HIok _ FF' LK1 cr1 Aw1 (vml_of model1) [] (sp - 104) 56 M1 M3 _ _ s1 HH1 EK13 (PMKA.wapp_nil)); [| apply incl_appl; apply incl_refl| intros i _ rr []| intros B m _ i _ rr []| exact PA1].
      apply PMAUAR.aobjA_push. apply (PNAPAR.aobj_fbB FF fb (fb + 464) PNM.PSIZE FOK); unfold PNM.PSIZE; clear; lia.
    - apply (PMKA.iss_keepA RSEGS PMA.AD L ar _ FF' (sp - 104) 56 [] M1 M3 EK13 (PMKA.wapp_nil) FRB1 BRB1 (fb + 96) str sm1); [| apply incl_appr; exact INCS| intros i _ rr []| intros c0 n0 p0 _ i _ rr []| exact IA1].
      apply PMAUAR.aobjA_push. apply (PNAPAR.aobj_fbB FF fb (fb + 96) 272 FOK); clear; lia.
    - apply (PMASK.base_keep L ar C LY _ FF' (sp - 104) 56 [] M1 M3 EK13); [intros a _ rr []| exact BASE1].
    - apply (berr_keep _ FF' (sp - 104) 56 [] M1 M3 ax1 EK13); [intros a _ rr []| exact ERR1]. }
  split; [exact STEP1|]. split; [exact AXL1|]. split; [exact CK1|]. split; [| exact EBB1].
  apply (L5C.u8_at_agree RSEGS M1 M3); [| exact R4a| exact R4b| exact SHC1].
  intros j Hj. apply FR3; [clear - Hj R4a R4b; lia|]. intros Wj. pose proof (WP _ Wj) as X. clear - X Hj SL160 GSPT GF2.
  pose proof (Z.div_le_upper_bound F 8 17592186044400 ltac:(lia) ltac:(lia)). lia.
Qed.


(* [comment removed for export] *)
Lemma ed_piece_top K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1
      (fx1 fx2 : FPState) R1 R2 (pc1 pc2 : Z) (M2v : mem) pre top (pos' : Z) :
  ed_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  ed_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  ed_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
  PNRA.binv s1 -> PNM.b_stk s1 = pre ++ [top] ->
  msteps RSEGS (st fx1 R1 pc1 (mrestrict (ahid Aw1 model1) M1)) (st fx2 R2 pc2 M2v) ->
  mem_grows (mrestrict (ahid Aw1 model1) M1) M2v ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (PNM.b_sb s1 + 40 * Z.of_nat (length pre) + 40 - 24 <= a < PNM.b_sb s1 + 40 * Z.of_nat (length pre) + 40 - 24 + 8) ->
             M2v (Z_to_bv 64 a) = mrestrict (ahid Aw1 model1) M1 (Z_to_bv 64 a)) ->
  L5.u64_at RSEGS M2v (PNM.b_sb s1 + 40 * Z.of_nat (length pre) + 40 - 24) pos' -> 0 <= pos' < 2 ^ 64 ->
  (forall (M3 : mem) model3,
      ed_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK1 Aw1
             (PNBO.set_stk s1 (pre ++ [PNM.BS (PNM.bs_mode top) (PNM.bs_len top) pos' (PNM.bs_type top) (PNM.bs_idx top)])) sm1 ax1 cr1 ->
      ahid Aw1 model3 = ahid Aw1 model1 -> mrestrict (ahid Aw1 model1) M3 = M2v ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ (PNM.b_sb s1 + 40 * Z.of_nat (length pre) + 40 - 24 <= a < PNM.b_sb s1 + 40 * Z.of_nat (length pre) + 40 - 24 + 8) -> M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
      mem_grows M1 M3 ->
      (forall v c, PMSPA.ec_at RSEGS M1 (fb + 1024) v c -> PMSPA.ec_at RSEGS M3 (fb + 1024) v c) ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx2 R2 pc2 M3 model3) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 pc1 M1 model1) K.
Proof.
  intros CTX G LM INV1 ES MS MG FRZ P9 Hp KR.
  pose proof CTX as (Hw & HH & AM & K0 & ENT & FRM & FRS & FOK & SP32 & ARGS & RPRE & INCS & INV & EC0 & HE & UNR & CRED & KONT).
  destruct ENT as (Rra & RAok0 & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 3) with 18432 in *.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof FOK as ((rs & Hfb) & Fal).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _).
  pose proof (WF _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 5) with 2048 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL, FSIMG, F1, F2.
  rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in FSIMG.
  assert (FBI : 6905856 <= fb) by (clear - F1 FSAPP FSIMG; lia).
  pose proof (tfacts_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 pre top CTX G LM INV1 ES)
    as (TF & PT & OKt & VIN & TB1 & TB2 & TB3 & TB4).
  pose proof LM as (BI & RP1 & STEP1 & AXL1 & CK1 & SHC1 & EBB1).
  pose proof G as G'. unfold ed_frame in G'.
  destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 1) with 128 in *. change (128 / 8) with 16 in *.
  pose proof BI as (HH1 & AM1 & MRT1 & INCA1 & INCL1 & ASTK1 & EK1 & DK1 & OWN1 & DSH1).
  set (FF' := (F, 1, sp - 160 + 32) :: FF) in *.
  assert (FOK' : PNRA.frame_okB FF' fb). { split; [exists rs; right; exact Hfb| exact Fal]. }
  pose proof RP1 as (PA1 & IA1 & VIS1 & VREF1 & OACC1 & BASE1 & ERR1 & GR1).
  change (PNRA.o_p PMA.AD fb) with (fb + 464) in PA1, IA1, VIS1, VREF1, OACC1. change (PNRA.o_is PMA.AD fb) with (fb + 96) in PA1, IA1. change (PNRA.o_v PMA.AD fb) with (fb + 432) in VIS1, VREF1.
  change (PNM.PSIZE + 8) with 424 in OACC1.
  pose proof (PNAPAR.op_visB L ar C HI LY HIok _ FF' LK1 cr1 Aw1 M1 model1 fb _ s1 HH1 FOK' PA1 OACC1) as ((O1 & O8 & ONSH) & Zop & OWR & OCE & OVIS & AOP).
  pose proof GFR as (GF1 & GF2 & _).
  assert (R4a : 0 <= F / 8 + 2147450880) by (clear - GF1; lia).
  assert (R4b : F / 8 + 2147450880 + 1 <= 2 ^ 64) by (clear - GF2; pose proof (Z.div_le_upper_bound F 8 17592186044400 ltac:(lia) ltac:(lia)); lia).
  pose proof (PMASK.stk_vis L ar C HI LY HIok _ FF' LK1 cr1 Aw1 M1 model1 sp 18432 160 HH1 ASTK1 ltac:(lia)) as (SL160 & SH160 & SWR).
  set (op := fb + 464) in *. set (ois := fb + 96) in *.
  set (T := PNM.b_sb s1 + 40 * Z.of_nat (length pre)) in *.
  replace (T + 40 - 24) with (T + 16) in FRZ by (clear; lia). replace (T + 40 - 24) with (T + 16) in P9 by (clear; lia). replace (T + 40 - 24) with (T + 16) in KR by (clear; lia).
  set (W := fun a => T + 16 <= a < T + 16 + 8).
  assert (VINL : In (PNM.b_sb s1, 40 * 2 ^ PNM.b_sk s1) (PNM.bparser_own s1 ++ LBX)) by (apply in_or_app; left; exact VIN).
  pose proof (blk_ceil _ _ _ _ _ _ _ _ _ HH1 VINL) as (_ & (BA0 & BAPP & BA2)). unfold BIGSHADOW_LO, BIGSHADOW_HI in BAPP.
  pose proof (PMASK.blk_img L ar C HI LY HIok _ _ _ _ _ _ _ _ _ HH1 VINL) as BIMG.
  set (H1 := ahid Aw1 model1) in *.
  apply (L5SAR.apiece L ar C HI LYa HIok _ FF' LK1 cr1 Aw1 M1 model1 fx1 fx2 R1 pc1 R2 pc2 M2v W K HH1 AM1 MS MG FRZ).
  { intros a Ha Wa. unfold W in Wa. split; [| clear - Wa BIMG TB1 TB2; lia].
    unfold aclientw, aclient_g. left. exists (PNM.b_sb s1, 40 * 2 ^ PNM.b_sk s1). split; [exact VINL| cbn [fst snd]; clear - Wa TB1 TB2; lia]. }
  intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MG3 FR3 VV3.
  assert (NCW : forall a sp0 scr0, W a -> ~ aclient L ar LBX FF' sp0 scr0 a).
  { intros a sp0 scr0 Wa. unfold W in Wa. apply (PMARS1.own_not_aclient L ar C HI HIok (PNM.bparser_own s1) LBX FF' LK1 cr1 Aw1 M1 _ (PNM.b_sb s1) (40 * 2 ^ PNM.b_sk s1) a sp0 scr0 HH1 VIN). clear - Wa TB1 TB2; lia. }
  assert (EK13 : L5SAR.ek L ar LBX FF' 0 0 [] M1 M3).
  { intros a (Ha & Hc & _). apply FR3; [exact Ha|]. intros Wa. exact (NCW a 0 0 Wa Hc). }
  pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH1) as FRB1. pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH1) as BRB1.
  assert (BRBx : forall b, In b LBX -> 0 <= fst b /\ fst b + snd b <= 2 ^ 47) by (intros b Hb; apply BRB1; apply in_or_app; right; exact Hb).
  set (c' := PNM.BS (PNM.bs_mode top) (PNM.bs_len top) pos' (PNM.bs_type top) (PNM.bs_idx top)) in *.
  set (s3 := PNBO.set_stk s1 (pre ++ [c'])) in *.
  assert (EO3 : PNM.bparser_own s3 = PNM.bparser_own s1) by (unfold s3; destruct s1; reflexivity).
  assert (ECK : forall v c, PMSPA.ec_at RSEGS M1 (fb + 1024) v c -> PMSPA.ec_at RSEGS M3 (fb + 1024) v c).
  { intros v0 c0 E0. apply (PMKA.ec_keepA RSEGS L ar _ FF' 0 0 [] M1 M3 EK13 PMKA.wapp_nil FRB1 (fb + 1024) v0 c0); [| intros i _ rr []| exact E0].
    apply PMAUAR.aobjA_push. apply (PNAPAR.aobj_fbB FF fb (fb + 1024) 16 FOK); clear; lia. }
  apply (KR M3 model3); [| exact HID3| exact VIS3| exact FR3| exact MG3| exact ECK].
  split.
  { rewrite EO3. destruct BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10). unfold PMAUK.binv.
    split; [exact HH3|]. split; [exact AM3|]. split; [eapply L5LZ.model_rt_trans; [exact B3| exact MRT3]|]. split; [exact B4|]. split; [exact B5|].
    split; [eapply L5SAR.astk_grows; [exact B6| exact MG3]|].
    split. { eapply L5SAR.ek_trans; [exact B7|]. intros a (Ha & Hc & Ho). apply FR3; [exact Ha|]. intros Wa. apply (NCW a sp 18432 Wa). apply L5SAR.aclient_cons. exact Hc. }
    split; [eapply L5SAR.dk_trans; [exact B8| apply L5SAR.dk_grows; exact MG3]|].
    split. { apply (own_agree sp R M1 M3 ltac:(clear - GSPC; lia) ltac:(clear - GSPC; lia) B9). intros a Ha. unfold ocell in Ha. apply FR3; [clear - Ha GSPC; lia|]. intros Wa. unfold W in Wa. clear - Ha Wa TB3 TB2 GSLO; lia. }
    eapply L5.defined_grows; [exact MG3| exact B10]. }
  split.
  { apply (pre_after_call LBX FF' 0 0 [] M1 M3 fb s1 s3 str sm1 sm1 ax1 ax1 FRB1 EK13 (PMKA.wapp_nil) FOK'); [intros i _ rr []| exact RP1| | | unfold s3; exact GR1| |].
    - apply (PNBOA.bparser_top_upd RSEGS PMA.AD (pa_vp_parser PMA.AD) M1 M3 W FR3 MG3 op ois s1 pre top c' ltac:(clear - O1; lia) ltac:(unfold PNM.PSIZE; clear - O1; lia) PA1 ES).
      + pose proof PA1 as (_ & _ & _ & _ & _ & _ & _ & _ & SRC1 & _). pose proof SRC1 as (_ & _ & _ & _ & _ & _ & _ & _ & Qr & _).
        split.
        * intros i Hi. unfold PNBOA.nsh, S, W, SB. unfold PNM.PSIZE in Hi.
          pose proof (Z.div_pos i 8 ltac:(clear - Hi O1; lia) ltac:(clear; lia)) as D0. pose proof (Z.div_le_upper_bound i 8 17592186044415 ltac:(clear; lia) ltac:(clear - Hi O1; lia)) as D1.
          clear - D0 D1 BAPP TB1 TB2. split; lia.
        * intros B m HB i Hi. assert (HBL : In (B, m) (PNM.bparser_own s1 ++ LBX)) by (apply in_or_app; left; exact HB).
          pose proof (blk_ceil _ _ _ _ _ _ _ _ _ HH1 HBL) as (BC & (BB0 & _ & BB2)).
          pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH1) as (WBb & _). destruct (WBb _ HBL) as ((_ & _ & _ & Bpos & _) & _). cbn [fst snd] in Bpos.
          pose proof (PNBOA.gspan_ge m ltac:(clear - Bpos; lia)) as GS.
          unfold PNBOA.nsh, S, W, SB. pose proof (Z.div_le_upper_bound i 8 17592186044415 ltac:(clear; lia) ltac:(clear - Hi BC GS GSLO GSHI GSPT; lia)) as D1.
          pose proof (Z.div_pos i 8 ltac:(clear - Hi BB0; lia) ltac:(clear; lia)) as D0. clear - D0 D1 BAPP TB1 TB2. split; lia.
      + intros a Ha Wa. unfold W in Wa. unfold PNM.PSIZE in Ha.
        pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH1) as (WB1 & _). destruct (WB1 _ VINL) as (_ & _ & _ & _ & _ & BFA & _).
        pose proof (BFA (fb, 5, rs) (in_or_app FF' LK1 (fb, 5, rs) (or_introl (or_intror Hfb)))) as Z2. cbn [ff_addr ff_class fst snd] in Z2. change (ff_bytes 5) with 2048 in Z2.
        unfold op in Ha. clear - Ha Wa Z2 TB1 TB2; lia.
      + intros i Hi Wi. unfold W in Wi.
        pose proof (PMASK.lb_nodup L ar C HI HIok _ _ _ _ _ _ _ HH1) as ND. unfold PNM.bparser_own, PM.src_own, PNM.brest_own, PNM.bvec_own in ND. cbn [map fst app] in ND.
        assert (NE : PM.sr_qc (PNM.b_src s1) <> PNM.b_sb s1).
        { inversion ND; subst. intros E. match goal with NI : not (elem_of _ _) |- _ => apply NI; rewrite E; left end. }
        destruct (PMASK.blk_apart L ar C HI HIok _ _ _ _ _ _ _ (PM.sr_qc (PNM.b_src s1)) PM.CHUNK (PNM.b_sb s1) (40 * 2 ^ PNM.b_sk s1) HH1 (in_or_app _ _ _ (or_introl (PNBOA.PNM_own_src s1))) VINL NE) as [X|X];
          [clear - Hi Wi X TB1 TB2; lia| clear - Hi Wi X TB1 TB2; lia].
      + intros i Hi Wi. unfold W in Wi. unfold T in Wi |- *. clear - Wi; lia.
      + destruct PT as (PT0 & PT8 & PT16 & PT24 & PT32). unfold c', PNM.bstate_at. cbn [PNM.bs_mode PNM.bs_len PNM.bs_pos PNM.bs_type PNM.bs_idx]. fold T.
        assert (AGT : forall a n, T <= a -> a + n <= T + 40 -> (a + n <= T + 16 \/ T + 24 <= a) -> L5C.agree_on M1 M3 a n).
        { intros a n X1 X2 X3 j Hj. apply FR3; [clear - Hj X1 X2 TB1 TB2 TB3 TB4 GSHI GSPT GSLO; lia| unfold W; clear - Hj X3; lia]. }
        split; [apply (PMF.u32_at_agree RSEGS M1 M3); [apply AGT; clear; lia| clear - TB4 TB1; lia| clear - TB2 TB3 GSLO GSHI GSPT; lia| exact PT0]|].
        split; [apply (L5C.u64_at_agree RSEGS M1 M3); [apply AGT; clear; lia| clear - TB4 TB1; lia| clear - TB2 TB3 GSLO GSHI GSPT; lia| exact PT8]|].
        split. { destruct TF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
                 pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ _ LK1 cr1 Aw1 M1 model1 HH1) as VP; cbv zeta in VP; destruct VP as (_ & _ & _ & _ & VB & _).
                 assert (TV : L5A.avis (ahid Aw1 model1) (T + 16) 8) by (apply (VB _ _ (T + 16) 8 VINL); clear - TB1 TB2; lia).
                 rewrite <- HID3 in TV. apply (proj1 (L5A.u64_at_vis _ M3 (T + 16) pos' TV ltac:(clear - TB4 TB1; lia) ltac:(clear - TB2 TB3 GSLO GSHI GSPT; lia))).
                 rewrite HID3. rewrite VIS3. exact P9. }
        split; [apply (L5C.u8_at_agree RSEGS M1 M3); [apply AGT; clear; lia| clear - TB4 TB1; lia| clear - TB2 TB3 GSLO GSHI GSPT; lia| exact PT24]|].
        apply (L5C.u64_at_agree RSEGS M1 M3); [apply AGT; clear; lia| clear - TB4 TB1; lia| clear - TB2 TB3 GSLO GSHI GSPT; lia| exact PT32].
      + clear - TB4; lia.
      + change PNM.BSZ with 40. clear - TB3 GSLO GSHI GSPT; lia.
      + destruct (BRB1 _ (in_or_app _ _ _ (or_introl (PNBOA.PNM_own_src s1)))) as (Q0 & _). cbn [fst snd] in Q0. exact Q0.
      + pose proof (blk_ceil _ _ _ _ _ _ _ _ _ HH1 (in_or_app _ _ _ (or_introl (PNBOA.PNM_own_src s1)))) as (QC & _). clear - QC GSLO GSHI GSPT; lia.
    - apply (PMKA.iss_keepA RSEGS PMA.AD L ar _ FF' 0 0 [] M1 M3 EK13 (PMKA.wapp_nil) FRB1 BRBx (fb + 96) str sm1); [| exact INCS| intros i _ rr []| intros c0 n0 p0 _ i _ rr []| exact IA1].
      apply PMAUAR.aobjA_push. apply (PNAPAR.aobj_fbB FF fb (fb + 96) 272 FOK); clear; lia.
    - apply (PMASK.base_keep L ar C LY _ FF' 0 0 [] M1 M3 EK13); [intros a _ rr []| exact BASE1].
    - apply (berr_keep _ FF' 0 0 [] M1 M3 ax1 EK13); [intros a _ rr []| exact ERR1]. }
  split; [unfold s3; cbn [PNBO.set_stk PNM.b_src]; exact STEP1|]. split; [exact AXL1|].
  split; [unfold s3, PNRA.pot_bparser; cbn [PNBO.set_stk PNM.b_sk PNM.b_tb PNM.b_tg PNM.b_nb PNM.b_ng PNM.b_bb PNM.b_bg]; exact CK1|].
  split; [| unfold s3; cbn [PNBO.set_stk PNM.b_bb]; exact EBB1].
  apply (L5C.u8_at_agree RSEGS M1 M3); [| exact R4a| exact R4b| exact SHC1].
  intros j Hj. apply FR3; [clear - Hj R4a R4b; lia|]. unfold W. clear - Hj BAPP TB1 TB2 GF1 GF2. unfold SB in *.
  pose proof (Z.div_le_upper_bound F 8 17592186044400 ltac:(lia) ltac:(lia)). pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)). lia.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition sz64 (m : Z) : Z :=
  bv_unsigned (mul_div Instr.M_MUL (Z_to_bv 64 (-3689348814741910323)) (alu64 Instr.ALU_SRA (Z_to_bv 64 m) (Z_to_bv 64 3))).
Definition sz32 (m : Z) : Z :=
  bv_unsigned (sext 64 (mul_div Instr.M_MUL (low32 (alu64 Instr.ALU_SRA (Z_to_bv 64 m) (Z_to_bv 64 3))) (low32 (Z_to_bv 64 14757395258967641293)))).
Lemma sz_tab : forallb (fun n => Z.eqb (sz64 (40 * Z.of_nat n)) (Z.of_nat n) && Z.eqb (sz32 (40 * Z.of_nat n)) (Z.of_nat n)) (seq 0 1026) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma sz_ok n : 0 <= n <= 1025 -> sz64 (40 * n) = n /\ sz32 (40 * n) = n.
Proof.
  intros Hn. pose proof sz_tab as T. rewrite forallb_forall in T. specialize (T (Z.to_nat n)).
  rewrite Z2Nat.id in T by lia. assert (I : In (Z.to_nat n) (seq 0 1026)) by (apply in_seq; lia).
  specialize (T I). apply andb_true_iff in T. destruct T as (A & B). apply Z.eqb_eq in A. apply Z.eqb_eq in B. split; assumption.
Qed.

Lemma perm2 {T} (a v b n t x : list T) : Permutation ((a ++ v ++ b ++ n ++ t) ++ x) (v ++ (a ++ b ++ n ++ t) ++ x).
Proof.
  rewrite <- !app_assoc. rewrite (app_assoc a v), (app_assoc v a). apply Permutation_app_tail. apply Permutation_app_comm.
Qed.

(* [comment removed for export] *)
Lemma bparser_set_stkS (M M' : mem) vp op ois s stk' :
  6905856 <= op -> op + 416 <= 2 ^ 64 ->
  (forall i, op <= i < op + 416 -> ~ (op + 400 <= i < op + 408) -> PNBOA.snt M M' i) ->
  (forall i, op + 400 <= i < op + 408 -> M' (Z_to_bv 64 i) <> None) ->
  (forall i, op <= i < op + 416 -> PNBOA.sns M M' i) ->
  (forall B m, In (B, m) (PM.src_own (PNM.b_src s) ++ PGV8.v8_own (PNM.b_bb s) ++ PM.vs_own (PNM.b_nb s) ++ PM.vs_own (PNM.b_tb s)) -> 0 <= B /\ B + m <= 2 ^ 64 /\ PMFA.agA M M' B m) ->
  PNM.bvec_at RSEGS PMSPA.accA PMSPA.annA M' (op + 392) (PNM.b_sb s) (PNM.b_sk s) stk' ->
  PNM.bparser_at RSEGS PMA.AD PMSPA.accA PMSPA.annA vp M op ois s -> PNM.bparser_at RSEGS PMA.AD PMSPA.accA PMSPA.annA vp M' op ois (PNBO.set_stk s stk').
Proof.
  intros Ho Ho' No Yo So AGb BV' PA. pose proof PA as (_ & Dop & _ & H8 & H9 & _ & _ & _ & SRC & _ & _ & BB & NB & TB & STK & M01 & D01).
  unfold PNM.PSIZE, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK in *.
  set (REST := PM.src_own (PNM.b_src s) ++ PGV8.v8_own (PNM.b_bb s) ++ PM.vs_own (PNM.b_nb s) ++ PM.vs_own (PNM.b_tb s)) in *.
  assert (BLK : forall B m, In (B, m) REST -> 0 <= m -> (forall i, B <= i < B + m -> PNBOA.snt M M' i) /\ (forall i, B <= i < B + m -> PNBOA.sns M M' i) /\ 0 <= B /\ B + m <= 2 ^ 64).
  { intros B m Hi Hm. destruct (AGb B m Hi) as (B0 & B1 & AG). split; [exact (PNBOA.agA_snt M M' _ _ AG)|]. split; [exact (PNBOA.agA_sns M M' _ _ AG)|]. lia. }
  assert (BLKG : forall B m, In (B, m) REST -> 0 <= m -> B mod 8 = 0 -> forall i, B <= i < B + PNBOA.gspan m -> PNBOA.sns M M' i).
  { intros B m Hi Hm HB. destruct (AGb B m Hi) as (B0 & B1 & [_ AG]). exact (PNBOA.agsh_gspan M M' B m HB Hm AG). }
  pose proof SRC as (_ & _ & _ & _ & _ & _ & _ & _ & Qr & _).
  assert (Iq : In (PM.sr_qc (PNM.b_src s), PM.CHUNK) REST) by (unfold REST, PM.src_own; left; reflexivity).
  assert (Ib : forall B m, In (B, m) (PGV8.v8_own (PNM.b_bb s)) -> In (B, m) REST) by (intros B m X; unfold REST; rewrite !in_app_iff; tauto).
  assert (In_ : forall B m, In (B, m) (PM.vs_own (PNM.b_nb s)) -> In (B, m) REST) by (intros B m X; unfold REST; rewrite !in_app_iff; tauto).
  assert (It : forall B m, In (B, m) (PM.vs_own (PNM.b_tb s)) -> In (B, m) REST) by (intros B m X; unfold REST; rewrite !in_app_iff; tauto).
  destruct (BLK _ _ Iq ltac:(unfold PM.CHUNK; lia)) as (NTq & NSq & Q0 & Q1).
  set (Yd := fun i => M (Z_to_bv 64 i) <> None -> M' (Z_to_bv 64 i) <> None).
  assert (YS : forall i, PNBOA.snt M M' i -> Yd i) by (intros i E D; unfold PNBOA.snt in E; unfold Yd; rewrite E; exact D).
  pose proof (PNBOA.bparser_at_xfer RSEGS PMA.AD vp M M' (PNBOA.snt M M') Yd (PNBOA.sns M M') (PNBOA.sAGX M M') (fun i H => H) (PNBOA.sSHX M M')) as XFER.
  pose proof (PNBOA.src_keep_x RSEGS M M' (PNBOA.snt M M') (PNBOA.sns M M') (PNBOA.sAGX M M') (PNBOA.sSHX M M')) as SRCK.
  pose proof (PNBOA.v8_keep_x RSEGS M M' (PNBOA.snt M M') Yd (PNBOA.sns M M') (PNBOA.sAGX M M') (fun i H => H) (PNBOA.sSHX M M')) as V8K.
  pose proof (PNBOA.vstr_keep_x RSEGS M M' (PNBOA.snt M M') Yd (PNBOA.sns M M') (PNBOA.sAGX M M') (fun i H => H) (PNBOA.sSHX M M')) as VSK.
  assert (VKEEP : forall o y, (o = op + 344 /\ y = PNM.b_nb s) \/ (o = op + 368 /\ y = PNM.b_tb s) -> PM.vstr_at RSEGS PMSPA.accA M o y -> PM.vstr_at RSEGS PMSPA.accA M' o y).
  { intros o y Hoy VY. assert (Hoi : op + 16 <= o /\ o + 24 <= op + 392 /\ forall B m, In (B, m) (PM.vs_own y) -> In (B, m) REST).
    { destruct Hoy as [(-> & ->)|(-> & ->)]; (split; [lia| split; [lia|]]); [exact In_| exact It]. }
    destruct Hoi as (O1 & O2 & OWNy).
    apply (VSK o y); [lia| lia| intros i Hi; apply No; lia| intros i Hi; apply YS; apply No; lia| intros i Hi; apply So; lia| | | exact VY].
    - intros B m Hi. pose proof (OWNy B m Hi) as OI. destruct y eqn:EVS; cbn in Hi; [destruct Hi| destruct Hi as [Hi|[]]; inversion Hi; subst].
      unfold PM.vstr_at in VY. destruct VY as (_ & _ & _ & _ & _ & Hn & Hc & _). destruct (BLK _ _ OI ltac:(lia)) as (X & _). intros i Hr. apply YS. apply X. exact Hr.
    - intros B m Hi. pose proof (OWNy B m Hi) as OI. destruct y eqn:EVS; cbn in Hi; [destruct Hi| destruct Hi as [Hi|[]]; inversion Hi; subst].
      unfold PM.vstr_at in VY. destruct VY as (_ & _ & _ & _ & _ & Hn & Hc & _). destruct (BLK _ _ OI ltac:(lia)) as (_ & X & _). exact X. }
  replace (PNBO.set_stk s stk') with (PNM.BPST (PNM.b_more s) (PNM.b_done s) (PNM.b_src s) (PNM.b_bb s) (PNM.b_nb s) (PNM.b_tb s) (PNM.b_ng s) (PNM.b_tg s) (PNM.b_bg s) (PNM.b_sb s) (PNM.b_sk s) stk') by (destruct s; reflexivity).
  apply (XFER op ois s _ ltac:(lia) ltac:(unfold PNM.PSIZE; lia) PA); unfold PNM.PSIZE, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK;
    cbn [PNM.b_more PNM.b_done PNM.b_src PNM.b_bb PNM.b_nb PNM.b_tb PNM.b_sb PNM.b_sk PNM.b_stk].
  - intros i Hi. destruct (Z_lt_le_dec i (op + 400)) as [X|X]; [apply YS; apply No; lia|]. destruct (Z_lt_le_dec i (op + 408)) as [X'|X']; [intros _; apply Yo; lia| apply YS; apply No; lia].
  - exact So.
  - intros i Hi. apply No; lia.
  - intros i Hi. apply No; lia.
  - intros i Hi. apply No; lia.
  - intros i Hi. apply No; lia.
  - apply (L5C.u8_at_agree RSEGS M M'); [apply PNBOA.sAGX; [lia|lia|intros i Hi; apply No; lia]|lia|lia|exact H8].
  - apply (L5C.u8_at_agree RSEGS M M'); [apply PNBOA.sAGX; [lia|lia|intros i Hi; apply No; lia]|lia|lia|exact H9].
  - exact M01.
  - exact D01.
  - apply SRCK; [lia|lia|lia|lia| intros i Hi; apply No; lia| exact NTq| intros i Hi; apply So; lia| exact NSq| exact SRC].
  - apply V8K; [lia|lia| intros i Hi; apply No; lia| intros i Hi; apply So; lia| | | exact BB].
    + intros B m Hi i Hr. pose proof (Ib B m Hi) as OI. destruct (PNM.b_bb s) eqn:EBB; cbn in Hi; [destruct Hi| destruct Hi as [Hi|[]]; inversion Hi; subst].
      unfold PGV8.v8_at in BB. destruct BB as (_ & _ & _ & _ & _ & Hn & Hc & _). destruct (BLK _ _ OI ltac:(lia)) as (X & _). apply YS. apply X. exact Hr.
    + intros B m Hi. pose proof (Ib B m Hi) as OI. destruct (PNM.b_bb s) eqn:EBB; cbn in Hi; [destruct Hi| destruct Hi as [Hi|[]]; inversion Hi; subst].
      unfold PGV8.v8_at in BB. destruct BB as (_ & _ & _ & _ & _ & Hn & Hc & _ & Hal & _). exact (BLKG _ _ OI ltac:(lia) (PMFA.mod16_8 _ Hal)).
  - apply VKEEP; [left; auto| exact NB].
  - apply VKEEP; [right; auto| exact TB].
  - exact BV'.
Qed.

(* [comment removed for export] *)
Lemma ed_piece_more K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1
      (fx1 fx2 : FPState) R1 R2 (pc1 pc2 : Z) (M2v : mem) (mo : Z) :
  ed_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  ed_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  ed_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
  msteps RSEGS (st fx1 R1 pc1 (mrestrict (ahid Aw1 model1) M1)) (st fx2 R2 pc2 M2v) ->
  mem_grows (mrestrict (ahid Aw1 model1) M1) M2v ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (fb + 472 <= a < fb + 473) -> M2v (Z_to_bv 64 a) = mrestrict (ahid Aw1 model1) M1 (Z_to_bv 64 a)) ->
  L5.u8_at RSEGS M2v (fb + 472) mo -> (mo = 0 \/ mo = 1) ->
  (forall (M3 : mem) model3,
      ed_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK1 Aw1 (PNBO.set_more s1 mo) sm1 ax1 cr1 ->
      ahid Aw1 model3 = ahid Aw1 model1 -> mrestrict (ahid Aw1 model1) M3 = M2v ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ (fb + 472 <= a < fb + 473) -> M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> mem_grows M1 M3 ->
      (forall v c, PMSPA.ec_at RSEGS M1 (fb + 1024) v c -> PMSPA.ec_at RSEGS M3 (fb + 1024) v c) ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx2 R2 pc2 M3 model3) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 pc1 M1 model1) K.
Proof.
  intros CTX G LM MS MG FRZ MO9 Hmo KR.
  pose proof CTX as (Hw & HH & AM & K0 & ENT & FRM & FRS & FOK & SP32 & ARGS & RPRE & INCS & INV & EC0 & HE & UNR & CRED & KONT).
  destruct ENT as (Rra & RAok0 & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 3) with 18432 in *.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof FOK as ((rs & Hfb) & Fal).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _).
  pose proof (WF _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 5) with 2048 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL, FSIMG, F1, F2.
  rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in FSIMG.
  assert (FBI : 6905856 <= fb) by (clear - F1 FSAPP FSIMG; lia).
  pose proof LM as (BI & RP1 & STEP1 & AXL1 & CK1 & SHC1 & EBB1).
  pose proof G as G'. unfold ed_frame in G'.
  destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 1) with 128 in *. change (128 / 8) with 16 in *.
  pose proof BI as (HH1 & AM1 & MRT1 & INCA1 & INCL1 & ASTK1 & EK1 & DK1 & OWN1 & DSH1).
  set (FF' := (F, 1, sp - 160 + 32) :: FF) in *.
  assert (FOK' : PNRA.frame_okB FF' fb). { split; [exists rs; right; exact Hfb| exact Fal]. }
  pose proof RP1 as (PA1 & IA1 & VIS1 & VREF1 & OACC1 & BASE1 & ERR1 & GR1).
  change (PNRA.o_p PMA.AD fb) with (fb + 464) in PA1, IA1, VIS1, VREF1, OACC1. change (PNRA.o_is PMA.AD fb) with (fb + 96) in PA1, IA1. change (PNRA.o_v PMA.AD fb) with (fb + 432) in VIS1, VREF1.
  change (PNM.PSIZE + 8) with 424 in OACC1.
  pose proof (PNAPAR.op_visB L ar C HI LY HIok _ FF' LK1 cr1 Aw1 M1 model1 fb _ s1 HH1 FOK' PA1 OACC1) as ((O1 & O8 & ONSH) & Zop & OWR & OCE & OVIS & AOP).
  set (op := fb + 464) in *. set (ois := fb + 96) in *.
  set (WR := PNRA.W_brun PMA.AD PMA.AN fb) in *.
  pose proof FSAPP as (FA0 & FA1 & FA2). unfold BIGSHADOW_LO, BIGSHADOW_HI in FA1.
  pose proof GFR as (GF1 & GF2 & _).
  assert (DF1 : 0 <= F / 8) by (apply Z.div_pos; clear - GF1; lia).
  assert (DF2 : F / 8 <= 17592186044400) by (apply Z.div_le_upper_bound; clear - GF2; lia).
  assert (R4a : 0 <= F / 8 + 2147450880) by (clear - DF1; lia).
  assert (R4b : F / 8 + 2147450880 + 1 <= 2 ^ 64) by (clear - DF2; lia).
  set (H1 := ahid Aw1 model1) in *.
  set (W := fun a => fb + 472 <= a < fb + 473).
  apply (L5SAR.apiece L ar C HI LYa HIok _ FF' LK1 cr1 Aw1 M1 model1 fx1 fx2 R1 pc1 R2 pc2 M2v W K HH1 AM1 MS MG FRZ).
  { intros a Ha Wa. unfold W in Wa. split; [| clear - Wa FBI; lia].
    apply (L5SAR.fframe_client L ar _ FF' 0 0 fb 5 rs); [right; exact Hfb| change (ff_bytes 5) with 2048; clear - Wa; lia]. }
  intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MG3 FR3 VV3. change (mrestrict H1 M3 = M2v) in VIS3.
  assert (EKf : L5SAR.ek L ar (PNM.bparser_own s1 ++ LBX) FF 0 0 [(fb + 472, 1)] M1 M3).
  { apply (PMAUAR.wret_ek L ar C HI LY HIok LBX FF LK Aw sp 18432 (sp - 160) (sp - 104) sp (ocell sp) (own sp R) F fl 1 LK2 M2 model2 cr (PNM.bparser_own s)
             (PNM.bparser_own s1 ++ LBX) LK1 cr1 Aw1 M1 M3 _ [(fb + 472, 1)] W G HH1).
    - intros a X O. apply (O (fb + 472, 1)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; unfold W in X; clear - X; lia].
    - intros a Ha N. apply FR3; [exact Ha|]. intros Wa. apply N. right. exact Wa. }
  pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB. pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH1) as BRB1.
  assert (MOf : L5.u8_at RSEGS M3 (op + 8) mo).
  { apply (proj1 (L5A.u8_at_vis H1 M3 (op + 8) mo (OVIS (op + 8) 1 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - O1; lia) ltac:(clear - O1; lia))). rewrite VIS3. replace (op + 8) with (fb + 472) by (unfold op; clear; lia). exact MO9. }
  assert (WAPP8 : PMKA.wapp [(fb + 472, 1)]).
  { apply PMKA.wapp_cons; [| apply PMKA.wapp_nil]. cbn [fst snd]. unfold BIGSHADOW_LO, BIGSHADOW_HI. destruct FA1 as [Y|Y]; clear - Y F1 F2; lia. }
  assert (OUT8 : forall a n, (a + n <= op + 8 \/ op + 9 <= a) -> forall i, a <= i < a + n -> L5.outside [(fb + 472, 1)] i).
  { intros a n X3 i Hi rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. unfold op in X3. clear - Hi Hr X3. lia. }
  assert (OUTB8 : forall q m, In (q, m) (PNM.bparser_own s1 ++ LBX) -> forall i, q <= i < q + m -> L5.outside [(fb + 472, 1)] i).
  { intros q m Hq i Hi rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr.
    destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q m op 416 HH1 Hq (PMAUAR.aobjA_push FF op 416 _ (PNAPAR.aobj_fbB FF fb op 416 FOK ltac:(unfold op; clear; lia) ltac:(unfold op; clear; lia)))) as [Z0|Z0]; unfold op in Z0; clear - Hi Hr Z0; lia. }
  set (s9 := PNBO.set_more s1 mo).
  assert (EO9 : PNM.bparser_own s9 = PNM.bparser_own s1) by (unfold s9; destruct s1; reflexivity).
  assert (PA9 : PNM.bparser_at RSEGS PMA.AD PMSPA.accA PMSPA.annA (pa_vp_parser PMA.AD) M3 op ois s9).
  { apply (bparser_set_moreS M1 M3 (pa_vp_parser PMA.AD) op ois s1 mo ltac:(clear - O1; lia) ltac:(clear - O1; lia)); [| | | exact MOf| exact Hmo| exact PA1].
    - intros i Hi Hn. destruct (Z_lt_le_dec i (op + 8)) as [X|X].
      + refine (proj1 (PMKA.agA_obj L ar _ FF 0 0 _ M1 M3 EKf WAPP8 FRB op 8 _ _) i _); [| apply OUT8; clear; lia| clear - Hi X; lia].
        apply (PNAPAR.aobj_fbB FF fb op 8 FOK); unfold op; clear; lia.
      + refine (proj1 (PMKA.agA_obj L ar _ FF 0 0 _ M1 M3 EKf WAPP8 FRB (op + 9) 407 _ _) i _); [| apply OUT8; clear; lia| clear - Hi X Hn; lia].
        apply (PNAPAR.aobj_fbB FF fb (op + 9) 407 FOK); unfold op; clear; lia.
    - intros i Hi. refine (PMKA.agsh_obj L ar _ FF 0 0 _ M1 M3 EKf WAPP8 FRB op 416 _ i Hi). apply (PNAPAR.aobj_fbB FF fb op 416 FOK); unfold op; clear; lia.
    - intros q m Hq. assert (HqL : In (q, m) (PNM.bparser_own s1 ++ LBX)) by (apply in_or_app; left; exact Hq). destruct (BRB1 _ HqL) as (B0 & B1). cbn [fst snd] in B0, B1.
      split; [exact B0|]. split; [clear - B1; lia|]. apply (PMKA.agA_blk L ar _ FF 0 0 _ M1 M3 EKf WAPP8 BRB1 q m HqL). apply OUTB8. exact HqL. }
  assert (IA9 : PM.iss_at RSEGS PMA.AD PMSPA.accA M3 ois str sm1).
  { apply (PMKA.iss_keepA RSEGS PMA.AD L ar _ FF 0 0 _ M1 M3 EKf WAPP8 FRB BRB1 ois str sm1); [| | | | exact IA1].
    - apply (PNAPAR.aobj_fbB FF fb ois 272 FOK); unfold ois; clear; lia.
    - apply incl_appr. exact INCS.
    - apply OUT8. unfold ois, op; clear; lia.
    - intros c0 n0 p0 E0. unfold PMKA.blk_out. apply OUTB8. apply in_or_app; right. apply INCS. rewrite E0. left; reflexivity. }
  assert (BASE9 : PMSTA.base_okA RSEGS PMA.AD M3).
  { apply (PMASK.base_keep L ar C LY _ FF 0 0 _ M1 M3 EKf); [| exact BASE1]. intros a Ha rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - Ha Hr FBI; lia. }
  assert (ERR9 : PNSTA.berr_okA RSEGS PMA.AD PMA.AAD PMA.AN M3 ax1).
  { apply (berr_keep _ FF 0 0 _ M1 M3 ax1 EKf); [| exact ERR1]. intros a Ha rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - Ha Hr FBI; lia. }
  assert (PRE9 : PNRA.brun_pre RSEGS PMA.AD PMA.AN PMA.AAD M3 fb s9 str sm1 ax1).
  { apply (pre_after_call _ FF 0 0 _ M1 M3 fb s1 s9 str sm1 sm1 ax1 ax1 FRB EKf WAPP8 FOK); [| exact RP1| exact PA9| exact IA9| unfold s9; exact GR1| exact BASE9| exact ERR9].
    intros i Hi. apply (OUT8 i 1); [unfold op; clear - Hi; lia| clear; lia]. }
  assert (ECf : forall v c, PMSPA.ec_at RSEGS M1 (fb + 1024) v c -> PMSPA.ec_at RSEGS M3 (fb + 1024) v c).
  { intros v c EC5. apply (PMKA.ec_keepA RSEGS L ar _ FF 0 0 _ M1 M3 EKf WAPP8 FRB (fb + 1024) v c); [| | exact EC5].
    - apply (PNAPAR.aobj_fbB FF fb (fb + 1024) 16 FOK); clear; lia.
    - apply OUT8. unfold op; clear; lia. }
  apply (KR M3 model3); [| exact HID3| exact VIS3| exact FR3| exact MG3| exact ECf].
  fold s9. split.
  { rewrite EO9.
    apply (PMAUK.binv_pieceW L ar HI M model LBX FF LK Aw sp 18432 (sp - 160) (sp - 104) sp (ocell sp) (own sp R) F fl 1 LK2 M2 model2 cr (PNM.bparser_own s) G
             _ (PNM.bparser_own s1) M1 model1 LK1 cr1 Aw1 M3 model3 W BI HH3 AM3 MRT3 MG3 FR3).
    intros a Wa. unfold W in Wa. split; [unfold ocell; clear - Wa GSLO F2 FSCEIL; lia|]. right; right; right.
    intros O. apply (O (PNRA.o_p PMA.AD fb + 8, 8)); [unfold PNRA.W_brun; left; reflexivity| unfold L5.in_rng, PNRA.o_p, PMSP.o_p; cbn [fst snd pa_off_p PMA.AD PnLayoutA_b.ADDR_A]; clear - Wa; lia]. }
  split; [exact PRE9|].
  split; [unfold s9; cbn [PNBO.set_more PNM.b_src]; exact STEP1|]. split; [exact AXL1|].
  split; [unfold s9, PNRA.pot_bparser; cbn [PNBO.set_more PNM.b_sk PNM.b_tb PNM.b_tg PNM.b_nb PNM.b_ng PNM.b_bb PNM.b_bg]; exact CK1|].
  split; [| unfold s9; cbn [PNBO.set_more PNM.b_bb]; exact EBB1].
  apply (L5C.u8_at_agree RSEGS M1 M3); [| exact R4a| exact R4b| exact SHC1].
  intros j Hj. apply FR3; [clear - Hj R4a R4b; lia|]. unfold W. destruct FA1 as [Y|Y]; clear - Hj Y F1 F2 DF1 DF2; lia.
Qed.

(* [comment removed for export] *)
Lemma tlen_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 pre top :
  ed_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  ed_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  ed_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
  PNRA.binv s1 -> PNM.b_stk s1 = pre ++ [top] ->
  L5.u64_at RSEGS (mrestrict (ahid Aw1 model1) M1) (PNM.b_sb s1 + 40 * Z.of_nat (length pre) + 40 - 32) (PNM.bs_len top)
  /\ L5KA.zeros_at (mrestrict (ahid Aw1 model1) M1) (((PNM.b_sb s1 + 40 * Z.of_nat (length pre) + 40 - 32) / 8) + 2147450880) 1
  /\ 0 <= PNM.bs_len top < 2 ^ 64.
Proof.
  intros CTX G LM INV1 ES.
  pose proof (tfacts_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 pre top CTX G LM INV1 ES)
    as (TF & PT & OKt & VIN & TB1 & TB2 & TB3 & TB4).
  destruct CTX as (Hw & HH & AM & K0 & ENT & FRM & FRS & FOK & SP32 & ARGS & RPRE & INCS & INV & EC0 & HE & UNR & CRED & KONT).
  destruct LM as (BI & RP1 & STEP1 & AXL1 & CK1 & SHC1 & EBB1).
  pose proof G as G'. unfold ed_frame in G'.
  destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  pose proof BI as (HH1 & AM1 & MRT1 & INCA1 & INCL1 & ASTK1 & EK1 & DK1 & OWN1 & DSH1).
  destruct RP1 as (PA1 & _).
  pose proof PA1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PVEC & _).
  destruct PVEC as (VC0 & VC8 & VC16 & Hk & Hlen & Hal & DB & CB & AN & EL).
  rewrite ES in Hlen, CB. rewrite length_app in Hlen, CB. cbn [length] in Hlen, CB. rewrite Nat2Z.inj_add in Hlen, CB. cbn [Z.of_nat Pos.of_succ_nat] in Hlen, CB.
  change PNM.BSZ with 40 in *.
  set (sb1 := PNM.b_sb s1) in *. set (sk1 := PNM.b_sk s1) in *.
  assert (VINL : In (sb1, 40 * 2 ^ sk1) (PNM.bparser_own s1 ++ LBX)) by (apply in_or_app; left; exact VIN).
  set (T := sb1 + 40 * Z.of_nat (length pre)) in *.
  assert (TAL : T mod 8 = 0).
  { unfold T. replace (sb1 + 40 * Z.of_nat (length pre)) with (sb1 + (Z.of_nat (length pre) * 5) * 8) by (clear; lia). rewrite Z.mod_add by lia. apply PMKA.mod16_8'. exact Hal. }
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ _ LK1 cr1 Aw1 M1 model1 HH1) as VP; cbv zeta in VP; destruct VP as (_ & _ & _ & VFS & VB & _).
  assert (TV : L5A.avis (ahid Aw1 model1) T 40) by (apply (VB sb1 (40 * 2 ^ sk1) T 40 VINL); clear - TB1 TB2; lia).
  destruct PT as (PT0 & PT8 & PT16 & PT24 & PT32). pose proof OKt as (_ & LEN & _).
  replace (T + 40 - 32) with (T + 8) by (clear; lia).
  split; [apply (proj2 (L5A.u64_at_vis _ M1 (T + 8) _ ltac:(eapply L5A.avis_sub; [exact TV| clear; lia| clear; lia]) ltac:(clear - TB4 TB1; lia) ltac:(clear - TB2 TB3 GSLO GSHI GSPT; lia))); exact PT8|].
  split; [| exact LEN].
  change 2147450880 with SB. replace 1 with (8 / 8) by reflexivity.
  apply (PMKA.blk_shadow_vis L ar C HI LYa HIok _ _ LK1 cr1 Aw1 M1 model1 sb1 (40 * 2 ^ sk1) (T + 8) 8 HH1 VINL); [clear - TB1 TB2; lia| clear - TB1 TB2; lia| | clear; lia| reflexivity|].
  - replace (T + 8) with (T + 1 * 8) by (clear; lia). rewrite Z_mod_plus_full. exact TAL.
  - intros a Ha. apply CB. clear - Ha TB1 TB2 Hlen; unfold T in *; lia.
Qed.

(* [comment removed for export] *)
Lemma ed_call_shrink K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1
      (fx1 fx2 : FPState) R1 R2 (pc1 ra : Z) (M2v : mem) l c top :
  PNSAX.ann_shrink_spec RSEGS PMA.AD L ar HI 0xab89c ->
  ed_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  ed_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  ed_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
  PNRA.binv s1 -> PNM.b_stk s1 = l ++ [c; top] ->
  msteps RSEGS (st fx1 R1 pc1 (mrestrict (ahid Aw1 model1) M1)) (st fx2 R2 0xab89c M2v) ->
  mem_grows (mrestrict (ahid Aw1 model1) M1) M2v ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (fb + 864 <= a < fb + 872) -> ~ (sp - 176 <= a < sp - 176 + 16) -> M2v (Z_to_bv 64 a) = mrestrict (ahid Aw1 model1) M1 (Z_to_bv 64 a)) ->
  L5.u64_at RSEGS M2v (fb + 864) (PNM.b_sb s1 + 40 * (Z.of_nat (length l) + 1)) ->
  getr R2 (reg 1) = Z_to_bv 64 ra -> L5.ra_ok ra -> getr R2 (reg 2) = Z_to_bv 64 (sp - 160) ->
  getr R2 (reg 3) = Z_to_bv 64 (pa_gp PMA.AD) -> getr R2 (reg 4) = Z_to_bv 64 (hl_tp L) ->
  getr R2 (reg 10) = Z_to_bv 64 (fb + 856) -> getr R2 (reg 11) = Z_to_bv 64 (Z.of_nat (length l) + 2) ->
  (forall (fx4 : FPState) R4 (M4 : mem) model4 LK4 Aw4,
      regs_preserved R2 R4 ->
      ed_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M4 model4 LK4 Aw4 (PNBO.set_stk s1 (l ++ [c])) sm1 ax1 cr1 ->
      (forall a, sp - 160 <= a < sp - 104 -> M4 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
      (forall v c0, PMSPA.ec_at RSEGS M1 (fb + 1024) v c0 -> PMSPA.ec_at RSEGS M4 (fb + 1024) v c0) ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx4 R4 ra M4 model4) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 pc1 M1 model1) K.
Proof.
  intros ASH CTX G LM INV1 ES MS MG FRZ E9 X1 RAok X2 X3 X4 X10 X11 KR.
  pose proof CTX as (Hw & HH & AM & K0 & ENT & FRM & FRS & FOK & SP32 & ARGS & RPRE & INCS & INV & EC0 & HE & UNR & CRED & KONT).
  destruct ENT as (Rra & RAok0 & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 3) with 18432 in *. change (18432 / 8) with 2304 in STKSH.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof FOK as ((rs & Hfb) & Fal).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _).
  pose proof (WF _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 5) with 2048 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL, FSIMG, F1, F2.
  rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in FSIMG.
  assert (FBI : 6905856 <= fb) by (clear - F1 FSAPP FSIMG; lia).
  pose proof LM as (BI & RP1 & STEP1 & AXL1 & CK1 & SHC1 & EBB1).
  pose proof G as G'. unfold ed_frame in G'.
  destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 1) with 128 in *. change (128 / 8) with 16 in *.
  pose proof BI as (HH1 & AM1 & MRT1 & INCA1 & INCL1 & ASTK1 & EK1 & DK1 & OWN1 & DSH1).
  pose proof (pstk176_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 CTX G LM) as (_ & D176o & _ & _).
  set (FF' := (F, 1, sp - 160 + 32) :: FF) in *.
  assert (FOK' : PNRA.frame_okB FF' fb). { split; [exists rs; right; exact Hfb| exact Fal]. }
  pose proof RP1 as (PA1 & IA1 & VIS1 & VREF1 & OACC1 & BASE1 & ERR1 & GR1).
  change (PNRA.o_p PMA.AD fb) with (fb + 464) in PA1, IA1, VIS1, VREF1, OACC1. change (PNRA.o_is PMA.AD fb) with (fb + 96) in PA1, IA1. change (PNRA.o_v PMA.AD fb) with (fb + 432) in VIS1, VREF1.
  change (PNM.PSIZE + 8) with 424 in OACC1.
  pose proof (PNAPAR.op_visB L ar C HI LY HIok _ FF' LK1 cr1 Aw1 M1 model1 fb _ s1 HH1 FOK' PA1 OACC1) as ((O1 & O8 & ONSH) & Zop & OWR & OCE & OVIS & AOP).
  set (op := fb + 464) in *. set (ois := fb + 96) in *.
  replace (fb + 864) with (op + 400) in E9 by (unfold op; clear; lia). replace (fb + 856) with (op + 392) in X10 by (unfold op; clear; lia).
  set (WR := PNRA.W_brun PMA.AD PMA.AN fb) in *.
  assert (WAPPR : PMKA.wapp WR).
  { unfold WR, PNRA.W_brun, PGS.W_srcfG, PNST.berr_W, PNST.cat_W, PNST.dec_W, PNRA.o_src, PNRA.o_is, PNRA.o_bb, PNRA.o_nb, PNRA.o_tb, PNRA.o_stk, PNRA.o_ec, PNRA.o_p, PMSP.o_p, PMSP.o_is, PMSP.o_ec.
    cbn [app pa_off_p pa_off_is pa_off_ec pa_errcat_guard pa_atexit PMA.AD ADDR_A PMA.AN NADDR_A PNL.pn_inf_guard PNL.pn_nan_guard PNL.pn_inf_obj PNL.pn_nan_obj].
    unfold PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK.
    pose proof FSAPP as (FA0 & FA1 & FA2). unfold BIGSHADOW_LO, BIGSHADOW_HI in FA1.
    repeat apply PMKA.wapp_cons; [..| apply PMKA.wapp_nil]; cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct FA1 as [FA1|FA1]; clear - FA0 FA1 FA2 F1 F2; lia. }
  pose proof FSAPP as (FA0 & FA1 & FA2). unfold BIGSHADOW_LO, BIGSHADOW_HI in FA1.
  pose proof GFR as (GF1 & GF2 & _).
  assert (DF1 : 0 <= F / 8) by (apply Z.div_pos; clear - GF1; lia).
  assert (DF2 : F / 8 <= 17592186044400) by (apply Z.div_le_upper_bound; clear - GF2; lia).
  assert (R4a : 0 <= F / 8 + 2147450880) by (clear - DF1; lia).
  assert (R4b : F / 8 + 2147450880 + 1 <= 2 ^ 64) by (clear - DF2; lia).
  (* [comment removed for export] *)
  set (b := PNM.b_sb s1) in *. set (k := PNM.b_sk s1) in *. set (n := Z.of_nat (length l)) in *.
  pose proof PA1 as (_ & Dop & _ & _ & _ & _ & _ & _ & SRC1 & _ & _ & BB1 & NB1 & TB1 & PVEC & _).
  destruct PVEC as (VC0 & VC8 & VC16 & Hk & Hlen & Hal & DB & CB & AN & EL). fold b k in VC0, VC8, VC16, Hk, Hlen, Hal, DB, CB, AN, EL.
  rewrite ES in Hlen, VC8, CB, AN, EL. rewrite length_app in Hlen, VC8, CB, AN, EL. cbn [length] in Hlen, VC8, CB, AN, EL.
  replace (Z.of_nat (length l + 2)) with (n + 2) in Hlen, VC8, CB, AN by (unfold n; clear; lia).
  change PNM.BSZ with 40 in *. change PNM.OFF_STK with 392 in *.
  assert (Hn : 0 <= n) by (unfold n; clear; lia).
  pose proof (PM.pow2_pos k ltac:(clear - Hk; lia)) as P2K.
  assert (VIN : In (b, 40 * 2 ^ k) (PNM.bparser_own s1)) by (exact (PNBOA.PNM_own_stk s1)).
  assert (VINL : In (b, 40 * 2 ^ k) (PNM.bparser_own s1 ++ LBX)) by (apply in_or_app; left; exact VIN).
  pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH1) as FRB1. pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH1) as BRB1.
  destruct (BRB1 _ VINL) as (BB0 & BB47). cbn [fst snd] in BB0, BB47.
  assert (AOP' : PMSPA.aobjA FF' op 416) by (apply PMAUAR.aobjA_push; apply (PNAPAR.aobj_fbB FF fb op 416 FOK); unfold op; clear; lia).
  pose proof (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ b (40 * 2 ^ k) op 416 HH1 VINL AOP') as BOA.
  set (H1 := ahid Aw1 model1) in *.
  set (W := fun a => fb + 864 <= a < fb + 872 \/ sp - 176 <= a < sp - 160).
  assert (FRZW : forall a, 0 <= a < 2 ^ 64 -> ~ W a -> M2v (Z_to_bv 64 a) = mrestrict H1 M1 (Z_to_bv 64 a)) by (intros a Ha Wa; apply FRZ; [exact Ha| intros X; apply Wa; unfold W; left; exact X| intros X; apply Wa; unfold W; right; clear - X; lia]).
  apply (L5SAR.apiece L ar C HI LYa HIok _ FF' LK1 cr1 Aw1 M1 model1 fx1 fx2 R1 pc1 R2 0xab89c M2v W K HH1 AM1 MS MG FRZW).
  { intros a Ha Wa. unfold W in Wa. destruct Wa as [Wa|Wa]; [split; [| clear - Wa FBI; lia]|].
    - apply (L5SAR.fframe_client L ar _ FF' 0 0 fb 5 rs); [right; exact Hfb| change (ff_bytes 5) with 2048; clear - Wa; lia].
    - split; [unfold aclientw, aclient_g; right; left; split; [clear - Wa GSLO GSHI GSPT; lia| intros Y; clear - Y; lia]| clear - Wa GSLO GSHI GSPT FBI; lia]. }
  intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MG3 FR3 VV3. change (mrestrict H1 M3 = M2v) in VIS3.
  (* [comment removed for export] *)
  assert (AG13 : forall a m, 0 <= a -> a + m <= 2 ^ 64 -> (a + m <= op + 400 \/ op + 408 <= a) -> (forall j, a <= j < a + m -> ~ (sp - 176 <= j < sp - 160)) -> L5C.agree_on M1 M3 a m).
  { intros a m A0 A1 X XS j Hj. apply FR3; [clear - Hj A0 A1; lia| unfold W; unfold op in X; intros [Wj|Wj]; [clear - Hj X Wj; lia| exact (XS j ltac:(clear - Hj; lia) Wj)]]. }
  assert (SH13 : forall a m, 0 <= a -> a + m <= 2 ^ 47 -> PMFA.agsh M1 M3 a m).
  { intros a m A0 A1 x Hx. unfold S, SB.
    pose proof (Z.div_pos x 8 ltac:(clear - Hx A0; lia) ltac:(clear; lia)) as D0. pose proof (Z.div_lt_upper_bound x 8 17592186044416 ltac:(clear; lia) ltac:(clear - Hx A1; lia)) as D1.
    apply FR3; [clear - D0 D1; lia| unfold W; destruct FA1 as [Y|Y]; clear - D0 D1 Y F1 F2 GSLO GSPT; lia]. }
  assert (E3 : L5.u64_at RSEGS M3 (op + 400) (b + 40 * (n + 1))).
  { apply (proj1 (L5A.u64_at_vis H1 M3 (op + 400) _ (OVIS (op + 400) 8 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - O1; lia) ltac:(clear - O1; lia))). rewrite VIS3. exact E9. }
  assert (BI3 : PMAUK.binv L ar HI M model LBX FF LK Aw sp 18432 (sp - 160) (own sp R) F 1 WR (PNM.bparser_own s1) M3 model3 LK1 cr1 Aw1).
  { unfold PMAUK.binv. split; [exact HH3|]. split; [exact AM3|]. split; [eapply L5LZ.model_rt_trans; [exact MRT1| exact MRT3]|]. split; [exact INCA1|]. split; [exact INCL1|].
    split; [eapply L5SAR.astk_grows; [exact ASTK1| exact MG3]|].
    split. { eapply L5SAR.ek_trans; [exact EK1|]. intros a (Ha & Hc & Ho). apply FR3; [exact Ha|]. unfold W. intros [Wa|Wa].
             - apply (Ho (PNRA.o_stk PMA.AD fb, 24)); [unfold WR, PNRA.W_brun, PGS.W_srcfG; cbn [app]; do 7 right; left; reflexivity|
                 unfold L5.in_rng, PNRA.o_stk, PNRA.o_p, PMSP.o_p, PNM.OFF_STK; cbn [fst snd pa_off_p PMA.AD PnLayoutA_b.ADDR_A]; clear - Wa; lia].
             - destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK cr Aw M _ sp _ a HH GSPT (L5SAR.aclient_appb L ar _ (PNM.bparser_own s) _ _ _ _ Hc)) as [Y|Y]; clear - Wa Y GSLO; lia. }
    split. { eapply L5SAR.dk_trans; [exact DK1|]. apply L5SAR.dk_grows. exact MG3. }
    split. { apply (GOWN M1 M3 OWN1). intros a Ha. pose proof (GOCR a Ha) as OC. apply FR3; [clear - OC GSPC GSLO; lia|]. unfold W. intros [Wa|Wa]; [revert Ha; unfold ocell; clear - Wa GSLO F2 FSCEIL; lia| clear - Wa OC; lia]. }
    eapply L5.defined_grows; [exact MG3| exact DSH1]. }
  pose proof BI3 as (_ & _ & _ & _ & _ & ASTK3 & EK3 & _).
  (* [comment removed for export] *)
  set (REST := PM.src_own (PNM.b_src s1) ++ PGV8.v8_own (PNM.b_bb s1) ++ PM.vs_own (PNM.b_nb s1) ++ PM.vs_own (PNM.b_tb s1)).
  set (LBc := REST ++ LBX).
  assert (PERM1 : Permutation (PNM.bparser_own s1 ++ LBX) (PNM.bvec_own b k ++ LBc)).
  { unfold LBc, REST, PNM.bparser_own, PNM.brest_own. fold b k. apply perm2. }
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH3) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND3 & NDF3 & _).
  assert (NDFF : base.NoDup (map ff_addr FF')) by (rewrite map_app in NDF3; apply stdpp.list_relations.list.NoDup_app in NDF3; exact (proj1 NDF3)).
  assert (HHp : ri_inv HI (PNM.bvec_own b k ++ LBc) FF' LK1 cr1 Aw1 M3 (vml_of model3)).
  { apply (HAJ.aior_perm _ _ _ _ _ HIok _ _ FF' FF' LK1 cr1 Aw1 M3 _ HH3).
    - intros x. split; [apply Permutation_in; exact PERM1| apply Permutation_in; apply Permutation_sym; exact PERM1].
    - apply (ln_nodup_perm (PNM.bparser_own s1 ++ LBX)); [exact PERM1| exact ND3].
    - intros f. split; intros Xf; exact Xf.
    - exact NDFF. }
  assert (INCc : forall x, In x LBc -> In x (PNM.bparser_own s1 ++ LBX)).
  { intros x Hx. apply (Permutation_in x (Permutation_sym PERM1)). apply in_or_app; right. exact Hx. }
  assert (BRBc : forall x, In x LBc -> 0 <= fst x /\ fst x + snd x <= 2 ^ 47) by (intros x Hx; exact (BRB1 x (INCc x Hx))).
  assert (V8m : (op + 392) mod 8 = 0) by (replace (op + 392) with (op + 49 * 8) by (clear; lia); rewrite Z.mod_add by (clear; lia); exact O8).
  unfold PNSAX.ann_shrink_spec in ASH.
  apply (ASH fx2 R2 M3 model3 K LBc FF' LK1 Aw1 cr1 (op + 392) b k (n + 2) (l ++ [c]) (sp - 160) ra HHp AM3 K0).
  { unfold PMSPA.entryA. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact X1|]. split; [exact RAok|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|].
    change (PMSPA.pm_scr 0) with 12288. change (12288 / 8) with 1536.
    split; [apply (L5SAR.astk_sub ar M3 M3 sp 18432 160 12288 ASTK3 (mem_grows_refl M3)); [clear; lia| clear; lia| clear; lia| replace (sp - 160) with (sp + (-10) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact A16]|].
    apply (PMKA.shadow_zero_sub M3 (sp - 18432) 2304); [| | clear; lia| clear; lia| clear; lia|].
    - apply PMKA.mod16_8'. replace (sp - 18432) with (sp + (-1152) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16.
    - apply PMKA.mod16_8'. replace (sp - 160 - 12288) with (sp + (-778) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16.
    - apply (PMKA.stksh_keepA L ar LBX FF sp 18432 WR M M3 EK3 WAPPR (sp - 18432) 2304); [clear - SLO SPT; lia| clear - SLO; lia| clear - SHI SPT; lia| | clear; lia| exact STKSH].
      apply PMKA.mod16_8'. replace (sp - 18432) with (sp + (-1152) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  { apply (PMAUAR.ffrsA_push FF sp (sp - 160) F 1 (sp - 160 + 32) FRS); clear; lia. }
  { rewrite L5K.rl10. exact X10. }
  { rewrite L5K.rl11. exact X11. }
  { apply PMAUAR.aobjA_push. apply (PNAPAR.aobj_fbB FF fb (op + 392) 24 FOK); unfold op; clear; lia. }
  { exact V8m. }
  { apply (PMFA.accA_agree M1 M3 (op + 392) 24); [apply SH13; clear - O1; lia|]. intros x Hx. apply OACC1. clear - Hx. lia. }
  { rewrite length_app. cbn [length]. fold n. clear - Hlen Hn. lia. }
  { apply (L5C.u64_at_agree RSEGS M1 M3); [apply AG13; [clear - O1; lia| clear - O1; lia| clear - O1; lia| intros j Hj; clear - Hj O1 D176o; lia]| clear - O1; lia| clear - O1; lia| exact VC0]. }
  { rewrite length_app. cbn [length]. change PNM.BSZ with 40. replace (Z.of_nat (length l + 1)) with (n + 1) by (unfold n; clear; lia). replace (op + 392 + 8) with (op + 400) by (clear; lia). exact E3. }
  { change PNM.BSZ with 40. apply (L5C.u64_at_agree RSEGS M1 M3); [apply AG13; [clear - O1; lia| clear - O1; lia| clear - O1; lia| intros j Hj; clear - Hj O1 D176o; lia]| clear - O1; lia| clear - O1; lia| exact VC16]. }
  { exact Hk. }
  { exact Hal. }
  { change PNM.BSZ with 40. exact (L5.defined_grows M1 M3 _ _ MG3 DB). }
  { change PNM.BSZ with 40. apply (PMFA.accA_agree M1 M3 b (40 * (n + 2))); [apply SH13; clear - BB0 BB47 Hlen Hn; lia| exact CB]. }
  { change PNM.BSZ with 40. apply (PNBOA.annA_agree M1 M3 b (40 * (n + 2)) (40 * 2 ^ k)); [apply PMKA.mod16_8'; exact Hal| clear - Hlen Hn; lia| | exact AN].
    apply SH13; [exact BB0|]. pose proof (PNBOA.gspan_ge (40 * 2 ^ k) ltac:(clear - P2K; lia)) as GS. unfold PNBOA.gspan in *.
    replace (40 * 2 ^ k + 7) with (7 + (5 * 2 ^ k) * 8) by (clear; lia). rewrite Z.div_add by (clear; lia). change (7 / 8) with 0. clear - BB47; lia. }
  { intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. change PNM.BSZ with 40.
    assert (Ei : nth i (l ++ [c]) PNM.bs_root = nth i (l ++ [c; top]) PNM.bs_root).
    { destruct (Nat.eq_dec i (length l)) as [->|NE]; [rewrite !nth_middle; reflexivity| rewrite !app_nth1 by (clear - Hi NE; lia); reflexivity]. }
    rewrite Ei. apply (PNMF.bstate_at_agree RSEGS M1 M3); [clear - BB0; lia| clear - BB47 Hi Hlen; unfold n in *; lia| | apply EL; clear - Hi; lia].
    apply AG13; [clear - BB0; lia| clear - BB47 Hi Hlen; unfold n in *; lia| destruct BOA as [Z0|Z0]; [left| right]; clear - Z0 Hi Hlen; unfold n in *; lia|]. intros j Hj Sj. assert (ACj : aclient L ar (PNM.bparser_own s1 ++ LBX) FF' (sp - 160) 16 j) by (left; exists (b, 40 * 2 ^ k); split; [exact VINL| cbn [fst snd]; clear - Hj Hi Hlen; unfold n in *; lia]). destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF' LK1 cr1 Aw1 M1 _ (sp - 160) 16 j HH1 GSPT ACj) as [Y|Y]; clear - Sj Y GSLO; lia. }
  intros fx4 R4 M4 model4 LK4 Aw4 RP4 BV4 ACV4 HP4 MRT4 INCL4 INCA4 AM4 HH4.
  change (PMSPA.pm_scr 0) with 12288 in HP4.
  set (s3 := PNBO.set_stk s1 (l ++ [c])).
  assert (EO3 : PNM.bparser_own s3 = PNM.bparser_own s1) by (unfold s3; destruct s1; reflexivity).
  assert (HH4' : ri_inv HI (PNM.bparser_own s3 ++ LBX) FF' LK4 cr1 Aw4 M4 (vml_of model4)).
  { rewrite EO3. pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH4) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND4 & NDF4 & _).
    apply (HAJ.aior_perm _ _ _ _ _ HIok _ _ FF' FF' LK4 cr1 Aw4 M4 _ HH4).
    - intros x. split; [apply Permutation_in; apply Permutation_sym; exact PERM1| apply Permutation_in; exact PERM1].
    - apply (ln_nodup_perm (PNM.bvec_own b k ++ LBc)); [apply Permutation_sym; exact PERM1| exact ND4].
    - intros f. split; intros Xf; exact Xf.
    - exact NDFF. }
  assert (BI4 : PMAUK.binv L ar HI M model LBX FF LK Aw sp 18432 (sp - 160) (own sp R) F 1 WR (PNM.bparser_own s3) M4 model4 LK4 cr1 Aw4).
  { apply (PMAUK.binv_callee L ar C HI HIok M model LBX FF LK Aw sp 18432 (sp - 160) (sp - 104) sp (ocell sp) (own sp R) F fl 1 LK2 M2 model2 cr (PNM.bparser_own s) G
             WR WR (PNM.bparser_own s1) REST (PNM.bparser_own s3) M3 model3 LK1 cr1 Aw1 M4 model4 LK4 cr1 Aw4 12288 [] BI3 HP4 HH4' AM4 MRT4 INCA4 INCL4);
      [clear; lia| clear; lia| intros rr a []| intros a _ _ rr []| intros a X; exact X]. }
  pose proof (proj1 HP4 : ek L ar LBc FF' (sp - 160) 12288 [] M3 M4) as EK34.
  set (Wc := [(op + 400, 8)]).
  assert (EK14 : ek L ar LBc FF' (sp - 160) 12288 Wc M1 M4).
  { apply (L5SAR.ek_trans L ar LBc FF' (sp - 160) 12288 Wc M1 M3 M4).
    - apply (L5SAR.ek_piece L ar LBc FF' (sp - 160) 12288 Wc M1 M3 W FR3). intros a Ha Hc Ho Wa. unfold W in Wa. destruct Wa as [Wa|Wa]; [apply (Ho (op + 400, 8)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; unfold op; clear - Wa; lia]| destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF' LK1 cr1 Aw1 M3 _ (sp - 160) _ a HHp GSPT (L5SAR.aclient_appb L ar _ (PNM.bvec_own b k) _ _ _ _ Hc)) as [Y|Y]; clear - Wa Y GSLO; lia].
    - apply (L5SAR.ek_W L ar LBc FF' (sp - 160) 12288 Wc [] M3 M4 EK34). intros a _ rr []. }
  assert (WAPPc : PMKA.wapp Wc).
  { apply PMKA.wapp_cons; [| apply PMKA.wapp_nil]. cbn [fst snd]. unfold BIGSHADOW_LO, BIGSHADOW_HI, op. destruct FA1 as [Y|Y]; clear - Y F1 F2; lia. }
  assert (OUTc : forall a m, (a + m <= op + 400 \/ op + 408 <= a) -> forall i, a <= i < a + m -> L5.outside Wc i).
  { intros a m Xo i Hi rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - Hi Hr Xo. lia. }
  assert (OUTBc : forall q m, In (q, m) LBc -> forall i, q <= i < q + m -> L5.outside Wc i).
  { intros q m Hq i Hi rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr.
    destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q m op 416 HH1 (INCc _ Hq) AOP') as [Z0|Z0]; clear - Hi Hr Z0; lia. }
  assert (PA4 : PNM.bparser_at RSEGS PMA.AD PMSPA.accA PMSPA.annA (pa_vp_parser PMA.AD) M4 op ois s3).
  { apply (bparser_set_stkS M1 M4 (pa_vp_parser PMA.AD) op ois s1 (l ++ [c]) ltac:(clear - O1; lia) ltac:(clear - O1; lia)); [| | | | exact BV4| exact PA1].
    - intros i Hi Hn'. destruct (Z_lt_le_dec i (op + 400)) as [X|X].
      + refine (proj1 (PMKA.agA_obj L ar _ FF' (sp - 160) 12288 _ M1 M4 EK14 WAPPc FRB1 op 400 _ _) i _); [| apply OUTc; clear; lia| clear - Hi X; lia].
        apply PMAUAR.aobjA_push. apply (PNAPAR.aobj_fbB FF fb op 400 FOK); unfold op; clear; lia.
      + refine (proj1 (PMKA.agA_obj L ar _ FF' (sp - 160) 12288 _ M1 M4 EK14 WAPPc FRB1 (op + 408) 8 _ _) i _); [| apply OUTc; clear; lia| clear - Hi X Hn'; lia].
        apply PMAUAR.aobjA_push. apply (PNAPAR.aobj_fbB FF fb (op + 408) 8 FOK); unfold op; clear; lia.
    - intros i Hi. destruct HP4 as (_ & _ & DK4).
      apply DK4; [clear - Hi O1; lia| apply (L5SAR.fframe_client L ar _ FF' (sp - 160) 12288 fb 5 rs); [right; exact Hfb| change (ff_bytes 5) with 2048; unfold op in Hi; clear - Hi; lia]|].
      apply MG3. replace i with (op + (i - op)) by (clear; lia). apply Dop. unfold PNM.PSIZE. clear - Hi; lia.
    - intros i Hi. refine (PMKA.agsh_obj L ar _ FF' (sp - 160) 12288 _ M1 M4 EK14 WAPPc FRB1 op 416 AOP' i Hi).
    - intros q m Hq. assert (HqL : In (q, m) LBc) by (apply in_or_app; left; exact Hq). destruct (BRBc _ HqL) as (B0 & B1). cbn [fst snd] in B0, B1.
      split; [exact B0|]. split; [clear - B1; lia|]. apply (PMKA.agA_blk L ar _ FF' (sp - 160) 12288 _ M1 M4 EK14 WAPPc BRBc q m HqL). apply OUTBc. exact HqL. }
  assert (IA4 : PM.iss_at RSEGS PMA.AD PMSPA.accA M4 ois str sm1).
  { apply (PMKA.iss_keepA RSEGS PMA.AD L ar _ FF' (sp - 160) 12288 _ M1 M4 EK14 WAPPc FRB1 BRBc ois str sm1); [| | | | exact IA1].
    - apply PMAUAR.aobjA_push. apply (PNAPAR.aobj_fbB FF fb ois 272 FOK); unfold ois; clear; lia.
    - apply incl_appr. exact INCS.
    - apply OUTc. unfold ois, op; clear; lia.
    - intros c0 n0 p0 E0. unfold PMKA.blk_out. apply OUTBc. apply in_or_app; right. apply INCS. rewrite E0. left; reflexivity. }
  assert (BASE4 : PMSTA.base_okA RSEGS PMA.AD M4).
  { apply (PMASK.base_keep L ar C LY _ FF' (sp - 160) 12288 _ M1 M4 EK14); [| exact BASE1]. intros a Ha rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. unfold op in Hr. clear - Ha Hr FBI; lia. }
  assert (ERR4 : PNSTA.berr_okA RSEGS PMA.AD PMA.AAD PMA.AN M4 ax1).
  { apply (berr_keep _ FF' (sp - 160) 12288 _ M1 M4 ax1 EK14); [| exact ERR1]. intros a Ha rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. unfold op in Hr. clear - Ha Hr FBI; lia. }
  assert (PRE4 : PNRA.brun_pre RSEGS PMA.AD PMA.AN PMA.AAD M4 fb s3 str sm1 ax1).
  { apply (pre_after_call _ FF' (sp - 160) 12288 _ M1 M4 fb s1 s3 str sm1 sm1 ax1 ax1 FRB1 EK14 WAPPc FOK'); [| exact RP1| exact PA4| exact IA4| unfold s3; exact GR1| exact BASE4| exact ERR4].
    intros i Hi. apply (OUTc i 1); [unfold op; clear - Hi; lia| clear; lia]. }
  apply (KR fx4 R4 M4 model4 LK4 Aw4 RP4).
  - fold s3. split; [exact BI4|]. split; [exact PRE4|].
    split; [unfold s3; cbn [PNBO.set_stk PNM.b_src]; exact STEP1|]. split; [exact AXL1|].
    split; [unfold s3, PNRA.pot_bparser; cbn [PNBO.set_stk PNM.b_sk PNM.b_tb PNM.b_tg PNM.b_nb PNM.b_ng PNM.b_bb PNM.b_bg]; exact CK1|].
    split; [| unfold s3; cbn [PNBO.set_stk PNM.b_bb]; exact EBB1].
    apply (L5C.u8_at_agree RSEGS M1 M4); [| exact R4a| exact R4b| exact SHC1].
    intros j Hj. apply EK14. split; [clear - Hj R4a R4b; lia|]. split.
    + apply (L5SAR.fframe_shadow_client L ar _ FF' (sp - 160) 12288 F 1 (sp - 160 + 32)); [left; reflexivity|]. change (ff_bytes 1) with 128.
      unfold in_shadow_of, S. rewrite (proj1 (proj2 GF8)). unfold SB. clear - Hj; lia.
    + intros rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. unfold op in Hr. destruct FA1 as [Y|Y]; clear - Hj Hr Y F1 F2 DF1 DF2; lia.
  - intros a Ha. apply EK14. split; [clear - Ha GSLO GSHI GSPT; lia|]. split.
    + apply (L5SAR.stack_client L ar _ FF' (sp - 160) 12288 a); clear - Ha GSLO GSHI GSPT; lia.
    + intros rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. unfold op in Hr. clear - Ha Hr GSLO F2 FSCEIL; lia.
  - intros v0 c0 E0. apply (PMKA.ec_keepA RSEGS L ar _ FF' (sp - 160) 12288 Wc M1 M4 EK14 WAPPc FRB1 (fb + 1024) v0 c0); [| | exact E0].
    + apply PMAUAR.aobjA_push. apply (PNAPAR.aobj_fbB FF fb (fb + 1024) 16 FOK); clear; lia.
    + apply OUTc. unfold op; clear; lia.
Qed.


End WithHeap.
End PNAEAK.
