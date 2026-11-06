(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_bson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx IcptIfaceA
     L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsA L5CoreA L5StepAR PmLayout PnLayoutA PmModel PmModelFacts PmStatics PmStaticsA PmSpecs PmParSpecs PmSpecsA PmSpecsAX PnSpecsAa
     PmModelFactsA PnStepA PmStep PmParStep PnASrcKit PnASrcReadK PnASrcRead1 PnASrcReadP Ba0_code_raf314_af318 PgSrc PgSrcA PgSrcKitA PnRunA.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := first [ L5FastLia.plia | Lia.lia ].

Module PGSRDA.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).
Ltac vis64 OAV := lazymatch goal with |- L5.u64_at ?sg (mrestrict ?H ?M0) ?a ?v =>
  apply (proj2 (L5A.u64_at_vis H M0 a v ltac:(apply OAV; lia) ltac:(lia) ltac:(lia))); assumption end.
Ltac vis32 OAV := lazymatch goal with |- L5.u32_at ?sg (mrestrict ?H ?M0) ?a ?v =>
  apply (proj2 (L5A.u32_at_vis H M0 a v ltac:(apply OAV; lia) ltac:(lia) ltac:(lia))); assumption end.
Ltac pdestr PP := repeat match type of PP with _ /\ _ => let H := fresh "Q" in destruct PP as (H & PP) end.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.

Theorem src_read_okG : PGSA.fill_buffer_specG RSEGS PMA.AD L ar HI PNRA.FCB -> PMA.xsgetn_spec L ar HI -> PGSA.src_read_specG RSEGS PMA.AD L ar HI PNRA.FCB.
Proof.
  intros FB XS. unfold PGSA.src_read_specG, PGSA.src_specG.
  intros O OK fx R M model K OB LBX FF LK Aw cr sp r src str sm Wextra HH AM K0 ENT FRM FRS OFR A10 ARGS WX PA IA BASE INCS KONT.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH).
  destruct ARGS as (p & k & A11 & A12 & Hk & DST). destruct WX as (p' & k' & A11' & A12' & Hp' & Hk' & ->).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10.
  rewrite L5SAR.r11 in A11, A11'. rewrite L5SAR.r12 in A12, A12'. unfold PM.CHUNK in Hk.
  change (PMSPA.pm_scr 4) with 20480 in *. pose proof RAok as (Hr1 & Hr2).
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof (PGSA.oo_lay _ _ _ _ _ _ OK) as (LY1 & LY2 & LY3 & LY4 & LY5 & O8 & I8 & LY6 & LYD).
  pose proof (PGSA.oo_src _ _ _ _ _ _ OK M src OB PA) as (PSRC & PNI & SDEF0).
  set (os := PGS.ow_os O) in *. set (ois := PGS.ow_ois O) in *. set (lo := PGS.ow_lo O) in *. set (hi := PGS.ow_hi O) in *.
  set (LB := PM.src_own src ++ OB ++ LBX) in *.
  assert (AO : PMSPA.aobjA FF os 296) by (apply (PGSKA.aobjA_sub FF lo hi); [exact OFR| exact LY1| exact LY2]).
  assert (AOI : PMSPA.aobjA FF ois 272) by (apply (PGSKA.aobjA_sub FF lo hi); [exact OFR| exact LY3| exact LY4]).
  pose proof (PGSKA.src_visG L ar C HI LY HIok LB FF LK cr Aw M model os _ _ src sp 20480 HH AO O8 PSRC PNI ASTK)
    as ((O1 & _ & OBIG) & OZ & OW & OCE & OAV & _ & OFS1 & OFS2).
  pose proof (PGSKA.iss_visG L ar C HI LY HIok LB FF LK cr Aw M model ois str sm sp 20480 HH AOI I8 IA ASTK)
    as ((I1 & _ & IBIG) & IZ & IW & ICE & IAV & _).
  pose proof (PMASK.mach_vis L ar C HI LY HIok LB FF LK cr Aw M model HH BASE) as (V0 & V1 & V2).
  pose proof (PMASK.stk_vis L ar C HI LY HIok LB FF LK cr Aw M model sp 20480 80 HH ASTK ltac:(lia)) as (SL80 & SH80 & V3).
  pose proof (PMASK.img_shz_vis L ar C HI LY IL ICok ILY LB FF LK cr Aw M model 0x132c30 1 HH ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia)) as VT1.
  pose proof (PMASK.img_shz_vis L ar C HI LY IL ICok ILY LB FF LK cr Aw M model 0x132b98 1 HH ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia)) as VT2.
  cbn in VT1, VT2.
  pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB. pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB.
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _ & _ & _ & _ & _ & TOP & _).
  pose proof (PMASK.fs_above_img L ar C HI LY HIok _ _ _ _ _ _ _ HH) as FSI.
  pose proof OFR as (ff & Hff & FLO & FHI). destruct (WF _ Hff) as (FB1 & FB2 & _).
  destruct src as [qc de rem]. destruct sm as [g eg sst].
  cbn [PM.sr_qc PM.sr_de PM.sr_rem PM.sm_g PM.sm_eg PM.sm_st] in *.
  pose proof PSRC as PSRC0.
  destruct PSRC as (S240 & S248 & SD256 & S264 & S272 & S280 & S288 & G1 & G2 & G3 & G16 & DCH & ACH & ACC240).
  cbn [PM.sr_qc PM.sr_de PM.sr_rem] in *. unfold PM.CHUNK in *.
  pose proof IA as (H0i & _ & _ & H16i & _ & _ & _ & _ & _ & _ & _ & _ & IOSB & _ & _).
  destruct IOSB as (I0 & I32 & I36 & I40 & _ & _ & _ & _ & IST).
  cbn [PM.sm_g PM.sm_eg PM.sm_st pa_vp_iss pa_vp_strbuf pa_vp_iss_ios PMA.AD ADDR_A] in *.
  replace (ois + 120 + 32) with (ois + 152) in I32 by lia. replace (ois + 120 + 36) with (ois + 156) in I36 by lia.
  replace (ois + 120 + 40) with (ois + 160) in I40 by lia.
  assert (SOWN : incl (PM.vs_own str) LB) by (unfold LB; intros x Hx; apply in_or_app; right; apply in_or_app; right; exact (INCS x Hx)).
  assert (QIN : In (qc, 16384) LB) by (unfold LB, PM.src_own; cbn; left; reflexivity).
  assert (OBIN : forall B m, In (B, m) OB -> In (B, m) LB) by (intros B m Hin; unfold LB, PM.src_own; cbn; right; apply in_or_app; left; exact Hin).
  assert (ND : NoDup (map fst LB)) by exact (PMASK.lb_nodup L ar C HI HIok _ _ _ _ _ _ _ HH).
  destruct (WB _ QIN) as ((Q0 & QI & Q16 & _ & Q4 & QAPP) & _). cbn [fst snd] in Q0, QI, Q16, Q4, QAPP.
  rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in QI.
  unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in QAPP, FSAPP.
  set (MV := mrestrict (ahid Aw model) M) in *.
  assert (STb : forall c1 n1 q1, str = PM.VLong c1 n1 q1 -> In (q1, c1) LB).
  { intros c1 n1 q1 E. apply SOWN. rewrite E. cbn. left. reflexivity. }
  assert (STbX : forall c1 n1 q1, str = PM.VLong c1 n1 q1 -> In (q1, c1) LBX).
  { intros c1 n1 q1 E. apply INCS. rewrite E. cbn. left. reflexivity. }
  (* [comment removed for export] *)
  assert (DF : 0 <= p /\ p + k <= 2 ^ 47 /\ L5.defined M p k /\ aacc M p k /\ app_rng ar p k
     /\ (forall a, p <= a < p + k -> in_block LB a \/ in_fframe FF a)
     /\ (forall a, p <= a < p + k -> ~ (sp - 20480 <= a < sp) /\ ~ (ois <= a < ois + 272) /\ ~ (os <= a < os + 296)
           /\ ~ (qc <= a < qc + 16384) /\ (forall c1 n1 q1, str = PM.VLong c1 n1 q1 -> ~ (q1 <= a < q1 + c1))
           /\ ~ (65536 <= a < 6897664))
     /\ (p + k <= BIGSHADOW_LO \/ BIGSHADOW_HI <= p)
     /\ (k = 16384 -> PGS.in_blk OB p k)
     /\ (PMSPA.aobjA FF p k \/ exists q m, In (q, m) LB /\ q <= p /\ p + k <= q + m)
     /\ (p + k <= qc \/ qc + 16384 <= p)
     /\ (((p + k <= lo \/ hi <= p) /\ (forall B m, In (B, m) OB -> p + k <= B \/ B + m <= p)) \/ PGS.ow_win O M (PM.SRC qc de rem) OB p k)).
  { destruct FSAPP as (FSA0 & FSAs & FSA47). destruct QAPP as (QA0 & QAs & QA47).
    (* [comment removed for export] *)
    assert (OBJ : forall (APo : p + k <= os \/ os + 296 <= p) (APi : p + k <= ois \/ ois + 272 <= p),
      PMSPA.aobjA FF p k -> L5.defined M p k -> aacc M p k -> k < 16384 ->
      (((p + k <= lo \/ hi <= p) /\ (forall B m, In (B, m) OB -> p + k <= B \/ B + m <= p)) \/ PGS.ow_win O M (PM.SRC qc de rem) OB p k) ->
      0 <= p /\ p + k <= 2 ^ 47 /\ L5.defined M p k /\ aacc M p k /\ app_rng ar p k
     /\ (forall a, p <= a < p + k -> in_block LB a \/ in_fframe FF a)
     /\ (forall a, p <= a < p + k -> ~ (sp - 20480 <= a < sp) /\ ~ (ois <= a < ois + 272) /\ ~ (os <= a < os + 296)
           /\ ~ (qc <= a < qc + 16384) /\ (forall c1 n1 q1, str = PM.VLong c1 n1 q1 -> ~ (q1 <= a < q1 + c1))
           /\ ~ (65536 <= a < 6897664))
     /\ (p + k <= BIGSHADOW_LO \/ BIGSHADOW_HI <= p)
     /\ (k = 16384 -> PGS.in_blk OB p k)
     /\ (PMSPA.aobjA FF p k \/ exists q m, In (q, m) LB /\ q <= p /\ p + k <= q + m)
     /\ (p + k <= qc \/ qc + 16384 <= p)
     /\ (((p + k <= lo \/ hi <= p) /\ (forall B m, In (B, m) OB -> p + k <= B \/ B + m <= p)) \/ PGS.ow_win O M (PM.SRC qc de rem) OB p k)).
    { intros APo APi AOD DD AD Hk16 DWX.
      pose proof AOD as (f & Hf & X1 & X2). destruct (WF f Hf) as (Y1 & Y2 & _).
      pose proof (PMASK.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ qc 16384 p k HH QIN AOD) as APQ.
      split; [clear - X1 Y1 FSI; lia|]. split; [clear - X2 Y2 FSCEIL SLO SHI SPT; lia|]. split; [exact DD|]. split; [exact AD|].
      split; [apply (L5SAR.app_rng_fs L ar C HI HIok LB FF LK cr Aw M _ p k HH); clear - X1 X2 Y1 Y2; lia|].
      split; [intros a Ha; right; apply (PMASR1.in_fframe_of_aobjA FF p k a AOD Ha)|].
      split; [|split; [unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct FSAs as [Z|Z]; [left|right]; clear - Z X1 X2 Y1 Y2; lia|
               split; [intros E; exfalso; clear - E Hk16; lia| split; [left; exact AOD| split; [clear - APQ; Lia.lia| exact DWX]]]]].
      intros a Ha. split; [clear - Ha X2 Y2 FSCEIL SLO; lia|]. split; [clear - Ha APi; lia|]. split; [clear - Ha APo; lia|].
      split; [clear - Ha APQ; lia|]. split; [|clear - Ha X1 Y1 FSI; lia].
      intros c1 n1 q1 E; destruct (PMASK.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ q1 c1 p k HH (STb c1 n1 q1 E) AOD) as [Z|Z]; clear - Ha Z; lia. }
    destruct DST as [(AOD & Hk8 & DD & AD & APF)|DW].
    - (* [comment removed for export] *)
      apply OBJ; [clear - APF LY1 LY2; lia| clear - APF LY3 LY4; lia| exact AOD| exact DD| exact AD| clear - Hk8; lia|].
      left. split; [exact APF|]. intros B m Hin.
      destruct (PMASK.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ B m p k HH (OBIN B m Hin) AOD) as [Z|Z]; clear - Z; lia.
    - destruct (PGSA.oo_win _ _ _ _ _ _ OK M (PM.SRC qc de rem) OB p k PA DW) as (W0 & WD & [(B & m & BIN & WB1 & WB2)|(W1 & W2 & WL1 & WL2 & WL3 & WL4 & WL5)] & WACC).
      + (* [comment removed for export] *)
        pose proof (OBIN B m BIN) as TIN.
        destruct (WB _ TIN) as ((T0 & TI & _ & _ & T4 & TAPP) & _). cbn [fst snd] in T0, TI, T4, TAPP.
        rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in TI. unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in TAPP. destruct TAPP as (TA0 & TAs & TA47).
        assert (NQ : B <> qc).
        { intros E. apply (PMASK.fst_neq_appA [(qc, 16384)] (OB ++ LBX) qc 16384 B m); [exact ND| left; reflexivity| apply in_or_app; left; exact BIN| symmetry; exact E]. }
        pose proof (PMASK.blk_apart L ar C HI HIok LB FF LK cr Aw M _ B m qc 16384 HH TIN QIN NQ) as APQ.
        pose proof (PMASK.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ B m os 296 HH TIN AO) as APP.
        pose proof (PMASK.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ B m ois 272 HH TIN AOI) as API.
        split; [clear - WB1 T0; lia|]. split; [clear - WB2 T4 SLO SHI SPT; lia|]. split; [exact WD|]. split; [exact WACC|].
        split; [apply (L5SAR.app_rng_block L ar C HI HIok LB FF LK cr Aw M _ B m p k HH TIN); clear - WB1 WB2; lia|].
        split; [intros a Ha; left; apply (PMASR1.in_block_of LB B m a TIN); clear - Ha WB1 WB2; lia|].
        split; [|split; [unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct TAs as [Z|Z]; [left|right]; clear - Z WB1 WB2; lia
                        | split; [intros _; exists B, m; split; [exact BIN|]; split; [exact WB1| exact WB2]|
                          split; [right; exists B, m; split; [exact TIN|]; split; [exact WB1| exact WB2]| split; [clear - APQ WB1 WB2; Lia.lia| right; exact DW]]]]].
        intros a Ha. split; [clear - Ha WB1 WB2 T4 SLO; lia|]. split; [clear - Ha WB1 WB2 API; lia|]. split; [clear - Ha WB1 WB2 APP; lia|].
        split; [clear - Ha WB1 WB2 APQ; lia|]. split; [|clear - Ha WB1 WB2 TI T0; lia].
        intros c1 n1 q1 E.
        assert (NS : B <> q1) by (apply (PMASK.fst_neq_appA ((qc, 16384) :: OB) LBX B m q1 c1); [exact ND| right; exact BIN| exact (STbX c1 n1 q1 E)]).
        destruct (PMASK.blk_apart L ar C HI HIok LB FF LK cr Aw M _ B m q1 c1 HH TIN (STb c1 n1 q1 E) NS) as [Z|Z]; clear - Ha WB1 WB2 Z; lia.
      + (* [comment removed for export] *)
        unfold PM.CHUNK in WL3.
        apply OBJ; [exact WL4| exact WL5| apply (PGSKA.aobjA_sub FF lo hi p k OFR WL1 WL2)| exact WD| exact WACC| exact WL3| right; exact DW]. }
  destruct DF as (DP0 & DP1 & DDP & DAP & DAPP & DCL & DX & DSH & D16K & DLOC & DQA & DWX).
  assert (pk : p' = p /\ k' = k).
  { rewrite A11 in A11'. rewrite A12 in A12'. apply (f_equal bv_unsigned) in A11', A12'.
    rewrite !L5.unsigned_lit in A11', A12' by (clear - Hp' Hk' DP0 DP1 Hk; lia). split; congruence. }
  destruct pk as (-> & ->). clear A11' A12'.
  destruct FSAPP as (FSA0 & FSAs & FSA47). destruct QAPP as (QA0 & QAs & QA47).
  assert (APQO : forall o n, PMSPA.aobjA FF o n -> qc + 16384 <= o \/ o + n <= qc).
  { intros o n AOo. exact (PMASK.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ qc 16384 o n HH QIN AOo). }
  (* [comment removed for export] *)
  set (WA := PGS.W_srcG os ois (PM.SRC qc de rem) ++ [(p, k)]).
  assert (OUTWA : forall i, ~ (os + 256 <= i < os + 296) -> ~ (ois + 40 <= i < ois + 48) -> ~ (ois + 152 <= i < ois + 156) ->
                  ~ (qc <= i < qc + 16384) -> ~ (p <= i < p + k) -> L5.outside WA i).
  { intros i N1 N2 N3 N4 N5 r0 Hr. unfold WA, PGS.W_srcG, PGS.W_srcfG in Hr. cbn [PM.sr_qc app] in Hr. unfold L5.in_rng.
    destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd]; unfold PM.CHUNK; clear - N1 N2 N3 N4 N5; lia. }
  assert (WAPP : PMKA.wapp WA).
  { unfold WA, PGS.W_srcG, PGS.W_srcfG. cbn [PM.sr_qc app]. unfold BIGSHADOW_LO, BIGSHADOW_HI in OBIG, IBIG, DSH.
    apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; clear - OBIG; Lia.lia|].
    apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; clear - IBIG; Lia.lia|].
    apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; clear - IBIG; Lia.lia|].
    apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI, PM.CHUNK; clear - QAs; Lia.lia|].
    apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; clear - DSH; Lia.lia| apply PMKA.wapp_nil]. }
  assert (OUTIMG : forall a, 65536 <= a < 6897664 -> L5.outside WA a).
  { intros a Ha. apply OUTWA; [clear - Ha O1; lia| clear - Ha I1; lia| clear - Ha I1; lia| clear - Ha QI; lia|].
    intros Y. destruct (DX a Y) as (_ & _ & _ & _ & _ & X6). apply X6. exact Ha. }
  (* [comment removed for export] *)
  assert (OWA : Forall (fun b => fst b + snd b <= lo \/ hi <= fst b) (PM.src_own (PM.SRC qc de rem) ++ OB)).
  { apply Forall_forall. intros [B m] Hin. cbn [fst snd].
    assert (HB : In (B, m) LB) by (unfold LB; rewrite app_assoc; apply in_or_app; left; exact Hin).
    destruct (PMASK.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ B m lo (hi - lo) HH HB OFR) as [X|X]; [left; exact X| right; clear - X; lia]. }
  assert (OWB : forall b, In b OB -> fst b + snd b <= PM.sr_qc (PM.SRC qc de rem) \/ PM.sr_qc (PM.SRC qc de rem) + PM.CHUNK <= fst b).
  { intros [B m] Hin. cbn [fst snd PM.sr_qc]. unfold PM.CHUNK.
    assert (NE : B <> qc).
    { intros E. apply (PMASK.fst_neq_appA [(qc, 16384)] (OB ++ LBX) qc 16384 B m); [exact ND| left; reflexivity| apply in_or_app; left; exact Hin| symmetry; exact E]. }
    destruct (PMASK.blk_apart L ar C HI HIok LB FF LK cr Aw M _ B m qc 16384 HH (OBIN B m Hin) QIN NE) as [X|X]; clear - X; lia. }
  assert (OWC : Forall (fun r => ((fst r + snd r <= lo \/ hi <= fst r) /\ (forall B m, In (B, m) OB -> fst r + snd r <= B \/ B + m <= fst r) /\ app_mem (fst r) (snd r))
                              \/ PGS.ow_win O M (PM.SRC qc de rem) OB (fst r) (snd r)) [(p, k)]).
  { constructor; [| constructor]. cbn [fst snd]. destruct DWX as [(DW1 & DW2)|DW]; [left| right; exact DW].
    split; [exact DW1|]. split; [exact DW2|]. unfold app_mem. split; [exact DP0|]. split; [exact DSH| exact DP1]. }
  assert (OWU : forall (M3 : word -> option byte) (de' rem' : Z),
      L5SAR.ek L ar LB FF sp 20480 WA M M3 -> L5SAR.dk L ar LB FF sp 20480 M M3 -> L5CA.astk ar M3 sp 20480 ->
      L5.u64_at RSEGS M3 (os + 264) qc -> L5.u64_at RSEGS M3 (os + 272) 16384 ->
      L5.u64_at RSEGS M3 (os + 280) de' -> L5.u64_at RSEGS M3 (os + 288) rem' ->
      qc <= de' -> 0 <= rem' -> de' + rem' <= qc + 16384 ->
      PGS.ow_at O M3 (PM.SRC qc de' rem') OB).
  { intros M3 de' rem' EK DK ASTK3 C264 C272 C280 C288 Q1' Q2' Q3'.
    assert (OUTO : forall i, os <= i < os + 256 -> L5.outside WA i).
    { intros i Hi. apply OUTWA; [clear - Hi; lia| clear - Hi LYD; lia| clear - Hi LYD; lia| destruct (APQO os 296 AO) as [Z|Z]; clear - Hi Z; lia|].
      intros Y. destruct (DX i Y) as (_ & _ & X3 & _). apply X3. clear - Hi; lia. }
    apply (PGSA.oo_upd _ _ _ _ _ _ OK LBX sp 20480 [(p, k)] M M3 (PM.SRC qc de rem) (PM.SRC qc de' rem') OB FF LK Aw cr (vml_of model) OFR PA HH OWA OWB OWC).
    - apply (L5SAR.ahpres_of L ar LB FF sp 20480 WA M M3 EK); [pose proof ASTK3 as (_ & _ & _ & _ & DS3 & _); exact DS3| exact DK].
    - apply (PGSKA.src_fields_updG M M3 os ois (ois + 16) qc de rem de' rem' PSRC0); unfold PM.CHUNK.
      + clear - O1; lia.
      + clear - O1; lia.
      + apply (PMKA.agA_obj L ar LB FF sp 20480 WA M M3 EK WAPP FRB os 256); [apply (PGSKA.aobjA_sub FF lo hi); [exact OFR| clear - LY1; lia| clear - LY2; lia]| exact OUTO].
      + apply (PMKA.agsh_obj L ar LB FF sp 20480 WA M M3 EK WAPP FRB (os + 256) 40). apply (PGSKA.aobjA_sub FF lo hi); [exact OFR| clear - LY1; lia| clear - LY2; lia].
      + apply (PMASK.defined_dk L ar LB FF sp 20480 M M3 (os + 256) 8 DK); [| clear - O1; lia| clear - O1; lia| exact SD256].
        intros i Hi. apply PMASR1.cl_of_bf. right. apply (PMASR1.in_fframe_of_aobjA FF os 296 i AO). clear - Hi; lia.
      + apply (PMASK.agsh_blk L ar LB FF sp 20480 WA M M3 qc 16384 EK WAPP QIN); [clear - Q0; lia| clear - Q4 SLO SHI SPT; lia].
      + apply (PMASK.defined_dk L ar LB FF sp 20480 M M3 qc 16384 DK); [| clear - Q0; lia| clear - Q4 SLO SHI SPT; lia| exact DCH].
        intros i Hi. apply PMASR1.cl_of_bf. left. apply (PMASR1.in_block_of LB qc 16384 i QIN Hi).
      + exact C264. + exact C272. + exact C280. + exact C288. + exact Q1'. + exact Q2'. + exact Q3'.
    - reflexivity. }
  assert (FIN : forall (fx3 : FPState) (R3 : bvmap 5 word) (M3 : word -> option byte) (model3 : Model) (LK3 : list fframe) (Aw3 : list (Z * Z))
                       (de' rem' g' st' d : Z),
      getr R3 (reg 1) = Z_to_bv 64 r ->
      (forall x, In x L5SAR.cs_all -> getr R3 (reg x) = getr R (reg x)) ->
      getr R3 (reg 10) = Z_to_bv 64 d ->
      L5.u64_at RSEGS M3 (os + 264) qc -> L5.u64_at RSEGS M3 (os + 272) 16384 ->
      L5.u64_at RSEGS M3 (os + 280) de' -> L5.u64_at RSEGS M3 (os + 288) rem' ->
      qc <= de' -> 0 <= rem' -> de' + rem' <= qc + 16384 ->
      PM.iss_at RSEGS PMA.AD PMSPA.accA M3 ois str (PM.STRM g' eg st') ->
      g <= g' <= eg -> (sst = 2 -> st' = 2) ->
      0 <= d <= k -> (rem + (eg - g)) - (rem' + (eg - g')) = d ->
      (1 <= rem -> 1 <= d) -> (d = 0 -> rem' = 0 /\ st' = 2) ->
      L5.defined M3 p d ->
      L5SAR.ek L ar LB FF sp 20480 WA M M3 -> L5SAR.dk L ar LB FF sp 20480 M M3 -> L5CA.astk ar M3 sp 20480 ->
      ri_inv HI LB FF LK3 cr Aw3 M3 (vml_of model3) -> L5CA.amodel_ok Aw3 model3 -> model_rt model model3 -> incl LK3 LK -> incl Aw Aw3 ->
      srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx3 R3 0xade1c M3 model3) K).
  { intros fx3 R3 M3 model3 LK3 Aw3 de' rem' g' st' d E1 E2 E10 C264 C272 C280 C288 Q1' Q2' Q3' IA3 Hg Hst2 Hd Hcons HR1 HR0 DD3 EK DK ASTK3 HH3 AM3 MRT3 INC3 INCA3.
    unfold PMSPA.cfg, PMSP.cfg.
    apply (PMASK.ret_exit L ar C HI LY HIok fx3 R3 M3 model3 K LB FF LK3 cr Aw3 0xade1c r W_addcc HH3 AM3 F_addcc eq_refl D_addcc E1 ltac:(clear - Hr1; lia) Hr2).
    intros model4 MRT4 AM4 HH4.
    apply (KONT fx3 R3 M3 model4 LK3 Aw3 (PM.SRC qc de' rem') (PM.STRM g' eg st')).
    + apply L5SAR.preserved_by_index. exact E2.
    + apply OWU; assumption.
    + exact IA3.
    + unfold PMSP.src_step, PM.unread. cbn [PM.sr_qc PM.sr_rem PM.sm_eg PM.sm_g PM.sm_st]. split; [reflexivity|]. split; [reflexivity|].
      split; [clear - Hg; lia|]. split; [exact Hst2| clear - Hcons Hd; lia].
    + unfold PMPS.read_res, PMSP.consumed, PM.unread. cbn [PM.sr_rem PM.sm_eg PM.sm_g PM.sm_st]. exists p, k, d.
      rewrite L5SAR.r11, L5SAR.r12, L5K.rl10. split; [exact A11|]. split; [exact A12|]. split; [clear - DP0 DP1 Hk; lia|]. split; [unfold PM.CHUNK; clear - Hk; lia|].
      split; [exact E10|]. split; [exact Hd|]. split; [exact Hcons|]. split; [exact DD3|]. split; [exact HR1| exact HR0].
    + apply (L5SAR.ahpres_of L ar LB FF sp 20480 WA M M3 EK); [pose proof ASTK3 as (_ & _ & _ & _ & DS3 & _); exact DS3| exact DK].
    + eapply L5LZ.model_rt_trans; [exact MRT3| exact MRT4].
    + exact INC3.
    + exact INCA3.
    + exact AM4.
    + exact HH4. }
  assert (AGSHP : forall M0 M1 W, L5SAR.ek L ar LB FF sp 20480 W M0 M1 -> PMKA.wapp W -> PMFA.agsh M0 M1 p k).
  { intros M0 M1 W E WP. destruct DLOC as [AOD|(q & m & Hq & X1 & X2)].
    - exact (PMKA.agsh_obj L ar LB FF sp 20480 W M0 M1 E WP FRB p k AOD).
    - destruct (BRB _ Hq) as (Y1 & Y2). cbn [fst snd] in Y1, Y2.
      intros x Hx. apply (PMASK.agsh_blk L ar LB FF sp 20480 W M0 M1 q m E WP Hq ltac:(clear - Y1; lia) ltac:(clear - Y2; lia)). clear - Hx X1 X2; lia. }
  assert (CLP : forall a sp0 scr0, p <= a < p + k -> aclient L ar LB FF sp0 scr0 a) by (intros a sp0 scr0 Ha; apply PMASR1.cl_of_bf; exact (DCL a Ha)).
  assert (CLPw : forall a sp0 scr0, p <= a < p + k -> aclientw L ar LB FF sp0 scr0 a) by (intros a sp0 scr0 Ha; apply PMASR1.cl_of_bf; exact (DCL a Ha)).
  assert (CLQ : forall a sp0 scr0, qc <= a < qc + 16384 -> aclient L ar LB FF sp0 scr0 a).
  { intros a sp0 scr0 Ha. apply PMASR1.cl_of_bf. left. exact (PMASR1.in_block_of LB qc 16384 a QIN Ha). }
  pose proof (bv_unsigned_in_range 64 (getr R (reg 1))) as B1.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 8))) as B8. pose proof (bv_unsigned_in_range 64 (getr R (reg 9))) as B9.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 18))) as B18. pose proof (bv_unsigned_in_range 64 (getr R (reg 19))) as B19.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 20))) as B20. pose proof (bv_unsigned_in_range 64 (getr R (reg 21))) as B21.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 22))) as B22. pose proof (bv_unsigned_in_range 64 (getr R (reg 23))) as B23.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 24))) as B24.
  change (bv_modulus 64) with (2 ^ 64) in B1, B8, B9, B18, B19, B20, B21, B22, B23, B24.
  set (W1 := fun a => (sp - 80 <= a < sp - 80 + 80) \/ (os + 256 <= a < os + 256 + 40)).
  assert (W1ok : forall a, 0 <= a < 2 ^ 64 -> W1 a -> aclientw L ar LB FF 0 0 a /\ ~ 65536 <= a < 6897664).
  { intros a Ha Wa. split; [|unfold W1 in Wa; intros X; clear - Wa X O1 SL80 SPT; lia]. destruct Wa as [Wa|Wa].
    - unfold aclientw, aclient_g. right; left. split; [clear - Wa SL80 SH80; lia| intros X; clear - X; lia].
    - unfold aclientw, aclient_g. do 3 right. left. destruct AO as (f & Hf & X1 & X2). exists f. split; [exact Hf|]. split; [clear - Wa X1 X2; lia| intros X; clear - Wa X X1; lia]. }
  assert (EKW1 : forall M0 M1 LK0 Aw0 V0, ri_inv HI LB FF LK0 cr Aw0 M0 V0 -> (forall a, 0 <= a < 2 ^ 64 -> ~ W1 a -> M1 (Z_to_bv 64 a) = M0 (Z_to_bv 64 a)) ->
                 L5SAR.ek L ar LB FF sp 20480 [(os + 256, 40)] M0 M1).
  { intros M0 M1 LK0 Aw0 Vv HH0 FR. apply (L5SAR.ek_piece L ar LB FF sp 20480 [(os + 256, 40)] M0 M1 W1 FR). intros a Ha CL Oq [X|X].
    - destruct (L5SAR.aclient_cases L ar C HI LYa HIok LB FF LK0 cr Aw0 M0 _ sp 20480 a HH0 SPT CL) as [(Y1 & Y2)|Y]; [apply Y2; clear - X; lia| clear - X Y SL80; lia].
    - apply (Oq (os + 256, 40)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - X; lia]. }
  assert (EKWA : forall M0 M1, L5SAR.ek L ar LB FF sp 20480 [(os + 256, 40)] M0 M1 -> L5SAR.ek L ar LB FF sp 20480 WA M0 M1).
  { intros M0 M1 E. apply (L5SAR.ek_W L ar LB FF sp 20480 WA [(os + 256, 40)] M0 M1 E). intros a Oq r0 [<-|[]] X. apply (Oq (os + 256, 40)); [unfold WA, PGS.W_srcG, PGS.W_srcfG; cbn [PM.sr_qc app]; left; reflexivity| exact X]. }
  (* [comment removed for export] *)
  assert (CPART : forall (fx2 : FPState) (R2 : bvmap 5 word) (M2 : word -> option byte) (model2 : Model) (LK2 : list fframe) (Aw2 : list (Z * Z)) (len1 c g2 st2 : Z),
      getr R2 (reg 10) = Z_to_bv 64 c -> getr R2 (reg 2) = Z_to_bv 64 (sp - 80) -> getr R2 (reg 8) = Z_to_bv 64 len1 -> getr R2 (reg 9) = Z_to_bv 64 os ->
      getr R2 (reg 18) = Z_to_bv 64 (os + 288) -> getr R2 (reg 19) = Z_to_bv 64 p -> getr R2 (reg 20) = Z_to_bv 64 (os + 280) ->
      getr R2 (reg 21) = Z_to_bv 64 (k - len1) -> getr R2 (reg 22) = Z_to_bv 64 2147450880 ->
      getr R2 (reg 23) = Z_to_bv 64 ((os + 288) / 8 + 2147450880) -> getr R2 (reg 24) = Z_to_bv 64 ((os + 280) / 8 + 2147450880) ->
      (forall x, In x [3; 4; 25; 26; 27]%nat -> getr R2 (reg x) = getr R (reg x)) ->
      L5.u64_at RSEGS M2 (sp - 8) (bv_unsigned (getr R (reg 1))) -> L5.u64_at RSEGS M2 (sp - 16) (bv_unsigned (getr R (reg 8))) ->
      L5.u64_at RSEGS M2 (sp - 24) (bv_unsigned (getr R (reg 9))) -> L5.u64_at RSEGS M2 (sp - 32) (bv_unsigned (getr R (reg 18))) ->
      L5.u64_at RSEGS M2 (sp - 40) (bv_unsigned (getr R (reg 19))) -> L5.u64_at RSEGS M2 (sp - 48) (bv_unsigned (getr R (reg 20))) ->
      L5.u64_at RSEGS M2 (sp - 56) (bv_unsigned (getr R (reg 21))) -> L5.u64_at RSEGS M2 (sp - 64) (bv_unsigned (getr R (reg 22))) ->
      L5.u64_at RSEGS M2 (sp - 72) (bv_unsigned (getr R (reg 23))) -> L5.u64_at RSEGS M2 (sp - 80) (bv_unsigned (getr R (reg 24))) ->
      PGS.ow_at O M2 (PM.SRC qc qc 0) OB ->
      PM.iss_at RSEGS PMA.AD PMSPA.accA M2 ois str (PM.STRM g2 eg st2) -> PMSTA.base_okA RSEGS PMA.AD M2 ->
      len1 = rem -> len1 < k -> k - len1 <= 16383 -> 0 <= c <= 16384 -> g2 = g + c -> g2 <= eg -> (sst = 2 -> st2 = 2) -> (c = 0 -> st2 = 2) ->
      L5.defined M2 p len1 ->
      L5SAR.ek L ar LB FF sp 20480 WA M M2 -> L5SAR.dk L ar LB FF sp 20480 M M2 -> L5CA.astk ar M2 sp 20480 ->
      ri_inv HI LB FF LK2 cr Aw2 M2 (vml_of model2) -> L5CA.amodel_ok Aw2 model2 -> model_rt model model2 -> incl LK2 LK -> incl Aw Aw2 ->
      srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx2 R2 0xadc18 M2 model2) K).
  { intros fx2 R2 M2 model2 LK2 Aw2 len1 c g2 st2 Y10 Y2 Y8 Y9 Y18 Y19 Y20 Y21 Y22 Y23 Y24 KS2 C8 C16 C24 C32 C40 C48 C56 C64 C72 C80 PA2 IA2 BASE2
           Hl1 Hl1k Hl1k' Hc Hg2 Hg2e Hst2 Hc0 DP2 EK2 DK2 ASTK2 HH2 AM2 MRT2 INC2 INCA2.
    set (MV2 := mrestrict (ahid Aw2 model2) M2).
    pose proof (PGSKA.src_visG L ar C HI LY HIok LB FF LK2 cr Aw2 M2 model2 os _ _ _ sp 20480 HH2 AO O8 (proj1 (PGSA.oo_src _ _ _ _ _ _ OK M2 _ OB PA2)) (proj1 (proj2 (PGSA.oo_src _ _ _ _ _ _ OK M2 _ OB PA2))) ASTK2) as ((P1 & P8 & PBIG) & PZ & PW & PCE & PAV & _ & _).
    fold os MV2 in P1, P8, PBIG, PZ, PW, PCE, PAV.
    pose proof (PMASK.mach_vis L ar C HI LY HIok LB FF LK2 cr Aw2 M2 model2 HH2 BASE2) as (W0 & W1' & W2'). fold MV2 in W0, W1', W2'.
    pose proof (PMASK.stk_vis L ar C HI LY HIok LB FF LK2 cr Aw2 M2 model2 sp 20480 80 HH2 ASTK2 ltac:(lia)) as (_ & _ & W3). fold MV2 in W3.
    pose proof (proj1 (PGSA.oo_src _ _ _ _ _ _ OK _ _ _ PA2)) as PSRC2.
    destruct PSRC2 as (_ & _ & SD2 & S264b & S272b & S280b & S288b & _ & _ & _ & _ & DCH2 & ACH2 & _).
    cbn [PM.sr_qc PM.sr_de PM.sr_rem] in SD2, S264b, S272b, S280b, S288b, DCH2, ACH2. unfold PM.CHUNK in *.
    fold os in SD2, S264b, S272b, S280b, S288b.
    assert (VD2 : L5.defined MV2 (os + 256) 8) by (apply (proj2 (L5A.defined_vis _ M2 (os + 256) 8 ltac:(apply PAV; lia))); exact SD2).
    pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK2 cr Aw2 M2 model2 HH2) as (_ & VIS2s & _).
    assert (TS2 : forall kk v, 8 <= kk <= 80 -> L5.u64_at RSEGS M2 (sp - kk) v -> L5.u64_at RSEGS MV2 (sp - kk) v).
    { intros kk v Hkk X. apply (proj2 (L5A.u64_at_vis _ M2 (sp - kk) v (VIS2s (sp - kk) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact X. }
    set (VS := fun j => match j with 2%nat => sp | 33%nat => c | 34%nat => qc | 36%nat => os | 37%nat => p | 38%nat => k - len1 | 39%nat => len1
                                | 64%nat => bv_unsigned (getr R (reg 1)) | 65%nat => bv_unsigned (getr R (reg 8)) | 66%nat => bv_unsigned (getr R (reg 9))
                                | 67%nat => bv_unsigned (getr R (reg 18)) | 68%nat => bv_unsigned (getr R (reg 19)) | 69%nat => bv_unsigned (getr R (reg 20))
                                | 70%nat => bv_unsigned (getr R (reg 21)) | 71%nat => bv_unsigned (getr R (reg 22)) | 72%nat => bv_unsigned (getr R (reg 23))
                                | 73%nat => bv_unsigned (getr R (reg 24)) | _ => 0 end).
    destruct (Z.eq_dec c 0) as [CZ|CNZ].
    - (* [comment removed for export] *)
      subst c.
      (let T := type of (PMASRP.asrC0_conc fx2 R2 MV2 VS) in let T := eval unfold VS in T in let T := eval cbn beta iota in T in LeanFeed.pfeed_at P (PMASRP.asrC0_conc fx2 R2 MV2 VS) T ltac:(try (unfold VS); cbn beta iota) ltac:(idtac; first [assumption | lazymatch goal with
          | |- L5.u64_at _ _ (sp - _) _ => apply TS2; [lia| assumption]
          | |- L5.u64_at _ _ (os + _) _ => unfold MV2; vis64 PAV
          | |- PMASRP.aligned _ _ => unfold PMASRP.aligned; lia
          | |- _ \/ _ => right; L5FastLia.plia
          | |- _ => L5FastLia.plia end])).
      destruct P as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & PP). pdestr PP.
      unfold PMSPA.cfg, PMSP.cfg.
      apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK2 cr Aw2 M2 model2 fx2 fx3 R2 0xadc18 R3 0xade1c M3v W1 K HH2 AM2 MS3 MG3).
      { intros a Ha N. apply FRZ3; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
      { exact W1ok. }
      intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3.
      assert (EK23 : L5SAR.ek L ar LB FF sp 20480 [(os + 256, 40)] M2 M3) by exact (EKW1 M2 M3 LK2 Aw2 _ HH2 FR3).
      assert (TO3 : forall a v, os <= a -> a + 8 <= os + 296 -> L5.u64_at RSEGS M3v a v -> L5.u64_at RSEGS M3 a v).
      { intros a v Ha Hb X. rewrite <- VIS3 in X. apply (proj1 (L5A.u64_at_vis _ M3 a v ltac:(apply PAV; lia) ltac:(lia) ltac:(lia))). exact X. }
      apply (FIN fx3 R3 M3 model3 LK2 Aw2 qc 0 g2 st2 len1).
      + match goal with H : getr R3 (reg 1) = _ |- _ => rewrite H end. rewrite Z_to_bv_bv_unsigned. exact Rra.
      + intros x Hx. unfold L5SAR.cs_all in Hx.
        repeat (destruct Hx as [<-|Hx];
          [ first [ match goal with H : getr R3 (reg ?y) = Z_to_bv 64 (bv_unsigned (getr R (reg ?y))) |- getr R3 (reg ?y) = _ => rewrite H, Z_to_bv_bv_unsigned; reflexivity end
                  | match goal with H : getr R3 (reg 2) = Z_to_bv 64 sp |- getr R3 (reg 2) = _ => rewrite H; exact (eq_sym Rsp) end
                  | rewrite (KS3 _) by inl; apply KS2; inl ] |]).
        destruct Hx.
      + assumption.
      + apply TO3; [lia|lia| assumption].
      + apply TO3; [lia|lia| assumption].
      + apply TO3; [lia|lia| assumption].
      + apply TO3; [lia|lia| assumption].
      + clear; lia.
      + clear; lia.
      + clear - Q0; lia.
      + apply (PGSKA.src_piece_issG L ar C HI HIok LB FF LK2 cr Aw2 M2 M3 _ os ois str _ sp 20480 HH2 AO AOI LYD SOWN EK23 IA2).
      + clear - Hg2 Hg2e; lia.
      + exact Hst2.
      + clear - Hl1 Hl1k G2; lia.
      + clear - Hl1 Hg2; lia.
      + clear - Hl1; lia.
      + intros X. split; [reflexivity| apply Hc0; reflexivity].
      + apply (L5.defined_grows M2 M3 p len1 MGM3 DP2).
      + apply (L5SAR.ek_trans L ar LB FF sp 20480 WA M M2 M3 EK2). apply EKWA. exact EK23.
      + apply (L5SAR.dk_trans L ar LB FF sp 20480 M M2 M3 DK2). apply L5SAR.dk_grows. exact MGM3.
      + apply (L5SAR.astk_grows ar M2 M3 sp 20480 ASTK2 MGM3).
      + exact HH3.
      + exact AM3.
      + eapply L5LZ.model_rt_trans; [exact MRT2| exact MRT3].
      + exact INC2.
      + exact INCA2.
    - (* [comment removed for export] *)
      set (len2 := Z.min c (k - len1)).
      assert (L2R : 1 <= len2 <= k - len1 /\ len2 <= c /\ (len2 = k - len1 \/ len2 = c)).
      { unfold len2. clear - CNZ Hc Hl1k. destruct (Z.min_spec c (k - len1)) as [[X1 X2]|[X1 X2]]; rewrite X2; lia. }
      assert (HEADC : exists fx3 R3 M3v, msteps RSEGS (st fx2 R2 0xadc18 MV2) (st fx3 R3 0x778cc M3v) /\ mem_grows MV2 M3v
                 /\ (forall a, 0 <= a < 2 ^ 64 -> ~ W1 a -> M3v (Z_to_bv 64 a) = MV2 (Z_to_bv 64 a))
                 /\ (forall x, In x [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 25; 26; 27]%nat -> getr R3 (reg x) = getr R2 (reg x))
                 /\ getr R3 (reg 1) = Z_to_bv 64 711752 /\ getr R3 (reg 10) = Z_to_bv 64 (p + len1) /\ getr R3 (reg 11) = Z_to_bv 64 qc
                 /\ getr R3 (reg 12) = Z_to_bv 64 len2 /\ getr R3 (reg 21) = Z_to_bv 64 len2
                 /\ L5.u64_at RSEGS M3v (os + 288) c /\ L5.u64_at RSEGS M3v (os + 280) qc /\ L5.u64_at RSEGS M3v (os + 264) qc
                 /\ L5.u64_at RSEGS M3v (os + 272) 16384 /\ L5.defined M3v (os + 256) 8
                 /\ L5.u64_at RSEGS M3v (sp - 8) (bv_unsigned (getr R (reg 1))) /\ L5.u64_at RSEGS M3v (sp - 16) (bv_unsigned (getr R (reg 8)))
                 /\ L5.u64_at RSEGS M3v (sp - 24) (bv_unsigned (getr R (reg 9))) /\ L5.u64_at RSEGS M3v (sp - 32) (bv_unsigned (getr R (reg 18)))
                 /\ L5.u64_at RSEGS M3v (sp - 40) (bv_unsigned (getr R (reg 19))) /\ L5.u64_at RSEGS M3v (sp - 48) (bv_unsigned (getr R (reg 20)))
                 /\ L5.u64_at RSEGS M3v (sp - 56) (bv_unsigned (getr R (reg 21))) /\ L5.u64_at RSEGS M3v (sp - 64) (bv_unsigned (getr R (reg 22)))
                 /\ L5.u64_at RSEGS M3v (sp - 72) (bv_unsigned (getr R (reg 23))) /\ L5.u64_at RSEGS M3v (sp - 80) (bv_unsigned (getr R (reg 24)))).
      { destruct (Z_le_gt_dec c (k - len1)) as [CLE|CGT].
        - assert (E2 : len2 = c) by (unfold len2; clear - CLE; lia).
          assert (Cr1 : 1 <= c <= 16383) by (clear - CNZ Hc CLE Hl1k'; lia).
          assert (Cr2 : 0 <= -1 * c + (k - len1) <= 16383) by (clear - CNZ Hc CLE Hl1k'; lia).
          assert (Cr3 : 0 <= p <= 140737488355328) by (clear - DP0 DP1 Hk; lia).
          (let T := type of (PMASRP.asrCge_conc fx2 R2 MV2 VS) in let T := eval unfold VS in T in let T := eval cbn beta iota in T in LeanFeed.pfeed_at P (PMASRP.asrCge_conc fx2 R2 MV2 VS) T ltac:(try (unfold VS); cbn beta iota) ltac:(idtac; first [assumption | lazymatch goal with
              | |- L5.u64_at _ _ (sp - _) _ => apply TS2; [lia| assumption]
              | |- L5.u64_at _ _ (os + _) _ => unfold MV2; vis64 PAV
              | |- PMASRP.aligned _ _ => unfold PMASRP.aligned; lia
              | |- _ \/ _ => right; L5FastLia.plia
              | |- _ => L5FastLia.plia end])).
          destruct P as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & T1 & T10 & T11 & T12 & T21 & U288 & U264 & U272 & U280 & UD & S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80).
          exists fx3, R3, M3v. split; [exact MS3|]. split; [exact MG3|].
          split; [intros a Ha N; apply FRZ3; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]|].
          split; [intros x Hx; apply KS3; revert x Hx; apply (PMASR1.sub_in PMASRP.KS_asrCge); vm_compute; reflexivity|].
          rewrite E2. split; [exact T1|]. split; [exact T10|]. split; [exact T11|]. split; [exact T12|]. split; [exact T21|].
          split; [exact U288|]. split; [exact U280|]. split; [exact U264|]. split; [exact U272|]. split; [exact UD|].
          split; [exact S8|]. split; [exact S16|]. split; [exact S24|]. split; [exact S32|]. split; [exact S40|].
          split; [exact S48|]. split; [exact S56|]. split; [exact S64|]. split; [exact S72| exact S80].
        - assert (E2 : len2 = k - len1) by (unfold len2; clear - CGT; lia).
          assert (Cr1 : 2 <= c <= 16384) by (clear - CGT Hc Hl1k; lia).
          assert (Cr2 : 1 <= c - (k - len1) <= 16383) by (clear - CGT Hc Hl1k; lia).
          assert (Cr3 : 0 <= p <= 140737488355328) by (clear - DP0 DP1 Hk; lia).
          (let T := type of (PMASRP.asrClt_conc fx2 R2 MV2 VS) in let T := eval unfold VS in T in let T := eval cbn beta iota in T in LeanFeed.pfeed_at P (PMASRP.asrClt_conc fx2 R2 MV2 VS) T ltac:(try (unfold VS); cbn beta iota) ltac:(idtac; first [assumption | lazymatch goal with
              | |- L5.u64_at _ _ (sp - _) _ => apply TS2; [lia| assumption]
              | |- L5.u64_at _ _ (os + _) _ => unfold MV2; vis64 PAV
              | |- PMASRP.aligned _ _ => unfold PMASRP.aligned; lia
              | |- _ \/ _ => right; L5FastLia.plia
              | |- _ => L5FastLia.plia end])).
          destruct P as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & T1 & T10 & T11 & T12 & U288 & U264 & U272 & U280 & UD & S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80).
          exists fx3, R3, M3v. split; [exact MS3|]. split; [exact MG3|].
          split; [intros a Ha N; apply FRZ3; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]|].
          split; [intros x Hx; apply KS3; revert x Hx; apply (PMASR1.sub_in PMASRP.KS_asrClt); vm_compute; reflexivity|].
          rewrite E2. split; [exact T1|]. split; [exact T10|]. split; [exact T11|]. split; [exact T12|]. split; [rewrite (KS3 21%nat) by inl; exact Y21|].
          split; [exact U288|]. split; [exact U280|]. split; [exact U264|]. split; [exact U272|]. split; [exact UD|].
          split; [exact S8|]. split; [exact S16|]. split; [exact S24|]. split; [exact S32|]. split; [exact S40|].
          split; [exact S48|]. split; [exact S56|]. split; [exact S64|]. split; [exact S72| exact S80]. }
      destruct HEADC as (fx3 & R3 & M3v & MS3 & MG3 & FRZ3 & KS3 & T1 & T10 & T11 & T12 & T21 & U288 & U280 & U264 & U272 & UD
                         & S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80).
      unfold PMSPA.cfg, PMSP.cfg.
      apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK2 cr Aw2 M2 model2 fx2 fx3 R2 0xadc18 R3 0x778cc M3v W1 K HH2 AM2 MS3 MG3 FRZ3 W1ok).
      intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3.
      assert (EK23 : L5SAR.ek L ar LB FF sp 20480 [(os + 256, 40)] M2 M3) by exact (EKW1 M2 M3 LK2 Aw2 _ HH2 FR3).
      assert (TO3 : forall a v, os <= a -> a + 8 <= os + 296 -> L5.u64_at RSEGS M3v a v -> L5.u64_at RSEGS M3 a v).
      { intros a v Ha Hb X. rewrite <- VIS3 in X. apply (proj1 (L5A.u64_at_vis _ M3 a v ltac:(apply PAV; lia) ltac:(lia) ltac:(lia))). exact X. }
      pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK2 cr Aw2 M3 model3 HH3) as (_ & VIS3s & _).
      assert (TS3 : forall kk v, 8 <= kk <= 80 -> L5.u64_at RSEGS M3v (sp - kk) v -> L5.u64_at RSEGS M3 (sp - kk) v).
      { intros kk v Hkk X. rewrite <- VIS3, <- HID3 in X.
        apply (proj1 (L5A.u64_at_vis _ M3 (sp - kk) v (VIS3s (sp - kk) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact X. }
      assert (EK03 : L5SAR.ek L ar LB FF sp 20480 WA M M3) by (apply (L5SAR.ek_trans L ar LB FF sp 20480 WA M M2 M3 EK2); apply EKWA; exact EK23).
      assert (DK03 : L5SAR.dk L ar LB FF sp 20480 M M3) by (apply (L5SAR.dk_trans L ar LB FF sp 20480 M M2 M3 DK2); apply L5SAR.dk_grows; exact MGM3).
      assert (ASTK3 : L5CA.astk ar M3 sp 20480) by (apply (L5SAR.astk_grows ar M2 M3 sp 20480 ASTK2 MGM3)).
      assert (WS1 : PMKA.wapp [(os + 256, 40)]).
      { apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI in *; clear - OBIG; Lia.lia| apply PMKA.wapp_nil]. }
      assert (Hl10 : 0 <= len1) by (clear - Hl1 G2; lia).
      (* [comment removed for export] *)
      apply (PMASRK.memcpy_call L ar C HI LY HIok fx3 R3 M3 model3 K LB FF LK2 cr Aw2 (sp - 80) 711752 (p + len1) qc len2 HH3 AM3 K0).
      { exact T1. }
      { split; [clear; lia| reflexivity]. }
      { rewrite (KS3 2%nat) by inl. exact Y2. }
      { rewrite (KS3 4%nat) by inl. rewrite (KS2 4%nat) by inl. exact Rtp. }
      { exact T10. }
      { exact T11. }
      { exact T12. }
      { clear - L2R Hl1k'; lia. }
      { apply (L5SAR.astk_sub ar M3 M3 sp 20480 80 2560 ASTK3 (fun _ X => X)); [clear; lia| clear; lia| clear; lia|].
        replace (sp - 80) with (sp + (-5) * 16) by (clear; lia). rewrite Z.mod_add by (clear; lia). exact A16. }
      { intros a Ha. apply (PMFA.accA_agree M M3 p k (AGSHP M M3 WA EK03 WAPP) DAP a). clear - Ha L2R Hl10; lia. }
      { intros i Hi. apply CLPw. clear - Hi L2R Hl10; lia. }
      { apply (L5.defined_sub M3 p k); [| clear - L2R Hl10; lia| clear - L2R Hl10; lia].
        apply (PMASK.defined_dk L ar LB FF sp 20480 M M3 p k DK03); [intros i Hi; apply CLP; exact Hi| clear - DP0; lia| clear - DP1; lia| exact DDP]. }
      { clear - DP0 Hl10; lia. }
      { clear - DP1 L2R Hl10; lia. }
      { unfold app_rng in DAPP |- *. clear - DAPP L2R Hl10. Lia.lia. }
      { intros a Ha. apply (PMFA.accA_agree M2 M3 qc 16384); [apply (PMASK.agsh_blk L ar LB FF sp 20480 _ M2 M3 qc 16384 EK23 WS1 QIN); clear - Q0 Q4 SLO SHI SPT; lia| exact ACH2| clear - Ha L2R Hl1k'; lia]. }
      { clear - Q0; lia. }
      { clear - Q4 SLO SHI SPT L2R Hl1k'; lia. }
      { apply (L5SAR.app_rng_block L ar C HI HIok LB FF LK2 cr Aw2 M3 _ qc 16384 qc len2 HH3 QIN); clear - L2R Hl1k'; lia. }
      { intros i Hi. apply CLQ. clear - Hi L2R Hl1k'; lia. }
      { apply (L5.defined_sub M3 qc 16384); [apply (L5.defined_grows M2 M3 qc 16384 MGM3 DCH2)| clear; lia| clear - L2R Hl1k'; lia]. }
      { clear - DQA L2R Hl10 Hl1k'. Lia.lia. }
      intros fx4 R4 M4 model4 RP4 DEF4 HP4 MRT4 AM4 HH4.
      assert (OUTD : forall a, aclient L ar LB FF sp 20480 a -> L5.outside WA a -> L5.outside [(p + len1, len2)] a).
      { intros a _ Oq r0 [<-|[]] X. apply (Oq (p, k)); [unfold WA; apply in_or_app; right; left; reflexivity| unfold L5.in_rng in *; cbn [fst snd] in *; clear - X L2R Hl10; lia]. }
      assert (EK34 : L5SAR.ek L ar LB FF sp 20480 WA M3 M4).
      { apply (L5SAR.ek_callee L ar LB [] FF [] sp 20480 (sp - 80) 2560 WA [(p + len1, len2)] M3 M4 HP4); [clear; lia| clear; lia| exact OUTD]. }
      assert (EK34d : L5SAR.ek L ar LB FF sp 20480 [(p + len1, len2)] M3 M4).
      { apply (L5SAR.ek_callee L ar LB [] FF [] sp 20480 (sp - 80) 2560 _ [(p + len1, len2)] M3 M4 HP4); [clear; lia| clear; lia| intros a _ Oq; exact Oq]. }
      assert (DK34 : L5SAR.dk L ar LB FF sp 20480 M3 M4) by (apply (L5SAR.dk_callee L ar LB [] FF [] sp 20480 (sp - 80) 2560 _ M3 M4 HP4); clear; lia).
      assert (ASTK4 : L5CA.astk ar M4 sp 20480) by (apply (PMKA.astk_after_ahpres L ar LB FF M3 M4 sp 20480 (sp - 80) 2560 _ ASTK3 HP4); clear - TOP; lia).
      assert (NDP : forall a, ~ (p <= a < p + k) -> ~ (p + len1 <= a < p + len1 + len2)) by (intros a N X; apply N; clear - X L2R Hl10; lia).
      assert (KF4 : forall a, sp - 80 <= a < sp -> M4 (Z_to_bv 64 a) = M3 (Z_to_bv 64 a)).
      { intros a Ha. destruct HP4 as (E & _). apply E. split; [clear - Ha SLO SHI SPT; lia|]. split.
        - apply (L5SAR.stack_client L ar LB FF (sp - 80) 2560 a); clear - Ha SL80 SHI SPT; lia.
        - intros r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. apply NDP. intros Y. destruct (DX a Y) as (X1 & _). apply X1. clear - Ha; lia. }
      assert (KO4 : forall a, os + 256 <= a < os + 296 -> M4 (Z_to_bv 64 a) = M3 (Z_to_bv 64 a)).
      { intros a Ha. destruct HP4 as (E & _). apply E. split; [clear - Ha O1; lia|]. split.
        - apply PMASR1.cl_of_bf. right. apply (PMASR1.in_fframe_of_aobjA FF os 296 a AO). clear - Ha; lia.
        - intros r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. apply NDP. intros Y. destruct (DX a Y) as (_ & _ & X3 & _). apply X3. clear - Ha; lia. }
      assert (WSP : PMKA.wapp [(p + len1, len2)]).
      { apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI in *; clear - DSH L2R Hl10; Lia.lia| apply PMKA.wapp_nil]. }
      assert (EK04 : L5SAR.ek L ar LB FF sp 20480 WA M M4) by exact (L5SAR.ek_trans L ar LB FF sp 20480 WA M M3 M4 EK03 EK34).
      assert (DK04 : L5SAR.dk L ar LB FF sp 20480 M M4) by exact (L5SAR.dk_trans L ar LB FF sp 20480 M M3 M4 DK03 DK34).
      assert (T4 : forall a v, os + 256 <= a -> a + 8 <= os + 296 -> L5.u64_at RSEGS M3v a v -> L5.u64_at RSEGS M4 a v).
      { intros a v Ha Hb X. apply (L5C.u64_at_agree RSEGS M3 M4); [intros i Hi; apply KO4; clear - Ha Hb Hi; lia| clear - Ha O1; lia| clear - Hb O1; lia|].
        apply TO3; [clear - Ha; lia| clear - Hb; lia| exact X]. }
      assert (PA4 : PGS.ow_at O M4 (PM.SRC qc qc c) OB).
      { apply (OWU M4 qc c EK04 DK04 ASTK4); [apply T4; [clear; lia| clear; lia| exact U264]| apply T4; [clear; lia| clear; lia| exact U272]
                                        | apply T4; [clear; lia| clear; lia| exact U280]| apply T4; [clear; lia| clear; lia| exact U288]| clear; lia| clear - Hc; lia| clear - Hc; lia]. }
      assert (IA3 : PM.iss_at RSEGS PMA.AD PMSPA.accA M3 ois str (PM.STRM g2 eg st2)) by exact (PGSKA.src_piece_issG L ar C HI HIok LB FF LK2 cr Aw2 M2 M3 _ os ois str _ sp 20480 HH2 AO AOI LYD SOWN EK23 IA2).
      assert (IA4 : PM.iss_at RSEGS PMA.AD PMSPA.accA M4 ois str (PM.STRM g2 eg st2)).
      { apply (PMKA.iss_keepA RSEGS PMA.AD L ar LB FF sp 20480 _ M3 M4 EK34d WSP FRB BRB ois str _ AOI SOWN); [| |exact IA3].
        - intros i Hi r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. apply NDP. intros Y. destruct (DX i Y) as (_ & X2 & _). apply X2. exact Hi.
        - intros c1 n1 q1 E i Hi r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. apply NDP. intros Y. destruct (DX i Y) as (_ & _ & _ & _ & X5 & _). apply (X5 c1 n1 q1 E). exact Hi. }
      assert (BASE3 : PMSTA.base_okA RSEGS PMA.AD M3).
      { apply (PMASK.base_keep L ar C LY LB FF sp 20480 _ M2 M3 EK23); [intros a Ha r0 [<-|[]]; unfold L5.in_rng; cbn [fst snd]; clear - Ha O1; lia| exact BASE2]. }
      assert (BASE4 : PMSTA.base_okA RSEGS PMA.AD M4).
      { apply (PMASK.base_keep L ar C LY LB FF sp 20480 _ M3 M4 EK34d); [| exact BASE3].
        intros a Ha r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. apply NDP. intros Y. destruct (DX a Y) as (_ & _ & _ & _ & _ & X6). apply X6. exact Ha. }
      set (MV4 := mrestrict (ahid Aw2 model4) M4).
      pose proof (PGSKA.src_visG L ar C HI LY HIok LB FF LK2 cr Aw2 M4 model4 os _ _ _ sp 20480 HH4 AO O8 (proj1 (PGSA.oo_src _ _ _ _ _ _ OK M4 _ OB PA4)) (proj1 (proj2 (PGSA.oo_src _ _ _ _ _ _ OK M4 _ OB PA4))) ASTK4) as ((P1' & P8' & PBIG') & PZ' & PW' & PCE' & PAV' & _ & _).
      fold os MV4 in P1', P8', PBIG', PZ', PW', PCE', PAV'.
      pose proof (PMASK.mach_vis L ar C HI LY HIok LB FF LK2 cr Aw2 M4 model4 HH4 BASE4) as (X0' & X1' & X2'). fold MV4 in X0', X1', X2'.
      pose proof (PMASK.stk_vis L ar C HI LY HIok LB FF LK2 cr Aw2 M4 model4 sp 20480 80 HH4 ASTK4 ltac:(lia)) as (_ & _ & X3'). fold MV4 in X3'.
      pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK2 cr Aw2 M4 model4 HH4) as (_ & VIS4s & _).
      assert (TS4 : forall kk v, 8 <= kk <= 80 -> L5.u64_at RSEGS M3v (sp - kk) v -> L5.u64_at RSEGS MV4 (sp - kk) v).
      { intros kk v Hkk X. apply (proj2 (L5A.u64_at_vis _ M4 (sp - kk) v (VIS4s (sp - kk) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
        apply (L5C.u64_at_agree RSEGS M3 M4); [intros i Hi; apply KF4; clear - Hkk Hi; lia| clear - Hkk SLO SHI SPT; lia| clear - Hkk SLO SHI SPT; lia|].
        apply TS3; [exact Hkk| exact X]. }
      assert (TO4 : forall a v, os + 256 <= a -> a + 8 <= os + 296 -> L5.u64_at RSEGS M3v a v -> L5.u64_at RSEGS MV4 a v).
      { intros a v Ha Hb X. apply (proj2 (L5A.u64_at_vis _ M4 a v ltac:(apply PAV'; clear - Ha Hb; lia) ltac:(clear - Ha O1; lia) ltac:(clear - Hb O1; lia))). apply T4; assumption. }
      assert (VD4 : L5.defined MV4 (os + 256) 8).
      { apply (proj2 (L5A.defined_vis _ M4 (os + 256) 8 ltac:(apply PAV'; lia))). pose proof (proj1 (PGSA.oo_src _ _ _ _ _ _ OK _ _ _ PA4)) as PS4.
        destruct PS4 as (_ & _ & SD4 & _). exact SD4. }
      assert (RG : forall x, In x [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R4 (reg x) = getr R3 (reg x)).
      { intros x Hx. apply (L5SAR.cs_of_preserved R3 R4 x RP4). cbn in Hx. repeat (destruct Hx as [<-|Hx]; [inl|]). destruct Hx. }
      assert (Dr1 : 1 <= c <= 16384) by (clear - CNZ Hc; lia).
      assert (Dr2 : 0 <= c - len2 <= 16383) by (clear - L2R Hc Hl1k'; lia).
      assert (Dr3 : 0 <= len1 <= 16383) by (clear - Hl10 Hl1k Hk Hl1k'; lia).
      assert (Dr4 : 1 <= len2 <= 16383) by (clear - L2R Hl1k'; lia).
      assert (Dr5 : 4096 <= qc <= 140737488338944) by (clear - Q0 Q4 SLO SHI SPT; lia).
      set (VD := fun j => match j with 2%nat => sp | 33%nat => c | 34%nat => qc | 35%nat => qc | 36%nat => os | 37%nat => p | 38%nat => len2 | 39%nat => len1
                                | 64%nat => bv_unsigned (getr R (reg 1)) | 65%nat => bv_unsigned (getr R (reg 8)) | 66%nat => bv_unsigned (getr R (reg 9))
                                | 67%nat => bv_unsigned (getr R (reg 18)) | 68%nat => bv_unsigned (getr R (reg 19)) | 69%nat => bv_unsigned (getr R (reg 20))
                                | 70%nat => bv_unsigned (getr R (reg 21)) | 71%nat => bv_unsigned (getr R (reg 22)) | 72%nat => bv_unsigned (getr R (reg 23))
                                | 73%nat => bv_unsigned (getr R (reg 24)) | _ => 0 end).
      (let T := type of (PMASRP.asrD_conc fx4 R4 MV4 VD) in let T := eval unfold VD in T in let T := eval cbn beta iota in T in LeanFeed.pfeed_at P (PMASRP.asrD_conc fx4 R4 MV4 VD) T ltac:(try (unfold VD); cbn beta iota) ltac:(idtac; first [assumption | lazymatch goal with
          | |- getr R4 (reg ?x) = _ => rewrite (RG x) by inl; first [assumption | rewrite (KS3 x) by inl; assumption]
          | |- L5.u64_at _ _ (sp - _) _ => apply TS4; [lia| assumption]
          | |- L5.u64_at _ _ (os + _) _ => apply TO4; [lia| lia| assumption]
          | |- PMASRP.aligned _ _ => unfold PMASRP.aligned; lia
          | |- _ \/ _ => right; L5FastLia.plia
          | |- _ => L5FastLia.plia end])).
      destruct P as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & Z1 & Z2 & Z8 & Z9 & Z10 & Z18 & Z19 & Z20 & Z21 & Z22 & Z23 & Z24
                     & V288 & V280 & V264 & V272 & _).
      apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK2 cr Aw2 M4 model4 fx4 fx5 R4 0xadc48 R5 0xade1c M5v W1 K HH4 AM4 MS5 MG5).
      { intros a Ha N. apply FRZ5; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
      { exact W1ok. }
      intros M5 model5 HH5 AM5 MRT5 HID5 VIS5 MGM5 FR5 VV5.
      assert (EK45 : L5SAR.ek L ar LB FF sp 20480 [(os + 256, 40)] M4 M5) by exact (EKW1 M4 M5 LK2 Aw2 _ HH4 FR5).
      assert (TO5 : forall a v, os <= a -> a + 8 <= os + 296 -> L5.u64_at RSEGS M5v a v -> L5.u64_at RSEGS M5 a v).
      { intros a v Ha Hb X. rewrite <- VIS5 in X. apply (proj1 (L5A.u64_at_vis _ M5 a v ltac:(apply PAV'; lia) ltac:(lia) ltac:(lia))). exact X. }
      apply (FIN fx5 R5 M5 model5 LK2 Aw2 (qc + len2) (c - len2) g2 st2 (len2 + len1)).
      + rewrite Z1, Z_to_bv_bv_unsigned. exact Rra.
      + intros x Hx. unfold L5SAR.cs_all in Hx.
        repeat (destruct Hx as [<-|Hx];
          [ first [ match goal with H : getr R5 (reg ?y) = Z_to_bv 64 (bv_unsigned (getr R (reg ?y))) |- getr R5 (reg ?y) = _ => rewrite H, Z_to_bv_bv_unsigned; reflexivity end
                  | rewrite Z2; exact (eq_sym Rsp)
                  | rewrite (KS5 _) by inl; rewrite (RG _) by inl; rewrite (KS3 _) by inl; apply KS2; inl ] |]).
        destruct Hx.
      + exact Z10.
      + apply TO5; [lia| lia| exact V264].
      + apply TO5; [lia| lia| exact V272].
      + apply TO5; [lia| lia| exact V280].
      + apply TO5; [lia| lia| exact V288].
      + clear - Dr4; lia.
      + clear - Dr2; lia.
      + clear - Hc; lia.
      + apply (PGSKA.src_piece_issG L ar C HI HIok LB FF LK2 cr Aw2 M4 M5 _ os ois str _ sp 20480 HH4 AO AOI LYD SOWN EK45 IA4).
      + clear - Hg2 Hg2e Hc; lia.
      + exact Hst2.
      + clear - L2R Hl10; lia.
      + clear - Hl1 Hg2; lia.
      + intros _. clear - Dr4 Hl10; lia.
      + intros X. exfalso. clear - X Dr4 Hl10; lia.
      + rewrite Z.add_comm. apply (PMASR1.defined_app M5 p len1 len2 Hl10).
        * apply (PMASK.defined_dk L ar LB FF sp 20480 M2 M5 p len1); [| | clear - DP0; lia| clear - DP1 L2R Hl10; lia| exact DP2].
          -- apply (L5SAR.dk_trans L ar LB FF sp 20480 M2 M4 M5); [apply (L5SAR.dk_trans L ar LB FF sp 20480 M2 M3 M4); [apply L5SAR.dk_grows; exact MGM3| exact DK34]| apply L5SAR.dk_grows; exact MGM5].
          -- intros i Hi. apply CLP. clear - Hi L2R Hl10; lia.
        * apply (L5.defined_grows M4 M5 _ _ MGM5 DEF4).
      + apply (L5SAR.ek_trans L ar LB FF sp 20480 WA M M4 M5 EK04). apply EKWA. exact EK45.
      + apply (L5SAR.dk_trans L ar LB FF sp 20480 M M4 M5 DK04). apply L5SAR.dk_grows. exact MGM5.
      + apply (L5SAR.astk_grows ar M4 M5 sp 20480 ASTK4 MGM5).
      + exact HH5.
      + exact AM5.
      + eapply L5LZ.model_rt_trans; [exact MRT2|]. eapply L5LZ.model_rt_trans; [exact MRT3|]. eapply L5LZ.model_rt_trans; [exact MRT4| exact MRT5].
      + exact INC2.
      + exact INCA2. }
  (* [comment removed for export] *)
  assert (FILLC : forall (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (len1 : Z),
      getr R1 (reg 1) = Z_to_bv 64 711704 -> getr R1 (reg 2) = Z_to_bv 64 (sp - 80) -> getr R1 (reg 8) = Z_to_bv 64 len1 -> getr R1 (reg 9) = Z_to_bv 64 os ->
      getr R1 (reg 10) = Z_to_bv 64 os -> getr R1 (reg 11) = Z_to_bv 64 qc -> getr R1 (reg 12) = Z_to_bv 64 16384 ->
      getr R1 (reg 18) = Z_to_bv 64 (os + 288) -> getr R1 (reg 19) = Z_to_bv 64 p -> getr R1 (reg 20) = Z_to_bv 64 (os + 280) ->
      getr R1 (reg 21) = Z_to_bv 64 (k - len1) -> getr R1 (reg 22) = Z_to_bv 64 2147450880 ->
      getr R1 (reg 23) = Z_to_bv 64 ((os + 288) / 8 + 2147450880) -> getr R1 (reg 24) = Z_to_bv 64 ((os + 280) / 8 + 2147450880) ->
      (forall x, In x [3; 4; 25; 26; 27]%nat -> getr R1 (reg x) = getr R (reg x)) ->
      L5.u64_at RSEGS M1 (sp - 8) (bv_unsigned (getr R (reg 1))) -> L5.u64_at RSEGS M1 (sp - 16) (bv_unsigned (getr R (reg 8))) ->
      L5.u64_at RSEGS M1 (sp - 24) (bv_unsigned (getr R (reg 9))) -> L5.u64_at RSEGS M1 (sp - 32) (bv_unsigned (getr R (reg 18))) ->
      L5.u64_at RSEGS M1 (sp - 40) (bv_unsigned (getr R (reg 19))) -> L5.u64_at RSEGS M1 (sp - 48) (bv_unsigned (getr R (reg 20))) ->
      L5.u64_at RSEGS M1 (sp - 56) (bv_unsigned (getr R (reg 21))) -> L5.u64_at RSEGS M1 (sp - 64) (bv_unsigned (getr R (reg 22))) ->
      L5.u64_at RSEGS M1 (sp - 72) (bv_unsigned (getr R (reg 23))) -> L5.u64_at RSEGS M1 (sp - 80) (bv_unsigned (getr R (reg 24))) ->
      L5.u64_at RSEGS M1 (os + 264) qc -> L5.u64_at RSEGS M1 (os + 272) 16384 -> L5.u64_at RSEGS M1 (os + 280) qc -> L5.u64_at RSEGS M1 (os + 288) 0 ->
      len1 = rem -> len1 < k -> k - len1 <= 16383 -> L5.defined M1 p len1 ->
      L5SAR.ek L ar LB FF sp 20480 WA M M1 -> L5SAR.dk L ar LB FF sp 20480 M M1 -> L5CA.astk ar M1 sp 20480 -> PMSTA.base_okA RSEGS PMA.AD M1 ->
      PM.iss_at RSEGS PMA.AD PMSPA.accA M1 ois str (PM.STRM g eg sst) ->
      ri_inv HI LB FF LK cr Aw M1 (vml_of model1) -> L5CA.amodel_ok Aw model1 -> model_rt model model1 ->
      srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx1 R1 0xb150c M1 model1) K).
  { intros fx1 R1 M1 model1 len1 T1 T2 T8 T9 T10 T11 T12 T18 T19 T20 T21 T22 T23 T24 KS1 C8 C16 C24 C32 C40 C48 C56 C64 C72 C80 C264 C272 C280 C288
           Hl1 Hl1k Hl1k' DP1' EK1 DK1 ASTK1 BASE1 IA1 HH1 AM1 MRT1.
    assert (PA1 : PGS.ow_at O M1 (PM.SRC qc qc 0) OB).
    { apply (OWU M1 qc 0 EK1 DK1 ASTK1 C264 C272 C280 C288); clear; lia. }
    assert (M8a : (sp - 20480) mod 8 = 0) by (apply PMKA.mod16_8'; replace (sp - 20480) with (sp + (-1280) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact A16).
    assert (M8b : (sp - 80 - 18432) mod 8 = 0) by (apply PMKA.mod16_8'; replace (sp - 80 - 18432) with (sp + (-1157) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact A16).
    assert (STK1 : shadow_zero M1 (sp - 80 - 18432) (18432 / 8)).
    { change (18432 / 8) with 2304. change (20480 / 8) with 2560 in STKSH.
      apply (PMKA.shadow_zero_sub M1 (sp - 20480) 2560); [exact M8a| exact M8b| clear; lia| clear; lia| clear; lia|].
      apply (PMKA.stksh_keepA L ar LB FF sp 20480 WA M M1 EK1 WAPP (sp - 20480) 2560); [clear - SLO SPT; lia| clear - SLO; lia| clear - SHI SPT; lia| exact M8a| clear; lia| exact STKSH]. }
    unfold PGSA.fill_buffer_specG, PGSA.src_specG in FB.
    apply (FB O OK fx1 R1 M1 model1 K OB LBX FF LK Aw cr (sp - 80) 0xadc18 (PM.SRC qc qc 0) str (PM.STRM g eg sst) [] HH1 AM1 K0).
    { split; [rewrite L5K.rl1; exact T1|]. split; [split; [clear; lia| reflexivity]|]. split; [rewrite L5K.rl2; exact T2|].
      split; [rewrite L5K.rl3; rewrite (KS1 3%nat) by inl; exact Rgp|]. split; [rewrite L5K.rl4; rewrite (KS1 4%nat) by inl; exact Rtp|].
      change (PMSPA.pm_scr 3) with 18432. split; [|exact STK1].
      apply (L5SAR.astk_sub ar M1 M1 sp 20480 80 18432 ASTK1 (fun _ X => X)); [clear; lia| clear; lia| clear; lia|].
      replace (sp - 80) with (sp + (-5) * 16) by (clear; lia). rewrite Z.mod_add by (clear; lia). exact A16. }
    { intros kk Hkk. specialize (FRM kk Hkk). clear - FRM. lia. }
    { intros f Hf. specialize (FRS f Hf). clear - FRS. lia. }
    { exact OFR. }
    { rewrite L5K.rl10. exact T10. }
    { split; [rewrite L5SAR.r11; exact T11| rewrite L5SAR.r12; exact T12]. }
    { reflexivity. }
    { exact PA1. }
    { exact IA1. }
    { exact BASE1. }
    { exact INCS. }
    intros fx2 R2 M2 model2 LK2 Aw2 src2 sm2 RP2 PA2 IA2 STEP2 RES2 HP2 MRT2 INC2 INCA2 AM2 HH2.
    destruct RES2 as (E2 & c & A10c & Hc & G2c & RS0 & RS2). subst src2. unfold PM.CHUNK in Hc.
    destruct sm2 as [g2 eg2 st2]. cbn [PM.sm_g PM.sm_eg PM.sm_st] in *.
    pose proof STEP2 as (_ & EG2 & _ & _ & _). cbn [PM.sm_eg] in EG2. subst eg2.
    change (PM.src_own (PM.SRC qc qc 0) ++ OB ++ LBX) with LB in HH2, HP2. rewrite app_nil_r in HP2. change (PMSPA.pm_scr 3) with 18432 in HP2.
    assert (EK12 : L5SAR.ek L ar LB FF sp 20480 WA M1 M2).
    { apply (L5SAR.ek_callee L ar LB [] FF [] sp 20480 (sp - 80) 18432 WA _ M1 M2 HP2); [clear; lia| clear; lia|].
      intros a _ Oq r0 Hr X. apply (Oq r0); [| exact X]. unfold WA. apply in_or_app. left. exact Hr. }
    assert (DK12 : L5SAR.dk L ar LB FF sp 20480 M1 M2) by (apply (L5SAR.dk_callee L ar LB [] FF [] sp 20480 (sp - 80) 18432 _ M1 M2 HP2); clear; lia).
    assert (ASTK2 : L5CA.astk ar M2 sp 20480) by (apply (PMKA.astk_after_ahpres L ar LB FF M1 M2 sp 20480 (sp - 80) 18432 _ ASTK1 HP2); clear - TOP; lia).
    assert (KF2 : forall a, sp - 80 <= a < sp -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
    { intros a Ha. destruct HP2 as (E & _). apply E. split; [clear - Ha SLO SHI SPT; lia|]. split.
      - apply (L5SAR.stack_client L ar LB FF (sp - 80) 18432 a); clear - Ha SL80 SHI SPT; lia.
      - intros r0 Hr. unfold PGS.W_srcG, PGS.W_srcfG in Hr. cbn [PM.sr_qc app] in Hr. unfold L5.in_rng.
        destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd]; unfold PM.CHUNK; clear - Ha OCE ICE Q4 SL80 SLO; lia. }
    assert (SV : forall kk v, 8 <= kk <= 80 -> L5.u64_at RSEGS M1 (sp - kk) v -> L5.u64_at RSEGS M2 (sp - kk) v).
    { intros kk v Hkk X. apply (L5C.u64_at_agree RSEGS M1 M2); [intros i Hi; apply KF2; clear - Hkk Hi; lia| clear - Hkk SLO SHI SPT; lia| clear - Hkk SLO SHI SPT; lia| exact X]. }
    assert (RG : forall x, In x L5SAR.cs_all -> getr R2 (reg x) = getr R1 (reg x)) by (intros x Hx; apply (L5SAR.cs_of_preserved R1 R2 x RP2 Hx)).
    pose proof (PMASK.iss_size_ltA M ois str _ IA) as SZ. cbn [PM.sm_g PM.sm_eg] in SZ.
    apply (CPART fx2 R2 M2 model2 LK2 Aw2 len1 c g2 st2).
    - rewrite L5K.rl10 in A10c. exact A10c.
    - rewrite (RG 2%nat) by inl. exact T2.
    - rewrite (RG 8%nat) by inl. exact T8.
    - rewrite (RG 9%nat) by inl. exact T9.
    - rewrite (RG 18%nat) by inl. exact T18.
    - rewrite (RG 19%nat) by inl. exact T19.
    - rewrite (RG 20%nat) by inl. exact T20.
    - rewrite (RG 21%nat) by inl. exact T21.
    - rewrite (RG 22%nat) by inl. exact T22.
    - rewrite (RG 23%nat) by inl. exact T23.
    - rewrite (RG 24%nat) by inl. exact T24.
    - intros x Hx. rewrite (RG x) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). apply KS1. exact Hx.
    - apply SV; [clear; lia| exact C8].
    - apply SV; [clear; lia| exact C16].
    - apply SV; [clear; lia| exact C24].
    - apply SV; [clear; lia| exact C32].
    - apply SV; [clear; lia| exact C40].
    - apply SV; [clear; lia| exact C48].
    - apply SV; [clear; lia| exact C56].
    - apply SV; [clear; lia| exact C64].
    - apply SV; [clear; lia| exact C72].
    - apply SV; [clear; lia| exact C80].
    - exact PA2.
    - exact IA2.
    - apply (PMASK.base_keep L ar C LY LB FF sp 20480 WA M1 M2 EK12 OUTIMG BASE1).
    - exact Hl1.
    - exact Hl1k.
    - exact Hl1k'.
    - exact Hc.
    - exact G2c.
    - destruct IST as [ST0|ST2]; [destruct (RS0 ST0) as (CE & _); unfold PM.CHUNK in CE; rewrite G2c, CE; clear - SZ; destruct (Z.min_spec 16384 (eg - g)) as [[X1 X2]|[X1 X2]]; rewrite X2; lia
                                 | destruct (RS2 ST2) as (CE & _); rewrite G2c, CE; clear - SZ; lia].
    - intros X. exact (proj2 (RS2 X)).
    - intros CZ. destruct IST as [ST0|ST2]; [destruct (RS0 ST0) as (_ & SE); rewrite SE, CZ; reflexivity| exact (proj2 (RS2 ST2))].
    - apply (PMASK.defined_dk L ar LB FF sp 20480 M1 M2 p len1 DK12); [intros i Hi; apply CLP; clear - Hi Hl1 Hl1k; lia| clear - DP0; lia| clear - DP1 Hl1k; lia| exact DP1'].
    - exact (L5SAR.ek_trans L ar LB FF sp 20480 WA M M1 M2 EK1 EK12).
    - exact (L5SAR.dk_trans L ar LB FF sp 20480 M M1 M2 DK1 DK12).
    - exact ASTK2.
    - exact HH2.
    - exact AM2.
    - eapply L5LZ.model_rt_trans; [exact MRT1| exact MRT2].
    - exact INC2.
    - exact INCA2. }
  (* [comment removed for export] *)
  assert (MEMC1 : forall (fx2 : FPState) (R2 : bvmap 5 word) (M2 : word -> option byte) (model2 : Model) (len1 : Z),
      getr R2 (reg 2) = Z_to_bv 64 (sp - 80) -> getr R2 (reg 8) = Z_to_bv 64 len1 -> getr R2 (reg 9) = Z_to_bv 64 os ->
      getr R2 (reg 18) = Z_to_bv 64 (os + 288) -> getr R2 (reg 19) = Z_to_bv 64 p -> getr R2 (reg 20) = Z_to_bv 64 (os + 280) ->
      getr R2 (reg 21) = Z_to_bv 64 k -> getr R2 (reg 22) = Z_to_bv 64 2147450880 -> getr R2 (reg 23) = Z_to_bv 64 ((os + 288) / 8 + 2147450880) ->
      (forall x, In x [3; 4; 24; 25; 26; 27]%nat -> getr R2 (reg x) = getr R (reg x)) ->
      L5.u64_at RSEGS M2 (sp - 8) (bv_unsigned (getr R (reg 1))) -> L5.u64_at RSEGS M2 (sp - 16) (bv_unsigned (getr R (reg 8))) ->
      L5.u64_at RSEGS M2 (sp - 24) (bv_unsigned (getr R (reg 9))) -> L5.u64_at RSEGS M2 (sp - 32) (bv_unsigned (getr R (reg 18))) ->
      L5.u64_at RSEGS M2 (sp - 40) (bv_unsigned (getr R (reg 19))) -> L5.u64_at RSEGS M2 (sp - 48) (bv_unsigned (getr R (reg 20))) ->
      L5.u64_at RSEGS M2 (sp - 56) (bv_unsigned (getr R (reg 21))) -> L5.u64_at RSEGS M2 (sp - 64) (bv_unsigned (getr R (reg 22))) ->
      L5.u64_at RSEGS M2 (sp - 72) (bv_unsigned (getr R (reg 23))) -> L5.u64_at RSEGS M2 (sp - 80) (bv_unsigned (getr R (reg 24))) ->
      L5.u64_at RSEGS M2 (os + 264) qc -> L5.u64_at RSEGS M2 (os + 272) 16384 -> L5.u64_at RSEGS M2 (os + 280) de -> L5.u64_at RSEGS M2 (os + 288) rem ->
      1 <= rem -> len1 = Z.min k rem -> L5.defined M2 p len1 ->
      L5SAR.ek L ar LB FF sp 20480 WA M M2 -> L5SAR.dk L ar LB FF sp 20480 M M2 -> L5CA.astk ar M2 sp 20480 -> PMSTA.base_okA RSEGS PMA.AD M2 ->
      PM.iss_at RSEGS PMA.AD PMSPA.accA M2 ois str (PM.STRM g eg sst) ->
      ri_inv HI LB FF LK cr Aw M2 (vml_of model2) -> L5CA.amodel_ok Aw model2 -> model_rt model model2 ->
      srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx2 R2 0xadb70 M2 model2) K).
  { intros fx2 R2 M2 model2 len1 Y2 Y8 Y9 Y18 Y19 Y20 Y21 Y22 Y23 KS2 C8 C16 C24 C32 C40 C48 C56 C64 C72 C80 C264 C272 C280 C288 Hr1' Hl1 DP2 EK2 DK2 ASTK2 BASE2 IA2 HH2 AM2 MRT2.
    assert (PA2 : PGS.ow_at O M2 (PM.SRC qc de rem) OB).
    { apply (OWU M2 de rem EK2 DK2 ASTK2 C264 C272 C280 C288); [exact G1| exact G2| exact G3]. }
    set (MV2 := mrestrict (ahid Aw model2) M2).
    pose proof (PGSKA.src_visG L ar C HI LY HIok LB FF LK cr Aw M2 model2 os _ _ _ sp 20480 HH2 AO O8 (proj1 (PGSA.oo_src _ _ _ _ _ _ OK M2 _ OB PA2)) (proj1 (proj2 (PGSA.oo_src _ _ _ _ _ _ OK M2 _ OB PA2))) ASTK2) as ((P1 & P8 & PBIG) & PZ & PW & PCE & PAV & _ & _).
    fold os MV2 in P1, P8, PBIG, PZ, PW, PCE, PAV.
    pose proof (PMASK.mach_vis L ar C HI LY HIok LB FF LK cr Aw M2 model2 HH2 BASE2) as (W0 & W1' & W2'). fold MV2 in W0, W1', W2'.
    pose proof (PMASK.stk_vis L ar C HI LY HIok LB FF LK cr Aw M2 model2 sp 20480 80 HH2 ASTK2 ltac:(lia)) as (_ & _ & W3). fold MV2 in W3.
    assert (VD2 : L5.defined MV2 (os + 256) 8).
    { apply (proj2 (L5A.defined_vis _ M2 (os + 256) 8 ltac:(apply PAV; lia))). pose proof (proj1 (PGSA.oo_src _ _ _ _ _ _ OK _ _ _ PA2)) as PS2.
      destruct PS2 as (_ & _ & SD2 & _). exact SD2. }
    pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw M2 model2 HH2) as (_ & VIS2s & _).
    assert (TS2 : forall kk v, 8 <= kk <= 80 -> L5.u64_at RSEGS M2 (sp - kk) v -> L5.u64_at RSEGS MV2 (sp - kk) v).
    { intros kk v Hkk X. apply (proj2 (L5A.u64_at_vis _ M2 (sp - kk) v (VIS2s (sp - kk) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact X. }
    set (VS := fun j => match j with 2%nat => sp | 33%nat => rem | 34%nat => qc | 35%nat => de | 36%nat => os | 37%nat => p | 38%nat => k | 39%nat => len1
                                | 64%nat => bv_unsigned (getr R (reg 1)) | 65%nat => bv_unsigned (getr R (reg 8)) | 66%nat => bv_unsigned (getr R (reg 9))
                                | 67%nat => bv_unsigned (getr R (reg 18)) | 68%nat => bv_unsigned (getr R (reg 19)) | 69%nat => bv_unsigned (getr R (reg 20))
                                | 70%nat => bv_unsigned (getr R (reg 21)) | 71%nat => bv_unsigned (getr R (reg 22)) | 72%nat => bv_unsigned (getr R (reg 23))
                                | 73%nat => bv_unsigned (getr R (reg 24)) | _ => 0 end).
    destruct (Z.eq_dec len1 k) as [LK1|LNK].
    - (* [comment removed for export] *)
      assert (Rr1 : 1 <= rem <= 16384) by (clear - Hr1' G3 G1; lia).
      assert (Rl1 : 1 <= len1 <= 16384) by (clear - LK1 Hk; lia).
      assert (Rr2 : 0 <= rem - len1 <= 16383) by (clear - Hl1 LK1 Rr1 Hk; rewrite LK1 in Hl1; destruct (Z.min_spec k rem) as [[X1 X2]|[X1 X2]]; lia).
      assert (Y21' : getr R2 (reg 21) = Z_to_bv 64 len1) by (rewrite LK1; exact Y21).
      (let T := type of (PMASRP.asrBeq_conc fx2 R2 MV2 VS) in let T := eval unfold VS in T in let T := eval cbn beta iota in T in LeanFeed.pfeed_at P (PMASRP.asrBeq_conc fx2 R2 MV2 VS) T ltac:(try (unfold VS); cbn beta iota) ltac:(idtac; first [assumption | lazymatch goal with
          | |- L5.u64_at _ _ (sp - _) _ => apply TS2; [L5FastLia.plia| assumption]
          | |- L5.u64_at _ _ (os + _) _ => unfold MV2; vis64 PAV
          | |- PMASRP.aligned _ _ => unfold PMASRP.aligned; L5FastLia.plia
          | |- _ \/ _ => right; L5FastLia.plia
          | |- _ => L5FastLia.plia end])).
      destruct P as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & Z1 & Z2 & Z8 & Z9 & Z10 & Z18 & Z19 & Z20 & Z21 & Z22 & Z23 & Z24
                     & V288 & V280 & V264 & V272 & _).
      unfold PMSPA.cfg, PMSP.cfg.
      apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr Aw M2 model2 fx2 fx3 R2 0xadb70 R3 0xade1c M3v W1 K HH2 AM2 MS3 MG3).
      { intros a Ha N. apply FRZ3; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
      { exact W1ok. }
      intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3.
      assert (EK23 : L5SAR.ek L ar LB FF sp 20480 [(os + 256, 40)] M2 M3) by exact (EKW1 M2 M3 LK Aw _ HH2 FR3).
      assert (TO3 : forall a v, os <= a -> a + 8 <= os + 296 -> L5.u64_at RSEGS M3v a v -> L5.u64_at RSEGS M3 a v).
      { intros a v Ha Hb X. rewrite <- VIS3 in X. apply (proj1 (L5A.u64_at_vis _ M3 a v ltac:(apply PAV; lia) ltac:(lia) ltac:(lia))). exact X. }
      apply (FIN fx3 R3 M3 model3 LK Aw (de + len1) (rem - len1) g sst len1).
      + rewrite Z1, Z_to_bv_bv_unsigned. exact Rra.
      + intros x Hx. unfold L5SAR.cs_all in Hx.
        repeat (destruct Hx as [<-|Hx];
          [ first [ match goal with H : getr R3 (reg ?y) = Z_to_bv 64 (bv_unsigned (getr R (reg ?y))) |- getr R3 (reg ?y) = _ => rewrite H, Z_to_bv_bv_unsigned; reflexivity end
                  | rewrite Z2; exact (eq_sym Rsp)
                  | rewrite (KS3 _) by inl; apply KS2; inl ] |]).
        destruct Hx.
      + exact Z10.
      + apply TO3; [lia| lia| exact V264].
      + apply TO3; [lia| lia| exact V272].
      + apply TO3; [lia| lia| exact V280].
      + apply TO3; [lia| lia| exact V288].
      + clear - G1 Rl1; lia.
      + clear - Rr2; lia.
      + clear - G3 Rl1; lia.
      + apply (PGSKA.src_piece_issG L ar C HI HIok LB FF LK cr Aw M2 M3 _ os ois str _ sp 20480 HH2 AO AOI LYD SOWN EK23 IA2).
      + pose proof (PMASK.iss_size_ltA M ois str _ IA) as SZ. cbn [PM.sm_g PM.sm_eg] in SZ. clear - SZ; lia.
      + intros X; exact X.
      + clear - LK1 Hk; lia.
      + clear; lia.
      + intros _; clear - Rl1; lia.
      + intros X. exfalso. clear - X Rl1; lia.
      + apply (L5.defined_grows M2 M3 p len1 MGM3 DP2).
      + apply (L5SAR.ek_trans L ar LB FF sp 20480 WA M M2 M3 EK2). apply EKWA. exact EK23.
      + apply (L5SAR.dk_trans L ar LB FF sp 20480 M M2 M3 DK2). apply L5SAR.dk_grows. exact MGM3.
      + apply (L5SAR.astk_grows ar M2 M3 sp 20480 ASTK2 MGM3).
      + exact HH3.
      + exact AM3.
      + eapply L5LZ.model_rt_trans; [exact MRT2| exact MRT3].
      + apply incl_refl.
      + apply incl_refl.
    - (* [comment removed for export] *)
      assert (LR : len1 = rem /\ rem < k) by (clear - Hl1 LNK; destruct (Z.min_spec k rem) as [[X1 X2]|[X1 X2]]; lia).
      destruct LR as (LR1 & LR2).
      assert (Rr1 : 1 <= len1 <= 16383) by (clear - Hr1' LR1 LR2 Hk; lia).
      assert (Rr2 : 2 <= k <= 16384) by (clear - Hr1' LR2 Hk; lia).
      assert (Rr3 : 1 <= k - len1 <= 16383) by (clear - Hr1' LR1 LR2 Hk; lia).
      assert (C288' : L5.u64_at RSEGS M2 (os + 288) len1) by (rewrite LR1; exact C288).
      (let T := type of (PMASRP.asrBne_conc fx2 R2 MV2 VS) in let T := eval unfold VS in T in let T := eval cbn beta iota in T in LeanFeed.pfeed_at P (PMASRP.asrBne_conc fx2 R2 MV2 VS) T ltac:(try (unfold VS); cbn beta iota) ltac:(idtac; first [assumption | lazymatch goal with
          | |- L5.u64_at _ _ (sp - _) _ => apply TS2; [L5FastLia.plia| assumption]
          | |- L5.u64_at _ _ (os + _) _ => unfold MV2; vis64 PAV
          | |- PMASRP.aligned _ _ => unfold PMASRP.aligned; L5FastLia.plia
          | |- _ \/ _ => right; L5FastLia.plia
          | |- _ => L5FastLia.plia end])).
      destruct P as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & Z1 & Z10 & Z11 & Z12 & Z21 & Z24 & V280 & V288 & V264 & V272 & PP). pdestr PP.
      unfold PMSPA.cfg, PMSP.cfg.
      apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr Aw M2 model2 fx2 fx3 R2 0xadb70 R3 0xb150c M3v W1 K HH2 AM2 MS3 MG3).
      { intros a Ha N. apply FRZ3; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
      { exact W1ok. }
      intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3.
      assert (EK23 : L5SAR.ek L ar LB FF sp 20480 [(os + 256, 40)] M2 M3) by exact (EKW1 M2 M3 LK Aw _ HH2 FR3).
      assert (TO3 : forall a v, os <= a -> a + 8 <= os + 296 -> L5.u64_at RSEGS M3v a v -> L5.u64_at RSEGS M3 a v).
      { intros a v Ha Hb X. rewrite <- VIS3 in X. apply (proj1 (L5A.u64_at_vis _ M3 a v ltac:(apply PAV; lia) ltac:(lia) ltac:(lia))). exact X. }
      pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw M3 model3 HH3) as (_ & VIS3s & _).
      assert (TS3 : forall kk v, 8 <= kk <= 80 -> L5.u64_at RSEGS M3v (sp - kk) v -> L5.u64_at RSEGS M3 (sp - kk) v).
      { intros kk v Hkk X. rewrite <- VIS3, <- HID3 in X.
        apply (proj1 (L5A.u64_at_vis _ M3 (sp - kk) v (VIS3s (sp - kk) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact X. }
      assert (KSB : forall x, In x [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 25; 26; 27]%nat -> getr R3 (reg x) = getr R2 (reg x)).
      { intros x Hx. apply KS3. revert x Hx. apply (PMASR1.sub_in PMASRP.KS_asrBne). vm_compute. reflexivity. }
      apply (FILLC fx3 R3 M3 model3 len1); try (apply TS3; [clear; lia| assumption]); try (apply TO3; [clear; lia| clear; lia| assumption]).
      + exact Z1. + rewrite (KSB 2%nat) by inl. exact Y2. + rewrite (KSB 8%nat) by inl. exact Y8. + rewrite (KSB 9%nat) by inl. exact Y9.
      + exact Z10. + exact Z11. + exact Z12.
      + rewrite (KSB 18%nat) by inl. exact Y18. + rewrite (KSB 19%nat) by inl. exact Y19. + rewrite (KSB 20%nat) by inl. exact Y20.
      + exact Z21. + rewrite (KSB 22%nat) by inl. exact Y22. + rewrite (KSB 23%nat) by inl. exact Y23. + exact Z24.
      + intros x Hx. rewrite (KSB x) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). apply KS2. revert x Hx. apply (PMASR1.sub_in [3; 4; 24; 25; 26; 27]%nat). vm_compute. reflexivity.
      + exact LR1.
      + clear - LR1 LR2; lia.
      + clear - Rr3; lia.
      + apply (L5.defined_grows M2 M3 p len1 MGM3 DP2).
      + apply (L5SAR.ek_trans L ar LB FF sp 20480 WA M M2 M3 EK2). apply EKWA. exact EK23.
      + apply (L5SAR.dk_trans L ar LB FF sp 20480 M M2 M3 DK2). apply L5SAR.dk_grows. exact MGM3.
      + apply (L5SAR.astk_grows ar M2 M3 sp 20480 ASTK2 MGM3).
      + apply (PMASK.base_keep L ar C LY LB FF sp 20480 WA M2 M3 (EKWA M2 M3 EK23) OUTIMG BASE2).
      + apply (PGSKA.src_piece_issG L ar C HI HIok LB FF LK cr Aw M2 M3 _ os ois str _ sp 20480 HH2 AO AOI LYD SOWN EK23 IA2).
      + exact HH3.
      + exact AM3.
      + eapply L5LZ.model_rt_trans; [exact MRT2| exact MRT3]. }
  (* [comment removed for export] *)
  assert (VD0 : L5.defined MV (os + 256) 8) by (apply (proj2 (L5A.defined_vis _ M (os + 256) 8 ltac:(apply OAV; lia))); exact SD256).
  assert (DEB : 4096 <= de <= 140737488338944) by (clear - G1 G2 G3 Q0 Q4 SLO SHI SPT; lia).
  set (W0 := fun a => sp - 80 <= a < sp - 80 + 80).
  assert (W0ok : forall a, 0 <= a < 2 ^ 64 -> W0 a -> aclientw L ar LB FF 0 0 a /\ ~ 65536 <= a < 6897664).
  { intros a Ha Wa. unfold W0 in Wa. split; [|intros X; clear - Wa X SL80 SPT; lia].
    unfold aclientw, aclient_g. right; left. split; [clear - Wa SL80 SH80; lia| intros X; clear - X; lia]. }
  assert (EKW0 : forall M0 M1 LK0 Aw0 Vv, ri_inv HI LB FF LK0 cr Aw0 M0 Vv -> (forall a, 0 <= a < 2 ^ 64 -> ~ W0 a -> M1 (Z_to_bv 64 a) = M0 (Z_to_bv 64 a)) ->
                 L5SAR.ek L ar LB FF sp 20480 [] M0 M1).
  { intros M0 M1 LK0 Aw0 Vv HH0 FR. apply (L5SAR.ek_piece L ar LB FF sp 20480 [] M0 M1 W0 FR). intros a Ha CL Oq X.
    destruct (L5SAR.aclient_cases L ar C HI LYa HIok LB FF LK0 cr Aw0 M0 _ sp 20480 a HH0 SPT CL) as [(Y1 & Y2)|Y]; [apply Y2; unfold W0 in X; clear - X; lia| unfold W0 in X; clear - X Y SL80; lia]. }
  unfold PMSPA.cfg, PMSP.cfg. cbn [pa_src_read PMA.AD ADDR_A].
  destruct (Z.eq_dec rem 0) as [RZ|RNZ].
  { (* [comment removed for export] *)
    subst rem.
    destruct (Z.eq_dec k 16384) as [KF|KNF].
    { (* [comment removed for export] *)
      subst k. destruct (D16K eq_refl) as (q0 & c0 & BIN0 & Dq1 & Dq2). pose proof (OBIN q0 c0 BIN0) as TIN.
      destruct IST as [ST0|ST2].
      2:{ (* [comment removed for export] *)
        subst sst.
        LeanFeed.pfeed P (PMASRP.asrA0e_conc fx R MV (fun j => match j with 2%nat => sp | 34%nat => qc | 35%nat => de | 36%nat => os | 37%nat => p | 45%nat => ois | _ => 0 end)) ltac:(idtac; first [assumption | lazymatch goal with
            | |- L5.u64_at _ _ (os + _) _ => unfold MV; vis64 OAV
            | |- L5.u64_at _ _ (ois + _) _ => unfold MV; vis64 IAV
            | |- L5.u64_at _ _ ois _ => unfold MV; apply (proj2 (L5A.u64_at_vis _ M ois _ ltac:(apply IAV; lia) ltac:(lia) ltac:(lia))); assumption
            | |- L5.u32_at _ _ (ois + _) _ => unfold MV; vis32 IAV
            | |- PMASRP.aligned _ _ => unfold PMASRP.aligned; L5FastLia.plia
            | |- _ \/ _ => right; L5FastLia.plia
            | |- _ => L5FastLia.plia end]).
        destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & Z10 & Z11 & Z12 & V288 & PP). pdestr PP.
        apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr Aw M model fx fx1 R 0xadae0 R1 0xade1c M1v W1 K HH AM MS1 MG1).
        { intros a Ha N. apply FRZ1; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
        { exact W1ok. }
        intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
        assert (EK01 : L5SAR.ek L ar LB FF sp 20480 [(os + 256, 40)] M M1) by exact (EKW1 M M1 LK Aw _ HH FR1).
        assert (TO1 : forall a v, os <= a -> a + 8 <= os + 296 -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v).
        { intros a v Ha Hb X. rewrite <- VIS1 in X. apply (proj1 (L5A.u64_at_vis _ M1 a v ltac:(apply OAV; lia) ltac:(lia) ltac:(lia))). exact X. }
        assert (KSA : forall x, In x L5SAR.cs_all -> getr R1 (reg x) = getr R (reg x)).
        { intros x Hx. apply KS1. revert x Hx. apply (PMASR1.sub_in PMASRP.KS_asrA0e). vm_compute. reflexivity. }
        apply (FIN fx1 R1 M1 model1 LK Aw de 0 g 2 0).
        + rewrite (KS1 1%nat) by inl. exact Rra.
        + exact KSA.
        + exact Z10.
        + apply TO1; [lia| lia| assumption].
        + apply TO1; [lia| lia| assumption].
        + apply TO1; [lia| lia| assumption].
        + apply TO1; [lia| lia| exact V288].
        + exact G1.
        + clear; lia.
        + clear - G3; lia.
        + apply (PGSKA.src_piece_issG L ar C HI HIok LB FF LK cr Aw M M1 _ os ois str _ sp 20480 HH AO AOI LYD SOWN EK01 IA).
        + pose proof (PMASK.iss_size_ltA M ois str _ IA) as SZ. cbn [PM.sm_g PM.sm_eg] in SZ. clear - SZ; lia.
        + intros X; exact X.
        + clear; lia.
        + clear; lia.
        + intros X. exfalso. clear - X; lia.
        + intros _. split; reflexivity.
        + intros i Hi. exfalso. clear - Hi; lia.
        + apply EKWA. exact EK01.
        + apply L5SAR.dk_grows. exact MGM1.
        + apply (L5SAR.astk_grows ar M M1 sp 20480 ASTK MGM1).
        + exact HH1.
        + exact AM1.
        + exact MRT1.
        + apply incl_refl.
        + apply incl_refl. }
      subst sst.
      LeanFeed.pfeed P (PMASRP.asrA0d_conc fx R MV (fun j => match j with 2%nat => sp | 34%nat => qc | 35%nat => de | 36%nat => os | 37%nat => p | 45%nat => ois | _ => 0 end)) ltac:(idtac; first [assumption | lazymatch goal with
          | |- L5.u64_at _ _ (os + _) _ => unfold MV; vis64 OAV
          | |- L5.u64_at _ _ (ois + _) _ => unfold MV; vis64 IAV
          | |- L5.u64_at _ _ ois _ => unfold MV; apply (proj2 (L5A.u64_at_vis _ M ois _ ltac:(apply IAV; lia) ltac:(lia) ltac:(lia))); assumption
          | |- L5.u32_at _ _ (ois + _) _ => unfold MV; vis32 IAV
          | |- PMASRP.aligned _ _ => unfold PMASRP.aligned; L5FastLia.plia
          | |- _ \/ _ => right; L5FastLia.plia
          | |- _ => L5FastLia.plia end]).
      destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & T13 & T18 & T19 & T20 & T21 & T22 & T23 & T24
                     & S80 & S72 & S64 & S56 & S48 & S40 & S32 & S24 & S16 & S8).
      apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr Aw M model fx fx1 R 0xadae0 R1 0xd8254 M1v W0 K HH AM MS1 MG1).
      { intros a Ha N. apply FRZ1; [exact Ha| exact N]. }
      { exact W0ok. }
      intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
      assert (EK01 : L5SAR.ek L ar LB FF sp 20480 [] M M1) by exact (EKW0 M M1 LK Aw _ HH FR1).
      pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw M1 model1 HH1) as (_ & VIS1s & _).
      assert (TS1 : forall kk v, 8 <= kk <= 80 -> L5.u64_at RSEGS M1v (sp - kk) v -> L5.u64_at RSEGS M1 (sp - kk) v).
      { intros kk v Hkk X. rewrite <- VIS1, <- HID1 in X.
        apply (proj1 (L5A.u64_at_vis _ M1 (sp - kk) v (VIS1s (sp - kk) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact X. }
      assert (ASTK1 : L5CA.astk ar M1 sp 20480) by (apply (L5SAR.astk_grows ar M M1 sp 20480 ASTK MGM1)).
      assert (OS1 : forall a, os <= a < os + 296 -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
      { intros a Ha. apply FR1; [clear - Ha O1; lia| unfold W0; clear - Ha OCE SL80 SLO; lia]. }
      assert (IA1 : PM.iss_at RSEGS PMA.AD PMSPA.accA M1 ois str (PM.STRM g eg 0)).
      { apply (PMKA.iss_keepA RSEGS PMA.AD L ar LB FF sp 20480 _ M M1 EK01 PMKA.wapp_nil FRB BRB ois str _ AOI SOWN); [intros i _ r0 []| intros c1 n1 p1 _ i _ r0 []| exact IA]. }
      assert (BASE1 : PMSTA.base_okA RSEGS PMA.AD M1) by (apply (PMASK.base_keep L ar C LY LB FF sp 20480 _ M M1 EK01); [intros a _ r0 []| exact BASE]).
      assert (M8a : (sp - 20480) mod 8 = 0) by (apply PMKA.mod16_8'; replace (sp - 20480) with (sp + (-1280) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact A16).
      assert (M8b : (sp - 80 - 16384) mod 8 = 0) by (apply PMKA.mod16_8'; replace (sp - 80 - 16384) with (sp + (-1029) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact A16).
      assert (STK1 : shadow_zero M1 (sp - 80 - 16384) (16384 / 8)).
      { change (16384 / 8) with 2048. change (20480 / 8) with 2560 in STKSH.
        apply (PMKA.shadow_zero_sub M1 (sp - 20480) 2560); [exact M8a| exact M8b| clear; lia| clear; lia| clear; lia|].
        apply (PMKA.stksh_keepA L ar LB FF sp 20480 [] M M1 EK01 PMKA.wapp_nil (sp - 20480) 2560); [clear - SLO SPT; lia| clear - SLO; lia| clear - SHI SPT; lia| exact M8a| clear; lia| exact STKSH]. }
      (* [comment removed for export] *)
      assert (APG : p + 16384 <= g \/ eg <= p).
      { pose proof (PMASK.iss_unread_whereA M ois str _ IA) as [(Y1 & Y2)|(c1 & n1 & q1 & E & Y1 & Y2)]; cbn [PM.sm_g PM.sm_eg] in *.
        - destruct (PMASK.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ q0 c0 ois 272 HH TIN AOI) as [Z1|Z1]; clear - Y1 Y2 Z1 Dq1 Dq2; Lia.lia.
        - assert (NS : q0 <> q1) by (apply (PMASK.fst_neq_appA ((qc, 16384) :: OB) LBX q0 c0 q1 c1); [exact ND| right; exact BIN0| exact (STbX c1 n1 q1 E)]).
          destruct (PMASK.blk_apart L ar C HI HIok LB FF LK cr Aw M _ q0 c0 q1 c1 HH TIN (STb c1 n1 q1 E) NS) as [Z1|Z1]; clear - Y1 Y2 Z1 Dq1 Dq2; Lia.lia. }
      unfold PMA.xsgetn_spec, PMSPA.xsgetn_spec in XS. cbn [pa_xsgetn PMA.AD ADDR_A] in XS.
      apply (XS fx1 R1 M1 model1 K LB FF LK Aw cr (sp - 80) 712008 ois p str (PM.STRM g eg 0) HH1 AM1 K0).
      { split; [rewrite L5K.rl1; exact T1|]. split; [split; [clear; lia| reflexivity]|]. split; [rewrite L5K.rl2; exact T2|].
        split; [rewrite L5K.rl3; rewrite (KS1 3%nat) by inl; exact Rgp|]. split; [rewrite L5K.rl4; rewrite (KS1 4%nat) by inl; exact Rtp|].
        change (PMSPA.pm_scr 2) with 16384. split; [|exact STK1].
        apply (L5SAR.astk_sub ar M1 M1 sp 20480 80 16384 ASTK1 (fun _ X => X)); [clear; lia| clear; lia| clear; lia|].
        replace (sp - 80) with (sp + (-5) * 16) by (clear; lia). rewrite Z.mod_add by (clear; lia). exact A16. }
      { intros kk Hkk. specialize (FRM kk Hkk). clear - FRM. lia. }
      { intros f Hf. specialize (FRS f Hf). clear - FRS. lia. }
      { rewrite L5K.rl10. exact T10. }
      { rewrite L5SAR.r11. rewrite (KS1 11%nat) by inl. exact A11. }
      { rewrite L5SAR.r12. rewrite (KS1 12%nat) by inl. exact A12. }
      { exact AOI. }
      { exact I8. }
      { exact IA1. }
      { exact BASE1. }
      { exact SOWN. }
      { exists q0, c0. split; [exact TIN| unfold PM.CHUNK; split; [exact Dq1| exact Dq2]]. }
      { unfold PM.CHUNK. intros a Ha. apply (PMFA.accA_agree M M1 p 16384 (AGSHP M M1 [] EK01 PMKA.wapp_nil) DAP a). exact Ha. }
      { cbn [PM.sm_g PM.sm_eg]. unfold PM.CHUNK. exact APG. }
      intros fx2 R2 M2 model2 LK2 Aw2 c RP2 A10c Hc IA2 D2 HP2 MRT2 INC2 INCA2 AM2 HH2.
      change (PMSPA.pm_scr 2) with 16384 in HP2. unfold PM.CHUNK in Hc, HP2. cbn [PM.sm_g PM.sm_eg PM.sm_st] in Hc, IA2. rewrite L5K.rl10 in A10c.
      assert (C0 : 0 <= c <= 16384 /\ g + c <= eg).
      { pose proof (PMASK.iss_size_ltA M ois str _ IA) as SZ. cbn [PM.sm_g PM.sm_eg] in SZ. rewrite Hc. clear - SZ.
        destruct (Z.min_spec 16384 (eg - g)) as [[X1 X2]|[X1 X2]]; rewrite X2; lia. }
      assert (OUTX : forall a, aclient L ar LB FF sp 20480 a -> L5.outside WA a -> L5.outside [(ois + 40, 8); (p, 16384)] a).
      { intros a _ Oq r0 [<-|[<-|[]]] X.
        - apply (Oq (ois + 40, 8)); [unfold WA, PGS.W_srcG, PGS.W_srcfG; cbn [PM.sr_qc app]; right; left; reflexivity| exact X].
        - apply (Oq (p, 16384)); [unfold WA; apply in_or_app; right; left; reflexivity| exact X]. }
      assert (EK12 : L5SAR.ek L ar LB FF sp 20480 WA M1 M2).
      { apply (L5SAR.ek_callee L ar LB [] FF [] sp 20480 (sp - 80) 16384 WA _ M1 M2 HP2); [clear; lia| clear; lia| exact OUTX]. }
      assert (DK12 : L5SAR.dk L ar LB FF sp 20480 M1 M2) by (apply (L5SAR.dk_callee L ar LB [] FF [] sp 20480 (sp - 80) 16384 _ M1 M2 HP2); clear; lia).
      assert (ASTK2 : L5CA.astk ar M2 sp 20480) by (apply (PMKA.astk_after_ahpres L ar LB FF M1 M2 sp 20480 (sp - 80) 16384 _ ASTK1 HP2); clear - TOP; lia).
      assert (KF2 : forall a, sp - 80 <= a < sp -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
      { intros a Ha. destruct HP2 as (E & _). apply E. split; [clear - Ha SLO SHI SPT; lia|]. split.
        - apply (L5SAR.stack_client L ar LB FF (sp - 80) 16384 a); clear - Ha SL80 SHI SPT; lia.
        - intros r0 [<-|[<-|[]]]; unfold L5.in_rng; cbn [fst snd]; [clear - Ha ICE SL80 SLO; lia|].
          intros Y. destruct (DX a Y) as (X1 & _). apply X1. clear - Ha; lia. }
      assert (KO2 : forall a, os <= a < os + 296 -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
      { intros a Ha. destruct HP2 as (E & _). apply E. split; [clear - Ha O1; lia|]. split.
        - apply PMASR1.cl_of_bf. right. apply (PMASR1.in_fframe_of_aobjA FF os 296 a AO). clear - Ha; lia.
        - intros r0 [<-|[<-|[]]]; unfold L5.in_rng; cbn [fst snd]; [clear - Ha LYD; lia|].
          intros Y. destruct (DX a Y) as (_ & _ & X3 & _). apply X3. clear - Ha; lia. }
      assert (CO : forall a v, os <= a -> a + 8 <= os + 296 -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M2 a v).
      { intros a v Ha Hb X. apply (L5C.u64_at_agree RSEGS M M2); [intros i Hi; rewrite KO2, OS1 by (clear - Ha Hb Hi; lia); reflexivity| clear - Ha O1; lia| clear - Hb O1; lia| exact X]. }
      assert (EK02 : L5SAR.ek L ar LB FF sp 20480 WA M M2).
      { apply (L5SAR.ek_trans L ar LB FF sp 20480 WA M M1 M2); [| exact EK12]. apply (L5SAR.ek_W L ar LB FF sp 20480 WA [] M M1 EK01). intros a _ r0 []. }
      assert (DK02 : L5SAR.dk L ar LB FF sp 20480 M M2) by (apply (L5SAR.dk_trans L ar LB FF sp 20480 M M1 M2); [apply L5SAR.dk_grows; exact MGM1| exact DK12]).
      assert (PA2 : PGS.ow_at O M2 (PM.SRC qc de 0) OB).
      { apply (OWU M2 de 0 EK02 DK02 ASTK2); [apply CO; [clear; lia| clear; lia| exact S264]| apply CO; [clear; lia| clear; lia| exact S272]
                                       | apply CO; [clear; lia| clear; lia| exact S280]| apply CO; [clear; lia| clear; lia| exact S288]| exact G1| clear; lia| clear - G3; lia]. }
      assert (BASE2 : PMSTA.base_okA RSEGS PMA.AD M2) by (apply (PMASK.base_keep L ar C LY LB FF sp 20480 WA M1 M2 EK12 OUTIMG BASE1)).
      set (MV2 := mrestrict (ahid Aw2 model2) M2).
      pose proof (PGSKA.src_visG L ar C HI LY HIok LB FF LK2 cr Aw2 M2 model2 os _ _ _ sp 20480 HH2 AO O8 (proj1 (PGSA.oo_src _ _ _ _ _ _ OK M2 _ OB PA2)) (proj1 (proj2 (PGSA.oo_src _ _ _ _ _ _ OK M2 _ OB PA2))) ASTK2) as ((P1 & P8 & PBIG) & PZ & PW & PCE & PAV & _ & _).
      fold os MV2 in P1, P8, PBIG, PZ, PW, PCE, PAV.
      pose proof (PGSKA.iss_visG L ar C HI LY HIok LB FF LK2 cr Aw2 M2 model2 ois str _ sp 20480 HH2 AOI I8 IA2 ASTK2) as ((J1 & J8 & JBIG) & JZ & JW & JCE & JAV & _).
      fold ois MV2 in J1, J8, JBIG, JZ, JW, JCE, JAV.
      pose proof (PMASK.mach_vis L ar C HI LY HIok LB FF LK2 cr Aw2 M2 model2 HH2 BASE2) as (W0' & W1' & W2'). fold MV2 in W0', W1', W2'.
      pose proof (PMASK.stk_vis L ar C HI LY HIok LB FF LK2 cr Aw2 M2 model2 sp 20480 80 HH2 ASTK2 ltac:(lia)) as (_ & _ & W3'). fold MV2 in W3'.
      pose proof (PMASK.img_shz_vis L ar C HI LY IL ICok ILY LB FF LK2 cr Aw2 M2 model2 0x132c30 1 HH2 ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia)) as VT1'.
      pose proof (PMASK.img_shz_vis L ar C HI LY IL ICok ILY LB FF LK2 cr Aw2 M2 model2 0x132b98 1 HH2 ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia)) as VT2'.
      cbn in VT1', VT2'. fold MV2 in VT1', VT2'.
      pose proof IA2 as (H0j & _ & _ & H16j & _ & _ & _ & _ & _ & _ & _ & _ & IOSBj & _ & _).
      destruct IOSBj as (I0j & I32j & I36j & I40j & _ & _ & _ & _ & _).
      cbn [PM.sm_g PM.sm_eg PM.sm_st pa_vp_iss pa_vp_strbuf pa_vp_iss_ios PMA.AD ADDR_A] in H0j, H16j, I0j, I32j, I36j, I40j.
      replace (ois + 120 + 32) with (ois + 152) in I32j by lia. replace (ois + 120 + 36) with (ois + 156) in I36j by lia.
      replace (ois + 120 + 40) with (ois + 160) in I40j by lia.
      assert (S264' : L5.u64_at RSEGS M2 (os + 264) qc) by (apply CO; [clear; lia| clear; lia| exact S264]).
      assert (S272' : L5.u64_at RSEGS M2 (os + 272) 16384) by (apply CO; [clear; lia| clear; lia| exact S272]).
      assert (S280' : L5.u64_at RSEGS M2 (os + 280) de) by (apply CO; [clear; lia| clear; lia| exact S280]).
      assert (S288' : L5.u64_at RSEGS M2 (os + 288) 0) by (apply CO; [clear; lia| clear; lia| exact S288]).
      assert (S240' : L5.u64_at RSEGS M2 (os + 240) ois) by (apply CO; [clear; lia| clear; lia| exact S240]).
      assert (S248' : L5.u64_at RSEGS M2 (os + 248) (ois + 16)) by (apply CO; [clear; lia| clear; lia| exact S248]).
      pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK2 cr Aw2 M2 model2 HH2) as (_ & VIS2s & _).
      assert (TS2 : forall kk v, 8 <= kk <= 80 -> L5.u64_at RSEGS M1v (sp - kk) v -> L5.u64_at RSEGS MV2 (sp - kk) v).
      { intros kk v Hkk X. apply (proj2 (L5A.u64_at_vis _ M2 (sp - kk) v (VIS2s (sp - kk) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
        apply (L5C.u64_at_agree RSEGS M1 M2); [intros i Hi; apply KF2; clear - Hkk Hi; lia| clear - Hkk SLO SHI SPT; lia| clear - Hkk SLO SHI SPT; lia|].
        apply TS1; [exact Hkk| exact X]. }
      assert (VD2 : L5.defined MV2 (os + 256) 8).
      { apply (proj2 (L5A.defined_vis _ M2 (os + 256) 8 ltac:(apply PAV; lia))). pose proof (proj1 (PGSA.oo_src _ _ _ _ _ _ OK _ _ _ PA2)) as PS2.
        destruct PS2 as (_ & _ & SD2 & _). exact SD2. }
      assert (RG : forall x, In x L5SAR.cs_all -> getr R2 (reg x) = getr R1 (reg x)) by (intros x Hx; apply (L5SAR.cs_of_preserved R1 R2 x RP2 Hx)).
      assert (Y2 := T2). rewrite <- (RG 2%nat ltac:(inl)) in Y2. assert (Y8 := T8). rewrite <- (RG 8%nat ltac:(inl)) in Y8.
      assert (Y9 := T9). rewrite <- (RG 9%nat ltac:(inl)) in Y9. assert (Y18 := T18). rewrite <- (RG 18%nat ltac:(inl)) in Y18.
      assert (Y19 := T19). rewrite <- (RG 19%nat ltac:(inl)) in Y19. assert (Y20 := T20). rewrite <- (RG 20%nat ltac:(inl)) in Y20.
      assert (Y21 := T21). rewrite <- (RG 21%nat ltac:(inl)) in Y21. assert (Y22 := T22). rewrite <- (RG 22%nat ltac:(inl)) in Y22.
      assert (Y23 := T23). rewrite <- (RG 23%nat ltac:(inl)) in Y23. assert (Y24 := T24). rewrite <- (RG 24%nat ltac:(inl)) in Y24.
      set (VE := fun j => match j with 2%nat => sp | 33%nat => c | 34%nat => qc | 35%nat => de | 36%nat => os | 37%nat => p | 45%nat => ois
                                | 64%nat => bv_unsigned (getr R (reg 1)) | 65%nat => bv_unsigned (getr R (reg 8)) | 66%nat => bv_unsigned (getr R (reg 9))
                                | 67%nat => bv_unsigned (getr R (reg 18)) | 68%nat => bv_unsigned (getr R (reg 19)) | 69%nat => bv_unsigned (getr R (reg 20))
                                | 70%nat => bv_unsigned (getr R (reg 21)) | 71%nat => bv_unsigned (getr R (reg 22)) | 72%nat => bv_unsigned (getr R (reg 23))
                                | 73%nat => bv_unsigned (getr R (reg 24)) | _ => 0 end).
      destruct (Z.eq_dec c 16384) as [CF|CNF].
      - (* [comment removed for export] *)
        rewrite CF in A10c, D2, C0, IA2.
        (let T := type of (PMASRP.asrE1_conc fx2 R2 MV2 VE) in let T := eval unfold VE in T in let T := eval cbn beta iota in T in LeanFeed.pfeed_at P (PMASRP.asrE1_conc fx2 R2 MV2 VE) T ltac:(try (unfold VE); cbn beta iota) ltac:(idtac; first [assumption | lazymatch goal with
            | |- L5.u64_at _ _ (sp - _) _ => apply TS2; [L5FastLia.plia| assumption]
            | |- L5.u64_at _ _ (os + _) _ => unfold MV2; vis64 PAV
            | |- L5.u64_at _ _ (ois + _) _ => unfold MV2; vis64 JAV
            | |- L5.u64_at _ _ ois _ => unfold MV2; apply (proj2 (L5A.u64_at_vis _ M2 ois _ ltac:(apply JAV; lia) ltac:(lia) ltac:(lia))); assumption
            | |- L5.u32_at _ _ (ois + _) _ => unfold MV2; vis32 JAV
            | |- PMASRP.aligned _ _ => unfold PMASRP.aligned; L5FastLia.plia
            | |- _ \/ _ => right; L5FastLia.plia
            | |- _ => L5FastLia.plia end])).
        destruct P as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & Z1 & Z2 & Z8 & Z9 & Z18 & Z19 & Z20 & Z21 & Z22 & Z23 & Z24
                       & V264 & V272 & V280 & V288 & _).
        apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK2 cr Aw2 M2 model2 fx2 fx3 R2 0xadd48 R3 0xade1c M3v W1 K HH2 AM2 MS3 MG3).
        { intros a Ha N. apply FRZ3; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
        { exact W1ok. }
        intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3.
        assert (EK23 : L5SAR.ek L ar LB FF sp 20480 [(os + 256, 40)] M2 M3) by exact (EKW1 M2 M3 LK2 Aw2 _ HH2 FR3).
        assert (TO3 : forall a v, os <= a -> a + 8 <= os + 296 -> L5.u64_at RSEGS M3v a v -> L5.u64_at RSEGS M3 a v).
        { intros a v Ha Hb X. rewrite <- VIS3 in X. apply (proj1 (L5A.u64_at_vis _ M3 a v ltac:(apply PAV; lia) ltac:(lia) ltac:(lia))). exact X. }
        apply (FIN fx3 R3 M3 model3 LK2 Aw2 de 0 (g + 16384) 0 16384).
        + rewrite Z1, Z_to_bv_bv_unsigned. exact Rra.
        + intros x Hx. unfold L5SAR.cs_all in Hx.
          repeat (destruct Hx as [<-|Hx];
            [ first [ match goal with H : getr R3 (reg ?y) = Z_to_bv 64 (bv_unsigned (getr R (reg ?y))) |- getr R3 (reg ?y) = _ => rewrite H, Z_to_bv_bv_unsigned; reflexivity end
                    | rewrite Z2; exact (eq_sym Rsp)
                    | rewrite (KS3 _) by inl; rewrite (RG _) by inl; apply KS1; inl ] |]).
          destruct Hx.
        + rewrite (KS3 10%nat) by inl. exact A10c.
        + apply TO3; [lia| lia| exact V264].
        + apply TO3; [lia| lia| exact V272].
        + apply TO3; [lia| lia| exact V280].
        + apply TO3; [lia| lia| exact V288].
        + exact G1.
        + clear; lia.
        + clear - G3; lia.
        + apply (PGSKA.src_piece_issG L ar C HI HIok LB FF LK2 cr Aw2 M2 M3 _ os ois str _ sp 20480 HH2 AO AOI LYD SOWN EK23 IA2).
        + clear - C0; lia.
        + intros X; exact X.
        + clear; lia.
        + clear; lia.
        + intros X. exfalso. clear - X; lia.
        + intros X. exfalso. clear - X; lia.
        + apply (L5.defined_grows M2 M3 p 16384 MGM3 D2).
        + apply (L5SAR.ek_trans L ar LB FF sp 20480 WA M M2 M3 EK02). apply EKWA. exact EK23.
        + apply (L5SAR.dk_trans L ar LB FF sp 20480 M M2 M3 DK02). apply L5SAR.dk_grows. exact MGM3.
        + apply (L5SAR.astk_grows ar M2 M3 sp 20480 ASTK2 MGM3).
        + exact HH3.
        + exact AM3.
        + eapply L5LZ.model_rt_trans; [exact MRT1|]. eapply L5LZ.model_rt_trans; [exact MRT2| exact MRT3].
        + exact INC2.
        + exact INCA2.
      - (* [comment removed for export] *)
        assert (Cr : 0 <= c <= 16383) by (clear - C0 CNF; lia).
        (let T := type of (PMASRP.asrE2_conc fx2 R2 MV2 VE) in let T := eval unfold VE in T in let T := eval cbn beta iota in T in LeanFeed.pfeed_at P (PMASRP.asrE2_conc fx2 R2 MV2 VE) T ltac:(try (unfold VE); cbn beta iota) ltac:(idtac; first [assumption | lazymatch goal with
            | |- L5.u64_at _ _ (sp - _) _ => apply TS2; [L5FastLia.plia| assumption]
            | |- L5.u64_at _ _ (os + _) _ => unfold MV2; vis64 PAV
            | |- L5.u64_at _ _ (ois + _) _ => unfold MV2; vis64 JAV
            | |- L5.u64_at _ _ ois _ => unfold MV2; apply (proj2 (L5A.u64_at_vis _ M2 ois _ ltac:(apply JAV; lia) ltac:(lia) ltac:(lia))); assumption
            | |- L5.u32_at _ _ (ois + _) _ => unfold MV2; vis32 JAV
            | |- PMASRP.aligned _ _ => unfold PMASRP.aligned; L5FastLia.plia
            | |- _ \/ _ => right; L5FastLia.plia
            | |- _ => L5FastLia.plia end])).
        destruct P as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & Z1 & Z2 & Z8 & Z9 & Z12 & Z13 & Z18 & Z19 & Z20 & Z21 & Z22 & Z23 & Z24
                       & V152 & V264 & V272 & V280 & V288 & _).
        set (W2 := fun a => (sp - 80 <= a < sp - 80 + 80) \/ (os + 256 <= a < os + 256 + 40) \/ (ois + 152 <= a < ois + 152 + 4)).
        assert (W2ok : forall a, 0 <= a < 2 ^ 64 -> W2 a -> aclientw L ar LB FF 0 0 a /\ ~ 65536 <= a < 6897664).
        { intros a Ha Wa. destruct Wa as [Wa|[Wa|Wa]]; [apply W1ok; [exact Ha| left; exact Wa]| apply W1ok; [exact Ha| right; exact Wa]|].
          split; [|intros X; clear - Wa X I1; lia].
          unfold aclientw, aclient_g. do 3 right. left. destruct AOI as (f & Hf & X1 & X2). exists f. split; [exact Hf|]. split; [clear - Wa X1 X2; lia| intros X; clear - Wa X X1; lia]. }
        apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK2 cr Aw2 M2 model2 fx2 fx3 R2 0xadd48 R3 0xade1c M3v W2 K HH2 AM2 MS3 MG3).
        { intros a Ha N. apply FRZ3; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; left; exact X| intros X; apply N; right; right; exact X]. }
        { exact W2ok. }
        intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3.
        set (WE := [(os + 256, 40); (ois + 152, 4)]).
        assert (EK23 : L5SAR.ek L ar LB FF sp 20480 WE M2 M3).
        { apply (L5SAR.ek_piece L ar LB FF sp 20480 WE M2 M3 W2 FR3). intros a Ha CL Oq [X|[X|X]].
          - destruct (L5SAR.aclient_cases L ar C HI LYa HIok LB FF LK2 cr Aw2 M2 _ sp 20480 a HH2 SPT CL) as [(Yc1 & Yc2)|Yc]; [apply Yc2; clear - X; lia| clear - X Yc SL80; lia].
          - apply (Oq (os + 256, 40)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - X; lia].
          - apply (Oq (ois + 152, 4)); [right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - X; lia]. }
        assert (WSE : PMKA.wapp WE).
        { unfold WE. apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI in *; clear - OBIG; Lia.lia|].
          apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI in *; clear - IBIG; Lia.lia| apply PMKA.wapp_nil]. }
        assert (EK23W : L5SAR.ek L ar LB FF sp 20480 WA M2 M3).
        { apply (L5SAR.ek_W L ar LB FF sp 20480 WA WE M2 M3 EK23). intros a Oq r0 [<-|[<-|[]]] X.
          - apply (Oq (os + 256, 40)); [unfold WA, PGS.W_srcG, PGS.W_srcfG; cbn [PM.sr_qc app]; left; reflexivity| exact X].
          - apply (Oq (ois + 152, 4)); [unfold WA, PGS.W_srcG, PGS.W_srcfG; cbn [PM.sr_qc app]; right; right; left; reflexivity| exact X]. }
        assert (TO3 : forall a v, os <= a -> a + 8 <= os + 296 -> L5.u64_at RSEGS M3v a v -> L5.u64_at RSEGS M3 a v).
        { intros a v Ha Hb X. rewrite <- VIS3 in X. apply (proj1 (L5A.u64_at_vis _ M3 a v ltac:(apply PAV; lia) ltac:(lia) ltac:(lia))). exact X. }
        assert (U152 : L5.u32_at RSEGS M3 (ois + 152) 2).
        { rewrite <- VIS3 in V152. apply (proj1 (L5A.u32_at_vis _ M3 (ois + 152) 2 ltac:(apply JAV; lia) ltac:(lia) ltac:(lia))). exact V152. }
        assert (OUTI : forall i, ois <= i < ois + 272 -> ~ (ois + 152 <= i < ois + 156) -> L5.outside WE i).
        { intros i Hi N r0 [<-|[<-|[]]]; unfold L5.in_rng; cbn [fst snd]; [clear - Hi LYD; lia| clear - N; lia]. }
        assert (IA3 : PM.iss_at RSEGS PMA.AD PMSPA.accA M3 ois str (PM.STRM (g + c) eg 2)).
        { apply (PMASK.iss_st_updA M2 M3 ois str (g + c) eg 0 2 IA2); [clear - J1; lia| clear - J1; lia| | | | exact MGM3| | exact U152| right; reflexivity].
          - apply (PMKA.agA_obj L ar LB FF sp 20480 WE M2 M3 EK23 WSE FRB ois 152); [apply (PGSKA.aobjA_sub FF lo hi); [exact OFR| clear - LY3; lia| clear - LY4; lia]|].
            intros i Hi. apply OUTI; clear - Hi; lia.
          - apply (PMKA.agA_obj L ar LB FF sp 20480 WE M2 M3 EK23 WSE FRB (ois + 156) 116); [apply (PGSKA.aobjA_sub FF lo hi); [exact OFR| clear - LY3; lia| clear - LY4; lia]|].
            intros i Hi. apply OUTI; clear - Hi; lia.
          - apply (PMKA.agsh_obj L ar LB FF sp 20480 WE M2 M3 EK23 WSE FRB (ois + 152) 4). apply (PGSKA.aobjA_sub FF lo hi); [exact OFR| clear - LY3; lia| clear - LY4; lia].
          - intros c1 n1 q1 E. assert (SIN : In (q1, c1) LB) by (apply SOWN; rewrite E; left; reflexivity).
            apply (PMKA.agA_blk L ar LB FF sp 20480 WE M2 M3 EK23 WSE BRB q1 c1 SIN). intros i Hi r0 [<-|[<-|[]]]; unfold L5.in_rng; cbn [fst snd].
            + destruct (PMASK.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ q1 c1 os 296 HH SIN AO) as [Z|Z]; clear - Hi Z; lia.
            + destruct (PMASK.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ q1 c1 ois 272 HH SIN AOI) as [Z|Z]; clear - Hi Z; lia. }
        apply (FIN fx3 R3 M3 model3 LK2 Aw2 de 0 (g + c) 2 c).
        + rewrite Z1, Z_to_bv_bv_unsigned. exact Rra.
        + intros x Hx. unfold L5SAR.cs_all in Hx.
          repeat (destruct Hx as [<-|Hx];
            [ first [ match goal with H : getr R3 (reg ?y) = Z_to_bv 64 (bv_unsigned (getr R (reg ?y))) |- getr R3 (reg ?y) = _ => rewrite H, Z_to_bv_bv_unsigned; reflexivity end
                    | rewrite Z2; exact (eq_sym Rsp)
                    | rewrite (KS3 _) by inl; rewrite (RG _) by inl; apply KS1; inl ] |]).
          destruct Hx.
        + rewrite (KS3 10%nat) by inl. exact A10c.
        + apply TO3; [lia| lia| exact V264].
        + apply TO3; [lia| lia| exact V272].
        + apply TO3; [lia| lia| exact V280].
        + apply TO3; [lia| lia| exact V288].
        + exact G1.
        + clear; lia.
        + clear - G3; lia.
        + exact IA3.
        + clear - C0; lia.
        + intros X; discriminate X.
        + clear - Cr; lia.
        + clear; lia.
        + intros X. exfalso. clear - X; lia.
        + intros _. split; reflexivity.
        + apply (L5.defined_grows M2 M3 p c MGM3 D2).
        + apply (L5SAR.ek_trans L ar LB FF sp 20480 WA M M2 M3 EK02 EK23W).
        + apply (L5SAR.dk_trans L ar LB FF sp 20480 M M2 M3 DK02). apply L5SAR.dk_grows. exact MGM3.
        + apply (L5SAR.astk_grows ar M2 M3 sp 20480 ASTK2 MGM3).
        + exact HH3.
        + exact AM3.
        + eapply L5LZ.model_rt_trans; [exact MRT1|]. eapply L5LZ.model_rt_trans; [exact MRT2| exact MRT3].
        + exact INC2.
        + exact INCA2. }
    (* [comment removed for export] *)
    assert (Kr : 1 <= k <= 16383) by (clear - Hk KNF; lia).
    LeanFeed.pfeed P (PMASRP.asrA0f_conc fx R MV (fun j => match j with 2%nat => sp | 34%nat => qc | 35%nat => de | 36%nat => os | 37%nat => p | 38%nat => k | _ => 0 end)) ltac:(idtac; first [assumption | lazymatch goal with
        | |- L5.u64_at _ _ (os + _) _ => unfold MV; vis64 OAV
        | |- PMASRP.aligned _ _ => unfold PMASRP.aligned; L5FastLia.plia
        | |- _ \/ _ => right; L5FastLia.plia
        | |- _ => L5FastLia.plia end]).
    destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T11 & T12 & T18 & T19 & T20 & T21 & T22 & T23 & T24 & U280
                   & S80 & S72 & S64 & S56 & S48 & S40 & S32 & S24 & S16 & S8 & U264 & U272 & U288 & UD).
    apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr Aw M model fx fx1 R 0xadae0 R1 0xb150c M1v W1 K HH AM MS1 MG1).
    { intros a Ha N. apply FRZ1; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
    { exact W1ok. }
    intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
    assert (EK01 : L5SAR.ek L ar LB FF sp 20480 [(os + 256, 40)] M M1) by exact (EKW1 M M1 LK Aw _ HH FR1).
    assert (TO1 : forall a v, os <= a -> a + 8 <= os + 296 -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v).
    { intros a v Ha Hb X. rewrite <- VIS1 in X. apply (proj1 (L5A.u64_at_vis _ M1 a v ltac:(apply OAV; lia) ltac:(lia) ltac:(lia))). exact X. }
    pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw M1 model1 HH1) as (_ & VIS1s & _).
    assert (TS1 : forall kk v, 8 <= kk <= 80 -> L5.u64_at RSEGS M1v (sp - kk) v -> L5.u64_at RSEGS M1 (sp - kk) v).
    { intros kk v Hkk X. rewrite <- VIS1, <- HID1 in X.
      apply (proj1 (L5A.u64_at_vis _ M1 (sp - kk) v (VIS1s (sp - kk) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact X. }
    apply (FILLC fx1 R1 M1 model1 0); try (apply TS1; [clear; lia| assumption]); try (apply TO1; [clear; lia| clear; lia| assumption]).
    - exact T1. - exact T2. - exact T8. - exact T9.
    - rewrite (KS1 10%nat) by inl. unfold os. rewrite <- L5K.rl10. exact A10.
    - exact T11. - exact T12. - exact T18. - exact T19. - exact T20.
    - replace (k - 0) with k by (clear; lia). exact T21.
    - exact T22. - exact T23. - exact T24.
    - intros x Hx. apply KS1. revert x Hx. apply (PMASR1.sub_in PMASRP.KS_asrA0f). vm_compute. reflexivity.
    - reflexivity.
    - clear - Hk; lia.
    - clear - Kr; lia.
    - intros i Hi. exfalso. clear - Hi; lia.
    - apply EKWA. exact EK01.
    - apply L5SAR.dk_grows. exact MGM1.
    - apply (L5SAR.astk_grows ar M M1 sp 20480 ASTK MGM1).
    - apply (PMASK.base_keep L ar C LY LB FF sp 20480 WA M M1 (EKWA M M1 EK01) OUTIMG BASE).
    - apply (PGSKA.src_piece_issG L ar C HI HIok LB FF LK cr Aw M M1 _ os ois str _ sp 20480 HH AO AOI LYD SOWN EK01 IA).
    - exact HH1.
    - exact AM1.
    - exact MRT1. }
  (* [comment removed for export] *)
  assert (Rr0 : 1 <= rem <= 16384) by (clear - RNZ G1 G2 G3; lia).
  assert (HEADA : exists fx1 R1 M1v, msteps RSEGS (st fx R 0xadae0 MV) (st fx1 R1 0x778cc M1v) /\ mem_grows MV M1v
             /\ (forall a, 0 <= a < 2 ^ 64 -> ~ W0 a -> M1v (Z_to_bv 64 a) = MV (Z_to_bv 64 a))
             /\ (forall x, In x [3; 4; 24; 25; 26; 27]%nat -> getr R1 (reg x) = getr R (reg x))
             /\ getr R1 (reg 1) = Z_to_bv 64 711536 /\ getr R1 (reg 2) = Z_to_bv 64 (sp - 80) /\ getr R1 (reg 8) = Z_to_bv 64 (Z.min k rem)
             /\ getr R1 (reg 9) = Z_to_bv 64 os /\ getr R1 (reg 10) = Z_to_bv 64 p /\ getr R1 (reg 11) = Z_to_bv 64 de
             /\ getr R1 (reg 12) = Z_to_bv 64 (Z.min k rem) /\ getr R1 (reg 18) = Z_to_bv 64 (os + 288) /\ getr R1 (reg 19) = Z_to_bv 64 p
             /\ getr R1 (reg 20) = Z_to_bv 64 (os + 280) /\ getr R1 (reg 21) = Z_to_bv 64 k /\ getr R1 (reg 22) = Z_to_bv 64 2147450880
             /\ getr R1 (reg 23) = Z_to_bv 64 ((os + 288) / 8 + 2147450880)
             /\ L5.u64_at RSEGS M1v (sp - 8) (bv_unsigned (getr R (reg 1))) /\ L5.u64_at RSEGS M1v (sp - 16) (bv_unsigned (getr R (reg 8)))
             /\ L5.u64_at RSEGS M1v (sp - 24) (bv_unsigned (getr R (reg 9))) /\ L5.u64_at RSEGS M1v (sp - 32) (bv_unsigned (getr R (reg 18)))
             /\ L5.u64_at RSEGS M1v (sp - 40) (bv_unsigned (getr R (reg 19))) /\ L5.u64_at RSEGS M1v (sp - 48) (bv_unsigned (getr R (reg 20)))
             /\ L5.u64_at RSEGS M1v (sp - 56) (bv_unsigned (getr R (reg 21))) /\ L5.u64_at RSEGS M1v (sp - 64) (bv_unsigned (getr R (reg 22)))
             /\ L5.u64_at RSEGS M1v (sp - 72) (bv_unsigned (getr R (reg 23))) /\ L5.u64_at RSEGS M1v (sp - 80) (bv_unsigned (getr R (reg 24)))).
  { destruct (Z_le_gt_dec rem k) as [RLE|RGT].
    - assert (E1 : Z.min k rem = rem) by (clear - RLE; lia).
      assert (Ar : 0 <= -1 * rem + k <= 16383) by (clear - RLE Rr0 Hk; lia).
      LeanFeed.pfeed P (PMASRP.asrAge_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => rem | 34%nat => qc | 35%nat => de | 36%nat => os | 37%nat => p | 38%nat => k | _ => 0 end)) ltac:(idtac; first [assumption | lazymatch goal with
          | |- L5.u64_at _ _ (os + _) _ => unfold MV; vis64 OAV
          | |- PMASRP.aligned _ _ => unfold PMASRP.aligned; L5FastLia.plia
          | |- _ \/ _ => right; L5FastLia.plia
          | |- _ => L5FastLia.plia end]).
      destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & T11 & T12 & T18 & T19 & T20 & T21 & T22 & T23
                     & S80 & S72 & S64 & S56 & S48 & S40 & S32 & S24 & S16 & S8).
      exists fx1, R1, M1v. rewrite E1. split; [exact MS1|]. split; [exact MG1|]. split; [intros a Ha N; apply FRZ1; [exact Ha| exact N]|].
      split; [intros x Hx; apply KS1; revert x Hx; apply (PMASR1.sub_in PMASRP.KS_asrAge); vm_compute; reflexivity|].
      split; [exact T1|]. split; [exact T2|]. split; [exact T8|]. split; [exact T9|]. split; [exact T10|]. split; [exact T11|]. split; [exact T12|].
      split; [exact T18|]. split; [exact T19|]. split; [exact T20|]. split; [exact T21|]. split; [exact T22|]. split; [exact T23|].
      split; [exact S8|]. split; [exact S16|]. split; [exact S24|]. split; [exact S32|]. split; [exact S40|].
      split; [exact S48|]. split; [exact S56|]. split; [exact S64|]. split; [exact S72| exact S80].
    - assert (E1 : Z.min k rem = k) by (clear - RGT; lia).
      assert (Ar1 : 2 <= rem <= 16384) by (clear - RGT Rr0 Hk; lia).
      assert (Ar2 : 1 <= k <= 16383) by (clear - RGT Rr0 Hk; lia).
      assert (Ar3 : 1 <= rem - k <= 16383) by (clear - RGT Rr0 Hk; lia).
      LeanFeed.pfeed P (PMASRP.asrAlt_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => rem | 34%nat => qc | 35%nat => de | 36%nat => os | 37%nat => p | 38%nat => k | _ => 0 end)) ltac:(idtac; first [assumption | lazymatch goal with
          | |- L5.u64_at _ _ (os + _) _ => unfold MV; vis64 OAV
          | |- PMASRP.aligned _ _ => unfold PMASRP.aligned; L5FastLia.plia
          | |- _ \/ _ => right; L5FastLia.plia
          | |- _ => L5FastLia.plia end]).
      destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & T11 & T18 & T19 & T20 & T21 & T22 & T23
                     & S80 & S72 & S64 & S56 & S48 & S40 & S32 & S24 & S16 & S8).
      exists fx1, R1, M1v. rewrite E1. split; [exact MS1|]. split; [exact MG1|]. split; [intros a Ha N; apply FRZ1; [exact Ha| exact N]|].
      split; [intros x Hx; apply KS1; revert x Hx; apply (PMASR1.sub_in PMASRP.KS_asrAlt); vm_compute; reflexivity|].
      split; [exact T1|]. split; [exact T2|]. split; [exact T8|]. split; [exact T9|]. split; [exact T10|]. split; [exact T11|].
      split; [rewrite (KS1 12%nat) by inl; rewrite <- L5SAR.r12; exact A12|].
      split; [exact T18|]. split; [exact T19|]. split; [exact T20|]. split; [exact T21|]. split; [exact T22|]. split; [exact T23|].
      split; [exact S8|]. split; [exact S16|]. split; [exact S24|]. split; [exact S32|]. split; [exact S40|].
      split; [exact S48|]. split; [exact S56|]. split; [exact S64|]. split; [exact S72| exact S80]. }
  destruct HEADA as (fx1 & R1 & M1v & MS1 & MG1 & FRZ1 & KS1 & T1 & T2 & T8 & T9 & T10 & T11 & T12 & T18 & T19 & T20 & T21 & T22 & T23
                     & S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80).
  set (len1 := Z.min k rem) in *.
  assert (Hl1r : 1 <= len1 <= k /\ len1 <= rem) by (unfold len1; clear - Rr0 Hk; destruct (Z.min_spec k rem) as [[X1 X2]|[X1 X2]]; rewrite X2; lia).
  apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr Aw M model fx fx1 R 0xadae0 R1 0x778cc M1v W0 K HH AM MS1 MG1 FRZ1 W0ok).
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
  assert (EK01 : L5SAR.ek L ar LB FF sp 20480 [] M M1) by exact (EKW0 M M1 LK Aw _ HH FR1).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw M1 model1 HH1) as (_ & VIS1s & _).
  assert (TS1 : forall kk v, 8 <= kk <= 80 -> L5.u64_at RSEGS M1v (sp - kk) v -> L5.u64_at RSEGS M1 (sp - kk) v).
  { intros kk v Hkk X. rewrite <- VIS1, <- HID1 in X.
    apply (proj1 (L5A.u64_at_vis _ M1 (sp - kk) v (VIS1s (sp - kk) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact X. }
  assert (ASTK1 : L5CA.astk ar M1 sp 20480) by (apply (L5SAR.astk_grows ar M M1 sp 20480 ASTK MGM1)).
  assert (OS1 : forall a, os <= a < os + 296 -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha. apply FR1; [clear - Ha O1; lia| unfold W0; clear - Ha OCE SL80 SLO; lia]. }
  assert (DPL : L5.defined M1 p len1).
  { apply (L5.defined_sub M1 p k); [apply (L5.defined_grows M M1 p k MGM1 DDP)| clear; lia| clear - Hl1r; lia]. }
  (* [comment removed for export] *)
  apply (PMASRK.memcpy_call L ar C HI LY HIok fx1 R1 M1 model1 K LB FF LK cr Aw (sp - 80) 711536 p de len1 HH1 AM1 K0).
  { exact T1. }
  { split; [clear; lia| reflexivity]. }
  { exact T2. }
  { rewrite (KS1 4%nat) by inl. exact Rtp. }
  { exact T10. }
  { exact T11. }
  { exact T12. }
  { clear - Hl1r Hk; lia. }
  { apply (L5SAR.astk_sub ar M1 M1 sp 20480 80 2560 ASTK1 (fun _ X => X)); [clear; lia| clear; lia| clear; lia|].
    replace (sp - 80) with (sp + (-5) * 16) by (clear; lia). rewrite Z.mod_add by (clear; lia). exact A16. }
  { intros a Ha. apply (PMFA.accA_agree M M1 p k (AGSHP M M1 [] EK01 PMKA.wapp_nil) DAP a). clear - Ha Hl1r; lia. }
  { intros i Hi. apply CLPw. clear - Hi Hl1r; lia. }
  { exact DPL. }
  { exact DP0. }
  { clear - DP1 Hl1r; lia. }
  { unfold app_rng in DAPP |- *. clear - DAPP Hl1r. Lia.lia. }
  { intros a Ha. apply (PMFA.accA_agree M M1 qc 16384); [apply (PMASK.agsh_blk L ar LB FF sp 20480 _ M M1 qc 16384 EK01 PMKA.wapp_nil QIN); clear - Q0 Q4 SLO SHI SPT; lia| exact ACH| clear - Ha Hl1r G1 G3; lia]. }
  { clear - DEB; lia. }
  { clear - DEB Hl1r G3 Q4 SLO SHI SPT; lia. }
  { apply (L5SAR.app_rng_block L ar C HI HIok LB FF LK cr Aw M1 _ qc 16384 de len1 HH1 QIN); clear - G1 G3 Hl1r; lia. }
  { intros i Hi. apply CLQ. clear - Hi G1 G3 Hl1r; lia. }
  { apply (L5.defined_sub M1 qc 16384); [apply (L5.defined_grows M M1 qc 16384 MGM1 DCH)| clear - G1; lia| clear - G3 Hl1r; lia]. }
  { clear - DQA G1 G3 Hl1r. Lia.lia. }
  intros fx2 R2 M2 model2 RP2 DEF2 HP2 MRT2 AM2 HH2.
  assert (OUTD : forall a, aclient L ar LB FF sp 20480 a -> L5.outside WA a -> L5.outside [(p, len1)] a).
  { intros a _ Oq r0 [<-|[]] X. apply (Oq (p, k)); [unfold WA; apply in_or_app; right; left; reflexivity| unfold L5.in_rng in *; cbn [fst snd] in *; clear - X Hl1r; lia]. }
  assert (EK12 : L5SAR.ek L ar LB FF sp 20480 WA M1 M2).
  { apply (L5SAR.ek_callee L ar LB [] FF [] sp 20480 (sp - 80) 2560 WA [(p, len1)] M1 M2 HP2); [clear; lia| clear; lia| exact OUTD]. }
  assert (EK12d : L5SAR.ek L ar LB FF sp 20480 [(p, len1)] M1 M2).
  { apply (L5SAR.ek_callee L ar LB [] FF [] sp 20480 (sp - 80) 2560 _ [(p, len1)] M1 M2 HP2); [clear; lia| clear; lia| intros a _ Oq; exact Oq]. }
  assert (DK12 : L5SAR.dk L ar LB FF sp 20480 M1 M2) by (apply (L5SAR.dk_callee L ar LB [] FF [] sp 20480 (sp - 80) 2560 _ M1 M2 HP2); clear; lia).
  assert (ASTK2 : L5CA.astk ar M2 sp 20480) by (apply (PMKA.astk_after_ahpres L ar LB FF M1 M2 sp 20480 (sp - 80) 2560 _ ASTK1 HP2); clear - TOP; lia).
  assert (NDP : forall a, ~ (p <= a < p + k) -> ~ (p <= a < p + len1)) by (intros a N X; apply N; clear - X Hl1r; lia).
  assert (KF2 : forall a, sp - 80 <= a < sp -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { intros a Ha. destruct HP2 as (E & _). apply E. split; [clear - Ha SLO SHI SPT; lia|]. split.
    - apply (L5SAR.stack_client L ar LB FF (sp - 80) 2560 a); clear - Ha SL80 SHI SPT; lia.
    - intros r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. apply NDP. intros Y. destruct (DX a Y) as (X1 & _). apply X1. clear - Ha; lia. }
  assert (KO2 : forall a, os <= a < os + 296 -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { intros a Ha. destruct HP2 as (E & _). apply E. split; [clear - Ha O1; lia|]. split.
    - apply PMASR1.cl_of_bf. right. apply (PMASR1.in_fframe_of_aobjA FF os 296 a AO). clear - Ha; lia.
    - intros r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. apply NDP. intros Y. destruct (DX a Y) as (_ & _ & X3 & _). apply X3. clear - Ha; lia. }
  assert (WSP : PMKA.wapp [(p, len1)]).
  { apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI in *; clear - DSH Hl1r; Lia.lia| apply PMKA.wapp_nil]. }
  assert (CO : forall a v, os <= a -> a + 8 <= os + 296 -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M2 a v).
  { intros a v Ha Hb X. apply (L5C.u64_at_agree RSEGS M M2); [intros i Hi; rewrite KO2, OS1 by (clear - Ha Hb Hi; lia); reflexivity| clear - Ha O1; lia| clear - Hb O1; lia| exact X]. }
  assert (SV : forall kk v, 8 <= kk <= 80 -> L5.u64_at RSEGS M1v (sp - kk) v -> L5.u64_at RSEGS M2 (sp - kk) v).
  { intros kk v Hkk X. apply (L5C.u64_at_agree RSEGS M1 M2); [intros i Hi; apply KF2; clear - Hkk Hi; lia| clear - Hkk SLO SHI SPT; lia| clear - Hkk SLO SHI SPT; lia|].
    apply TS1; [exact Hkk| exact X]. }
  assert (RG : forall x, In x L5SAR.cs_all -> getr R2 (reg x) = getr R1 (reg x)) by (intros x Hx; apply (L5SAR.cs_of_preserved R1 R2 x RP2 Hx)).
  apply (MEMC1 fx2 R2 M2 model2 len1).
  - rewrite (RG 2%nat) by inl. exact T2.
  - rewrite (RG 8%nat) by inl. exact T8.
  - rewrite (RG 9%nat) by inl. exact T9.
  - rewrite (RG 18%nat) by inl. exact T18.
  - rewrite (RG 19%nat) by inl. exact T19.
  - rewrite (RG 20%nat) by inl. exact T20.
  - rewrite (RG 21%nat) by inl. exact T21.
  - rewrite (RG 22%nat) by inl. exact T22.
  - rewrite (RG 23%nat) by inl. exact T23.
  - intros x Hx. rewrite (RG x) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). apply KS1. exact Hx.
  - apply SV; [clear; lia| exact S8].
  - apply SV; [clear; lia| exact S16].
  - apply SV; [clear; lia| exact S24].
  - apply SV; [clear; lia| exact S32].
  - apply SV; [clear; lia| exact S40].
  - apply SV; [clear; lia| exact S48].
  - apply SV; [clear; lia| exact S56].
  - apply SV; [clear; lia| exact S64].
  - apply SV; [clear; lia| exact S72].
  - apply SV; [clear; lia| exact S80].
  - apply CO; [clear; lia| clear; lia| exact S264].
  - apply CO; [clear; lia| clear; lia| exact S272].
  - apply CO; [clear; lia| clear; lia| exact S280].
  - apply CO; [clear; lia| clear; lia| exact S288].
  - clear - Rr0; lia.
  - reflexivity.
  - exact DEF2.
  - apply (L5SAR.ek_trans L ar LB FF sp 20480 WA M M1 M2); [| exact EK12].
    apply (L5SAR.ek_W L ar LB FF sp 20480 WA [] M M1 EK01). intros a _ r0 [].
  - apply (L5SAR.dk_trans L ar LB FF sp 20480 M M1 M2); [apply L5SAR.dk_grows; exact MGM1| exact DK12].
  - exact ASTK2.
  - apply (PMASK.base_keep L ar C LY LB FF sp 20480 _ M1 M2 EK12 OUTIMG).
    apply (PMASK.base_keep L ar C LY LB FF sp 20480 _ M M1 EK01); [intros a _ r0 []| exact BASE].
  - apply (PMKA.iss_keepA RSEGS PMA.AD L ar LB FF sp 20480 _ M1 M2 EK12d WSP FRB BRB ois str _ AOI SOWN).
    + intros i Hi r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. apply NDP. intros Y. destruct (DX i Y) as (_ & X2 & _). apply X2. exact Hi.
    + intros c1 n1 q1 E i Hi r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. apply NDP. intros Y. destruct (DX i Y) as (_ & _ & _ & _ & X5 & _). apply (X5 c1 n1 q1 E). exact Hi.
    + apply (PMKA.iss_keepA RSEGS PMA.AD L ar LB FF sp 20480 _ M M1 EK01 PMKA.wapp_nil FRB BRB ois str _ AOI SOWN); [intros i _ r0 []| intros c0 n0 p0 _ i _ r0 []| exact IA].
  - exact HH2.
  - exact AM2.
  - eapply L5LZ.model_rt_trans; [exact MRT1| exact MRT2].
Qed.

End WithHeap.
End PGSRDA.
