(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnASrcKit_b PgSrcKitA_b PnASrcRead1_b PnASrcReadK_b PnASrcReadP_b Ba0PgSrcReadK_b Ba0PgSrcReadC_b Ba0PgSrcReadMS_b Ba0PgSrcReadMS1_b Ba0PgSrcReadMS2_b Ba0PgSrcReadMT_b Ba0PgSrcReadMC_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs PmParSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PmSpecsAX_b PnSpecsAa_b
     PmModelFactsA_b PnStepA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmParStep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnASrcKit_b PnASrcReadK_b PnASrcRead1_b PnASrcReadP_b Ba0_code_raf314_af318_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b PgSrcKitA_b PnRunA_b PmAUarK_b PmAUar_b PnAReadCsK_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := first [ L5FastLia.plia | Lia.lia ].

Module PGSRDM.
Abbreviation RSEGS := PGSRDK.RSEGS.
Abbreviation mem := (word -> option byte).
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom PGSRDK.RSEGS)) (only parsing).
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Ltac pdestr PP := repeat match type of PP with _ /\ _ => let H := fresh "S" in destruct PP as (H & PP) end.

Section Mc.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.

Definition srd_mc_head_T (al : Z) : Prop :=
  forall (O : PGS.owner) (R0 : bvmap 5 word) (M0 : mem) (model0 : Model) (K : TSet) (OB LBX : list (Z * Z))
         (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r : Z) (str : PM.vstr) (Wextra : list L5.range)
         (qc de rem g eg sst p k : Z),
    PGSRDK.srd_ctx L ar HI al O R0 M0 model0 K OB LBX FF LK Aw cr sp r (PM.SRC qc de rem) str (PM.STRM g eg sst) Wextra ->
    getr R0 (reg 11) = Z_to_bv 64 p -> getr R0 (reg 12) = Z_to_bv 64 k ->
    forall (F fl : Z) (LK2 : list fframe) (M2 : mem) (model2 : Model),
    PGSRDK.srd_frame L ar HI al R0 OB LBX FF LK Aw cr sp (PM.SRC qc de rem) F fl LK2 M2 model2 ->
    forall (fx : FPState) (R : bvmap 5 word) (M : mem) (model : Model) (LKc : list fframe) (Ac : list (Z * Z))
           (V : nat -> Z),
    PGSRDK.srd_body L ar HI al O R0 M0 model0 OB LBX FF LK Aw sp (PM.SRC qc de rem) Wextra F M model LKc cr Ac ->
    V 2%nat = sp - al -> V 36%nat = PGS.ow_os O -> V 37%nat = p -> V 38%nat = k -> 32 * V 50%nat = F -> V 51%nat = fl ->
    (forall i, In i [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> V i = bv_unsigned (getr R0 (reg i))) ->
    getr R (reg 3) = getr R0 (reg 3) -> getr R (reg 4) = getr R0 (reg 4) ->
    V 34%nat = qc -> V 35%nat = de -> V 45%nat = PGS.ow_ois O ->
    PM.iss_at RSEGS PMA.AD PMSPA.accA M (PGS.ow_ois O) str (PM.STRM g eg sst) ->
    PGSRDK.srd_stA V R (mrestrict (ahid Ac model) M) -> PGSRDK.srd_pathG V R (mrestrict (ahid Ac model) M) rem sst ->
    exists (fx1 : FPState) (R1 : bvmap 5 word) (M1v : mem),
      (msteps RSEGS (st fx R 716228 (mrestrict (ahid Ac model) M)) (st fx1 R1 0x77c94 M1v))
      /\ (mem_grows (mrestrict (ahid Ac model) M) M1v)
      /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 152) <= i < ((V 2%nat) - 152) + 16) -> ~ (((V 2%nat) - 112) <= i < ((V 2%nat) - 112) + 8) -> ~ (((32 * (V 50%nat)) + 0) <= i < ((32 * (V 50%nat)) + 0) + 24) -> ~ (((32 * (V 50%nat)) + 32) <= i < ((32 * (V 50%nat)) + 32) + 8) -> ~ (((4 * (V 50%nat)) + 2147450880) <= i < ((4 * (V 50%nat)) + 2147450880) + 12) -> M1v (Z_to_bv 64 i) = (mrestrict (ahid Ac model) M) (Z_to_bv 64 i))
      /\ (forall x, In x [3; 4; 27]%nat -> getr R1 (reg x) = getr R (reg x))
      /\ (getr R1 (reg 1) = Z_to_bv 64 716500)
      /\ (getr R1 (reg 2) = Z_to_bv 64 ((V 2%nat) - 160))
      /\ (getr R1 (reg 8) = Z_to_bv 64 (V 2%nat))
      /\ (getr R1 (reg 9) = Z_to_bv 64 ((V 2%nat) - 160))
      /\ (getr R1 (reg 10) = Z_to_bv 64 (V 37%nat))
      /\ (getr R1 (reg 11) = Z_to_bv 64 (V 35%nat))
      /\ (getr R1 (reg 12) = Z_to_bv 64 (Z.min k rem))
      /\ (getr R1 (reg 13) = Z_to_bv 64 18446744073709551602)
      /\ (getr R1 (reg 14) = Z_to_bv 64 18446744073709551601)
      /\ (getr R1 (reg 15) = Z_to_bv 64 18446744073709551603)
      /\ (getr R1 (reg 16) = Z_to_bv 64 (32 * (V 50%nat)))
      /\ (getr R1 (reg 18) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880))
      /\ (getr R1 (reg 19) = Z_to_bv 64 (V 36%nat))
      /\ (getr R1 (reg 20) = Z_to_bv 64 (Z.min k rem))
      /\ (getr R1 (reg 21) = Z_to_bv 64 ((((V 36%nat) + 280) / 8) + 2147450880))
      /\ (getr R1 (reg 22) = Z_to_bv 64 (V 38%nat))
      /\ (getr R1 (reg 23) = Z_to_bv 64 ((V 36%nat) + 288))
      /\ (getr R1 (reg 24) = Z_to_bv 64 ((V 36%nat) + 280))
      /\ (getr R1 (reg 25) = Z_to_bv 64 ((4 * (V 50%nat)) + 2147450880))
      /\ (getr R1 (reg 26) = Z_to_bv 64 (32 * (V 50%nat)))
      /\ (L5.u64_at RSEGS M1v ((V 2%nat) - 152) ((32 * (V 50%nat)) + 32))
      /\ (L5.u64_at RSEGS M1v ((V 2%nat) - 144) (32 * (V 50%nat)))
      /\ (L5.u64_at RSEGS M1v ((V 2%nat) - 112) (32 * (V 50%nat)))
      /\ (L5.u64_at RSEGS M1v ((32 * (V 50%nat)) + 32) (V 38%nat))
      /\ (L5.u8_at RSEGS M1v ((4 * (V 50%nat)) + 2147450891) 243)
      /\ (L5.u8_at RSEGS M1v ((4 * (V 50%nat)) + 2147450890) 243)
      /\ (L5.u8_at RSEGS M1v ((4 * (V 50%nat)) + 2147450889) 243)
      /\ (L5.u8_at RSEGS M1v ((4 * (V 50%nat)) + 2147450888) 248)
      /\ (L5.u8_at RSEGS M1v ((4 * (V 50%nat)) + 2147450883) 241)
      /\ (L5.u8_at RSEGS M1v ((4 * (V 50%nat)) + 2147450882) 241)
      /\ (L5.u8_at RSEGS M1v ((4 * (V 50%nat)) + 2147450881) 241)
      /\ (L5.u8_at RSEGS M1v ((4 * (V 50%nat)) + 2147450880) 241)
      /\ (L5.u8_at RSEGS M1v ((4 * (V 50%nat)) + 2147450887) 242)
      /\ (L5.u8_at RSEGS M1v ((4 * (V 50%nat)) + 2147450886) 242)
      /\ (L5.u8_at RSEGS M1v ((4 * (V 50%nat)) + 2147450885) 242)
      /\ (L5.u8_at RSEGS M1v ((4 * (V 50%nat)) + 2147450884) 0)
      /\ (L5.u64_at RSEGS M1v ((32 * (V 50%nat)) + 16) 716108)
      /\ (L5.u64_at RSEGS M1v ((32 * (V 50%nat)) + 8) 127274)
      /\ (L5.u64_at RSEGS M1v (32 * (V 50%nat)) 1102416563)
      /\ (L5.defined M1v ((32 * (V 50%nat)) + 24) 8)
      /\ (L5.defined M1v ((32 * (V 50%nat)) + 40) 88).

Ltac hd_sfind := match goal with
  | H : ?a <= ?x <= ?b |- ?a <= ?x <= ?b => exact H
  | H : ?a <= ?x < ?b |- ?a <= ?x < ?b => exact H
  | H : ?a <= ?b \/ ?c <= ?d |- ?a <= ?b \/ ?c <= ?d => exact H
  | H : ?a mod ?b = ?c |- ?a mod ?b = ?c => exact H
  | H : getr ?R ?r = ?v |- getr ?R ?r = ?v => exact H
  | H : L5.u64_at ?s ?m ?a ?v |- L5.u64_at ?s ?m ?a ?v => exact H
  | H : L5.u32_at ?s ?m ?a ?v |- L5.u32_at ?s ?m ?a ?v => exact H
  | H : L5.u8_at ?s ?m ?a ?v |- L5.u8_at ?s ?m ?a ?v => exact H
  | H : L5.defined ?m ?a ?n |- L5.defined ?m ?a ?n => exact H
  | H : L5.writable ?s ?m ?a ?n |- L5.writable ?s ?m ?a ?n => exact H
  | H : L5KA.zeros_at ?m ?a ?n |- L5KA.zeros_at ?m ?a ?n => exact H
  | H : L5.img_clear ?m ?a ?n |- L5.img_clear ?m ?a ?n => exact H
  end.
Ltac hd_feed P tac :=
  lazymatch type of P with
  | ?A -> _ =>
      let H := fresh "FD" in
      assert (H : A) by (first [ tac | fail 100 "hd_feed: premise" A ]);
      specialize (P H); clear H; hd_feed P tac
  | _ => idtac
  end.
Ltac hd_dsp LIA :=
  lazymatch goal with
  | |- PMASRP.aligned _ _ => unfold PMASRP.aligned; hd_sfind
  | |- 0 <= bv_unsigned _ < 2 ^ 64 => exact (bv_unsigned_in_range _ _)
  | |- _ <= _ <= _ => first [ hd_sfind | LIA ]
  | |- _ <= _ < _ => first [ hd_sfind | LIA ]
  | |- getr _ _ = Z_to_bv 64 (bv_unsigned _) => symmetry; apply Z_to_bv_bv_unsigned
  | |- _ => hd_sfind
  end.
Ltac hd_fin1 KS := first [ hd_sfind | (intros x Hx; apply KS; destruct Hx as [<-|[<-|[<-|[]]]]; inl) ].
Ltac hd_fin KS := lazymatch goal with
  | |- _ /\ _ => split; [hd_fin1 KS | hd_fin KS]
  | |- _ => hd_fin1 KS
  end.

Lemma srd_mc_head : srd_mc_head_T 0.
Proof.
  unfold srd_mc_head_T.
  intros O R0 M0 model0 K OB LBX FF LK Aw cr sp r str Wextra qc de rem g eg sst p k CTX R11 R12 F fl LK2 M2 model2 G
         fx R M model LKc Ac V BD XV2 XV36 XV37 XV38 XV50 XV51 XVS XR3 XR4 XV34 XV35 XV45 XIS STA PTH.
  pose proof PTH as (V33 & REM1 & PG). pose proof PG as (G33 & G288 & G35).
  pose proof STA as STAp. unfold PGSRDK.srd_stA in STAp. pdestr STAp.
  pose proof CTX as (OK & _ & _ & _ & _ & _ & _ & _ & _ & _ & ARGS & _ & PA0 & _).
  destruct ARGS as (p' & k' & _ & A12 & Hk & _). rewrite L5SAR.r12 in A12. unfold PM.CHUNK in Hk.
  pose proof R12 as R12k. rewrite A12 in R12k. apply (f_equal bv_unsigned) in R12k.
  rewrite !L5.unsigned_lit in R12k by (first [clear - Hk; lia | rewrite <- XV38; hd_sfind]). subst k'.
  pose proof (PGSA.oo_src _ _ _ _ _ _ OK M0 _ OB PA0) as (PSRC & _ & _).
  pose proof PSRC as (_ & _ & _ & _ & _ & _ & _ & QD1 & QD2 & QD3 & _). cbn [PM.sr_qc PM.sr_de PM.sr_rem] in QD1, QD2, QD3.
  try unfold PM.CHUNK in QD1, QD2, QD3.
  assert (RB : rem <= 16384) by (clear - QD1 QD2 QD3; lia).
  clear PSRC QD1 QD2 QD3.
  match goal with
  | H2 : _ <= V 2%nat <= _, H36 : _ <= V 36%nat <= _, H50 : _ <= V 50%nat <= _, H51 : 4096 <= V 51%nat <= _ |- _ =>
      pose proof (conj H2 (conj H36 (conj H50 H51))) as KB
  end.
  destruct (Z.le_gt_cases rem k) as [Hc|Hc]; pose proof (conj V33 (conj REM1 (conj RB (conj Hk (conj Hc XV38))))) as PK.
  - pose proof (PMASRP.asrAge_conc fx R (mrestrict (ahid Ac model) M) V) as P0.
    hd_feed P0 ltac:(idtac; hd_dsp ltac:(idtac; clear - KB PK; lia)).
    destruct P0 as (fx1 & R1 & M1v & MG & _ & AG & MS & KS & PP).
    exists fx1, R1, M1v. replace (Z.min k rem) with (V 33%nat) by (rewrite V33; clear - Hc; lia).
    split; [exact MS|]. split; [exact MG|]. split; [exact AG|]. pdestr PP. hd_fin KS.
  - pose proof (PMASRP.asrAlt_conc fx R (mrestrict (ahid Ac model) M) V) as P0.
    hd_feed P0 ltac:(idtac; hd_dsp ltac:(idtac; clear - KB PK; lia)).
    destruct P0 as (fx1 & R1 & M1v & MG & _ & AG & MS & KS & PP).
    exists fx1, R1, M1v. replace (Z.min k rem) with (V 38%nat) by (rewrite XV38; clear - Hc; lia).
    split; [exact MS|]. split; [exact MG|]. split; [exact AG|]. pdestr PP. hd_fin KS.
Qed.

Lemma srd_mc_ok : PGSA.fill_buffer_specG RSEGS PMA.AD L ar HI PNRA.FCB ->
  PGSRDK.srd_exit_T L ar HI 0 -> PGSRDK.srd_fill_ret_T L ar HI 0 -> PGSRDK.srd_a0_T L ar HI 0 PGSRDK.srd_pathG.
Proof.
  intros FB EXT FRT.
  pose proof (PGSRDMS.srd_mc_post_ok L ar C HI LY HIok IL ICok ILY EXT FRT FB
    (PGSRDMS1.ms_g1_ok L ar C HI LY HIok IL ICok ILY) (PGSRDMS2.ms_g2_ok L ar C HI LY HIok IL ICok ILY)) as POST.
  pose proof (PGSRDMC.srd_mc_call_ok L ar C HI LY HIok POST) as PRE.
  pose proof (PGSRDMT.srd_mc_args_ok L ar C HI LY HIok IL ICok ILY) as ARG.
  pose proof (PGSRDMT.srd_mc_keep_ok L ar C HI LY HIok IL ICok ILY) as KEEP.
  unfold PGSRDK.srd_a0_T.
  intros O R0 M0 model0 K OB LBX FF LK Aw cr sp r str Wextra qc de rem g eg sst p k CTX R11 R12
         F fl LK2 M2 model2 G fx R M model LKc Ac V BD XV2 XV36 XV37 XV38 XV50 XV51 XVS XR3 XR4 XV34 XV35 XV45 XIA ST PTH.
  destruct (srd_mc_head O R0 M0 model0 K OB LBX FF LK Aw cr sp r str Wextra qc de rem g eg sst p k CTX R11 R12
         F fl LK2 M2 model2 G fx R M model LKc Ac V BD XV2 XV36 XV37 XV38 XV50 XV51 XVS XR3 XR4 XV34 XV35 XV45 XIA ST PTH)
    as (fx1 & R1 & M1v & MS1 & MG1 & AG1 & K327 & HR1 & HR2 & HR8 & HR9 & HR10 & HR11 & HR12 & HR13 & HR14 & HR15 & HR16 & HR18 & HR19 & HR20 & HR21 & HR22 & HR23 & HR24 & HR25 & HR26 & HC1 & HC2 & HC3 & HC4 & HC5 & HC6 & HC7 & HC8 & HC9 & HC10 & HC11 & HC12 & HC13 & HC14 & HC15 & HC16 & HC17 & HC18 & HC19 & HC20 & HC21).
  assert (HPB : 0 <= p < 2 ^ 64) by (rewrite <- XV37; unfold PGSRDK.srd_stA in ST; pdestr ST; assumption).
  assert (HKB : 0 <= k < 2 ^ 64) by (rewrite <- XV38; unfold PGSRDK.srd_stA in ST; pdestr ST; assumption).
  assert (C264 : L5.u64_at RSEGS (mrestrict (ahid Ac model) M) (PGS.ow_os O + 264) qc) by (rewrite <- XV36, <- XV34; unfold PGSRDK.srd_stA in ST; pdestr ST; assumption).
  assert (C272 : L5.u64_at RSEGS (mrestrict (ahid Ac model) M) (PGS.ow_os O + 272) 16384) by (rewrite <- XV36; unfold PGSRDK.srd_stA in ST; pdestr ST; assumption).
  assert (C280 : L5.u64_at RSEGS (mrestrict (ahid Ac model) M) (PGS.ow_os O + 280) de) by (rewrite <- XV36, <- XV35; unfold PGSRDK.srd_stA in ST; pdestr ST; assumption).
  assert (C288 : L5.u64_at RSEGS (mrestrict (ahid Ac model) M) (PGS.ow_os O + 288) rem).
  { pose proof PTH as (XV33 & _ & PG). pose proof PG as (_ & P288 & _). rewrite <- XV36, <- XV33. exact P288. }
  pose proof CTX as (_ & _ & _ & _ & ENT & _). pose proof ENT as (_ & _ & _ & _ & Rtp & _). rewrite L5K.rl4 in Rtp.
  apply (PGSRDC.srd_piece L ar C HI LY HIok O R0 M0 model0 K OB LBX FF LK Aw cr sp r (PM.SRC qc de rem) str (PM.STRM g eg sst) Wextra
           F fl LK2 M2 model2 M model LKc Ac fx fx1 R R1 _ _ M1v
           (fun a : Z => (((V 2%nat) - 152) <= a < ((V 2%nat) - 152) + 16) \/ (((V 2%nat) - 112) <= a < ((V 2%nat) - 112) + 8) \/ (((32 * (V 50%nat)) + 0) <= a < ((32 * (V 50%nat)) + 0) + 24) \/ (((32 * (V 50%nat)) + 32) <= a < ((32 * (V 50%nat)) + 32) + 8) \/ (((4 * (V 50%nat)) + 2147450880) <= a < ((4 * (V 50%nat)) + 2147450880) + 12))
           CTX G BD MS1 MG1).
  - intros a Ha NW. apply AG1; [exact Ha| | | | |]; intro X; apply NW; cbv beta; clear - X; tauto.
  - intros a Wa. cbv beta in Wa. destruct Wa as [Y|[Y|[Y|[Y|Y]]]];
      [right; right; right| right; right; right| left| left| right; left]; try unfold SB; clear - Y XV2 XV50; lia.
  - intros M1 model1 BD1 HID1 MRT1 MGM1 FRM1 VV1 EK1.
    assert (MV1E : mrestrict (ahid Ac model1) M1 = M1v) by (rewrite HID1; exact MRT1).
    assert (HR4 : getr R1 (reg 4) = Z_to_bv 64 (hl_tp L)).
    { rewrite (K327 4%nat ltac:(cbn; right; left; reflexivity)), XR4. exact Rtp. }
    assert (AGM : forall i, 0 <= i < 2 ^ 64 ->
        ~ ((sp - 160 - 0 <= i < sp - 104 - 0) \/ (F <= i < F + 128) \/ (F / 8 + SB <= i < F / 8 + SB + 16)) ->
        M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros i Hi NR. apply FRM1; [exact Hi|]. intros Wa. cbv beta in Wa. apply NR.
      destruct Wa as [Y|[Y|[Y|[Y|Y]]]]; [left| left| right; left| right; left| right; right]; try unfold SB; clear - Y XV2 XV50; lia. }
    pose proof (ARG O R0 M0 model0 K OB LBX FF LK Aw cr sp r str Wextra qc de rem g eg sst p k CTX R11 R12 HPB HKB F fl LK2 M2 model2 G M1 model1 LKc Ac (Z.min k rem) BD1 eq_refl) as ARGS1.
    refine (PRE O R0 M0 model0 K OB LBX FF LK Aw cr sp r str Wextra qc de rem g eg sst p k CTX R11 R12
         F fl LK2 M2 model2 G fx R M model LKc Ac V BD XV2 XV36 XV37 XV38 XV50 XV51 XVS XR3 XR4 XV34 XV35 XV45 XIA ST PTH
              (Z.min k rem) fx1 R1 M1 model1 eq_refl BD1 HID1 HR1 HR4 HR10 HR11 HR12 HR2 HR8 HR9 HR18 HR19 HR20 HR21 HR22 HR23 HR24 HR25 HR26 K327 ARGS1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    { intros M3 model3 BD3 AH.
      exact (KEEP O R0 M0 model0 K OB LBX FF LK Aw cr sp r str Wextra qc de rem g eg sst p k CTX R11 R12 HPB HKB F fl LK2 M2 model2 G M model LKc Ac BD XIA (Z.min k rem) M1 model1 M3 model3 eq_refl BD1 EK1
               C264 C272 C280 C288 AGM BD3 AH). }
    { intros i Hi _ NA. rewrite MV1E. apply AG1; [exact Hi| | | | |]; intro X; apply NA; clear - X; tauto. }
    all: rewrite MV1E; assumption.
Qed.

End Mc.
End PGSRDM.
