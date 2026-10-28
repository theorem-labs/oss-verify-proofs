(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx PropExec CatExec CatSim SeqExec StreamSim StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5CoreKit L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5CoreSpecsA_b L5StepAR_b L5CoreBR_b L5ADetailHR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmParSpecs PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PnSpecsAa_b
     PmModelFactsA_b PnStepA_b PnStepA2_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PgSrc PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnLayout PnModel PnModelFacts PnStatics PnStaticsA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b PnRunAa_b PnASrcKit_b PmAUarK_b PmAUar_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnDecFacts. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnSpecsAXD_b PnADec128Defs_b PnADec128K_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNADC1.
Import L5A. Import L5CA. Import L5SAR. Import PNADK.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation mem := (word -> option byte).
Definition XSCR : Z := 4096.
Definition DXd (a : Z) : Prop := 6759112 <= a < 6759176.
Definition DXa (a : Z) : Prop := 6896976 <= a < 6896976 + 544.
Definition DX (a : Z) : Prop := DXd a \/ DXa a.
Lemma DX_dec a : DX a \/ ~ DX a.
Proof. unfold DX, DXd, DXa. destruct (L5SAR.rng_dec a 6759112 6759176) as [Y|Y]; [left; left; exact Y|].
  destruct (L5SAR.rng_dec a 6896976 (6896976 + 544)) as [Z0|Z0]; [left; right; exact Z0| right; intros [Q|Q]; [exact (Y Q)| exact (Z0 Q)]]. Qed.
Lemma DX_img a : DX a -> 6759112 <= a < 6897520.
Proof. unfold DX, DXd, DXa. intros [Y|Y]; clear - Y; lia. Qed.
Lemma DX_dep a : DX a -> PNST.dep PMA.AD PMA.AN a.
Proof.
  unfold DX, DXd, DXa. intros [Y|Y].
  - assert (C : 6759112 <= a < 6759136 \/ 6759136 <= a < 6759144 \/ 6759144 <= a < 6759168 \/ 6759168 <= a < 6759176) by (clear - Y; lia).
    destruct C as [C|[C|[C|C]]].
    + apply (PNST.in_foot_d128 PMA.AD PMA.AN (6759112, 6759136)); [unfold PNL.pn_d128_foot; cbn [PNL.pn_inf_guard PNL.pn_nan_guard PNL.pn_inf_obj PNL.pn_nan_obj PMA.AN NADDR_A In]; clear; tauto| cbn [fst snd]; exact C].
    + apply (PNST.in_foot_d128 PMA.AD PMA.AN (6759136, 6759144)); [unfold PNL.pn_d128_foot; cbn [PNL.pn_inf_guard PNL.pn_nan_guard PNL.pn_inf_obj PNL.pn_nan_obj PMA.AN NADDR_A In]; clear; tauto| cbn [fst snd]; exact C].
    + apply (PNST.in_foot_d128 PMA.AD PMA.AN (6759144, 6759168)); [unfold PNL.pn_d128_foot; cbn [PNL.pn_inf_guard PNL.pn_nan_guard PNL.pn_inf_obj PNL.pn_nan_obj PMA.AN NADDR_A In]; clear; tauto| cbn [fst snd]; exact C].
    + apply (PNST.in_foot_d128 PMA.AD PMA.AN (6759168, 6759176)); [unfold PNL.pn_d128_foot; cbn [PNL.pn_inf_guard PNL.pn_nan_guard PNL.pn_inf_obj PNL.pn_nan_obj PMA.AN NADDR_A In]; clear; tauto| cbn [fst snd]; exact C].
  - apply PNST.dep_of_j. apply PMST.in_foot_atexit. cbn [pa_atexit PMA.AD ADDR_A]. exact Y.
Qed.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Section WithHeap.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.
Lemma dep_client LB FF sp scr a : PNST.dep PMA.AD PMA.AN a -> aclient L ar LB FF sp scr a.
Proof.
  intros D. pose proof (PNADK.depA_img a D) as DI. unfold aclient, aclient_g. right; right; left.
  rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [clear - DI; lia| exact (PMA.ly_static L C LY a D)].
Qed.
Lemma dep_clientw LB FF sp scr a : PNST.dep PMA.AD PMA.AN a -> 0x139000 <= a -> aclientw L ar LB FF sp scr a /\ ~ hl_rt_ro L a.
Proof.
  intros D Ha. pose proof (PNADK.depA_img a D) as DI. split; [| exact (PMKA2.rt_ro_bss L C a LY Ha)].
  unfold aclientw, aclient_g. right; right; left.
  rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [clear - DI; lia|].
  intros [Y|Y]; [exact (PMA.ly_static L C LY a D Y)| exact (PMKA2.rt_ro_bss L C a LY Ha Y)].
Qed.

Lemma writable_img M a n : StreamSim.wseg_ok RSEGS (Z_to_bv 64 a) (Z.to_nat n) = true -> 0 <= a -> 0 < n -> a + n <= 2 ^ 64 -> L5.writable RSEGS M a n.
Proof.
  intros W Ha Hn Han d k Hd Hk. destruct k as [|k]. reflexivity.
  eapply (store_ok_sub RSEGS M (Z_to_bv 64 a) _ (Z.to_nat n) (Datatypes.S k)).
  - rewrite L5.unsigned_lit by lia. rewrite Z2Nat.id by lia. lia.
  - apply store_ok_wseg. exact W.
  - rewrite !L5.unsigned_lit by lia. lia.
  - rewrite !L5.unsigned_lit by lia. rewrite Z2Nat.id by lia. lia.
Qed.
(* [comment removed for export] *)
Lemma base_x (M M' : mem) :
  (forall a, 65536 <= a < 1282048 \/ 6896960 <= a < 6896968 \/ 6897555 <= a < 6897556 \/ 6897776 <= a < 6897780 -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> base_ok M -> base_ok M'.
Proof.
  intros AG (RO0 & (can & Hcan & CAN) & NL & LL).
  cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock PMA.AD ADDR_A] in *.
  split; [|split; [|split]]; cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock PMA.AD ADDR_A].
  - intros i Hi. rewrite AG by (clear - Hi; lia). apply RO0. exact Hi.
  - exists can. split; [exact Hcan|]. apply (L5C.u64_at_agree RSEGS M M'); [| clear; lia| clear; lia| exact CAN]. intros i Hi. apply AG. clear - Hi; lia.
  - apply (L5C.u8_at_agree RSEGS M M'); [| clear; lia| clear; lia| exact NL]. intros i Hi. apply AG. clear - Hi; lia.
  - unfold L5.u32_at in *. rewrite (L5C.rdn_agree RSEGS M M' 4%nat); [exact LL| clear; lia| cbn; clear; lia|]. intros i Hi. apply AG. cbn in Hi. clear - Hi; lia.
Qed.

(* [comment removed for export] *)
Lemma xgeo E (X : dkc L ar HI E) :
  ahl_ceil ar + 4096 + 18432 <= vsp E /\ vsp E <= ar_sptop ar /\ 140735340871680 <= ar_sptop ar <= 2 ^ 47 /\ vsp E mod 32 = 0 /\ 6905856 <= ahl_ceil ar.
Proof.
  pose proof (c_G L ar HI E X) as G'. destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  unfold SCR in *. pose proof (c_GEOM L ar HI E X) as G. unfold PNADD.geom in G. destruct G as (GS1 & GS32 & _).
  change (ff_bytes 3) with 512 in *.
  split; [exact GSLO|]. split; [exact GSHI|]. split; [exact GSPT|]. split; [exact GS32|]. clear - GFCEIL GFR. lia.
Qed.

(* [comment removed for export] *)
Lemma xpiece E (X : dkc L ar HI E) LKc (fx1 fx2 : FPState) R1 R2 (pc1 pc2 : Z) M1 model1 A1 (M2v : mem) (Wp : Z -> Prop) :
  ri_inv HI (vLB E) (FF' E) LKc (vcr E) A1 M1 (vml_of model1) -> amodel_ok A1 model1 -> astk ar M1 (vsp E) SCR ->
  msteps RSEGS (st fx1 R1 pc1 (mrestrict (ahid A1 model1) M1)) (st fx2 R2 pc2 M2v) ->
  mem_grows (mrestrict (ahid A1 model1) M1) M2v ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> M2v (Z_to_bv 64 a) = mrestrict (ahid A1 model1) M1 (Z_to_bv 64 a)) ->
  (forall a, Wp a -> (vsp E - 256 - XSCR <= a < vsp E - 256) \/ DXd a) ->
  (forall (M3 : mem) model3,
      ri_inv HI (vLB E) (FF' E) LKc (vcr E) A1 M3 (vml_of model3) -> amodel_ok A1 model3 -> model_rt model1 model3 -> astk ar M3 (vsp E) SCR ->
      ahid A1 model3 = ahid A1 model1 -> mrestrict (ahid A1 model1) M3 = M2v -> mem_grows M1 M3 ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
      srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx2 R2 pc2 M3 model3) (vK E)) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx1 R1 pc1 M1 model1) (vK E).
Proof.
  intros HH AM ASTK MS MG FRZ WP KONT.
  pose proof (xgeo E X) as (GSLO & GSHI & GSPT & GS32 & GCEIL). unfold XSCR in *.
  unfold PMSPA.cfg.
  apply (PMKA2.apiece_img L ar C HI LYa HIok (vLB E) (FF' E) LKc (vcr E) A1 M1 model1 fx1 fx2 R1 pc1 R2 pc2 M2v Wp (vK E) HH AM MS MG FRZ).
  { intros a Ha Wa. destruct (WP a Wa) as [Y|Y].
    - split; [| intros Q; pose proof (PMA.ly_ro L C LY a Q) as Q'; clear - Q' Y GSLO GCEIL; lia].
      unfold aclientw, aclient_g. right; left. split; [clear - Y GSLO GSHI GSPT; lia| intros Q; clear - Q; lia].
    - apply dep_clientw; [apply DX_dep; left; exact Y| unfold DXd in Y; clear - Y; lia]. }
  intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MG3 FR3 VV3.
  apply (KONT M3 model3 HH3 AM3 MRT3 (L5SAR.astk_grows ar M1 M3 _ _ ASTK MG3) HID3 VIS3 MG3 FR3).
Qed.

(* [comment removed for export] *)
Lemma xview E (X : dkc L ar HI E) LKc A1 M1 model1 :
  ri_inv HI (vLB E) (FF' E) LKc (vcr E) A1 M1 (vml_of model1) -> astk ar M1 (vsp E) SCR ->
  (L5.img_clear (mrestrict (ahid A1 model1) M1) 1249280 1282048 /\ L5.u64_at RSEGS (mrestrict (ahid A1 model1) M1) 1309752 2147450880
   /\ L5.u32_at RSEGS (mrestrict (ahid A1 model1) M1) 1309760 1
   /\ L5.writable RSEGS (mrestrict (ahid A1 model1) M1) (vsp E - 256) 256 /\ L5.writable RSEGS (mrestrict (ahid A1 model1) M1) (vsp E - 320) 64)
  /\ (forall a n, ahl_ceil ar <= a -> a + n <= 2 ^ 64 -> avis (ahid A1 model1) a n)
  /\ (forall a n, 0 <= a -> a + n <= 6905856 -> avis (ahid A1 model1) a n)
  /\ (forall o n, 6759112 <= o -> o + n <= 6759176 -> 0 < n -> o mod 8 = 0 -> n mod 8 = 0 ->
        L5KA.zeros_at M1 (o / 8 + 2147450880) (n / 8) /\ avis (ahid A1 model1) (o / 8 + 2147450880) (n / 8) /\ aacc M1 o n).
Proof.
  intros HH ASTK.
  pose proof (xgeo E X) as (GSLO & GSHI & GSPT & GS32 & GCEIL).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ _ _ _ _ _ _ HH) as (_ & VIS & VIMG & _).
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as ST. rewrite (L5A.aly_segs L C LYa) in ST.
  pose proof (L5A.statics_facts L C M1 LYa ST) as (GOT & CSB & CUAR & _).
  pose proof ASTK as (A16 & _ & _ & _ & SDEF & _). unfold SCR in SDEF.
  set (H := ahid A1 model1) in *.
  assert (WST : forall a n, vsp E - 18432 <= a -> a + n <= vsp E -> 0 <= n -> L5.writable RSEGS (mrestrict H M1) a n).
  { intros a n H1 H2 H3. apply (proj2 (L5A.writable_vis H M1 a n (VIS a n ltac:(clear - H1 GSLO; lia) ltac:(clear - H2 GSPT GSHI; lia)) ltac:(clear - H1 GSLO GCEIL; lia) ltac:(clear - H2 GSPT GSHI; lia))).
    apply (L5C.writable_of_defined RSEGS); [| clear - H1 GSLO GCEIL; lia| clear - H2 GSPT GSHI; lia]. apply (L5.defined_sub M1 (vsp E - 18432) 18432); [exact SDEF| clear - H1; lia| clear - H2; lia]. }
  split.
  { split; [apply L5A.img_clear_mrestrict; exact GOT|].
    split; [apply (proj2 (L5A.u64_at_vis H M1 1309752 2147450880 (VIMG 1309752 8 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear; lia) ltac:(clear; lia))); exact CSB|].
    split; [apply (proj2 (L5A.u32_at_vis H M1 1309760 1 (VIMG 1309760 4 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear; lia) ltac:(clear; lia))); exact CUAR|].
    split; apply WST; clear; lia. }
  split; [exact VIS|]. split; [exact VIMG|].
  intros o n Ho1 Ho2 Hn O8 N8.
  destruct (aic_img_shadow _ _ _ _ _ ICok _ _ _ _ _ _ _ HH o n) as (Z0 & SAL).
  { rewrite (L5A.aly_img_lo L C LYa). clear - Ho1; lia. }
  { rewrite (L5A.aly_img_hi L C LYa). clear - Ho2; lia. }
  { exact Hn. }
  { rewrite (aicl_poison IL ILY). repeat (apply Forall_cons; [cbn [fst snd]; clear - Ho1 Ho2; lia|]). apply Forall_nil. }
  assert (EO : o = 8 * (o / 8)) by (clear - O8; pose proof (Z.div_mod o 8 ltac:(lia)); lia).
  assert (EN : n = 8 * (n / 8)) by (clear - N8; pose proof (Z.div_mod n 8 ltac:(lia)); lia).
  assert (INS : forall i, 0 <= i < n / 8 -> in_shadow_of o n (o / 8 + 2147450880 + i)).
  { intros i Hi. unfold in_shadow_of, S, SB. split; [clear - Hi; lia|].
    assert (Q : o / 8 + n / 8 - 1 <= (o + n - 1) / 8) by (apply Z.div_le_lower_bound; [clear; lia| clear - EO EN Hn; lia]). clear - Q Hi. lia. }
  split; [intros i Hi; exact (Z0 _ (INS i Hi))|].
  split; [apply (L5A.avis_of_shadow_allowed A1 model1 o n _ _ SAL); exact INS|].
  intros a Ha. left. apply Z0. unfold in_shadow_of. unfold S. split.
  - pose proof (Z.div_le_mono o a 8 ltac:(clear; lia) ltac:(clear - Ha; lia)). clear - H0. lia.
  - pose proof (Z.div_le_mono a (o + n - 1) 8 ltac:(clear; lia) ltac:(clear - Ha; lia)). clear - H0. lia.
Qed.

(* [comment removed for export] *)
Definition xpres (E : dve) (Mc M1 : mem) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> aclient L ar (vLB E) (FF' E) (vsp E - 256) XSCR a -> ~ DX a -> M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a).
Definition xdk (E : dve) (Mc M1 : mem) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> aclient L ar (vLB E) (FF' E) (vsp E - 256) XSCR a -> Mc (Z_to_bv 64 a) <> None -> M1 (Z_to_bv 64 a) <> None.
Lemma xpres_refl E M : xpres E M M. Proof. intros a _ _ _. reflexivity. Qed.
Lemma xdk_refl E M : xdk E M M. Proof. intros a _ _ D. exact D. Qed.
Lemma xpres_trans E M1 M2 M3 : xpres E M1 M2 -> xpres E M2 M3 -> xpres E M1 M3.
Proof. intros P1 P2 a Ha Hc Hn. rewrite (P2 a Ha Hc Hn). exact (P1 a Ha Hc Hn). Qed.
Lemma xdk_trans E M1 M2 M3 : xdk E M1 M2 -> xdk E M2 M3 -> xdk E M1 M3.
Proof. intros P1 P2 a Ha Hc D. exact (P2 a Ha Hc (P1 a Ha Hc D)). Qed.

(* [comment removed for export] *)
Lemma dx_close E (X : dkc L ar HI E) Mc modelc LKc Ac (M1 : mem) model1 A1 :
  dsg L ar HI E (vax E) Mc modelc LKc Ac -> PNST.bax_dec (vax E) = false ->
  ri_inv HI (vLB E) (FF' E) LKc (vcr E) A1 M1 (vml_of model1) -> L5CA.amodel_ok A1 model1 -> model_rt modelc model1 -> incl Ac A1 ->
  astk ar M1 (vsp E) SCR -> xpres E Mc M1 -> xdk E Mc M1 ->
  PNST.bdec_ok RSEGS PMA.AN M1 true -> PNSTA.atexit_stA RSEGS PMA.AD PMA.AAD PMA.AN M1 (PNST.bax_add_dec (vax E)) ->
  dsg L ar HI E (PNST.bax_add_dec (vax E)) M1 model1 LKc A1.
Proof.
  intros ST COLD HH1 AM1 RT1 IA1 ASTK1 PRES DK DEC1 ATX1.
  pose proof ST as (BI & DF & AF & DV & AV & BASE & ERR & C128 & C176).
  pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10). cbn [app] in B1.
  pose proof (c_G L ar HI E X) as G'. destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 3) with 512 in *. change (512 / 8) with 64 in *. unfold SCR in *. unfold xpres, xdk, XSCR in *.
  pose proof (c_GEOM L ar HI E X) as G. unfold PNADD.geom in G.
  destruct G as (GS1 & GS32 & GF1 & GFA8 & GFSH & GFS & GFI & GV1 & GV8 & GVSH & GVS & GVF & GFF1 & GFF32 & GFFSH & GFFS & GFFI & GFFf & GFFv & GFL1 & GFLSH & GFLF & GFLS & GFLf & GFLv).
  destruct (c_BLK L ar HI E X) as (Bq & Bm & HB & HB1 & HB2).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ B1) as (WB & _).
  destruct (WB _ HB) as ((BB0 & _ & _ & _ & BBC & _) & _). cbn [fst snd] in BB0, BBC.
  pose proof (geom_rng L ar HI E X) as (R1' & R2' & R3' & R4' & R5' & R6' & R7' & R8' & R9' & R10' & R11' & R12' & R13' & R14').
  assert (NDX : forall a, ~ (6759112 <= a < 6897520) -> ~ DX a) by (intros a N Da; apply N; exact (DX_img a Da)).
  (* [comment removed for export] *)
  assert (AGST : forall a, 0 <= a < 2 ^ 64 -> ahl_ceil ar <= a < 2 ^ 47 -> ~ (vsp E - 256 - 4096 <= a < vsp E - 256) -> M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)).
  { intros a Ha Hs Hns. apply PRES; [exact Ha| apply L5SAR.stack_client; [exact Hs| exact Hns]|]. apply NDX. clear - Hs GFCEIL GFR. lia. }
  assert (WDX : forall a, DX a -> ~ L5.outside (W E) a).
  { intros a Da Ho. unfold W in Ho. rewrite COLD in Ho. unfold PNST.dec_W in Ho. cbn [PNL.pn_inf_guard PNL.pn_nan_guard PNL.pn_inf_obj PNL.pn_nan_obj pa_atexit PMA.AN NADDR_A PMA.AD ADDR_A] in Ho.
    unfold DX, DXd, DXa in Da.
    assert (Cs : 6759112 <= a < 6759136 \/ 6759136 <= a < 6759144 \/ 6759144 <= a < 6759168 \/ 6759168 <= a < 6759176 \/ 6896976 <= a < 6896976 + 544) by (clear - Da; lia).
    destruct Cs as [Cs|[Cs|[Cs|[Cs|Cs]]]].
    - apply (Ho (6759112, 24)); [do 3 right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - Cs; lia].
    - apply (Ho (6759136, 8)); [right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - Cs; lia].
    - apply (Ho (6759144, 24)); [do 4 right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - Cs; lia].
    - apply (Ho (6759168, 8)); [do 2 right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - Cs; lia].
    - apply (Ho (6896976, 544)); [do 5 right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - Cs; lia]. }
  assert (CL0 : forall a, aclient L ar (vLB E) (vFF E) (vsp E) 18432 a -> aclient L ar (vLB E) (FF' E) (vsp E - 256) 4096 a).
  { intros a Hc. apply L5SAR.aclient_cons. apply (L5SAR.aclient_mono L ar (vLB E) (vFF E) (vsp E) 18432 (vsp E - 256) 4096 a Hc). intros x Hx. clear - Hx. lia. }
  assert (AGI : forall a, 65536 <= a < 6905856 -> ~ DX a -> (a < 1282048 \/ PNST.dep PMA.AD PMA.AN a) -> M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)).
  { intros a Ha ND Hd. apply PRES; [clear - Ha; lia| | exact ND]. destruct Hd as [Hd|Hd]; [| apply dep_client; exact Hd].
    unfold aclient, aclient_g. right; right; left. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [clear - Ha; lia|].
    intros Q. pose proof (L5A.aly_static_lo L C LYa a Q) as Q'. clear - Q' Hd. lia. }
  unfold dsg. split.
  { unfold PMAUK.binv. cbn [app]. split; [exact HH1|]. split; [exact AM1|]. split; [eapply L5LZ.model_rt_trans; [exact B3| exact RT1]|].
    split; [intros x Hx; apply IA1; apply B4; exact Hx|]. split; [exact B5|].
    split; [exact ASTK1|].
    split. { eapply L5SAR.ek_trans; [exact B7|]. intros a (Ha & Hc & Ho). apply PRES; [exact Ha| exact (CL0 a Hc)|]. intros Da. exact (WDX a Da Ho). }
    split. { eapply L5SAR.dk_trans; [exact B8|]. intros a Ha Hc HM. exact (DK a Ha (CL0 a Hc) HM). }
    split. { apply (GOWN Mc M1 B9). intros a Ha. pose proof (GOCR a Ha) as OC. apply AGST; [clear - OC R1' R2'; lia| clear - OC GSLO GSPT R2'; lia| clear - OC; lia]. }
    intros i Hi. rewrite PRES; [apply B10; exact Hi| | |]; change (ff_bytes 3) with 512 in Hi; change (512 / 8) with 64 in Hi.
    - clear - Hi R9' R10'; unfold PNADD.SH, PNADD.SBv, SB in *; lia.
    - apply (L5SAR.fframe_shadow_client L ar _ (FF' E) (vsp E - 256) 4096 (vF E) 3 (vsp E - 256 + 32)); [left; reflexivity|]. unfold in_shadow_of, S. change (ff_bytes 3) with 512.
      rewrite (proj1 (proj2 GF8)). clear - Hi; lia.
    - apply NDX. assert (E0 : 0 <= vF E / 8) by (clear - GFF1; apply Z.div_pos; lia). unfold SB. clear - Hi E0. lia. }
  split.
  { intros i Hi. rewrite PRES; [exact (DF i Hi)| clear - Hi R3' R4'; lia| |].
    - apply (L5SAR.block_client L ar _ (FF' E) _ _ Bq Bm); [exact HB| clear - Hi HB1 HB2; lia].
    - apply NDX. clear - Hi GFI. lia. }
  split.
  { apply (aacc_agree Mc M1 _ _); [| exact AF]. intros a Ha. pose proof (S_rng (vfirst E) 48 a GFA8 ltac:(clear; lia) Ha) as SR. change ((48 + 7) / 8) with 6 in SR.
    apply PRES; [clear - SR R11' R12'; unfold PNADD.SH, PNADD.SBv in *; lia| |].
    - unfold aclient, aclient_g. do 6 right. exists (Bq, Bm). split; [exact HB|]. cbn [fst snd]. unfold in_shadow_of.
      pose proof (sh6_in_blk (vfirst E) Bq Bm (S a - (vfirst E / 8 + 2147450880)) GFA8 ltac:(clear - BB0; lia) HB1 HB2 ltac:(clear - SR; lia)) as Y. unfold S, SB in *. clear - Y. lia.
    - apply NDX. assert (E0 : 0 <= vfirst E / 8) by (clear - GF1; apply Z.div_pos; lia). clear - SR E0. lia. }
  destruct (c_VST L ar HI E X) as (VST1 & VST2).
  split.
  { intros i Hi. rewrite AGST; [exact (DV i Hi)| clear - Hi R5' R6'; lia| clear - Hi VST1 VST2 GSLO GSPT; lia| clear - Hi VST1; lia]. }
  split.
  { apply (aacc_agree Mc M1 _ _); [| exact AV]. intros a Ha. pose proof (S_rng (vvp E) 16 a GV8 ltac:(clear; lia) Ha) as SR. change ((16 + 7) / 8) with 2 in SR.
    apply PRES; [clear - SR R13' R14'; unfold PNADD.SH, PNADD.SBv in *; lia| |].
    - apply (L5SAR.stk_shadow_client L ar (vLB E) (FF' E) (vsp E - 256) 4096 (S a)); [| clear - GSPT; lia].
      unfold in_shadow_of, S. pose proof (Z.div_le_mono (ahl_ceil ar) a 8 ltac:(clear; lia) ltac:(clear - Ha VST1 GSLO; lia)) as Q1.
      pose proof (Z.div_le_mono a (ahl_ceil ar + (ar_sptop ar - ahl_ceil ar) - 1) 8 ltac:(clear; lia) ltac:(clear - Ha VST2; lia)) as Q2. clear - Q1 Q2. lia.
    - apply NDX. assert (E0 : 0 <= vvp E / 8) by (clear - GV1; apply Z.div_pos; lia). clear - SR E0. lia. }
  split.
  { apply (base_x Mc M1); [| exact BASE]. intros a Ha.
    assert (ND : ~ DX a) by (unfold DX, DXd, DXa; clear - Ha; lia).
    apply AGI; [clear - Ha; lia| exact ND|].
    destruct Ha as [Ha|[Ha|[Ha|Ha]]]; [left; clear - Ha; lia| right; right; left; cbn [pa_canary PMA.AD ADDR_A]; exact Ha| |]; right; apply PNST.dep_of_j.
    - apply PMST.in_foot_nl. cbn [pa_need_locks PMA.AD ADDR_A]. exact Ha.
    - apply PMST.in_foot_ll. cbn [pa_locale_lock PMA.AD ADDR_A]. exact Ha. }
  split.
  { destruct ERR as (EG & EDEC & EA). split; [| split; [rewrite PNST.bax_dec_add; exact DEC1| exact ATX1]].
    replace (PNST.bax_cat (PNST.bax_add_dec (vax E))) with (PNST.bax_cat (vax E)) by (destruct (vax E); reflexivity).
    cbn [pa_errcat_guard PMA.AD ADDR_A] in *.
    assert (AGG : forall i, 6759104 <= i < 6759106 -> M1 (Z_to_bv 64 i) = Mc (Z_to_bv 64 i)).
    { intros i Hi. apply AGI; [clear - Hi; lia| apply NDX; clear - Hi; lia|]. right. apply PNST.dep_of_j. apply PMST.in_foot_errg. cbn [pa_errcat_guard PMA.AD ADDR_A]. exact Hi. }
    destruct (PNST.bax_cat (vax E)).
    - apply (L5C.u8_at_agree RSEGS Mc M1); [intros i Hi; apply AGG; clear - Hi; lia| clear; lia| clear; lia| exact EG].
    - intros i Hi. rewrite (AGG i Hi). exact (EG i Hi). }
  split; [apply (L5C.u64_at_agree RSEGS Mc M1); [| clear - R1'; lia| clear - R2'; lia| exact C128]| apply (L5C.u64_at_agree RSEGS Mc M1); [| clear - R1'; lia| clear - R2'; lia| exact C176]]; intros i Hi.
  all: apply AGST; [clear - Hi R1' R2'; lia| clear - Hi GSLO GSPT R2'; lia| clear - Hi; lia].
Qed.

(* [comment removed for export] *)
Definition xagr (E : dve) (sp' scr' : Z) (D : Z -> Prop) (M M' : mem) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> aclient L ar (vLB E) (FF' E) sp' scr' a -> ~ D a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Definition xdkl (E : dve) (sp' scr' : Z) (M M' : mem) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> aclient L ar (vLB E) (FF' E) sp' scr' a -> M (Z_to_bv 64 a) <> None -> M' (Z_to_bv 64 a) <> None.
Lemma xagr_trans E sp' scr' D M1 M2 M3 : xagr E sp' scr' D M1 M2 -> xagr E sp' scr' D M2 M3 -> xagr E sp' scr' D M1 M3.
Proof. intros P1 P2 a Ha Hc Hn. rewrite (P2 a Ha Hc Hn). exact (P1 a Ha Hc Hn). Qed.
Lemma xdkl_trans E sp' scr' M1 M2 M3 : xdkl E sp' scr' M1 M2 -> xdkl E sp' scr' M2 M3 -> xdkl E sp' scr' M1 M3.
Proof. intros P1 P2 a Ha Hc D. exact (P2 a Ha Hc (P1 a Ha Hc D)). Qed.
Lemma xagr_mono E sp1 scr1 sp2 scr2 (D1 D2 : Z -> Prop) M M' :
  xagr E sp1 scr1 D1 M M' -> (forall x, sp1 - scr1 <= x < sp1 -> sp2 - scr2 <= x < sp2) -> (forall a, D1 a -> D2 a) -> xagr E sp2 scr2 D2 M M'.
Proof.
  intros P HS HD a Ha Hc Hn. apply P; [exact Ha| | intros Da; exact (Hn (HD a Da))].
  apply (L5SAR.aclient_mono L ar (vLB E) (FF' E) sp2 scr2 sp1 scr1 a Hc HS).
Qed.
Lemma xdkl_mono E sp1 scr1 sp2 scr2 M M' :
  xdkl E sp1 scr1 M M' -> (forall x, sp1 - scr1 <= x < sp1 -> sp2 - scr2 <= x < sp2) -> xdkl E sp2 scr2 M M'.
Proof.
  intros P HS a Ha Hc Hn. apply P; [exact Ha| | exact Hn].
  apply (L5SAR.aclient_mono L ar (vLB E) (FF' E) sp2 scr2 sp1 scr1 a Hc HS).
Qed.
Lemma xagr_piece E LKc cr A Mh V sp' scr' (D Wp : Z -> Prop) M M' :
  ri_inv HI (vLB E) (FF' E) LKc cr A Mh V -> 0x7fff80000000 <= ar_sptop ar <= 2 ^ 47 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> (forall a, Wp a -> (sp' - scr' <= a < sp' /\ ahl_ceil ar <= a) \/ D a) ->
  xagr E sp' scr' D M M'.
Proof.
  intros HH SPT FR WP a Ha Hc Hn. apply FR; [exact Ha|]. intros Wa. destruct (WP a Wa) as [(Y & Y')|Y]; [| exact (Hn Y)].
  destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ _ _ _ _ _ _ sp' scr' a HH SPT Hc) as [(Y1 & Y2)|Y1]; [exact (Y2 Y)| clear - Y1 Y'; lia].
Qed.

(* [comment removed for export] *)
Lemma xstrlen E (X : dkc L ar HI E) LKc (fx : FPState) R M model A (fr lit K ra : Z) (buf : list byte) :
  ri_inv HI (vLB E) (FF' E) LKc (vcr E) A M (vml_of model) -> amodel_ok A model -> astk ar M (vsp E) SCR -> base_ok M ->
  256 <= fr -> fr + 2304 <= 256 + XSCR -> fr mod 16 = 0 ->
  getr R (reg 10) = Z_to_bv 64 lit -> getr R (reg 4) = Z_to_bv 64 (hl_tp L) -> getr R (reg 1) = Z_to_bv 64 ra -> ra mod 2 = 0 -> 0 <= ra < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (vsp E - fr) ->
  In (lit, K + 1) (icl_globals IL) -> 65536 <= lit -> lit + Z.of_nat (length buf) <= 1282048 -> 0 <= K < 2 ^ 27 ->
  rdn RSEGS (fun _ => None) (Z_to_bv 64 lit) (length buf) = Some buf ->
  (lit + K) / 8 * 8 + 8 <= lit + Z.of_nat (length buf) ->
  nth (Z.to_nat K) buf (Z_to_bv 8 0) = Z_to_bv 8 0 ->
  (forall j, (j < Z.to_nat K)%nat -> nth j buf (Z_to_bv 8 0) <> Z_to_bv 8 0) ->
  (forall R' M' model',
      getr R' (reg 10) = Z_to_bv 64 K -> regs_preserved R R' ->
      ri_inv HI (vLB E) (FF' E) LKc (vcr E) A M' (vml_of model') -> amodel_ok A model' -> model_rt model model' -> astk ar M' (vsp E) SCR ->
      xagr E (vsp E - fr) 2304 (fun _ => False) M M' -> mem_grows M M' ->
      srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R' ra M' model') (vK E)) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0x6336c M model) (vK E).
Proof.
  intros HH AM ASTK BASE Hfr1 Hfr2 Hfr16 R10 R4 R1 Hra Hra' R2 GIN Hl1 Hl2 HK RDN WEND NUL NNUL KONT.
  pose proof (xgeo E X) as (GSLO & GSHI & GSPT & GS32 & GCEIL). unfold XSCR, SCR in *.
  pose proof (aic_strlen _ _ _ _ _ ICok) as SL. unfold astrlen_spec in SL. cbv zeta in SL.
  rewrite (L5A.aly_segs L C LYa), (aicl_strlen IL ILY), (aicl_scr_strlen IL ILY), (aicl_ro_lo IL ILY), (aicl_ro_hi IL ILY) in SL.
  assert (U2 : bv_unsigned (getr R 2%bv) = vsp E - fr) by (rewrite L5K.rl2, R2; apply L5.unsigned_lit; clear - GSLO GSHI GSPT GCEIL Hfr1 Hfr2; lia).
  destruct BASE as (RO0 & _). cbn [pa_rw_lo PMA.AD ADDR_A] in RO0.
  pose proof (aic_globals _ _ _ _ _ ICok _ _ _ _ _ _ _ HH) as GL. rewrite Forall_forall in GL. destruct (GL _ GIN) as (GSB & _). cbn [fst snd] in GSB.
  pose proof (L5CBR.globals_facts IL ILY lit (K + 1) GIN) as (G0 & G1 & G8 & _).
  unfold PMSPA.cfg.
  apply (SL fx R M model (vLB E) (FF' E) LKc (vcr E) A lit K buf (vK E) HH (proj1 AM) (proj2 AM)); clear SL.
  - rewrite L5K.rl10. exact R10.
  - rewrite L5K.rl4. exact R4.
  - rewrite L5K.rl1, R1. apply Hoare.ret_ok_even. rewrite L5.unsigned_lit by exact Hra'. exact Hra.
  - rewrite U2. apply (L5SAR.astack_ok_of_astk L ar C LYa M M (vsp E) 18432 fr 2304 ASTK (fun x Hx => Hx)); [clear - Hfr1; lia| clear; lia| clear - Hfr2; lia|].
    rewrite Zminus_mod, Hfr16, Z.sub_0_r, Z.mod_mod by (clear; lia). clear - GS32. pose proof (Z.div_mod (vsp E) 32 ltac:(lia)) as D. rewrite GS32, Z.add_0_r in D. rewrite D. replace (32 * (vsp E / 32)) with ((2 * (vsp E / 32)) * 16) by lia. apply Z_mod_mult.
  - clear - Hl1; lia.
  - clear - Hl2; lia.
  - exact HK.
  - rewrite (L5C.rdn_agree RSEGS (fun _ => None) M (length buf) lit); [exact RDN| clear - Hl1; lia| clear - Hl2; lia|]. intros i Hi. apply RO0. clear - Hi Hl1 Hl2; lia.
  - exact WEND.
  - exact NUL.
  - exact NNUL.
  - intros i Hi. left. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). clear - Hi Hl1 Hl2. lia.
  - intros a Ha. apply RO0. clear - Ha; lia.
  - apply (L5CBR.aacc_of_blk M lit (K + 1) lit (K + 1) GSB G8); [clear - G0; lia| clear; lia| clear; lia].
  - apply (L5SAR.app_rng_img ar); [clear - GSPT; lia| clear - Hl1; lia| clear - G1; lia].
  - exact (c_K0 L ar HI E X).
  - intros R' M' model' R10' RP' PRES' SDEF' GROW' RT' MI' HH'. rewrite U2 in PRES', SDEF'. rewrite L5K.rl1, R1.
    assert (AM' : L5CA.amodel_ok A model') by (split; [rewrite (L5LZ.model_rt_halted _ _ RT'); exact (proj1 AM)| exact MI']).
    apply (KONT R' M' model'); [rewrite <- L5K.rl10; exact R10'| exact RP'| exact HH'| exact AM'| exact RT'| | | exact GROW'].
    + apply (L5SAR.astk_after_eq L ar C HI HIok _ _ _ _ _ M M M' _ (vsp E) _ (vsp E - fr) 2304 HH ASTK (mem_grows_refl M)); [| exact SDEF'| clear - Hfr2; lia| clear - Hfr1; lia| clear; lia].
      intros a Ha Hs Hns. apply PRES'; [exact Ha|]. apply L5SAR.stack_client; [exact Hs| exact Hns].
    + intros a Ha Hc _. exact (PRES' a Ha Hc).
Qed.

(* [comment removed for export] *)
Lemma xmemmove E (X : dkc L ar HI E) LKc (fx : FPState) R M model A (fr dst src n ra lit k : Z) (bs : list byte) :
  ri_inv HI (vLB E) (FF' E) LKc (vcr E) A M (vml_of model) -> amodel_ok A model -> astk ar M (vsp E) SCR -> base_ok M ->
  256 <= fr -> fr + 2560 <= 256 + XSCR -> fr mod 16 = 0 ->
  getr R (reg 10) = Z_to_bv 64 dst -> getr R (reg 11) = Z_to_bv 64 src -> getr R (reg 12) = Z_to_bv 64 n ->
  getr R (reg 4) = Z_to_bv 64 (hl_tp L) -> getr R (reg 1) = Z_to_bv 64 ra -> ra mod 2 = 0 -> 0 <= ra < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (vsp E - fr) ->
  6759112 <= dst -> dst + n <= 6759176 -> 0 < n <= 2 ^ 27 -> StreamSim.wseg_ok RSEGS (Z_to_bv 64 dst) (Z.to_nat n) = true ->
  In (lit, k) (icl_globals IL) -> lit <= src -> src + n <= lit + k ->
  rdn RSEGS (fun _ => None) (Z_to_bv 64 src) (Z.to_nat n) = Some bs ->
  (forall R' M' model',
      getr R' (reg 10) = Z_to_bv 64 dst -> regs_preserved R R' ->
      ri_inv HI (vLB E) (FF' E) LKc (vcr E) A M' (vml_of model') -> amodel_ok A model' -> model_rt model model' -> astk ar M' (vsp E) SCR ->
      xagr E (vsp E - fr) 2560 (fun a => dst <= a < dst + n) M M' -> xdkl E (vsp E - fr) 2560 M M' -> L5.defined M' dst n ->
      srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R' ra M' model') (vK E)) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0x78370 M model) (vK E).
Proof.
  intros HH AM ASTK BASE Hfr1 Hfr2 Hfr16 R10 R11 R12 R4 R1 Hra Hra' R2 Hd1 Hd2 Hn WSEG GIN Hs1 Hs2 RDN KONT.
  pose proof (xgeo E X) as (GSLO & GSHI & GSPT & GS32 & GCEIL). unfold XSCR, SCR in *.
  pose proof (HAJ.aior_memmove _ _ _ _ _ HIok) as MMV. unfold amemmove_spec, amemcpy_spec_at, amem_pre, amem_post in MMV.
  rewrite (L5A.aly_segs L C LYa), (L5A.aly_memmove L C LYa), (L5A.aly_scr_mem L C LYa), (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in MMV.
  assert (U2 : bv_unsigned (getr R 2%bv) = vsp E - fr) by (rewrite L5K.rl2, R2; apply L5.unsigned_lit; clear - GSLO GSHI GSPT GCEIL Hfr1 Hfr2; lia).
  destruct BASE as (RO0 & _). cbn [pa_rw_lo PMA.AD ADDR_A] in RO0.
  pose proof (aic_globals _ _ _ _ _ ICok _ _ _ _ _ _ _ HH) as GL. rewrite Forall_forall in GL. destruct (GL _ GIN) as (GSB & _). cbn [fst snd] in GSB.
  pose proof (L5CBR.globals_facts IL ILY lit k GIN) as (G0 & G1 & G8 & _).
  destruct (xview E X LKc A M model HH ASTK) as (_ & _ & _ & ZOBJ).
  destruct (ZOBJ 6759112 64 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(reflexivity) ltac:(reflexivity)) as (_ & _ & ACCD).
  unfold PMSPA.cfg. apply (MMV fx R M model (vLB E) (FF' E) LKc (vcr E) A dst src n bs (vK E)); clear MMV.
  - split; [exact HH|]. split; [exact (proj1 AM)|]. split; [exact (proj2 AM)|].
    split; [rewrite L5K.rl10; exact R10|]. split; [rewrite L5K.rl12; exact R12|]. split; [clear - Hn; lia|].
    split; [rewrite L5K.rl4; exact R4|]. split; [rewrite L5K.rl1, R1; apply Hoare.ret_ok_even; rewrite L5.unsigned_lit by exact Hra'; exact Hra|].
    split. { rewrite U2. apply (L5SAR.astack_ok_of_astk L ar C LYa M M (vsp E) 18432 fr 2560 ASTK (fun x Hx => Hx)); [clear - Hfr1; lia| clear; lia| clear - Hfr2; lia|].
             rewrite Zminus_mod, Hfr16, Z.sub_0_r, Z.mod_mod by (clear; lia). clear - GS32. pose proof (Z.div_mod (vsp E) 32 ltac:(lia)) as D. rewrite GS32, Z.add_0_r in D. rewrite D. replace (32 * (vsp E / 32)) with ((2 * (vsp E / 32)) * 16) by lia. apply Z_mod_mult. }
    split; [intros a Ha; apply ACCD; clear - Ha Hd1 Hd2; lia|].
    split. { intros i Hi. rewrite U2. apply dep_clientw; [apply DX_dep; left; unfold DXd; clear - Hi Hd1 Hd2; lia| clear - Hi Hd1; lia]. }
    split. { apply (writable_img M dst n WSEG); [clear - Hd1; lia| clear - Hn; lia| clear - Hd2; lia]. }
    split; [exact (c_K0 L ar HI E X)|]. apply (L5SAR.app_rng_img ar); [clear - GSPT; lia| clear - Hd1; lia| clear - Hd2; lia].
  - rewrite L5K.rl11. exact R11.
  - apply (L5CBR.aacc_of_blk M lit k src n GSB G8); [clear - G0; lia| exact Hs1| exact Hs2].
  - clear - Hs1 Hs2 G0 G1 Hn; lia.
  - apply (L5SAR.app_rng_img ar); [clear - GSPT; lia| clear - Hs1 G0; lia| clear - Hs2 G1; lia].
  - intros i Hi. left. clear - Hi Hs1 Hs2 G0 G1; lia.
  - rewrite (L5C.rdn_agree RSEGS (fun _ => None) M (Z.to_nat n) src); [exact RDN| clear - Hs1 G0; lia| rewrite Z2Nat.id by (clear - Hn; lia); clear - Hs2 G1; lia|].
    intros i Hi. rewrite Z2Nat.id in Hi by (clear - Hn; lia). apply RO0. clear - Hi Hs1 Hs2 G0 G1; lia.
  - intros _. right. clear - Hs2 G1 Hd1; lia.
  - intros R' M' model' R10' RP' BYTES PRES' SDEF' RT' MI' HH'. rewrite U2 in PRES', SDEF'. rewrite L5K.rl1, R1.
    assert (AM' : L5CA.amodel_ok A model') by (split; [rewrite (L5LZ.model_rt_halted _ _ RT'); exact (proj1 AM)| exact MI']).
    assert (DDEF : L5.defined M' dst n).
    { intros i Hi. destruct (BYTES i Hi) as (v & _ & Bv). unfold byte_at in Bv. rewrite Bv. discriminate. }
    apply (KONT R' M' model'); [rewrite <- L5K.rl10; exact R10'| exact RP'| exact HH'| exact AM'| exact RT'| | | | exact DDEF].
    + apply (L5SAR.astk_after_eq L ar C HI HIok _ _ _ _ _ M M M' _ (vsp E) _ (vsp E - fr) 2560 HH ASTK (mem_grows_refl M)); [| exact SDEF'| clear - Hfr2; lia| clear - Hfr1; lia| clear; lia].
      intros a Ha Hs Hns. apply PRES'; [exact Ha| apply L5SAR.stack_client; [exact Hs| exact Hns]|]. clear - Hs Hd2 GCEIL. lia.
    + intros a Ha Hc Hn'. exact (PRES' a Ha Hc Hn').
    + intros a Ha Hc HM. destruct (L5SAR.rng_dec a dst (dst + n)) as [Y|Y].
      * replace a with (dst + (a - dst)) by (clear; lia). apply DDEF. clear - Y; lia.
      * rewrite (PRES' a Ha Hc Y). exact HM.
Qed.

(* [comment removed for export] *)
Lemma xatexit E (X : dkc L ar HI E) (EXT : HAJ.asan_ext_ok L ar SCFG HI PMA.EXT) LKc (fx : FPState) R M model A (f a d ra : Z) (hs : list (Z * Z)) :
  ri_inv HI (vLB E) (FF' E) LKc (vcr E) A M (vml_of model) -> amodel_ok A model -> astk ar M (vsp E) SCR -> base_ok M ->
  getr R (reg 10) = Z_to_bv 64 f -> getr R (reg 11) = Z_to_bv 64 a -> getr R (reg 12) = Z_to_bv 64 d ->
  getr R (reg 4) = Z_to_bv 64 (hl_tp L) -> getr R (reg 1) = Z_to_bv 64 ra -> ra mod 2 = 0 -> 0 <= ra < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (vsp E - 256) ->
  (length hs <= 2)%nat -> HAJ.atexit_cells RSEGS M 6896976 1148964 619876 1148964 687916 449180 hs ->
  (forall fx' R' M' model' A',
      regs_preserved R R' ->
      ri_inv HI (vLB E) (FF' E) LKc (vcr E) A' M' (vml_of model') -> amodel_ok A' model' -> model_rt model model' -> incl A A' -> astk ar M' (vsp E) SCR ->
      xagr E (vsp E - 256) 1024 DXa M M' -> xdkl E (vsp E - 256) 1024 M M' ->
      HAJ.atexit_cells RSEGS M' 6896976 1148964 619876 1148964 687916 449180 (hs ++ [(f, a)]) ->
      srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx' R' ra M' model') (vK E)) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0x6da18 M model) (vK E).
Proof.
  intros HH AM ASTK BASE R10 R11 R12 R4 R1 Hra Hra' R2 HLEN ATX KONT.
  pose proof (xgeo E X) as (GSLO & GSHI & GSPT & GS32 & GCEIL). unfold XSCR, SCR in *.
  pose proof (HAJ.aex_cxa_atexit _ _ _ _ _ EXT) as CXA. unfold HAJ.cxa_atexit_spec in CXA.
  cbn [PMA.EXT HAJ.ec_cxa_pc HAJ.ec_cxa_scr HAJ.ec_atexit HAJ.ec_f0 HAJ.ec_a0 HAJ.ec_f1 HAJ.ec_a1 HAJ.ec_atc HAJ.ec_nl
       paa_cxa_atexit_icpt paa_atexit_f0 paa_atexit_a0 paa_at_cxa_atexit PMA.AAD AADDR_A pa_atexit pa_need_locks PMA.AD ADDR_A PNL.pn_drv_call PNL.pn_drv_guard PMA.AN NADDR_A] in CXA.
  rewrite (L5A.aly_segs L C LYa) in CXA.
  assert (U2 : bv_unsigned (getr R 2%bv) = vsp E - 256) by (rewrite L5K.rl2, R2; apply L5.unsigned_lit; clear - GSLO GSHI GSPT GCEIL; lia).
  destruct BASE as (_ & _ & NL & _). cbn [pa_need_locks PMA.AD ADDR_A] in NL.
  unfold PMSPA.cfg. apply (CXA fx R M model (vLB E) (FF' E) LKc (vcr E) A (vK E) hs f a d); clear CXA.
  { exact HH. }
  { exact (proj1 AM). }
  { exact (proj2 AM). }
  { rewrite L5K.rl10. exact R10. }
  { rewrite L5K.rl11. exact R11. }
  { rewrite L5K.rl12. exact R12. }
  { exact HLEN. }
  { exact ATX. }
  { exact NL. }
  { rewrite L5K.rl4. exact R4. }
  { rewrite L5K.rl1, R1. apply Hoare.ret_ok_even. rewrite L5.unsigned_lit by exact Hra'. exact Hra. }
  { rewrite U2. apply (L5SAR.astack_ok_of_astk L ar C LYa M M (vsp E) 18432 256 1024 ASTK (fun x Hx => Hx)); [clear; lia| clear; lia| clear; lia|].
    replace (vsp E - 256) with (vsp E + (-16) * 16) by (clear; lia). rewrite Z_mod_plus_full. clear - GS32.
    pose proof (Z.div_mod (vsp E) 32 ltac:(lia)) as D. rewrite GS32, Z.add_0_r in D. rewrite D. replace (32 * (vsp E / 32)) with ((2 * (vsp E / 32)) * 16) by lia. apply Z_mod_mult. }
  { exact (c_K0 L ar HI E X). }
  intros fx2 R2' M2 model2 Aw2 RP2 A02 ATX2 FRC2 DX2 SCR2 MRT2 INC2 MI2 HH2.
  rewrite U2 in FRC2, SCR2. rewrite L5K.rl1, R1.
  assert (AM2 : L5CA.amodel_ok Aw2 model2) by (split; [rewrite (L5LZ.model_rt_halted _ _ MRT2); exact (proj1 AM)| exact MI2]).
  apply (KONT fx2 R2' M2 model2 Aw2 RP2 HH2 AM2 MRT2 INC2); [| | | exact ATX2].
  - apply (L5SAR.astk_after_eq L ar C HI HIok _ _ _ _ _ M M M2 _ (vsp E) _ (vsp E - 256) 1024 HH ASTK (mem_grows_refl M)); [| exact SCR2| clear; lia| clear; lia| clear; lia].
    intros x Hx Hs Hns. apply FRC2; [exact Hx| apply L5SAR.stack_client; [exact Hs| exact Hns]|]. clear - Hs GCEIL. lia.
  - intros x Hx Hc Hn'. exact (FRC2 x Hx Hc Hn').
  - intros x Hx Hc HM. destruct (L5SAR.rng_dec x 6896976 (6896976 + 544)) as [Y|Y].
    + apply DX2; [exact Y| exact HM].
    + rewrite (FRC2 x Hx Hc Y). exact HM.
Qed.

End WithHeap.
End SCFG_1.
End PNADC1.
