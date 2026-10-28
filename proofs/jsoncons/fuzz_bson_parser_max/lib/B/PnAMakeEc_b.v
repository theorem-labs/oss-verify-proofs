(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StreamSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PmSpecsAX_b PnSpecsAa_b
     PmModelFactsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnStepA_b PnStepA2_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmCertKitG PnLayout PnStatics PnStaticsA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b PnRunAa_b PnAErrP_b Ba0_code_rae6a4_ae6a8_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PNAMKE.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

Lemma writable_img M a n : wseg_ok RSEGS (Z_to_bv 64 a) (Z.to_nat n) = true -> 0 <= a -> 0 < n -> a + n <= 2 ^ 64 -> L5.writable RSEGS M a n.
Proof.
  intros W Ha Hn Han d k Hd Hk. destruct k as [|k]. reflexivity.
  eapply (store_ok_sub RSEGS M (Z_to_bv 64 a) _ (Z.to_nat n) (Datatypes.S k)).
  - rewrite L5.unsigned_lit by lia. rewrite Z2Nat.id by lia. lia.
  - apply store_ok_wseg. exact W.
  - rewrite !L5.unsigned_lit by lia. lia.
  - rewrite !L5.unsigned_lit by lia. rewrite Z2Nat.id by lia. lia.
Qed.
Lemma u32_of_u64 M a v : L5.u64_at RSEGS M a v -> L5.u32_at RSEGS M a v.
Proof.
  unfold L5.u64_at, L5.u32_at. intros H. rewrite (SeqExec.rdn_firstn RSEGS M 8%nat (Z_to_bv 64 a) _ 4%nat H) by lia. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma nl_u8 M : L5.img_clear M 0x693f93 0x693f94 -> L5.u8_at RSEGS M 0x693f93 0.
Proof.
  intros IC. unfold L5.u8_at. rewrite (PMCG.rdn_img RSEGS M 0x693f93 0x693f94 0x693f93 1 IC) by lia. vm_compute. reflexivity.
Qed.
Lemma bvu (w : word) : 0 <= bv_unsigned w < 2 ^ 64.
Proof. pose proof (bv_unsigned_in_range 64 w) as X. change (bv_modulus 64) with (2 ^ 64) in X. exact X. Qed.

(* [comment removed for export] *)
Lemma bdep_img a : PNST.dep PMA.AD PMA.AN a -> 0x10000 <= a < 0x696000.
Proof.
  unfold PNST.dep, PNST.pn_foot, pm_foot, pm_initc, PNL.pn_d128_foot.
  cbn [pa_errcat_guard pa_syscat_guard pa_loc_foot pa_atexit pa_canary pa_need_locks pa_locale_lock PMA.AD PMA.AD PNL.pn_inf_guard PNL.pn_nan_guard PNL.pn_inf_obj PNL.pn_nan_obj PMA.AN PMA.AN app].
  intros [(iv & Hin & Hr)|[Hc|(iv & Hin & Hr)]].
  - repeat (destruct Hin as [<-|Hin]; [cbn [fst snd] in Hr; lia|]). destruct Hin.
  - lia.
  - repeat (destruct Hin as [<-|Hin]; [cbn [fst snd] in Hr; lia|]). destruct Hin.
Qed.
Lemma bdec_keep M M' d :
  (forall a, 0 <= a < 2 ^ 64 -> (PNL.pn_inf_guard PMA.AN <= a < PNL.pn_inf_guard PMA.AN + 8 \/ PNL.pn_nan_guard PMA.AN <= a < PNL.pn_nan_guard PMA.AN + 8
      \/ PNL.pn_inf_obj PMA.AN <= a < PNL.pn_inf_obj PMA.AN + 24 \/ PNL.pn_nan_obj PMA.AN <= a < PNL.pn_nan_obj PMA.AN + 24) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  PNST.bdec_ok RSEGS PMA.AN M d -> PNST.bdec_ok RSEGS PMA.AN M' d.
Proof.
  pose proof (PNST.aw_infg _ _ PMA.addrs_wf_B) as G1. pose proof (PNST.aw_nang _ _ PMA.addrs_wf_B) as G2.
  pose proof (PNST.aw_info _ _ PMA.addrs_wf_B) as G3. pose proof (PNST.aw_nano _ _ PMA.addrs_wf_B) as G4.
  intros AG. unfold PNST.bdec_ok, PNST.sso_lit. destruct d.
  - intros (A1 & A2 & (B1 & B2) & (C1 & C2)).
    split; [apply (L5C.u8_at_agree RSEGS M M'); [intros i Hi; apply AG; lia| lia| lia| exact A1]|].
    split; [apply (L5C.u8_at_agree RSEGS M M'); [intros i Hi; apply AG; lia| lia| lia| exact A2]|].
    split; [split; [apply (L5C.u8_at_agree RSEGS M M'); [intros i Hi; apply AG; lia| lia| lia| exact B1]| apply (L5C.defined_agree M M'); [intros i Hi; apply AG; lia| exact B2]]|].
    split; [apply (L5C.u8_at_agree RSEGS M M'); [intros i Hi; apply AG; lia| lia| lia| exact C1]| apply (L5C.defined_agree M M'); [intros i Hi; apply AG; lia| exact C2]].
  - intros (A1 & A2 & A3 & A4).
    split; [intros i Hi; rewrite AG by lia; apply A1; exact Hi|]. split; [intros i Hi; rewrite AG by lia; apply A2; exact Hi|].
    split; [intros i Hi; rewrite AG by lia; apply A3; exact Hi|]. intros i Hi; rewrite AG by lia; apply A4; exact Hi.
Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis EXT : HAJ.asan_ext_ok L ar SCFG HI PMA.EXT.
Let LYa := PMA.ly_as0 L C LY.

Theorem make_ec_ok : PNRAa.make_ec_spec L ar HI.
Proof.
  unfold PNRAa.make_ec_spec, PNRA.make_ec_spec.
  intros fx R M model K LB FF LK Aw cr o v sp r ax HH AM K0 ENT FRM FRS A10 A11 VR AO O8 OD ACC BASE ERR KONT.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH).
  pose proof AM as (Mh & MI). pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof RAok as (Hr1 & Hr2).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11.
  change (PMSPA.pm_scr 1) with 14336 in *.
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw M model HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
  set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK cr Aw M model o 16 sp 14336 HH (PMKA.aobj_of_aobjA FF o 16 AO O8) ltac:(lia) ltac:(reflexivity))
    as ((O1 & O2 & O3 & O4 & O5) & OBIG & ODEF & OVIS & OSHV & OCL & OSHCL).
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as ST. rewrite (L5A.aly_segs L C LYa) in ST.
  pose proof (L5A.statics_facts L C M LYa ST) as (GOT & CSB & CUAR & _).
  assert (HO : bv_unsigned (getr R (reg 10)) = o) by (rewrite A10; apply L5.unsigned_lit; lia).
  assert (V0 : L5.img_clear MV 1249280 1282048) by (apply L5A.img_clear_mrestrict; exact GOT).
  assert (V1 : L5.u64_at RSEGS MV 1309752 2147450880) by (apply (proj2 (L5A.u64_at_vis H M 1309752 2147450880 (VIMG 1309752 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB).
  assert (V2 : L5.u32_at RSEGS MV 1309760 1) by (apply (proj2 (L5A.u32_at_vis H M 1309760 1 (VIMG 1309760 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR).
  assert (V3 : L5.writable RSEGS MV (sp - 128) 128).
  { apply (proj2 (L5A.writable_vis H M (sp - 128) 128 (VIS (sp - 128) 128 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5C.writable_of_defined RSEGS). apply (L5.defined_sub M (sp - 14336) 14336); [exact SDEF| lia| lia]. lia. lia. }
  assert (VZ : L5KA.zeros_at MV ((o / 8) + 2147450880) 2).
  { pose proof (PMKA.obj_shadow_vis L ar C HI LYa HIok LB FF LK cr Aw M model o 16 HH AO O8 ltac:(lia) ltac:(reflexivity) ACC) as X.
    exact X. }
  assert (VW : L5.writable RSEGS MV o 16).
  { apply (proj2 (L5A.writable_vis H M o 16 OVIS ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS). exact ODEF. lia. lia. }
  (* [comment removed for export] *)
  set (WE := (o, 16) :: (if PNST.bax_cat ax then [] else PNST.cat_W PMA.AD)).
  assert (WAPP : PMKA.wapp WE).
  { unfold WE. apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; lia|].
    destruct (PNST.bax_cat ax); [apply PMKA.wapp_nil|]. unfold PNST.cat_W. cbn [pa_errcat_guard pa_atexit PMA.AD ADDR_A].
    apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO; lia|]. apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO; lia|]. apply PMKA.wapp_nil. }
  assert (FRB : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47).
  { intros f Hf. destruct (WF f Hf) as (X1 & X2 & _). unfold app_mem, FS_BYTES in *. lia. }
  destruct ERR as (EG & EDEC & EA). unfold PNSTA.atexit_stA in EA.
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & _ & _ & _ & FSIMG & _). rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in FSIMG.
  assert (OIMG : o + 16 <= 0x10000 \/ 0x696000 <= o).
  { destruct AO as (f & Hf & X1 & X2). destruct (WF f Hf) as (Y1 & Y2 & _). unfold app_mem, FS_BYTES in *. destruct FSIMG; [left; lia| right; lia]. }
  unfold PMSPA.cfg. cbn [pa_make_ec PMA.AD ADDR_A].
  destruct (PNST.bax_cat ax) eqn:EC.
  - (* [comment removed for export] *)
    cbn iota in EG. cbn [pa_errcat_guard PMA.AD ADDR_A] in EG.
    assert (VG : L5.u8_at RSEGS MV 6759104 1).
    { apply (proj2 (L5A.u8_at_vis H M 6759104 1 (VIMG 6759104 1 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact EG. }
    LeanFeed.pfeed P (PMAERP.aerA_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => v | _ => 0 end)) ltac:(first [assumption | exact Rsp | unfold PMAERP.aligned; lia | lia]).
    destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & B11 & C8 & C0).
    assert (R1ra : getr R1 (reg 1) = Z_to_bv 64 r) by (rewrite (KS1 1%nat) by inl; exact Rra).
    pose proof (PMK.ret_to RSEGS fx1 R1 M1v 0xae8d4 W_ad6d0 r F_ad6d0 eq_refl D_ad6d0 R1ra ltac:(lia) Hr2) as MS2.
    apply (PMKA2.apiece_img L ar C HI LYa HIok LB FF LK cr Aw M model fx fx1 R 0xae848 R1 r M1v
             (fun a => sp - 32 <= a < sp - 32 + 32 \/ o + 0 <= a < o + 0 + 16) K HH AM).
    { eapply msteps_trans; [exact MS1| exact MS2]. }
    { exact MG1. }
    { intros a Ha N. apply FRZ1; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
    { intros a Ha [Wa|Wa].
      - split; [|intros X; pose proof (PMA.ly_ro L C LY a X); lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia].
      - split; [|intros X; pose proof (PMA.ly_ro L C LY a X); lia]. unfold aclientw, aclient_g. do 3 right. left.
        destruct AO as (f & Hf & X1 & X2). exists f. split; [exact Hf|]. split; [lia| intros X; lia]. }
    intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
    assert (EK : L5SAR.ek L ar LB FF sp 14336 WE M M1).
    { apply (L5SAR.ek_piece L ar LB FF sp 14336 WE M M1 (fun a => (sp - 32 <= a < sp - 32 + 32) \/ (o + 0 <= a < o + 0 + 16))).
      { intros a Ha N. apply FR1; [exact Ha| exact N]. }
      intros a Ha Hc Ho [X|X].
      - destruct (L5SAR.aclient_cases L ar C HI LYa HIok LB FF LK cr Aw M (vml_of model) sp 14336 a HH SPT Hc) as [(Y1 & Y2)|Y]; [apply Y2; lia| exfalso; lia].
      - apply (Ho (o, 16)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]. }
    assert (U1 : forall a v0, o <= a -> a + 8 <= o + 16 -> L5.u64_at RSEGS M1v a v0 -> L5.u64_at RSEGS M1 a v0).
    { intros a v0 Ha Hb X. rewrite <- VIS1 in X. exact (proj1 (L5A.u64_at_vis H M1 a v0 ltac:(eapply L5A.avis_sub; [exact OVIS| lia| lia]) ltac:(lia) ltac:(lia)) X). }
    apply (KONT fx1 R1 M1 model1 LK Aw).
    + apply L5SAR.preserved_by_index. intros k Hk. apply KS1. unfold L5SAR.cs_all in Hk. repeat (destruct Hk as [<-|Hk]; [inl|]). destruct Hk.
    + split; [apply u32_of_u64; apply (U1 o v ltac:(lia) ltac:(lia) C0)|].
      split; [cbn [pa_errcat_obj PMA.AD ADDR_A]; apply (U1 (o + 8) _ ltac:(lia) ltac:(lia) C8)|].
      split; [apply (L5.defined_grows M M1 _ _ MGM1); exact OD|].
      apply (PMKA.acc_keepA' L ar LB FF sp 14336 WE M M1 EK WAPP FRB o 16 AO ACC).
    + rewrite (PNST.bax_add_cat_id ax EC). split; [|split].
      * rewrite EC. cbn [pa_errcat_guard PMA.AD ADDR_A]. apply (L5C.u8_at_agree RSEGS M M1); [intros i Hi; apply FR1; lia | lia | lia | exact EG].
      * apply (bdec_keep M M1); [|exact EDEC]. intros a Ha Da. cbn [PNL.pn_inf_guard PNL.pn_nan_guard PNL.pn_inf_obj PNL.pn_nan_obj PMA.AN PMA.AN] in Da. apply FR1; lia.
      * unfold PNSTA.atexit_stA. apply (PNSTA.atexit_stA_agree RSEGS PMA.AD PMA.AAD PMA.AN PMA.addrs_wf_A M M1 ax); [|exact EA].
        intros i Hi. cbn [pa_atexit PMA.AD ADDR_A] in Hi. apply FR1; lia.
    + apply (L5SAR.ahpres_of L ar LB FF sp 14336 WE M M1 EK).
      * intros i Hi. apply MGM1. apply SDEF. exact Hi.
      * apply (L5SAR.dk_grows L ar LB FF sp 14336 M M1 MGM1).
    + exact MRT1.
    + intros x Hx. exact Hx.
    + intros x Hx. exact Hx.
    + exact AM1.
    + exact HH1.
  - (* [comment removed for export] *)
    assert (HLEN : (length (PNST.bax_list PMA.AD PMA.AN ax) <= 2)%nat) by (destruct ax; cbn in EC |- *; try discriminate EC; lia).
    (* [comment removed for export] *)
    cbn [pa_errcat_guard PMA.AD ADDR_A] in EG.
    assert (V4 : L5.img_clear MV 6759104 6759106) by (apply L5A.img_clear_mrestrict; exact EG).
    assert (V5 : L5.writable RSEGS MV 6759104 2) by (apply writable_img; [vm_compute; reflexivity| lia| lia| lia]).
    LeanFeed.pfeed P (PMAERP.aerB1_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => v | _ => 0 end)) ltac:(first [assumption | exact Rsp | unfold PMAERP.aligned; lia | lia]).
    destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & R1ra & R1sp & R1s0 & R1s1 & R1a0 & R1a1 & R1a2 & R1s2 & G1 & S32 & S24 & S16 & S8).
    apply (PMKA2.apiece_img L ar C HI LYa HIok LB FF LK cr Aw M model fx fx1 R 0xae848 R1 0x6da18 M1v
             (fun a => sp - 32 <= a < sp - 32 + 32 \/ 0 + 6759104 <= a < 0 + 6759104 + 2) K HH AM MS1 MG1).
    { intros a Ha N. apply FRZ1; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
    { intros a Ha [Wa|Wa].
      - split; [|intros X; pose proof (PMA.ly_ro L C LY a X); lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia].
      - split; [|apply (PMKA2.rt_ro_bss L C a LY); lia]. unfold aclientw, aclient_g. right; right; left.
        rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [lia|].
        intros [X|X].
        + apply (fun D_ => PMA.ly_static L C LY a (PnStatics.PNST.dep_of_j _ _ a D_)); [|exact X]. apply PMST.in_foot_errg. cbn [pa_errcat_guard PMA.AD ADDR_A]. lia.
        + pose proof (PMA.ly_ro L C LY a X). lia. }
    intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
    pose proof AM1 as (Mh1 & MI1).
    assert (EK01 : L5SAR.ek L ar LB FF sp 14336 WE M M1).
    { apply (L5SAR.ek_piece L ar LB FF sp 14336 WE M M1 (fun a => (sp - 32 <= a < sp - 32 + 32) \/ (0 + 6759104 <= a < 0 + 6759104 + 2))).
      { intros a Ha N. apply FR1; [exact Ha| exact N]. }
      intros a Ha Hc Ho [X|X].
      - destruct (L5SAR.aclient_cases L ar C HI LYa HIok LB FF LK cr Aw M (vml_of model) sp 14336 a HH SPT Hc) as [(Y1 & Y2)|Y]; [apply Y2; lia| exfalso; lia].
      - apply (Ho (6759104, 2)); [right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]. }
    (* [comment removed for export] *)
    pose proof (HAJ.aex_cxa_atexit _ _ _ _ _ EXT) as CXA.
    unfold HAJ.cxa_atexit_spec in CXA.
    cbn [PMA.EXT HAJ.ec_cxa_pc HAJ.ec_cxa_scr HAJ.ec_atexit HAJ.ec_f0 HAJ.ec_a0 HAJ.ec_f1 HAJ.ec_a1 HAJ.ec_atc HAJ.ec_nl
         paa_cxa_atexit_icpt paa_atexit_f0 paa_atexit_a0 paa_at_cxa_atexit PMA.AAD AADDR_A pa_atexit pa_need_locks PMA.AD ADDR_A PNL.pn_drv_call PNL.pn_drv_guard PMA.AN NADDR_A] in CXA.
    rewrite (L5A.aly_segs L C LYa) in CXA.
    assert (ATX1 : HAJ.atexit_cells RSEGS M1 0x693d50 0x118824 0x97564 0x118824 0xa7f2c (paa_at_cxa_atexit PMA.AAD) (PNST.bax_list PMA.AD PMA.AN ax)).
    { pose proof (PNSTA.atexit_stA_agree RSEGS PMA.AD PMA.AAD PMA.AN PMA.addrs_wf_A M M1 ax) as X.
      unfold PNSTA.atexit_stA in X. cbn [pa_atexit paa_atexit_f0 paa_atexit_a0 PMA.AAD AADDR_A PMA.AD ADDR_A PNL.pn_drv_call PNL.pn_drv_guard PMA.AN NADDR_A] in X.
      apply X; [|exact EA]. intros i Hi. apply FR1; lia. }
    assert (NL1 : L5.u8_at RSEGS M1 0x693f93 0).
    { destruct BASE as (_ & _ & NL & _). cbn [pa_need_locks PMA.AD ADDR_A] in NL.
      apply (L5C.u8_at_agree RSEGS M M1); [intros i Hi; apply FR1; lia| lia| lia| exact NL]. }
    assert (ASO : astack_ok L ar M1 1024 (sp - 32)).
    { apply (L5SAR.astack_ok_of_astk L ar C LYa M M1 sp 14336 32 1024 ASTK MGM1); [lia| lia| lia|].
      replace (sp - 32) with (sp + (-2) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
    cbn [paa_at_cxa_atexit PMA.AAD PMA.AAD] in ATX1.
    apply (CXA fx1 R1 M1 model1 LB FF LK cr Aw K (PNST.bax_list PMA.AD PMA.AN ax) 872740 1293304 1282768); clear CXA.
    { exact HH1. }
    { exact Mh1. }
    { exact MI1. }
    { rewrite L5K.rl10. exact R1a0. }
    { rewrite L5K.rl11. exact R1a1. }
    { rewrite L5K.rl12. exact R1a2. }
    { exact HLEN. }
    { exact ATX1. }
    { exact NL1. }
    { rewrite L5K.rl4. rewrite (KS1 4%nat) by inl. exact Rtp. }
    { rewrite L5K.rl1, R1ra. vm_compute. reflexivity. }
    { rewrite L5K.rl2, R1sp. rewrite L5.unsigned_lit by lia. exact ASO. }
    { exact K0. }
    intros fx2 R2 M2 model2 Aw2 RP2 A02 ATX2 FRC2 DX2 SCR2 MRT2 INC2 MI2 HH2.
    rewrite L5K.rl2, R1sp, L5.unsigned_lit in FRC2, SCR2 by lia.
    rewrite L5K.rl1, R1ra.
    assert (AM2 : L5CA.amodel_ok Aw2 model2) by (split; [rewrite (L5LZ.model_rt_halted model1 model2 MRT2); exact Mh1| exact MI2]).
    assert (EK12 : L5SAR.ek L ar LB FF sp 14336 WE M1 M2).
    { apply (L5SAR.ek_mem L ar LB FF sp 14336 (sp - 32) 1024 (fun x => 0x693d50 <= x < 0x693d50 + 544) WE M1 M2); [| lia| lia|].
      - intros a Ha Hc Hn. apply FRC2; [exact Ha| exact Hc| exact Hn].
      - intros a Hc Ho X. apply (Ho (0x693d50, 544)); [right; right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]. }
    assert (EK02 : L5SAR.ek L ar LB FF sp 14336 WE M M2) by (apply (L5SAR.ek_trans L ar LB FF sp 14336 WE M M1 M2 EK01 EK12)).
    assert (DK02 : L5SAR.dk L ar LB FF sp 14336 M M2).
    { intros a Ha Hc HM. destruct (L5SAR.rng_dec a 0x693d50 (0x693d50 + 544)) as [I|N].
      - apply DX2; [exact I| apply MGM1; exact HM].
      - destruct (L5SAR.rng_dec a (sp - 32 - 1024) (sp - 32)) as [J|NJ]; [apply SCR2; exact J|].
        rewrite FRC2; [apply MGM1; exact HM| exact Ha| apply (L5SAR.aclient_narrow L ar LB FF sp 14336 (sp - 32) 1024 a Hc NJ)| exact N]. }
    (* [comment removed for export] *)
    pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw2 M2 model2 HH2) as (HOFF2 & VIS2 & VIMG2 & VFS2 & VBLK2 & VBSH2 & VFSSH2 & VSTSH2).
    set (H2 := ahid Aw2 model2) in *. set (MV2 := mrestrict H2 M2) in *.
    pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK cr Aw2 M2 model2 o 16 sp 14336 HH2 (PMKA.aobj_of_aobjA FF o 16 AO O8) ltac:(lia) ltac:(reflexivity))
      as (_ & _ & ODEF2 & OVIS2 & _ & _ & _).
    pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH2) as ST2. rewrite (L5A.aly_segs L C LYa) in ST2.
    pose proof (L5A.statics_facts L C M2 LYa ST2) as (GOT2 & CSB2 & CUAR2 & _).
    assert (ACC2 : PMSPA.accA M2 o 16) by (apply (PMKA.acc_keepA' L ar LB FF sp 14336 WE M M2 EK02 WAPP FRB o 16 AO ACC)).
    assert (Y0 : L5.img_clear MV2 1249280 1282048) by (apply L5A.img_clear_mrestrict; exact GOT2).
    assert (Y1 : L5.u64_at RSEGS MV2 1309752 2147450880) by (apply (proj2 (L5A.u64_at_vis H2 M2 1309752 2147450880 (VIMG2 1309752 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB2).
    assert (Y2 : L5.u32_at RSEGS MV2 1309760 1) by (apply (proj2 (L5A.u32_at_vis H2 M2 1309760 1 (VIMG2 1309760 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR2).
    assert (SD2 : L5.defined M2 (sp - 14336) 14336).
    { intros i Hi. destruct (Z_lt_le_dec (sp - 14336 + i) (sp - 32 - 1024)) as [X|X]; [|destruct (Z_lt_le_dec (sp - 14336 + i) (sp - 32)) as [Y|Y]].
      - rewrite FRC2; [apply MGM1; apply SDEF; exact Hi| lia| apply L5SAR.stack_client; lia| lia].
      - apply SCR2. lia.
      - rewrite FRC2; [apply MGM1; apply SDEF; exact Hi| lia| apply L5SAR.stack_client; lia| lia]. }
    assert (Y3 : L5.writable RSEGS MV2 (sp - 128) 128).
    { apply (proj2 (L5A.writable_vis H2 M2 (sp - 128) 128 (VIS2 (sp - 128) 128 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
      apply (L5C.writable_of_defined RSEGS). apply (L5.defined_sub M2 (sp - 14336) 14336); [exact SD2| lia| lia]. lia. lia. }
    assert (YZ : L5KA.zeros_at MV2 ((o / 8) + 2147450880) 2).
    { pose proof (PMKA.obj_shadow_vis L ar C HI LYa HIok LB FF LK cr Aw2 M2 model2 o 16 HH2 AO O8 ltac:(lia) ltac:(reflexivity) ACC2) as X. exact X. }
    assert (YW : L5.writable RSEGS MV2 o 16).
    { apply (proj2 (L5A.writable_vis H2 M2 o 16 OVIS2 ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS). exact ODEF2. lia. lia. }
    assert (YG : L5.writable RSEGS MV2 6759104 2) by (apply writable_img; [vm_compute; reflexivity| lia| lia| lia]).
    assert (SAVE : forall a v0, sp - 32 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1v a v0 -> L5.u64_at RSEGS MV2 a v0).
    { intros a v0 Ha Hb X. rewrite <- VIS1 in X.
      apply (proj1 (L5A.u64_at_vis H M1 a v0 (VIS a 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))) in X.
      apply (proj2 (L5A.u64_at_vis H2 M2 a v0 (VIS2 a 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
      apply (L5C.u64_at_agree RSEGS M1 M2); [|lia|lia|exact X].
      intros i Hi. apply FRC2; [lia| apply L5SAR.stack_client; lia| lia]. }
    pose proof (bvu (getr R (reg 8))) as Hs8. pose proof (bvu (getr R (reg 9))) as Hs9. pose proof (bvu (getr R (reg 18))) as Hs18.
    assert (Y8 : L5.u64_at RSEGS MV2 (sp - 8) r).
    { apply SAVE; [lia| lia|]. rewrite Rra, L5.unsigned_lit in S8 by lia. exact S8. }
    assert (Y16 : L5.u64_at RSEGS MV2 (sp - 16) (bv_unsigned (getr R (reg 8)))) by (apply SAVE; [lia| lia| exact S16]).
    assert (Y24 : L5.u64_at RSEGS MV2 (sp - 24) (bv_unsigned (getr R (reg 9)))) by (apply SAVE; [lia| lia| exact S24]).
    assert (Y32 : L5.u64_at RSEGS MV2 (sp - 32) (bv_unsigned (getr R (reg 18)))) by (apply SAVE; [lia| lia| exact S32]).
    assert (R2sp : getr R2 (reg 2) = Z_to_bv 64 (sp - 32)) by (rewrite (L5SAR.cs_of_preserved R1 R2 2 RP2) by inl; exact R1sp).
    assert (R2s0 : getr R2 (reg 8) = Z_to_bv 64 o) by (rewrite (L5SAR.cs_of_preserved R1 R2 8 RP2) by inl; exact R1s0).
    assert (R2s1 : getr R2 (reg 9) = Z_to_bv 64 v) by (rewrite (L5SAR.cs_of_preserved R1 R2 9 RP2) by inl; exact R1s1).
    assert (R2s2 : getr R2 (reg 18) = Z_to_bv 64 2147450880) by (rewrite (L5SAR.cs_of_preserved R1 R2 18 RP2) by inl; exact R1s2).
    LeanFeed.pfeed P (PMAERP.aerB2_conc fx2 R2 MV2 (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => v | 43%nat => r
                                                     | 44%nat => bv_unsigned (getr R (reg 8)) | 45%nat => bv_unsigned (getr R (reg 9))
                                                     | 46%nat => bv_unsigned (getr R (reg 18)) | _ => 0 end)) ltac:(first [assumption | unfold PMAERP.aligned; lia | lia]).
    destruct P as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & R3ra & R3sp & R3s0 & R3s1 & R3a0 & R3a1 & R3s2 & D8 & D0 & GB1 & GB0).
    pose proof (PMK.ret_to RSEGS fx3 R3 M3v 0xae8d4 W_ad6d0 r F_ad6d0 eq_refl D_ad6d0 R3ra ltac:(lia) Hr2) as MS4.
    apply (PMKA2.apiece_img L ar C HI LYa HIok LB FF LK cr Aw2 M2 model2 fx2 fx3 R2 0xae908 R3 r M3v
             (fun a => o + 0 <= a < o + 0 + 16 \/ 0 + 6759104 <= a < 0 + 6759104 + 2) K HH2 AM2).
    { eapply msteps_trans; [exact MS3| exact MS4]. }
    { exact MG3. }
    { intros a Ha N. apply FRZ3; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
    { intros a Ha [Wa|Wa].
      - split; [|intros X; pose proof (PMA.ly_ro L C LY a X); lia]. unfold aclientw, aclient_g. do 3 right. left.
        destruct AO as (f & Hf & X1 & X2). exists f. split; [exact Hf|]. split; [lia| intros X; lia].
      - split; [|apply (PMKA2.rt_ro_bss L C a LY); lia]. unfold aclientw, aclient_g. right; right; left.
        rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [lia|].
        intros [X|X].
        + apply (fun D_ => PMA.ly_static L C LY a (PnStatics.PNST.dep_of_j _ _ a D_)); [|exact X]. apply PMST.in_foot_errg. cbn [pa_errcat_guard PMA.AD ADDR_A]. lia.
        + pose proof (PMA.ly_ro L C LY a X). lia. }
    intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3.
    assert (EK23 : L5SAR.ek L ar LB FF sp 14336 WE M2 M3).
    { apply (L5SAR.ek_piece L ar LB FF sp 14336 WE M2 M3 (fun a => (o + 0 <= a < o + 0 + 16) \/ (0 + 6759104 <= a < 0 + 6759104 + 2))).
      { intros a Ha N. apply FR3; [exact Ha| exact N]. }
      intros a Ha Hc Ho [X|X].
      - apply (Ho (o, 16)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
      - apply (Ho (6759104, 2)); [right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]. }
    assert (EK03 : L5SAR.ek L ar LB FF sp 14336 WE M M3) by (apply (L5SAR.ek_trans L ar LB FF sp 14336 WE M M2 M3 EK02 EK23)).
    assert (U3 : forall a v0, o <= a -> a + 8 <= o + 16 -> L5.u64_at RSEGS M3v a v0 -> L5.u64_at RSEGS M3 a v0).
    { intros a v0 Ha Hb X. rewrite <- VIS3 in X. exact (proj1 (L5A.u64_at_vis H2 M3 a v0 ltac:(eapply L5A.avis_sub; [exact OVIS2| lia| lia]) ltac:(lia) ltac:(lia)) X). }
    assert (UG : forall a v0, 6759104 <= a < 6759106 -> L5.u8_at RSEGS M3v a v0 -> L5.u8_at RSEGS M3 a v0).
    { intros a v0 Ha X. rewrite <- VIS3 in X. exact (proj1 (L5A.u8_at_vis H2 M3 a v0 (VIMG2 a 1 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) X). }
    apply (KONT fx3 R3 M3 model3 LK Aw2).
    + apply L5SAR.preserved_by_index. intros k Hk. unfold L5SAR.cs_all in Hk.
      repeat (destruct Hk as [<-|Hk];
              [first [ rewrite R3sp, Rsp; reflexivity
                     | rewrite R3s0, Z_to_bv_bv_unsigned; reflexivity
                     | rewrite R3s1, Z_to_bv_bv_unsigned; reflexivity
                     | rewrite R3s2, Z_to_bv_bv_unsigned; reflexivity
                     | rewrite (KS3 _) by inl; rewrite (L5SAR.cs_of_preserved R1 R2 _ RP2) by inl; apply KS1; inl ]|]).
      destruct Hk.
    + split; [apply u32_of_u64; apply (U3 o v ltac:(lia) ltac:(lia) D0)|].
      split; [cbn [pa_errcat_obj PMA.AD ADDR_A]; apply (U3 (o + 8) _ ltac:(lia) ltac:(lia) D8)|].
      split; [apply (L5.defined_grows M2 M3 _ _ MGM3); exact ODEF2|].
      apply (PMKA.acc_keepA' L ar LB FF sp 14336 WE M M3 EK03 WAPP FRB o 16 AO ACC).
    + split; [|split].
      * rewrite PNST.bax_cat_add. cbn [pa_errcat_guard PMA.AD ADDR_A]. exact (UG 6759104 1 ltac:(lia) GB0).
      * replace (PNST.bax_dec (PNST.bax_add_cat ax)) with (PNST.bax_dec ax) by (destruct ax; reflexivity).
        apply (bdec_keep M M3); [|exact EDEC]. intros a Ha Da. cbn [PNL.pn_inf_guard PNL.pn_nan_guard PNL.pn_inf_obj PNL.pn_nan_obj PMA.AN PMA.AN] in Da.
        assert (E12 : M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
        { destruct Da as [Da|[Da|[Da|Da]]];
            (apply FRC2; [lia| | lia]; apply (L5SAR.aclient_narrow L ar LB FF sp 14336 (sp - 32) 1024 a); [| lia];
             unfold aclient, aclient_g; right; right; left; rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa); split; [lia|];
             intros X; apply (PMA.ly_static L C LY a); [|exact X]);
            [apply PnStatics.PNST.in_foot_infg| apply PnStatics.PNST.in_foot_nang| apply PnStatics.PNST.in_foot_info| apply PnStatics.PNST.in_foot_nano];
            cbn [PNL.pn_inf_guard PNL.pn_nan_guard PNL.pn_inf_obj PNL.pn_nan_obj PMA.AN PMA.AN]; lia. }
        rewrite (FR3 a Ha) by lia. rewrite E12. apply FR1; lia.
      * unfold PNSTA.atexit_stA. cbn [pa_atexit paa_atexit_f0 paa_atexit_a0 pa_errcat_dtor pa_errcat_obj paa_at_cxa_atexit PMA.AAD AADDR_A PMA.AD ADDR_A PNL.pn_drv_call PNL.pn_drv_guard PMA.AN NADDR_A].
        pose proof (PNSTA.atexit_stA_agree RSEGS PMA.AD PMA.AAD PMA.AN PMA.addrs_wf_A M2 M3 (PNST.bax_add_cat ax)) as X.
        unfold PNSTA.atexit_stA in X. cbn [pa_atexit paa_atexit_f0 paa_atexit_a0 pa_errcat_dtor pa_errcat_obj paa_at_cxa_atexit PMA.AAD AADDR_A PMA.AD ADDR_A PNL.pn_drv_call PNL.pn_drv_guard PMA.AN NADDR_A] in X.
        apply X; [intros i Hi; apply FR3; lia|].
        replace (PNST.bax_list PMA.AD PMA.AN (PNST.bax_add_cat ax)) with (PNST.bax_list PMA.AD PMA.AN ax ++ [(pa_errcat_dtor PMA.AD, pa_errcat_obj PMA.AD)]) by (destruct ax; cbn in EC |- *; try discriminate EC; reflexivity).
        cbn [pa_errcat_dtor pa_errcat_obj paa_at_cxa_atexit PMA.AAD PMA.AAD PMA.AD ADDR_A]. exact ATX2.
    + apply (L5SAR.ahpres_of L ar LB FF sp 14336 WE M M3 EK03).
      * intros i Hi. apply MGM3. apply SD2. exact Hi.
      * apply (L5SAR.dk_trans L ar LB FF sp 14336 M M2 M3 DK02 (L5SAR.dk_grows L ar LB FF sp 14336 M2 M3 MGM3)).
    + apply (L5LZ.model_rt_trans model model2 model3); [|exact MRT3]. apply (L5LZ.model_rt_trans model model1 model2); [exact MRT1| exact MRT2].
    + intros x Hx. exact Hx.
    + exact INC2.
    + exact AM3.
    + exact HH3.
Qed.
End WithHeap.
End PNAMKE.
