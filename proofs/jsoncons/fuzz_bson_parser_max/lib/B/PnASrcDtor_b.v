(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx HeapIfaceANull. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PmSpecsAX_b PnSpecsAa_b
     PmModelFactsA_b PnStepA_b PnASrcDtorP_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMASD.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMA.ly_as0 L C LY.

Lemma dep_img a : PMST.dep PMA.AD a -> 0x6722c0 <= a < 0x694074.
Proof.
  unfold PMST.dep, pm_foot, pm_initc. cbn [pa_errcat_guard pa_syscat_guard pa_loc_foot pa_atexit pa_canary pa_need_locks pa_locale_lock PMA.AD ADDR_A app].
  intros [(iv & Hin & Hr)|[Hc|(iv & Hin & Hr)]].
  - repeat (destruct Hin as [<-|Hin]; [cbn [fst snd] in Hr; lia|]). destruct Hin.
  - lia.
  - repeat (destruct Hin as [<-|Hin]; [cbn [fst snd] in Hr; lia|]). destruct Hin.
Qed.

Theorem src_dtor_ok : PMA.opdel_spec L ar HI -> PMA.locale_dtor_spec L ar HI -> PMA.ios_dtor_spec L ar HI -> PMA.src_dtor_spec L ar HI.
Proof.
  intros OPD LDT IDT. unfold PMA.src_dtor_spec, PMSPA.src_dtor_spec.
  intros fx R M model K LB FF LK Aw cr os isp sbp sp r src HH AM K0 ENT FRM FRS A10 AO O8 SRC NI Bq BASE KONT.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 2) with 16384 in *. change (16384 / 8) with 2048 in STKSH.
  pose proof AM as (Mh & MI). pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof RAok as (Hr1 & Hr2).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10.
  destruct SRC as (S240 & S248 & SD256 & S264 & S272 & S280 & S288 & Hq1 & Hq2 & Hq3 & Hq16 & QD & QC & SC240).
  destruct NI as (N0 & ND & NC & N16 & N24 & NIOS).
  set (qc := PM.sr_qc src) in *. unfold PM.CHUNK in *.
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _).
  pose proof (proj1 (WB _ Bq)) as (Q0 & Q1 & Q2 & Q3 & Q4 & Q5). cbn [fst snd] in *.
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw M model HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
  set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK cr Aw M model os 296 sp 16384 HH (PMKA.aobj_of_aobjA FF os 296 AO O8) ltac:(lia) ltac:(reflexivity))
    as ((O1 & O2 & O3 & O4 & O5) & OBIG & ODEF & OVIS & OSHV & OCL & OSHCL).
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as ST. rewrite (L5A.aly_segs L C LYa) in ST.
  pose proof (L5A.statics_facts L C M LYa ST) as (GOT & CSB & CUAR & _).
  assert (HO : bv_unsigned (getr R (reg 10)) = os) by (rewrite A10; apply L5.unsigned_lit; lia).
  (* [comment removed for export] *)
  assert (V0 : L5.img_clear MV 65536 1282048).
  { apply L5A.img_clear_mrestrict. destruct BASE as (IC & _). cbn [pa_rw_lo PMA.AD ADDR_A] in IC. exact IC. }
  assert (V1 : L5.u64_at RSEGS MV 1309752 2147450880) by (apply (proj2 (L5A.u64_at_vis H M 1309752 2147450880 (VIMG 1309752 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB).
  assert (V2 : L5.u32_at RSEGS MV 1309760 1) by (apply (proj2 (L5A.u32_at_vis H M 1309760 1 (VIMG 1309760 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR).
  assert (V3 : L5.writable RSEGS MV (sp - 48) 48).
  { apply (proj2 (L5A.writable_vis H M (sp - 48) 48 (VIS (sp - 48) 48 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5C.writable_of_defined RSEGS). apply (L5.defined_sub M (sp - 16384) 16384); [exact SDEF| lia| lia]. lia. lia. }
  assert (ACC8 : PMSPA.accA M (os + 8) 288).
  { intros a Ha. destruct (Z_lt_le_dec a (os + 88)) as [X|X]; [apply NC; lia|].
    destruct (Z_lt_le_dec a (os + 240)) as [Y|Y]; [destruct NIOS as (_ & _ & _ & _ & _ & _ & _ & IC & _); apply IC; lia| apply SC240; lia]. }
  assert (V4 : L5KA.zeros_at MV ((os / 8) + 2147450881) 36).
  { replace ((os / 8) + 2147450881) with ((os + 8) / 8 + SB).
    2:{ unfold SB. replace (os + 8) with (1 * 8 + os) by lia. rewrite Z.div_add_l by lia. lia. }
    apply (PMKA.obj_shadow_vis L ar C HI LYa HIok LB FF LK cr Aw M model (os + 8) 288 HH).
    - destruct AO as (f & Hf & X1 & X2). exists f. split; [exact Hf|]. lia.
    - replace (os + 8) with (os + 1 * 8) by lia. rewrite Z_mod_plus_full. exact O8.
    - lia. - reflexivity. - exact ACC8. }
  (* [comment removed for export] *)
  pose proof (PMASDP.asdA_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => qc | 34%nat => 16384 | _ => 0 end)) as P. cbn beta iota in P. rewrite HO in P.
  assert (VQ264 : L5.u64_at RSEGS MV (os + 264) qc).
  { apply (proj2 (L5A.u64_at_vis H M (os + 264) qc ltac:(eapply L5A.avis_sub; [exact OVIS| lia| lia]) ltac:(lia) ltac:(lia))). exact S264. }
  assert (VQ272 : L5.u64_at RSEGS MV (os + 272) 16384).
  { apply (proj2 (L5A.u64_at_vis H M (os + 272) 16384 ltac:(eapply L5A.avis_sub; [exact OVIS| lia| lia]) ltac:(lia) ltac:(lia))). exact S272. }
  L5SAR.feed P ltac:(first [assumption | exact Rsp | unfold PMASDP.aligned; lia | lia]).
  destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & A1 & A2 & A8 & B10 & B11 & B12 & B19 & C40 & C32 & C24 & C16 & C8).
  unfold PMSPA.cfg. cbn [pa_src_dtor PMA.AD ADDR_A].
  apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr Aw M model fx fx1 R 0xab344 R1 0xd39ac M1v (fun a => sp - 48 <= a < sp - 48 + 48) K HH AM MS1 MG1 FRZ1).
  { intros a Ha Wa. split; [|intros X; lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia]. }
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
  (* [comment removed for export] *)
  assert (ASTK1 : L5CA.astk ar M1 (sp - 48) PMSPA.OPDEL_SCR).
  { apply (L5SAR.astk_sub ar M M1 sp 16384 48 PMSPA.OPDEL_SCR ASTK MGM1); unfold PMSPA.OPDEL_SCR, PMSPA.MALLOC_SCR; [lia|lia|lia|].
    replace (sp - 48) with (sp + (-3) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
  unfold PMA.opdel_spec, PMSPA.opdel_spec, PMSPA.opdel_spec_at in OPD. cbn [pa_opdel PMA.AD ADDR_A] in OPD.
  apply (OPD fx1 R1 M1 model1 K LB FF LK Aw cr qc 16384 (sp - 48) 701348 HH1 AM1 K0 Bq).
  { rewrite L5K.rl10. exact B10. }
  { rewrite L5K.rl1. exact A1. }
  { split; [lia| reflexivity]. }
  { rewrite L5K.rl2. exact A2. }
  { rewrite L5K.rl4. rewrite (KS1 4%nat) by inl. exact Rtp. }
  { exact ASTK1. }
  intros fx2 R2 M2 model2 Aw2 RP2 HP2 MRT2 INC2 AM2 HH2.
  set (LB' := lb_remove qc LB) in *.
  assert (INCLB : incl LB' LB) by (intros x Hx; apply (L5C.in_lb_remove qc x LB); exact Hx).
  assert (EK01 : L5SAR.ek L ar LB' FF sp 16384 [] M M1).
  { apply (PMKA.ek_sublb L ar LB LB' FF sp 16384 [] M M1 INCLB).
    apply (PMKA.ek_own_frame L ar C HI LYa HIok LB FF LK cr Aw M M1 _ sp 16384 [] (sp - 48) (sp - 48 + 48) HH SPT); [lia|lia|lia|].
    intros a Ha Hn. apply FR1; [exact Ha| exact Hn]. }
  assert (EK12 : L5SAR.ek L ar LB' FF sp 16384 [] M1 M2).
  { apply (L5SAR.ek_callee L ar LB' [] FF [] sp 16384 (sp - 48) PMSPA.OPDEL_SCR [] [] M1 M2 HP2); unfold PMSPA.OPDEL_SCR, PMSPA.MALLOC_SCR; [lia|lia|].
    intros a _ O. exact O. }
  pose proof (L5SAR.ek_trans L ar LB' FF sp 16384 [] M M1 M2 EK01 EK12) as EK02.
  (* [comment removed for export] *)
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH2) as (WB2 & WF2 & FSAPP2 & FSCEIL2 & _).
  assert (FRB : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47).
  { intros f Hf. destruct (WF2 f Hf) as (X1 & X2 & _). unfold app_mem, FS_BYTES in *. lia. }
  assert (BRB : forall b, In b LB' -> 0 <= fst b /\ fst b + snd b <= 2 ^ 47).
  { intros b Hb. destruct (proj1 (WB2 b Hb)) as (X0 & _ & _ & _ & X4 & _). lia. }
  assert (ACC8_2 : PMSPA.accA M2 (os + 8) 288).
  { apply (PMKA.acc_keepA L ar LB' FF sp 16384 [] M M2 EK02 PMKA.wapp_nil FRB); [| intros i Hi r0 []| exact ACC8].
    destruct AO as (f & Hf & X1 & X2). exists f. split; [exact Hf|]. lia. }
  assert (ODEF2 : L5.defined M2 os 296).
  { apply (PMKA.defined_keepA L ar LB' FF sp 16384 [] M M2 EK02 PMKA.wapp_nil FRB); [exact AO| intros i Hi r0 []| exact ODEF]. }
  assert (IMG2 : L5.img_clear M2 65536 1282048).
  { apply (PMKA.img_clear_keepA L ar LB' FF sp 16384 [] M M2 EK02); [lia|lia| |].
    - intros a Ha. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [lia|]. split; [intros X; pose proof (L5A.aly_static_lo L C LYa a X); lia| intros r0 []].
    - destruct BASE as (IC & _). cbn [pa_rw_lo PMA.AD ADDR_A] in IC. exact IC. }
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB' FF LK cr Aw2 M2 model2 HH2) as (HOFF2 & VIS2 & VIMG2 & VFS2 & VBLK2 & VBSH2 & VFSSH2 & VSTSH2).
  set (H2 := ahid Aw2 model2) in *. set (MV2 := mrestrict H2 M2) in *.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB' FF LK cr Aw2 M2 model2 os 296 sp 16384 HH2 (PMKA.aobj_of_aobjA FF os 296 AO O8) ltac:(lia) ltac:(reflexivity))
    as (_ & _ & _ & OVIS2 & OSHV2 & _ & _).
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH2) as ST2. rewrite (L5A.aly_segs L C LYa) in ST2.
  pose proof (L5A.statics_facts L C M2 LYa ST2) as (_ & CSB2 & CUAR2 & _).
  assert (ASTK2 : L5CA.astk ar M2 sp 16384).
  { pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH2) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & TOP2 & _).
    apply (PMKA.astk_after_ahpres L ar LB' FF M1 M2 sp 16384 (sp - 48) PMSPA.OPDEL_SCR [] (L5SAR.astk_grows ar M M1 sp 16384 ASTK MGM1) HP2);
    unfold PMSPA.OPDEL_SCR, PMSPA.MALLOC_SCR; lia. }
  assert (VW2 : forall a n, os <= a -> a + n <= os + 296 -> 0 <= n -> L5.writable RSEGS MV2 a n).
  { intros a n Ha Hn Hn0. apply (proj2 (L5A.writable_vis H2 M2 a n ltac:(eapply L5A.avis_sub; [exact OVIS2|lia|lia]) ltac:(lia) ltac:(lia))).
    apply (L5C.writable_of_defined RSEGS). apply (L5.defined_sub M2 os 296); [exact ODEF2| lia| lia]. lia. lia. }
  (* [comment removed for export] *)
  idtac.
  assert (G2 : getr R2 (reg 2) = Z_to_bv 64 (sp - 48)) by (rewrite (L5SAR.cs_of_preserved R1 R2 2 RP2) by inl; exact A2).
  assert (G8 : getr R2 (reg 8) = Z_to_bv 64 os) by (rewrite (L5SAR.cs_of_preserved R1 R2 8 RP2) by inl; rewrite A8; exact A10).
  assert (G19 : getr R2 (reg 19) = Z_to_bv 64 2147450880) by (rewrite (L5SAR.cs_of_preserved R1 R2 19 RP2) by inl; exact B19).
  assert (W0 : L5.img_clear MV2 65536 1282048) by (apply L5A.img_clear_mrestrict; exact IMG2).
  assert (W1 : L5.u64_at RSEGS MV2 1309752 2147450880) by (apply (proj2 (L5A.u64_at_vis H2 M2 1309752 2147450880 (VIMG2 1309752 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB2).
  assert (W2 : L5.u32_at RSEGS MV2 1309760 1) by (apply (proj2 (L5A.u32_at_vis H2 M2 1309760 1 (VIMG2 1309760 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR2).
  assert (W3 : L5.writable RSEGS MV2 (sp - 48) 48).
  { pose proof ASTK2 as (_ & _ & _ & _ & SDEF2 & _).
    apply (proj2 (L5A.writable_vis H2 M2 (sp - 48) 48 (VIS2 (sp - 48) 48 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5C.writable_of_defined RSEGS). apply (L5.defined_sub M2 (sp - 16384) 16384); [exact SDEF2| lia| lia]. lia. lia. }
  assert (W4 : L5KA.zeros_at MV2 ((os / 8) + 2147450881) 36).
  { replace ((os / 8) + 2147450881) with ((os + 8) / 8 + SB).
    2:{ unfold SB. replace (os + 8) with (1 * 8 + os) by lia. rewrite Z.div_add_l by lia. lia. }
    apply (PMKA.obj_shadow_vis L ar C HI LYa HIok LB' FF LK cr Aw2 M2 model2 (os + 8) 288 HH2).
    - destruct AO as (f & Hf & X1 & X2). exists f. split; [exact Hf|]. lia.
    - replace (os + 8) with (os + 1 * 8) by lia. rewrite Z_mod_plus_full. exact O8.
    - lia. - reflexivity. - exact ACC8_2. }
  LeanFeed.pfeed P (PMASDP.asdB_conc fx2 R2 MV2 (fun j => match j with 2%nat => sp | 40%nat => os | _ => 0 end)) ltac:(first [assumption | apply VW2; lia | unfold PMASDP.aligned; lia | lia]).
  destruct P as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & A31 & A39 & A310 & A311 & A318 & C324 & C388 & C38).
  assert (FRZ3' : forall a, 0 <= a < 2 ^ 64 -> ~ ((os + 88 <= a < os + 88 + 8) \/ (os + 8 <= a < os + 8 + 8) \/ (os + 24 <= a < os + 24 + 8)) ->
                  M3v (Z_to_bv 64 a) = MV2 (Z_to_bv 64 a)).
  { intros a Ha NW. apply FRZ3; [exact Ha| intros X; apply NW; left; exact X| intros X; apply NW; right; left; exact X| intros X; apply NW; right; right; exact X]. }
  apply (L5SAR.apiece L ar C HI LYa HIok LB' FF LK cr Aw2 M2 model2 fx2 fx3 R2 701348 R3 0xfef40 M3v
           (fun a => (os + 88 <= a < os + 88 + 8) \/ (os + 8 <= a < os + 8 + 8) \/ (os + 24 <= a < os + 24 + 8)) K HH2 AM2 MS3 MG3 FRZ3').
  { intros a Ha Wa. split; [|intros X; lia]. unfold aclientw, aclient_g. do 3 right. left.
    destruct AO as (f & Hf & X1 & X2). exists f. split; [exact Hf|]. split; [lia| intros X; lia]. }
  intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3.
  set (WB3 := [(os + 8, 8); (os + 24, 8); (os + 88, 8)]).
  assert (EK23 : L5SAR.ek L ar LB' FF sp 16384 WB3 M2 M3).
  { apply (L5SAR.ek_piece L ar LB' FF sp 16384 WB3 M2 M3 _ FR3). intros a Ha _ O X.
    destruct X as [X|[X|X]]; [apply (O (os + 88, 8)); [right; right; left; reflexivity| exact X]
                            | apply (O (os + 8, 8)); [left; reflexivity| exact X] | apply (O (os + 24, 8)); [right; left; reflexivity| exact X]]. }
  assert (EK03 : L5SAR.ek L ar LB' FF sp 16384 WB3 M M3).
  { apply (L5SAR.ek_trans L ar LB' FF sp 16384 WB3 M M2 M3); [|exact EK23]. apply (L5SAR.ek_W L ar LB' FF sp 16384 WB3 [] M M2 EK02). intros a _ r0 []. }
  assert (WAPP3 : PMKA.wapp WB3).
  { assert (OB : forall k, 0 <= k <= 296 - 8 -> (os + k) + 8 <= BIGSHADOW_LO \/ BIGSHADOW_HI <= os + k).
    { intros k Hk. unfold BIGSHADOW_LO, BIGSHADOW_HI. destruct OBIG as [X|X]; [right; lia| left; lia]. }
    unfold WB3. apply PMKA.wapp_cons; [exact (OB 8 ltac:(lia))|]. apply PMKA.wapp_cons; [exact (OB 24 ltac:(lia))|].
    apply PMKA.wapp_cons; [exact (OB 88 ltac:(lia))|]. apply PMKA.wapp_nil. }
  assert (OUT3 : forall a, ~ (os + 8 <= a < os + 16) -> ~ (os + 24 <= a < os + 32) -> ~ (os + 88 <= a < os + 96) -> L5.outside WB3 a).
  { intros a N1 N2 N3 r0 [<-|[<-|[<-|[]]]]; unfold L5.in_rng; cbn [fst snd]; lia. }
  assert (ASTK3 : L5CA.astk ar M3 sp 16384).
  { apply (L5SAR.astk_grows ar M2 M3 sp 16384 ASTK2 MGM3). }
  (* [comment removed for export] *)
  assert (LOC3 : L5.u64_at RSEGS M3 (os + 32) (pa_classic_imp PMA.AD)).
  { apply (PMKA.u64_keepA RSEGS L ar LB' FF sp 16384 WB3 M M3 EK03 WAPP3 FRB).
    - destruct AO as (f & Hf & X1 & X2). exists f. split; [exact Hf|]. lia.
    - intros i Hi. apply OUT3; lia.
    - replace (os + 32) with (os + 8 + 24) by lia. exact N24. }
  unfold PMA.locale_dtor_spec, PMSPA.locale_dtor_spec in LDT. cbn [pa_locale_dtor PMA.AD ADDR_A] in LDT.
  assert (R3gp : getr R3 (reg 3) = Z_to_bv 64 (pa_gp ADDR_A)).
  { rewrite (KS3 3%nat) by inl. rewrite (L5SAR.cs_of_preserved R1 R2 3 RP2) by inl. rewrite (KS1 3%nat) by inl. exact Rgp. }
  assert (R3tp : getr R3 (reg 4) = Z_to_bv 64 (hl_tp L)).
  { rewrite (KS3 4%nat) by inl. rewrite (L5SAR.cs_of_preserved R1 R2 4 RP2) by inl. rewrite (KS1 4%nat) by inl. exact Rtp. }
  assert (R3sp : getr R3 (reg 2) = Z_to_bv 64 (sp - 48)) by (rewrite (KS3 2%nat) by inl; exact G2).
  apply (LDT fx3 R3 M3 model3 K LB' FF LK Aw2 cr (os + 32) (sp - 48) 701456 HH3 AM3 K0).
  { split; [rewrite L5K.rl1; exact A31|]. split; [split; [lia|reflexivity]|]. split; [rewrite L5K.rl2; exact R3sp|]. split; [rewrite L5K.rl3; exact R3gp|].
    split; [rewrite L5K.rl4; exact R3tp|]. change (PMSPA.pm_scr 0) with 12288. split.
    { apply (L5SAR.astk_sub ar M3 M3 sp 16384 48 12288 ASTK3 (fun _ X => X)); [lia|lia|lia|].
      replace (sp - 48) with (sp + (-3) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
    change (12288 / 8) with 1536. apply (PMKA.stksh_keepA L ar LB' FF sp 16384 WB3 M M3 EK03 WAPP3); [lia|lia|lia| |lia|].
    - apply PMKA.mod16_8'. replace (sp - 48 - 12288) with (sp + (-771) * 16) by lia. rewrite Z_mod_plus_full. exact A16.
    - apply (PMKA.shadow_zero_sub M (sp - 16384) 2048); [|  |lia|lia|lia| exact STKSH].
      + apply PMKA.mod16_8'. replace (sp - 16384) with (sp + (-1024) * 16) by lia. rewrite Z_mod_plus_full. exact A16.
      + apply PMKA.mod16_8'. replace (sp - 48 - 12288) with (sp + (-771) * 16) by lia. rewrite Z_mod_plus_full. exact A16. }
  { intros k Hk. specialize (FRM k Hk). lia. }
  { intros f Hf. specialize (FRS f Hf). lia. }
  { rewrite L5K.rl10. exact A310. }
  { destruct AO as (f & Hf & X1 & X2). exists f. split; [exact Hf|]. lia. }
  { exact LOC3. }
  intros fx4 R4 model3d RP4 MRTd AMd HHd.   (* [comment removed for export] *)
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB' FF LK cr Aw2 M3 model3d HHd) as (_ & VIS3d & VIMG3d & _).
  set (H3d := ahid Aw2 model3d) in *.
  (* [comment removed for export] *)
  assert (FRAME12 : forall a, sp - 48 <= a < sp -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { intros a Ha. destruct HP2 as (P2 & _ & _). apply P2. split; [lia|]. split; [|intros r0 []].
    unfold aclient, aclient_g. right; left. split; [lia| intros X; unfold PMSPA.OPDEL_SCR, PMSPA.MALLOC_SCR in X; lia]. }
  assert (SAVE : forall k v, 1 <= k <= 5 -> L5.u64_at RSEGS M1v (sp - 8 * k) v -> L5.u64_at RSEGS (mrestrict H3d M3) (sp - 8 * k) v).
  { intros k v Hk SV. rewrite <- VIS1 in SV. apply (proj1 (L5A.u64_at_vis H M1 (sp - 8 * k) v (VIS (sp - 8 * k) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))) in SV.
    apply (proj2 (L5A.u64_at_vis H3d M3 (sp - 8 * k) v (VIS3d (sp - 8 * k) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5C.u64_at_agree RSEGS M1 M3); [|lia|lia| exact SV].
    intros i Hi. rewrite FR3; [apply FRAME12; lia| lia|]. intros [X|[X|X]]; lia. }
  set (MV3 := mrestrict H3d M3) in *.
  assert (IMG3 : L5.img_clear M3 65536 1282048).
  { intros i Hi. rewrite FR3; [apply IMG2; exact Hi| lia|]. pose proof (L5A.aly_img_lo L C LYa). intros [X|[X|X]]; lia. }
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HHd) as ST3. rewrite (L5A.aly_segs L C LYa) in ST3.
  pose proof (L5A.statics_facts L C M3 LYa ST3) as (_ & CSB3 & CUAR3 & _).
  assert (HV3 : ahid Aw2 model3d = H3d) by reflexivity.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 1))) as Hs1. pose proof (bv_unsigned_in_range 64 (getr R (reg 8))) as Hs8.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 9))) as Hs9. pose proof (bv_unsigned_in_range 64 (getr R (reg 18))) as Hs18.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 19))) as Hs19. change (bv_modulus 64) with (2 ^ 64) in *.
  assert (X4_2 : getr R4 (reg 2) = Z_to_bv 64 (sp - 48)) by (rewrite (L5SAR.cs_of_preserved R3 R4 2 RP4) by inl; exact R3sp).
  assert (X4_9 : getr R4 (reg 9) = Z_to_bv 64 (os + 8)) by (rewrite (L5SAR.cs_of_preserved R3 R4 9 RP4) by inl; exact A39).
  assert (X4_18 : getr R4 (reg 18) = Z_to_bv 64 (os + 88)) by (rewrite (L5SAR.cs_of_preserved R3 R4 18 RP4) by inl; exact A318).
  assert (Y0 : L5.img_clear MV3 65536 1282048) by (apply L5A.img_clear_mrestrict; exact IMG3).
  assert (Y1 : L5.u64_at RSEGS MV3 1309752 2147450880) by (apply (proj2 (L5A.u64_at_vis H3d M3 1309752 2147450880 (VIMG3d 1309752 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB3).
  assert (Y2 : L5.u32_at RSEGS MV3 1309760 1) by (apply (proj2 (L5A.u32_at_vis H3d M3 1309760 1 (VIMG3d 1309760 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR3).
  assert (Y3 : L5.writable RSEGS MV3 (sp - 48) 48).
  { pose proof ASTK3 as (_ & _ & _ & _ & SDEF3 & _).
    apply (proj2 (L5A.writable_vis H3d M3 (sp - 48) 48 (VIS3d (sp - 48) 48 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5C.writable_of_defined RSEGS). apply (L5.defined_sub M3 (sp - 16384) 16384); [exact SDEF3| lia| lia]. lia. lia. }
  assert (Y8 : L5.u64_at RSEGS MV3 (sp - 8) (bv_unsigned (getr R (reg 1)))) by (replace (sp - 8) with (sp - 8 * 1) by lia; apply SAVE; [lia| exact C8]).
  assert (Y16 : L5.u64_at RSEGS MV3 (sp - 16) (bv_unsigned (getr R (reg 8)))) by (replace (sp - 16) with (sp - 8 * 2) by lia; apply SAVE; [lia| exact C16]).
  assert (Y24 : L5.u64_at RSEGS MV3 (sp - 24) (bv_unsigned (getr R (reg 9)))) by (replace (sp - 24) with (sp - 8 * 3) by lia; apply SAVE; [lia| exact C24]).
  assert (Y32 : L5.u64_at RSEGS MV3 (sp - 32) (bv_unsigned (getr R (reg 18)))) by (replace (sp - 32) with (sp - 8 * 4) by lia; apply SAVE; [lia| exact C32]).
  assert (Y40 : L5.u64_at RSEGS MV3 (sp - 40) (bv_unsigned (getr R (reg 19)))) by (replace (sp - 40) with (sp - 8 * 5) by lia; apply SAVE; [lia| exact C40]).
  LeanFeed.pfeed P (PMASDP.asdC_conc fx4 R4 MV3 (fun j => match j with 2%nat => sp | 35%nat => bv_unsigned (getr R (reg 19)) | 36%nat => bv_unsigned (getr R (reg 18))
                                                   | 37%nat => bv_unsigned (getr R (reg 9)) | 38%nat => bv_unsigned (getr R (reg 8)) | 39%nat => bv_unsigned (getr R (reg 1))
                                                   | 41%nat => os + 8 | 42%nat => os + 88 | _ => 0 end)) ltac:(first [assumption | unfold PMASDP.aligned; lia | lia]).
  destruct P as (fx5 & R5 & M5v & MG5 & _ & FZ5 & MS5 & KS5 & A51 & A52 & A58 & A59 & A510 & A511 & A518 & A519).
  apply (L5SAR.apiece_ro L ar C HI LYa HIok LB' FF LK cr Aw2 M3 model3d fx4 fx5 R4 701456 R5 0xda75c M5v K HHd AMd); [rewrite HV3; exact MS5| rewrite HV3; exact MG5| rewrite HV3; exact FZ5|].
  intros M5 model5 HH5 AM5 MRT5 HID5 VIS5 MGM5 FR5.
  (* [comment removed for export] *)
  assert (E53 : forall a, 0 <= a < 2 ^ 64 -> M5 (Z_to_bv 64 a) = M3 (Z_to_bv 64 a)) by exact FR5.
  assert (MG35 : mem_grows M3 M5) by exact MGM5.
  assert (R5gp : getr R5 (reg 3) = Z_to_bv 64 (pa_gp ADDR_A)) by (rewrite (KS5 3%nat) by inl; rewrite (L5SAR.cs_of_preserved R3 R4 3 RP4) by inl; exact R3gp).
  assert (R5tp : getr R5 (reg 4) = Z_to_bv 64 (hl_tp L)) by (rewrite (KS5 4%nat) by inl; rewrite (L5SAR.cs_of_preserved R3 R4 4 RP4) by inl; exact R3tp).
  assert (R5ra : getr R5 (reg 1) = Z_to_bv 64 r) by (rewrite A51, Z_to_bv_bv_unsigned; exact Rra).
  assert (STD : forall a, PMST.dep PMA.AD a -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a /\ L5.outside WB3 a).
  { intros a D. pose proof (dep_img a D) as DI. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [lia|].
    split; [exact (PMA.ly_static L C LY a (PnStatics.PNST.dep_of_j _ _ a D))|]. apply OUT3; lia. }
  assert (SRO : forall a, 65536 <= a < pa_rw_lo PMA.AD -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a /\ L5.outside WB3 a).
  { intros a Ha. cbn [pa_rw_lo PMA.AD ADDR_A] in Ha. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [lia|].
    split; [intros X; pose proof (L5A.aly_static_lo L C LYa a X); lia| apply OUT3; lia]. }
  assert (BASE5 : PMSTA.base_okA RSEGS PMA.AD M5).
  { pose proof (PMKA.base_ok_keepA RSEGS PMA.AD L ar LB' FF sp 16384 WB3 M M3 EK03 PMA.addrs_wf_A STD SRO BASE) as B3.
    destruct B3 as (X0 & (can & Hc & X1) & X2 & X3). split; [|split; [|split]].
    - intros i Hi. rewrite E53; [apply X0; exact Hi| cbn [pa_rw_lo PMA.AD ADDR_A] in Hi; lia].
    - exists can. split; [exact Hc|]. apply (L5C.u64_at_agree RSEGS M3 M5); [intros i Hi; apply E53; cbn [pa_canary PMA.AD ADDR_A] in Hi; lia|cbn; lia|cbn; lia| exact X1].
    - apply (L5C.u8_at_agree RSEGS M3 M5); [intros i Hi; apply E53; cbn [pa_need_locks PMA.AD ADDR_A] in Hi; lia|cbn; lia|cbn; lia| exact X2].
    - unfold L5.u32_at in *. rewrite (L5C.rdn_agree RSEGS M3 M5 4%nat (pa_locale_lock PMA.AD)); [exact X3|cbn; lia|cbn; lia|].
      intros i Hi. apply E53. cbn [pa_locale_lock PMA.AD ADDR_A] in Hi |- *. cbn in Hi. lia. }
  assert (IOS5 : PM.iosb_at RSEGS PMA.AD PMSPA.accA M5 (os + 88) (pa_vp_nullis_ios PMA.AD) (os + 24) 0).
  { replace (os + 88) with (os + 8 + 80) in * by lia. replace (os + 24) with (os + 8 + 16) by lia.
    destruct NIOS as (I0 & I32 & I36 & I40 & I48 & IZ & ID & IC & IST).
    assert (AGH : forall a n, os + 8 + 88 <= a -> a + n <= os + 8 + 80 + 152 -> L5C.agree_on M M5 a n).
    { intros a n Ha Hn j Hj. rewrite E53 by lia. apply EK03. split; [lia|]. split; [|apply OUT3; lia].
      unfold aclient, aclient_g. do 3 right. left. destruct AO as (f & Hf & X1 & X2). exists f. split; [exact Hf|]. split; [lia| intros X; lia]. }
    assert (VP5 : L5.u64_at RSEGS M5 (os + 8 + 80) (pa_vp_nullis_ios PMA.AD)).
    { cbn [pa_vp_nullis_ios PMA.AD ADDR_A]. apply (L5C.u64_at_agree RSEGS M3 M5); [intros j Hj; apply E53; lia|lia|lia|].
      unfold MV3 in *. rewrite <- VIS3 in C388.
      apply (proj1 (L5A.u64_at_vis H2 M3 (os + 8 + 80) 1252088 ltac:(eapply L5A.avis_sub; [exact OVIS2|lia|lia]) ltac:(lia) ltac:(lia))). exact C388. }
    split; [exact VP5|].
    split; [apply (PMF.u32_at_agree RSEGS M M5); [apply AGH; lia|lia|lia|exact I32]|].
    split; [apply (PMF.u32_at_agree RSEGS M M5); [apply AGH; lia|lia|lia|exact I36]|].
    split; [apply (L5C.u64_at_agree RSEGS M M5); [apply AGH; lia|lia|lia|exact I40]|].
    split; [apply (L5C.u64_at_agree RSEGS M M5); [apply AGH; lia|lia|lia|exact I48]|].
    split; [apply (PMF.zeros_at_agree M M5); [apply AGH; lia|exact IZ]|].
    split.
    { intros j Hj. rewrite E53 by lia. apply MGM3. replace (os + 8 + 80 + j) with (os + (88 + j)) by lia. apply ODEF2. lia. }
    split; [| exact IST].
    apply (PMFA.accA_agree M M5); [|exact IC].
    assert (SHX := PMKA.agsh_obj L ar LB' FF sp 16384 WB3 M M3 EK03 WAPP3 FRB (os + 8 + 80) 152 ltac:(destruct AO as (f & Hf & X1 & X2); exists f; split; [exact Hf|]; lia)).
    intros x Hx. pose proof (PMKA.S_in_shadow x ltac:(lia)) as SXB. unfold BIGSHADOW_LO, BIGSHADOW_HI in SXB.
    rewrite E53 by lia. apply (SHX x). exact Hx. }
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH5) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & TOP5 & _).
  assert (ASTK5 : L5CA.astk ar M5 sp 16384) by (apply (L5SAR.astk_grows ar M3 M5 sp 16384 ASTK3 MGM5)).
  unfold PMA.ios_dtor_spec, PMSPA.ios_dtor_spec in IDT. cbn [pa_ios_dtor PMA.AD ADDR_A] in IDT.
  apply (IDT fx5 R5 M5 model5 K LB' FF LK Aw2 cr (os + 88) (pa_vp_nullis_ios PMA.AD) (os + 24) 0 sp r HH5 AM5 K0).
  { split; [rewrite L5K.rl1; exact R5ra|]. split; [exact RAok|]. split; [rewrite L5K.rl2; exact A52|]. split; [rewrite L5K.rl3; exact R5gp|].
    split; [rewrite L5K.rl4; exact R5tp|]. change (PMSPA.pm_scr 1) with 14336. split.
    { pose proof (L5SAR.astk_sub ar M5 M5 sp 16384 0 14336 ASTK5 (fun _ X => X) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite Z.sub_0_r; exact A16)) as X.
      rewrite Z.sub_0_r in X. exact X. }
    change (14336 / 8) with 1792. intros j Hj. unfold byte_at. pose proof (PMKA.S_in_shadow (sp - 14336 + 8 * j) ltac:(lia)) as SXB. unfold BIGSHADOW_LO, BIGSHADOW_HI in SXB.
    assert (SJ : S (sp - 14336) + j = S (sp - 14336 + 8 * j)).
    { unfold S. replace (sp - 14336 + 8 * j) with (j * 8 + (sp - 14336)) by lia. rewrite Z.div_add_l by lia. lia. }
    rewrite E53 by lia.
    apply (PMKA.stksh_keepA L ar LB' FF sp 16384 WB3 M M3 EK03 WAPP3 (sp - 14336) 1792); [lia|lia|lia| | lia | | lia].
    - apply PMKA.mod16_8'. replace (sp - 14336) with (sp + (-896) * 16) by lia. rewrite Z_mod_plus_full. exact A16.
    - apply (PMKA.shadow_zero_sub M (sp - 16384) 2048); [| |lia|lia|lia| exact STKSH].
      + apply PMKA.mod16_8'. replace (sp - 16384) with (sp + (-1024) * 16) by lia. rewrite Z_mod_plus_full. exact A16.
      + apply PMKA.mod16_8'. replace (sp - 14336) with (sp + (-896) * 16) by lia. rewrite Z_mod_plus_full. exact A16. }
  { intros k Hk. specialize (FRM k Hk). lia. }
  { exact FRS. }
  { rewrite L5K.rl10. exact A510. }
  { destruct AO as (f & Hf & X1 & X2). exists f. split; [exact Hf|]. lia. }
  { replace (os + 88) with (os + 11 * 8) by lia. rewrite Z_mod_plus_full. exact O8. }
  { exact IOS5. }
  { exact BASE5. }
  intros fx6 R6 M6 model6 LK6 Aw6 RP6 HP6 MRT6 INC6 INC6A AM6 HH6.
  assert (CS5 : forall k, In k L5SAR.cs_all -> getr R5 (reg k) = getr R (reg k)).
  { intros k Hk. unfold L5SAR.cs_all in Hk.
    repeat (destruct Hk as [<-|Hk];
      [ first [ rewrite A52; exact (eq_sym Rsp)
              | rewrite A58; apply Z_to_bv_bv_unsigned | rewrite A59; apply Z_to_bv_bv_unsigned
              | rewrite A518; apply Z_to_bv_bv_unsigned | rewrite A519; apply Z_to_bv_bv_unsigned
              | rewrite (KS5 _) by inl; rewrite (L5SAR.cs_of_preserved R3 R4 _ RP4) by inl; rewrite (KS3 _) by inl;
                rewrite (L5SAR.cs_of_preserved R1 R2 _ RP2) by inl; rewrite (KS1 _) by inl; reflexivity ] |]).
    destruct Hk. }
  apply (KONT fx6 R6 M6 model6 LK6 Aw6).
  - apply (L5SAR.regs_preserved_trans R R5 R6); [apply L5SAR.preserved_by_index; intros k Hk; exact (CS5 k Hk)| exact RP6].
  - assert (EK35 : L5SAR.ek L ar LB' FF sp 16384 [(os, 296)] M3 M5).
    { intros a (Ha & _ & _). apply E53. exact Ha. }
    assert (EK56 : L5SAR.ek L ar LB' FF sp 16384 [(os, 296)] M5 M6).
    { apply (L5SAR.ek_callee L ar LB' [] FF [] sp 16384 sp (PMSPA.pm_scr 1) [(os, 296)] [(os + 88, 152)] M5 M6 HP6); [change (PMSPA.pm_scr 1) with 14336; lia| lia|].
      intros a _ O r0 [<-|[]] X. apply (O (os, 296)); [left; reflexivity|]. unfold L5.in_rng in *; cbn [fst snd] in *. lia. }
    assert (EK03' : L5SAR.ek L ar LB' FF sp 16384 [(os, 296)] M M3).
    { apply (L5SAR.ek_W L ar LB' FF sp 16384 [(os, 296)] WB3 M M3 EK03). intros a O r0 Hr X. apply (O (os, 296)); [left; reflexivity|].
      unfold WB3 in Hr. destruct Hr as [<-|[<-|[<-|[]]]]; unfold L5.in_rng in *; cbn [fst snd] in *; lia. }
    apply (L5SAR.ahpres_of L ar LB' FF sp 16384 [(os, 296)] M M6).
    + apply (L5SAR.ek_trans L ar LB' FF sp 16384 [(os, 296)] M M5 M6); [apply (L5SAR.ek_trans L ar LB' FF sp 16384 [(os, 296)] M M3 M5 EK03' EK35)| exact EK56].
    + pose proof (PMKA.astk_after_ahpres L ar LB' FF M5 M6 sp 16384 sp (PMSPA.pm_scr 1) [(os + 88, 152)] ASTK5 HP6) as X.
      change (PMSPA.pm_scr 1) with 14336 in X. destruct (X ltac:(lia) ltac:(lia) ltac:(lia) TOP5) as (_ & _ & _ & _ & D6 & _). exact D6.
    + apply (L5SAR.dk_trans L ar LB' FF sp 16384 M M5 M6).
      * apply (L5SAR.dk_trans L ar LB' FF sp 16384 M M2 M5).
        -- apply (L5SAR.dk_trans L ar LB' FF sp 16384 M M1 M2); [apply (L5SAR.dk_grows L ar LB' FF sp 16384 M M1 MGM1)|].
           apply (L5SAR.dk_callee L ar LB' [] FF [] sp 16384 (sp - 48) PMSPA.OPDEL_SCR [] M1 M2 HP2); unfold PMSPA.OPDEL_SCR, PMSPA.MALLOC_SCR; lia.
        -- apply (L5SAR.dk_grows L ar LB' FF sp 16384 M2 M5). intros x Hx. apply MGM5. apply MGM3. exact Hx.
      * apply (L5SAR.dk_callee L ar LB' [] FF [] sp 16384 sp (PMSPA.pm_scr 1) [(os + 88, 152)] M5 M6 HP6); change (PMSPA.pm_scr 1) with 14336; lia.
  - apply (L5LZ.model_rt_trans model model5 model6); [|exact MRT6].
    apply (L5LZ.model_rt_trans model model3d model5); [|exact MRT5].
    apply (L5LZ.model_rt_trans model model2 model3d); [|exact (L5LZ.model_rt_trans model2 model3 model3d MRT3 MRTd)].
    apply (L5LZ.model_rt_trans model model1 model2); [exact MRT1| exact MRT2].
  - exact INC6.
  - intros x Hx. apply INC6A. apply INC2. exact Hx.
  - exact AM6.
  - exact HH6.
Qed.
End WithHeap.
End PMASD.
