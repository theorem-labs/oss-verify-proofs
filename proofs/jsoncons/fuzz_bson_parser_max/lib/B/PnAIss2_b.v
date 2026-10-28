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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StreamSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PmSpecsAX_b PnSpecsAa_b
     PmModelFactsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnStepA_b PnStepA2_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmCertKitG. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import XIcptAs0_b PnAIssStmts_b PnAIssP_b PnAIss1_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import XIcptA_b XIcptAs0Kit_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia.
Ltac nodisj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Ltac dlia := first [ solve [ L5FastLia.prune_arith; nodisj; L5FastLia.lia_ne ]
                   | solve [ L5FastLia.prune_arith; match goal with H : _ \/ _ |- _ => L5SAR.clear_disj_but H; destruct H; L5FastLia.lia_ne end ]
                   | solve [ L5FastLia.prune_arith; nodisj; L5FastLia.lia_st ]
                   | solve [ L5FastLia.prune_arith; match goal with H : _ \/ _ |- _ => L5SAR.clear_disj_but H; destruct H; L5FastLia.lia_st end ] ].
Local Ltac lia := dlia.
Module PMAIS2.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).

Section Stage.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMA.ly_as0 L C LY.

Theorem memsets : forall (fx : FPState) R0 M0 model0 K LB FF LK0 Aw0 cr ois os sp r s b R1 M1 model1 LK1 Aw1,
    PMAIS.pre L ar HI R0 M0 model0 K LB FF LK0 Aw0 cr ois os sp r s b ->
    PMAIS.mid L ar HI R0 M0 model0 LB FF LK0 Aw0 cr ois os sp s b R1 M1 model1 LK1 Aw1 ->
    (forall (fx2 : FPState) R2 M2 model2 LK2 Aw2, PMAIS.mid2 L ar HI R0 M0 model0 LB FF LK0 Aw0 cr ois os sp s b R2 M2 model2 LK2 Aw2 ->
        srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx2) R2 0xac2e4 M2 model2) K) ->
    srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx) R1 0xac2a8 M1 model1) K.
Proof.
  intros fx R0 M0 model0 K LB FF LK0 Aw0 cr ois os sp r s b R1 M1 model1 LK1 Aw1 PRE MID KONT.
  destruct PRE as (HH0 & AM0 & K0 & ENT & FRM & FRS & A10 & A11 & A12 & AO & AOS & EOS & O8 & OS8 & ODEF0 & ACC0 & VS0 & INCL & SZ & LNG & BASE0 & LOCb & CRED).
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK0 & STKSH0).
  rewrite L5K.rl4 in Rtp.
  assert (EOS' : os = ois - 64) by lia. subst os.
  destruct MID as (M2' & M8 & M9 & M18 & M19 & M20 & M21 & M22 & M23 & M24 & M25 & M26 & M27 & MCSK & MC).
  destruct MC as (SVI & SVB & HC & ODEF & ACC & VS & ASTK & STKSH & BASE & LOC & HH & AM & MRT & INCK & INCA & EK & DK).
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof AM as (Mh & MI). unfold PMAIS.SCR in *. change (20480 / 8) with 2560 in STKSH.
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK1 cr Aw1 M1 model1 HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
  set (H := ahid Aw1 model1) in *. set (MV := mrestrict H M1) in *.
  pose proof (PMKA.aobj_of_aobjA FF ois 272 AO O8) as AOB.
  pose proof (PMKA.aobj_of_aobjA FF (ois - 64) 24 AOS OS8) as AOSB.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK1 cr Aw1 M1 model1 ois 272 sp 20480 HH AOB ltac:(lia) ltac:(reflexivity))
    as (OR & OBIG & _ & OVIS & OVSH & OCL & OCLSH).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK1 cr Aw1 M1 model1 (ois - 64) 24 sp 20480 HH AOSB ltac:(lia) ltac:(reflexivity))
    as (OSR & OSBIG & _).
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as ST. rewrite (L5A.aly_segs L C LYa) in ST.
  pose proof (L5A.statics_facts L C M1 LYa ST) as (GOT & CSB & CUAR & _).
  assert (V0 : L5.img_clear MV 1249280 1282048) by (apply L5A.img_clear_mrestrict; exact GOT).
  assert (V1 : L5.u64_at RSEGS MV 1309752 2147450880) by (apply (proj2 (L5A.u64_at_vis H M1 1309752 2147450880 (VIMG 1309752 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB).
  assert (V2 : L5.u32_at RSEGS MV 1309760 1) by (apply (proj2 (L5A.u32_at_vis H M1 1309760 1 (VIMG 1309760 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR).
  assert (W4096 : L5.writable RSEGS MV (sp - 4096) 4096).
  { apply (proj2 (L5A.writable_vis H M1 (sp - 4096) 4096 (VIS (sp - 4096) 4096 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5SAR.astk_writable ar M1 sp 20480); [exact ASTK| lia| lia| lia]. }
  assert (OZv : L5KA.zeros_at MV (ois / 8 + 2147450880) 34).
  { exact (PMKA.obj_shadow_vis L ar C HI LYa HIok LB FF LK1 cr Aw1 M1 model1 ois 272 HH AO O8 ltac:(lia) ltac:(reflexivity) ACC). }
  assert (OWv : L5.writable RSEGS MV ois 272).
  { apply (proj2 (L5A.writable_vis H M1 ois 272 OVIS ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS). exact ODEF. lia. lia. }
  (* [comment removed for export] *)
  LeanFeed.pfeed P (PMAISP.aicC1_conc as0_icpt_fill as0_icpt_copy as0_icpt_tls fx R1 MV (fun j => match j with 2%nat => sp | 33%nat => ois | _ => 0 end)) ltac:(first [assumption | unfold PMAISP.aligned; lia | lia]).
  destruct P as (fx1 & R2 & M1v & MG1 & _ & FZ1 & MS1 & KS1 & aR1 & aR10 & aR11 & aR12).
  assert (E1 : M1v = MV) by (apply L5SAR.mem_eq_of_agree; exact FZ1). subst M1v.
  unfold PMSPA.cfg.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok LB FF LK1 cr Aw1 M1 model1 fx fx1 R1 0xac2a8 R2 0x78130 MV K HH AM MS1 MG1 FZ1).
  intros M1' model1' HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1.
  assert (E1' : M1' = M1) by (apply L5SAR.mem_eq_of_agree; exact FR1). subst M1'.
  assert (CLo : forall a, ois <= a < ois + 272 -> aclient L ar LB FF 0 0 a) by (intros a Ha; apply (L5SAR.obj_client L ar LB FF 0 0 ois 272 a AOB); lia).
  assert (CLw : forall a, ois <= a < ois + 272 -> aclientw L ar LB FF 0 0 a) by (intros a Ha; apply (L5SAR.obj_client L ar LB FF 0 0 ois 272 a AOB); lia).
  assert (WAPP : PMKA.wapp (PMAIS.WF ois b)).
  { unfold PMAIS.WF. apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; lia|].
    destruct b; [apply PMKA.wapp_nil|]. unfold PMSPA.loc_W. cbn [map pa_loc_foot PMA.AD ADDR_A fst snd].
    apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO; lia|]. apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO; lia|]. apply PMKA.wapp_nil. }
  assert (FRB : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47).
  { intros f Hf. destruct (WF f Hf) as (X1 & X2 & _). unfold app_mem, FS_BYTES in *. lia. }
  (* [comment removed for export] *)
  assert (MSET : forall (fx0 : FPState) Ra Ma modela Kc d n ra, 0 <= d -> d + n <= 272 -> 0 < n <= 48 ->
     ri_inv HI LB FF LK1 cr Aw1 Ma (vml_of modela) -> L5CA.amodel_ok Aw1 modela -> L5CA.astk ar Ma sp 20480 -> PMSPA.accA Ma ois 272 -> L5.defined Ma ois 272 ->
     getr Ra (reg 10) = Z_to_bv 64 (ois + d) -> getr Ra (reg 11) = Z_to_bv 64 0 -> getr Ra (reg 12) = Z_to_bv 64 n -> getr Ra (reg 4) = Z_to_bv 64 (hl_tp L) ->
     getr Ra (reg 1) = Z_to_bv 64 ra -> ra mod 2 = 0 -> 0 <= ra < 2 ^ 64 -> getr Ra (reg 2) = Z_to_bv 64 (sp - 192) -> Kc [] ->
     (forall Rb Mb modelb, getr Rb (reg 10) = Z_to_bv 64 (ois + d) -> regs_preserved Ra Rb -> PM.zeros_at Mb (ois + d) n ->
        (forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF (sp - 192) 2560 a -> ~ (ois + d <= a < ois + d + n) -> Mb (Z_to_bv 64 a) = Ma (Z_to_bv 64 a)) ->
        (forall a, sp - 192 - 2560 <= a < sp - 192 -> Mb (Z_to_bv 64 a) <> None) ->
        L5.defined Mb (ois + d) n ->
        model_rt modela modelb -> L5CA.amodel_ok Aw1 modelb -> ri_inv HI LB FF LK1 cr Aw1 Mb (vml_of modelb) ->
        srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx0) Rb ra Mb modelb) Kc) ->
     srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx0) Ra 0x78130 Ma modela) Kc).
  { intros fx0 Ra Ma modela Kc d n ra Hd Hdn Hn HHa AMa ASTKa ACCa DEFa Ra10 Ra11 Ra12 Ra4 Ra1 Hra Hra' Ra2 Ka KC.
    pose proof (HAJ.aior_memset _ _ _ _ _ HIok) as MS. unfold amemset_spec, amem_pre, amem_post in MS.
    rewrite (L5A.aly_segs L C LYa), (L5A.aly_memset L C LYa), (L5A.aly_scr_mem L C LYa) in MS.
    assert (U2 : bv_unsigned (getr Ra 2%bv) = sp - 192) by (rewrite L5K.rl2, Ra2; apply L5.unsigned_lit; lia).
    pose proof ASTKa as (Aa16 & _ & _ & _ & _ & _).
    unfold PMSPA.cfg. apply (MS fx0 Ra Ma modela LB FF LK1 cr Aw1 (ois + d) 0 n Kc); clear MS.
    - split; [exact HHa|]. split; [exact (proj1 AMa)|]. split; [exact (proj2 AMa)|].
      split; [rewrite L5K.rl10; exact Ra10|]. split; [rewrite L5K.rl12; exact Ra12|]. split; [lia|].
      split; [rewrite L5K.rl4; exact Ra4|]. split; [rewrite L5K.rl1, Ra1; apply Hoare.ret_ok_even; rewrite L5.unsigned_lit by lia; exact Hra|].
      split. { rewrite U2. apply (L5SAR.astack_ok_of_astk L ar C LYa Ma Ma sp 20480 192 2560 ASTKa (fun x X => X)); [lia| lia| lia|].
               replace (sp - 192) with (sp + (-12) * 16) by lia. rewrite Z.mod_add by lia. exact Aa16. }
      split. { intros a Ha. apply ACCa. lia. }
      split. { intros i Hi. rewrite U2. apply (L5SAR.obj_client L ar LB FF _ _ ois 272 (ois + d + i) AOB). lia. }
      split. { intros i m Hi Hm. pose proof (L5C.writable_of_defined RSEGS Ma ois 272 DEFa ltac:(lia) ltac:(lia)) as W.
               replace (ois + d + i) with (ois + (d + i)) by lia. apply W; lia. }
      split; [exact Ka|]. apply (L5SAR.app_rng_aobj L ar C HI HIok LB FF LK1 cr Aw1 Ma _ ois 272 (ois + d) n HHa AOB); lia.
    - rewrite L5K.rl11. exact Ra11.
    - intros Rb Mb modelb Rb10 RPb BYTES PRES SDEFb RTb MIb HHb. rewrite U2 in PRES, SDEFb. rewrite L5K.rl1, Ra1.
      assert (ZB : PM.zeros_at Mb (ois + d) n).
      { intros i Hi. destruct (BYTES i Hi) as (v & Ev & Bv). unfold byte_at in Bv. rewrite Bv. subst v. reflexivity. }
      apply (KC Rb Mb modelb); [rewrite <- L5K.rl10; exact Rb10| exact RPb| exact ZB| exact PRES| exact SDEFb| | exact RTb| | exact HHb].
      + intros i Hi. rewrite (ZB i Hi). discriminate.
      + split; [rewrite (L5LZ.model_rt_halted _ _ RTb); exact (proj1 AMa)| exact MIb]. }
  (* [comment removed for export] *)
  assert (CS2 : forall k, In k L5SAR.cs_all -> getr R2 (reg k) = getr R1 (reg k)) by (intros k Hk; apply KS1; unfold L5SAR.cs_all in Hk; repeat (destruct Hk as [<-|Hk]; [inl|]); destruct Hk).
  apply (MSET fx1 R2 M1 model1' K 32 48 705208); [lia| lia| lia| exact HH1| exact AM1| exact ASTK| exact ACC| exact ODEF| exact aR10| exact aR11| exact aR12| | exact aR1| reflexivity| lia| | exact K0|].
  { rewrite (KS1 4%nat) by inl. rewrite (MCSK 4%nat) by (right; left; reflexivity). exact Rtp. }
  { rewrite CS2 by inl. exact M2'. }
  intros R3 M3 model3 R3a0 RP3 Z32 PRES3 SDEF3 DEF3 MRT3 AM3 HH3.
  assert (CS3 : forall k, In k L5SAR.cs_all -> getr R3 (reg k) = getr R2 (reg k)) by (intros k Hk; apply (L5SAR.cs_of_preserved R2 R3 k RP3 Hk)).
  (* [comment removed for export] *)
  assert (EK13 : L5SAR.ek L ar LB FF sp 20480 (PMAIS.WF ois b) M1 M3).
  { apply (L5SAR.ek_mem L ar LB FF sp 20480 (sp - 192) 2560 (fun a => ois + 32 <= a < ois + 32 + 48) (PMAIS.WF ois b) M1 M3 PRES3); [lia| lia|].
    intros a Hc Ho X. apply (Ho (ois, 272)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]. }
  assert (DK13 : L5SAR.dk L ar LB FF sp 20480 M1 M3).
  { apply (L5SAR.dk_mem L ar LB FF sp 20480 (sp - 192) 2560 (fun a => ois + 32 <= a < ois + 32 + 48) M1 M3 PRES3 SDEF3); [| | lia| lia].
    - intros a Ha. replace a with (ois + 32 + (a - (ois + 32))) by lia. apply DEF3. lia.
    - intros a. destruct (L5SAR.rng_dec a (ois + 32) (ois + 32 + 48)) as [X|X]; [left; exact X| right; exact X]. }
  assert (ASTK3 : L5CA.astk ar M3 sp 20480).
  { apply (L5SAR.astk_after_eq L ar C HI HIok LB FF LK1 cr Aw1 M1 M1 M3 _ sp _ (sp - 192) 2560 HH1 ASTK (fun x X => X)).
    - intros a Ha Hs Hns. apply PRES3. exact Ha. apply L5SAR.stack_client. exact Hs. exact Hns. lia.
    - exact SDEF3.
    - lia. - lia. - lia. }
  assert (ACC3 : PMSPA.accA M3 ois 272).
  { apply (PMKA.acc_keepA' L ar LB FF sp 20480 _ M1 M3 EK13 WAPP FRB ois 272 AO ACC). }
  assert (ODEF3 : L5.defined M3 ois 272).
  { pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK1 cr Aw1 M3 model3 ois 272 sp 20480 HH3 AOB ltac:(lia) ltac:(reflexivity)) as (_ & _ & X & _). exact X. }
  (* [comment removed for export] *)
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK1 cr Aw1 M3 model3 HH3) as (HOFF3 & VIS3 & VIMG3 & VFS3 & VBLK3 & VBSH3 & VFSSH3 & VSTSH3).
  set (H3 := ahid Aw1 model3) in *. set (MV3 := mrestrict H3 M3) in *.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK1 cr Aw1 M3 model3 ois 272 sp 20480 HH3 AOB ltac:(lia) ltac:(reflexivity)) as (_ & _ & _ & OVIS3 & _).
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH3) as ST3. rewrite (L5A.aly_segs L C LYa) in ST3.
  pose proof (L5A.statics_facts L C M3 LYa ST3) as (GOT3 & CSB3 & CUAR3 & _).
  assert (Y0 : L5.img_clear MV3 1249280 1282048) by (apply L5A.img_clear_mrestrict; exact GOT3).
  assert (Y1 : L5.u64_at RSEGS MV3 1309752 2147450880) by (apply (proj2 (L5A.u64_at_vis H3 M3 1309752 2147450880 (VIMG3 1309752 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB3).
  assert (Y2 : L5.u32_at RSEGS MV3 1309760 1) by (apply (proj2 (L5A.u32_at_vis H3 M3 1309760 1 (VIMG3 1309760 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR3).
  assert (Y3 : L5.writable RSEGS MV3 (sp - 4096) 4096).
  { apply (proj2 (L5A.writable_vis H3 M3 (sp - 4096) 4096 (VIS3 (sp - 4096) 4096 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5SAR.astk_writable ar M3 sp 20480); [exact ASTK3| lia| lia| lia]. }
  assert (YZ : L5KA.zeros_at MV3 (ois / 8 + 2147450880) 34).
  { exact (PMKA.obj_shadow_vis L ar C HI LYa HIok LB FF LK1 cr Aw1 M3 model3 ois 272 HH3 AO O8 ltac:(lia) ltac:(reflexivity) ACC3). }
  assert (YW : L5.writable RSEGS MV3 ois 272).
  { apply (proj2 (L5A.writable_vis H3 M3 ois 272 OVIS3 ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS). exact ODEF3. lia. lia. }
  assert (X2 : getr R3 (reg 2) = Z_to_bv 64 (sp - 192)) by (rewrite CS3, CS2 by inl; exact M2').
  assert (X8 : getr R3 (reg 8) = Z_to_bv 64 (ois + 16)) by (rewrite CS3, CS2 by inl; exact M8).
  assert (X9 : getr R3 (reg 9) = Z_to_bv 64 (ois + 24)) by (rewrite CS3, CS2 by inl; exact M9).
  assert (X18 : getr R3 (reg 18) = Z_to_bv 64 8) by (rewrite CS3, CS2 by inl; exact M18).
  assert (X19 : getr R3 (reg 19) = Z_to_bv 64 8) by (rewrite CS3, CS2 by inl; exact M19).
  assert (X20 : getr R3 (reg 20) = Z_to_bv 64 (ois - 64)) by (rewrite CS3, CS2 by inl; exact M20).
  assert (X21 : getr R3 (reg 21) = Z_to_bv 64 (((ois + 16) / 8) + 2147450880)) by (rewrite CS3, CS2 by inl; exact M21).
  assert (X22 : getr R3 (reg 22) = Z_to_bv 64 1265600) by (rewrite CS3, CS2 by inl; exact M22).
  assert (X23 : getr R3 (reg 23) = Z_to_bv 64 2147450880) by (rewrite CS3, CS2 by inl; exact M23).
  assert (X24 : getr R3 (reg 24) = Z_to_bv 64 2147450880) by (rewrite CS3, CS2 by inl; exact M24).
  assert (X25 : getr R3 (reg 25) = Z_to_bv 64 1265968) by (rewrite CS3, CS2 by inl; exact M25).
  assert (X26 : getr R3 (reg 26) = Z_to_bv 64 (((ois + 120) / 8) + 2147450880)) by (rewrite CS3, CS2 by inl; exact M26).
  assert (X27 : getr R3 (reg 27) = Z_to_bv 64 1266008) by (rewrite CS3, CS2 by inl; exact M27).
  LeanFeed.pfeed P (PMAISP.aicC2_conc as0_icpt_fill as0_icpt_copy as0_icpt_tls fx1 R3 MV3 (fun j => match j with 2%nat => sp | 33%nat => ois | _ => 0 end)) ltac:(first [assumption | unfold PMAISP.aligned; lia | lia]).
  destruct P as (fx4 & R4 & M4v & MG4 & _ & FZ4 & MS4 & KS4 & cR1 & cR10 & cR11 & cR12 & cR18 & cR21 & cV16).
  set (W4 := fun a => ois + 16 <= a < ois + 16 + 8).
  apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK1 cr Aw1 M3 model3 fx1 fx4 R3 0xac2b8 R4 0x78130 M4v W4 K HH3 AM3 MS4 MG4).
  { intros a Ha N. apply FZ4; [exact Ha| exact N]. }
  { intros a Ha Wa. unfold W4 in Wa. split; [apply CLw; lia| lia]. }
  intros M4 model4 HH4 AM4 MRT4 HID4 VIS4 MGM4 FR4 VV4.
  assert (EK34 : L5SAR.ek L ar LB FF sp 20480 (PMAIS.WF ois b) M3 M4).
  { apply (L5SAR.ek_piece L ar LB FF sp 20480 (PMAIS.WF ois b) M3 M4 W4 FR4). intros a Ha Hc Ho X.
    apply (Ho (ois, 272)); [left; reflexivity| unfold L5.in_rng, W4 in *; cbn [fst snd]; lia]. }
  assert (ASTK4 : L5CA.astk ar M4 sp 20480) by (apply (L5SAR.astk_grows ar M3 M4 sp 20480 ASTK3 MGM4)).
  assert (ACC4 : PMSPA.accA M4 ois 272).
  { apply (PMKA.acc_keepA' L ar LB FF sp 20480 _ M3 M4 EK34 WAPP FRB ois 272 AO ACC3). }
  assert (ODEF4 : L5.defined M4 ois 272) by (apply (L5.defined_grows M3 M4 _ _ MGM4); exact ODEF3).
  (* [comment removed for export] *)
  apply (MSET fx4 R4 M4 model4 K 80 24 705252); [lia| lia| lia| exact HH4| exact AM4| exact ASTK4| exact ACC4| exact ODEF4| exact cR10| exact cR11| exact cR12| | exact cR1| reflexivity| lia| | exact K0|].
  { rewrite (KS4 4%nat) by inl. rewrite CS3, CS2 by inl. rewrite (MCSK 4%nat) by (right; left; reflexivity). exact Rtp. }
  { rewrite (KS4 2%nat) by inl. exact X2. }
  intros R5 M5 model5 R5a0 RP5 Z80 PRES5 SDEF5 DEF5 MRT5 AM5 HH5.
  assert (CS5 : forall k, In k L5SAR.cs_all -> getr R5 (reg k) = getr R4 (reg k)) by (intros k Hk; apply (L5SAR.cs_of_preserved R4 R5 k RP5 Hk)).
  assert (EK45 : L5SAR.ek L ar LB FF sp 20480 (PMAIS.WF ois b) M4 M5).
  { apply (L5SAR.ek_mem L ar LB FF sp 20480 (sp - 192) 2560 (fun a => ois + 80 <= a < ois + 80 + 24) (PMAIS.WF ois b) M4 M5 PRES5); [lia| lia|].
    intros a Hc Ho X. apply (Ho (ois, 272)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]. }
  assert (DK45 : L5SAR.dk L ar LB FF sp 20480 M4 M5).
  { apply (L5SAR.dk_mem L ar LB FF sp 20480 (sp - 192) 2560 (fun a => ois + 80 <= a < ois + 80 + 24) M4 M5 PRES5 SDEF5); [| | lia| lia].
    - intros a Ha. replace a with (ois + 80 + (a - (ois + 80))) by lia. apply DEF5. lia.
    - intros a. destruct (L5SAR.rng_dec a (ois + 80) (ois + 80 + 24)) as [X|X]; [left; exact X| right; exact X]. }
  assert (EK15 : L5SAR.ek L ar LB FF sp 20480 (PMAIS.WF ois b) M1 M5).
  { apply (L5SAR.ek_trans L ar LB FF sp 20480 _ M1 M4 M5); [apply (L5SAR.ek_trans L ar LB FF sp 20480 _ M1 M3 M4 EK13 EK34)| exact EK45]. }
  assert (EK05 : L5SAR.ek L ar LB FF sp 20480 (PMAIS.WF ois b) M0 M5) by (apply (L5SAR.ek_trans L ar LB FF sp 20480 _ M0 M1 M5 EK EK15)).
  assert (AG15 : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF 0 0 a -> ~ (sp - 2752 <= a < sp - 192) -> ~ (ois + 16 <= a < ois + 24) -> ~ (ois + 32 <= a < ois + 112) ->
                 M5 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { intros a Ha Hc N1 N2 N3.
    rewrite PRES5; [| exact Ha| apply (L5SAR.aclient_narrow L ar LB FF 0 0); [exact Hc| lia]| lia].
    rewrite FR4; [| exact Ha| unfold W4; lia].
    apply PRES3; [exact Ha| apply (L5SAR.aclient_narrow L ar LB FF 0 0); [exact Hc| lia]| lia]. }
  assert (SCL : forall a, sp - 20480 <= a < sp -> aclient L ar LB FF 0 0 a) by (intros a Ha; apply L5SAR.stack_client; lia).
  assert (AGS : forall a, (sp - 192 <= a < sp) \/ (ois <= a < ois + 272 /\ ~ (ois + 16 <= a < ois + 24) /\ ~ (ois + 32 <= a < ois + 112)) ->
                M5 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { intros a Ha. apply AG15; [lia| destruct Ha as [Ha|Ha]; [apply SCL; lia| apply CLo; lia]| lia| lia| lia]. }
  Ltac a64 AG X Ms := apply (L5C.u64_at_agree RSEGS Ms); [intros i Hi; apply AG; (lia || fail 1 "AG")| (lia || fail 1 "B1")| (lia || fail 1 "B2")| exact X].
  Ltac a32 AG X Ms := apply (PMF.u32_at_agree RSEGS Ms); [intros i Hi; apply AG; (lia || fail 1 "AG")| (lia || fail 1 "B1")| (lia || fail 1 "B2")| exact X].
  unfold PMSPA.cfg in KONT. apply (KONT fx4 R5 M5 model5 LK1 Aw1).
  split; [rewrite CS5 by inl; rewrite (KS4 2%nat) by inl; exact X2|].
  split; [rewrite CS5 by inl; rewrite (KS4 8%nat) by inl; exact X8|].
  split; [rewrite CS5 by inl; rewrite (KS4 9%nat) by inl; exact X9|].
  split; [rewrite CS5 by inl; exact cR18|].
  split; [rewrite CS5 by inl; rewrite (KS4 19%nat) by inl; exact X19|].
  split; [rewrite CS5 by inl; rewrite (KS4 20%nat) by inl; exact X20|].
  split; [rewrite CS5 by inl; exact cR21|].
  split; [rewrite CS5 by inl; rewrite (KS4 22%nat) by inl; exact X22|].
  split; [rewrite CS5 by inl; rewrite (KS4 23%nat) by inl; exact X23|].
  split; [rewrite CS5 by inl; rewrite (KS4 24%nat) by inl; exact X24|].
  split; [rewrite CS5 by inl; rewrite (KS4 25%nat) by inl; exact X25|].
  split; [rewrite CS5 by inl; rewrite (KS4 26%nat) by inl; exact X26|].
  split; [rewrite CS5 by inl; rewrite (KS4 27%nat) by inl; exact X27|].
  split. { intros k Hk. assert (Hk' : In k L5SAR.cs_all) by (destruct Hk as [<-|[<-|[]]]; inl).
           rewrite (CS5 k Hk'). rewrite (KS4 k) by (destruct Hk as [<-|[<-|[]]]; inl). rewrite (CS3 k Hk'), (CS2 k Hk'). apply MCSK. exact Hk. }
  split. { cbn [pa_vp_strbuf PMA.AD ADDR_A]. apply (L5C.u64_at_agree RSEGS M4); [intros i Hi; apply PRES5; [lia| apply (L5SAR.aclient_narrow L ar LB FF 0 0); [apply CLo; lia| lia]| lia]| lia| lia|].
           apply (PMAIS1.vis_u64 _ _ _ (ois + 16) _ VIS4 ltac:(eapply L5A.avis_sub; [exact OVIS3| lia| lia]) ltac:(lia) ltac:(lia) cV16). }
  split. { apply (PMF.zeros_at_agree M3); [intros i Hi|exact Z32]. rewrite PRES5; [| lia| apply (L5SAR.aclient_narrow L ar LB FF 0 0); [apply CLo; lia| lia]| lia].
           apply FR4; [lia| unfold W4; lia]. }
  split; [exact Z80|].
  unfold PMAIS.midc.
  destruct SVI as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80 & S88 & S96 & S104).
  destruct SVB as (T120 & T128 & T136 & T144 & T152 & T160 & T168 & T176 & T184).
  destruct HC as (H0 & H24 & H120 & H152 & H156 & H160 & H168 & Z176).
  split. { unfold PMAIS.saves_iss.
           split; [a64 AGS S8 M1|]. split; [a64 AGS S16 M1|]. split; [a64 AGS S24 M1|]. split; [a64 AGS S32 M1|]. split; [a64 AGS S40 M1|].
           split; [a64 AGS S48 M1|]. split; [a64 AGS S56 M1|]. split; [a64 AGS S64 M1|]. split; [a64 AGS S72 M1|]. split; [a64 AGS S80 M1|].
           split; [a64 AGS S88 M1|]. split; [a64 AGS S96 M1| a64 AGS S104 M1]. }
  split. { unfold PMAIS.saves_sb.
           split; [a64 AGS T120 M1|]. split; [a64 AGS T128 M1|]. split; [a64 AGS T136 M1|]. split; [a64 AGS T144 M1|]. split; [a64 AGS T152 M1|].
           split; [a64 AGS T160 M1|]. split; [a64 AGS T168 M1|]. split; [a64 AGS T176 M1|]. a64 AGS T184 M1. }
  split. { unfold PMAIS.head_cells.
           split; [a64 AGS H0 M1|]. split; [a64 AGS H24 M1|]. split; [a64 AGS H120 M1|]. split; [a32 AGS H152 M1|]. split; [a32 AGS H156 M1|].
           split; [a64 AGS H160 M1|]. split; [a64 AGS H168 M1|].
           apply (PMF.zeros_at_agree M1); [intros i Hi; apply AGS; lia| exact Z176]. }
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK1 cr Aw1 M5 model5 ois 272 sp 20480 HH5 AOB ltac:(lia) ltac:(reflexivity)) as (_ & _ & ODEF5 & _).
  split; [exact ODEF5|].
  split; [apply (PMKA.acc_keepA' L ar LB FF sp 20480 _ M1 M5 EK15 WAPP FRB ois 272 AO ACC)|].
  split. { apply (PMKA.vstr_keepA RSEGS L ar LB FF sp 20480 _ M1 M5 EK15 WAPP FRB); [| exact AOS| exact INCL| | | exact VS].
           - intros bq Hbq. destruct (proj1 (WB bq Hbq)) as (Yb0 & _ & _ & _ & Yb4 & _). lia.
           - intros i Hi rg Hin Hr. unfold PMAIS.WF in Hin. destruct Hin as [<-|Hin]; [unfold L5.in_rng in Hr; cbn [fst snd] in Hr; lia|].
             destruct b; [destruct Hin|]. unfold PMSPA.loc_W in Hin. cbn [map pa_loc_foot PMA.AD ADDR_A fst snd] in Hin.
             destruct Hin as [<-|[<-|[]]]; unfold L5.in_rng in Hr; cbn [fst snd] in Hr; lia.
           - intros c n p E j Hj rg Hin Hr. subst s.
             destruct (proj1 (WB (p, c) (INCL (p, c) (or_introl eq_refl)))) as (Yp0 & Yp1 & _). cbn [fst snd] in *.
             rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in Yp1.
             pose proof (proj2 (proj2 (proj2 (proj2 (WB (p, c) (INCL (p, c) (or_introl eq_refl))))))) as (_ & FA & _).
             destruct AO as (g & Hg & Yg1 & Yg2). pose proof (FA g ltac:(apply in_or_app; left; exact Hg)) as Zg. cbn [fst snd ff_addr ff_class] in *.
             unfold PMAIS.WF in Hin. destruct Hin as [<-|Hin]; [unfold L5.in_rng in Hr; cbn [fst snd] in Hr; lia|].
             destruct b; [destruct Hin|]. unfold PMSPA.loc_W in Hin. cbn [map pa_loc_foot PMA.AD ADDR_A fst snd] in Hin.
             destruct Hin as [<-|[<-|[]]]; unfold L5.in_rng in Hr; cbn [fst snd] in Hr; lia. }
  assert (ASTK5 : L5CA.astk ar M5 sp 20480).
  { apply (L5SAR.astk_after_eq L ar C HI HIok LB FF LK1 cr Aw1 M4 M4 M5 _ sp _ (sp - 192) 2560 HH4 ASTK4 (fun x X => X)).
    - intros a Ha Hs Hns. apply PRES5. exact Ha. apply L5SAR.stack_client. exact Hs. exact Hns. lia.
    - exact SDEF5.
    - lia. - lia. - lia. }
  split; [unfold PMAIS.SCR; exact ASTK5|].
  split. { unfold PMAIS.SCR. change (20480 / 8) with 2560. apply (PMKA.stksh_keepA L ar LB FF sp 20480 (PMAIS.WF ois b) M1 M5 EK15 WAPP); [lia| lia| lia| | lia| exact STKSH].
           apply PMAIS1.sub8; [exact A16| reflexivity]. }
  split. { apply (PMAIS1.base_ok_agree M1 M5); [|exact BASE]. intros a Ha. unfold PMAIS1.brg in Ha. apply AG15; [lia| | lia| lia| lia].
           unfold aclient, aclient_g. right; right; left. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [lia|].
           destruct Ha as [Ha|Ha]; [intros X; pose proof (L5A.aly_static_lo L C LYa a X); lia|].
           apply (fun D_ => PMA.ly_static L C LY a (PnStatics.PNST.dep_of_j _ _ a D_)). unfold PMST.dep, pm_initc. cbn [pa_canary pa_need_locks pa_locale_lock PMA.AD ADDR_A].
           destruct Ha as [Ha|[Ha|Ha]];
             [right; left; lia
             | right; right; exists (0x693f93, 0x693f94); split; [left; reflexivity| cbn [fst snd]; lia]
             | right; right; exists (0x694070, 0x694074); split; [right; left; reflexivity| cbn [fst snd]; lia]]. }
  split. { apply (PMAIS1.loc_ok_agree M1 M5 true); [|exact LOC]. intros a Ha. apply AG15; [lia| | lia| lia| lia].
           unfold aclient, aclient_g. right; right; left. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [lia|].
           apply (fun D_ => PMA.ly_static L C LY a (PnStatics.PNST.dep_of_j _ _ a D_)). unfold PMST.dep, pm_foot. left. cbn [pa_errcat_guard pa_syscat_guard pa_loc_foot pa_atexit PMA.AD ADDR_A app].
           destruct Ha as [X|X]; [exists (0x672532, 0x672c70); split; [right; right; left; reflexivity| cbn [fst snd]; lia]
                                  | exists (0x673398, 0x6733f0); split; [right; right; right; left; reflexivity| cbn [fst snd]; lia]]. }
  split; [exact HH5|]. split; [exact AM5|].
  split. { apply (L5LZ.model_rt_trans model0 model4 model5); [|exact MRT5]. apply (L5LZ.model_rt_trans model0 model3 model4); [|exact MRT4].
           apply (L5LZ.model_rt_trans model0 model1' model3); [|exact MRT3]. apply (L5LZ.model_rt_trans model0 model1 model1'); [exact MRT| exact MRT1]. }
  split; [exact INCK|]. split; [exact INCA|].
  split; [exact EK05|].
  apply (L5SAR.dk_trans L ar LB FF sp 20480 M0 M1 M5 DK).
  apply (L5SAR.dk_trans L ar LB FF sp 20480 M1 M3 M5 DK13).
  apply (L5SAR.dk_trans L ar LB FF sp 20480 M3 M4 M5 (L5SAR.dk_grows L ar LB FF sp 20480 M3 M4 MGM4) DK45).
Qed.
End Stage.
End PMAIS2.
