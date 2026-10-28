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
     PmModelFactsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnStepA_b PnStepA2_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmCertKitG. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import XIcptAs0_b PnAIssStmts_b PnAIssP_b PnAIss1_b Ba0_code_ra806c_a8070_b.
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
Module PMAIS3S.
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

Theorem short : forall (fx : FPState) R0 M0 model0 K LB FF LK0 Aw0 cr ois os sp r n b R2 M2 model2 LK2 Aw2,
    PMAIS.pre L ar HI R0 M0 model0 K LB FF LK0 Aw0 cr ois os sp r (PM.VShort n) b ->
    PMAIS.kont L ar HI R0 M0 model0 K LB FF LK0 Aw0 cr ois sp r (PM.VShort n) b ->
    PMAIS.mid2 L ar HI R0 M0 model0 LB FF LK0 Aw0 cr ois os sp (PM.VShort n) b R2 M2 model2 LK2 Aw2 ->
    srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx) R2 0xac2e4 M2 model2) K.
Proof.
  intros fx R0 M0 model0 K LB FF LK0 Aw0 cr ois os sp r n b R2 M2 model2 LK2 Aw2 PRE KONT MID.
  destruct PRE as (HH0 & AM0 & K0 & ENT & FRM & FRS & A10 & A11 & A12 & AO & AOS & EOS & O8 & OS8 & ODEF0 & ACC0 & VS0 & INCL & SZ & LNG & BASE0 & LOCb & CRED).
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK0 & STKSH0). pose proof RAok as (Hr1 & Hr2).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl4 in Rtp.
  assert (EOS' : os = ois - 64) by lia. subst os.
  destruct MID as (M2' & M8 & M9 & M18 & M19 & M20 & M21 & M22 & M23 & M24 & M25 & M26 & M27 & MCSK & V16 & Z32 & Z80 & MC).
  destruct MC as (SVI & SVB & HC & ODEF & ACC & VS & ASTK & STKSH & BASE & LOC & HH & AM & MRT & INCK & INCA & EK & DK).
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof AM as (Mh & MI). unfold PMAIS.SCR in *. change (20480 / 8) with 2560 in STKSH.
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK2 cr Aw2 M2 model2 HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
  set (H := ahid Aw2 model2) in *. set (MV := mrestrict H M2) in *.
  pose proof (PMKA.aobj_of_aobjA FF ois 272 AO O8) as AOB.
  pose proof (PMKA.aobj_of_aobjA FF (ois - 64) 24 AOS OS8) as AOSB.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK2 cr Aw2 M2 model2 ois 272 sp 20480 HH AOB ltac:(lia) ltac:(reflexivity))
    as (OR & OBIG & _ & OVIS & OVSH & OCL & OCLSH).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK2 cr Aw2 M2 model2 (ois - 64) 24 sp 20480 HH AOSB ltac:(lia) ltac:(reflexivity))
    as (OSR & OSBIG & OSDEF & OSVIS & _).
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as ST. rewrite (L5A.aly_segs L C LYa) in ST.
  pose proof (L5A.statics_facts L C M2 LYa ST) as (GOT & CSB & CUAR & _).
  assert (V0 : L5.img_clear MV 1249280 1282048) by (apply L5A.img_clear_mrestrict; exact GOT).
  assert (V1 : L5.u64_at RSEGS MV 1309752 2147450880) by (apply (proj2 (L5A.u64_at_vis H M2 1309752 2147450880 (VIMG 1309752 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB).
  assert (V2 : L5.u32_at RSEGS MV 1309760 1) by (apply (proj2 (L5A.u32_at_vis H M2 1309760 1 (VIMG 1309760 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR).
  assert (W4096 : L5.writable RSEGS MV (sp - 4096) 4096).
  { apply (proj2 (L5A.writable_vis H M2 (sp - 4096) 4096 (VIS (sp - 4096) 4096 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5SAR.astk_writable ar M2 sp 20480); [exact ASTK| lia| lia| lia]. }
  assert (OZv : L5KA.zeros_at MV (ois / 8 + 2147450880) 34).
  { exact (PMKA.obj_shadow_vis L ar C HI LYa HIok LB FF LK2 cr Aw2 M2 model2 ois 272 HH AO O8 ltac:(lia) ltac:(reflexivity) ACC). }
  assert (OWv : L5.writable RSEGS MV ois 272).
  { apply (proj2 (L5A.writable_vis H M2 ois 272 OVIS ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS). exact ODEF. lia. lia. }
  (* [comment removed for export] *)
  destruct VS as (VSD & VSA & Hn & VS0b).
  destruct (PMCG.u64_of_defined RSEGS M2 (ois - 64) ltac:(lia) ltac:(lia) ltac:(apply (L5.defined_sub M2 (ois - 64) 24); [exact VSD| lia| lia])) as (w0 & Hw0 & W0).
  destruct (PMCG.u64_of_defined RSEGS M2 (ois - 56) ltac:(lia) ltac:(lia) ltac:(apply (L5.defined_sub M2 (ois - 64) 24); [exact VSD| lia| lia])) as (w8 & Hw8 & W8).
  destruct (PMCG.u64_of_defined RSEGS M2 (ois - 48) ltac:(lia) ltac:(lia) ltac:(apply (L5.defined_sub M2 (ois - 64) 24); [exact VSD| lia| lia])) as (w16 & Hw16 & W16).
  assert (EW0 : w0 mod 256 = 2 * n) by (apply (PMCG.u8_of_u64_eq RSEGS M2 (ois - 64) w0 (2 * n) Hw0 ltac:(lia) W0 VS0b)).
  assert (VU64 : forall a v, ois - 64 <= a -> a + 8 <= ois - 40 -> L5.u64_at RSEGS M2 a v -> L5.u64_at RSEGS MV a v).
  { intros a v Ha Hb X. apply (proj2 (L5A.u64_at_vis H M2 a v ltac:(eapply L5A.avis_sub; [exact OSVIS| lia| lia]) ltac:(lia) ltac:(lia))). exact X. }
  assert (Y0b : L5.u8_at RSEGS MV (ois - 64) (2 * n)) by (apply (proj2 (L5A.u8_at_vis H M2 (ois - 64) (2 * n) ltac:(eapply L5A.avis_sub; [exact OSVIS| lia| lia]) ltac:(lia) ltac:(lia))); exact VS0b).
  assert (YW0 : L5.u64_at RSEGS MV (ois - 64) w0) by (apply VU64; [lia| lia| exact W0]).
  assert (YW8 : L5.u64_at RSEGS MV (ois - 56) w8) by (apply VU64; [lia| lia| exact W8]).
  assert (YW16 : L5.u64_at RSEGS MV (ois - 48) w16) by (apply VU64; [lia| lia| exact W16]).
  assert (Y80 : L5.u8_at RSEGS MV (ois + 80) 0).
  { apply (proj2 (L5A.u8_at_vis H M2 (ois + 80) 0 ltac:(eapply L5A.avis_sub; [exact OVIS| lia| lia]) ltac:(lia) ltac:(lia))).
    apply (PMCG.u8_of_zeros RSEGS M2 (ois + 80)); [apply (PMCG.zeros_sub M2 (ois + 80) 24); [exact Z80| lia| lia]| lia| lia]. }
  assert (TB : Z.testbit (2 * n) 0 = false) by (apply Z.testbit_even_0).
  LeanFeed.pfeed P (PMAISP.aicCs1_conc as0_icpt_fill as0_icpt_copy as0_icpt_tls fx R2 MV
                (fun j => match j with 2%nat => sp | 33%nat => ois | 35%nat => w0 | 36%nat => w8 | 37%nat => w16 | 38%nat => 2 * n | _ => 0 end)) ltac:(first [assumption | unfold PMAISP.aligned; lia | lia]).
  destruct P as (fx1 & R3 & M3v & MG3 & _ & FZ3 & MS3 & KS3 & sR1 & sR10 & sR11 & sR12 & sR13 & sR14 & C80 & C88 & C96 & C112).
  set (W3 := fun a => ois + 80 <= a < ois + 80 + 36).
  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK2 cr Aw2 M2 model2 fx fx1 R2 0xac2e4 R3 0xac320 M3v W3 K HH AM MS3 MG3).
  { intros a Ha N. apply FZ3; [exact Ha| exact N]. }
  { intros a Ha Wa. unfold W3 in Wa. split; [apply (L5SAR.obj_client L ar LB FF 0 0 ois 272 a AOB); lia| lia]. }
  intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3.
  assert (CS3 : forall k, In k L5SAR.cs_all -> getr R3 (reg k) = getr R2 (reg k)) by (intros k Hk; apply KS3; unfold L5SAR.cs_all in Hk; repeat (destruct Hk as [<-|Hk]; [inl|]); destruct Hk).
  assert (WAPP : PMKA.wapp (PMAIS.WF ois b)).
  { unfold PMAIS.WF. apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; lia|].
    destruct b; [apply PMKA.wapp_nil|]. unfold PMSPA.loc_W. cbn [map pa_loc_foot PMA.AD ADDR_A fst snd].
    apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO; lia|]. apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO; lia|]. apply PMKA.wapp_nil. }
  assert (FRB : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47).
  { intros f Hf. destruct (WF f Hf) as (X1 & X2 & _). unfold app_mem, FS_BYTES in *. lia. }
  assert (EK23 : L5SAR.ek L ar LB FF sp 20480 (PMAIS.WF ois b) M2 M3).
  { apply (L5SAR.ek_piece L ar LB FF sp 20480 (PMAIS.WF ois b) M2 M3 W3 FR3). intros a Ha Hc Ho X.
    apply (Ho (ois, 272)); [left; reflexivity| unfold L5.in_rng, W3 in *; cbn [fst snd]; lia]. }
  assert (ACC3 : PMSPA.accA M3 ois 272) by (apply (PMKA.acc_keepA' L ar LB FF sp 20480 _ M2 M3 EK23 WAPP FRB ois 272 AO ACC)).
  assert (ASTK3 : L5CA.astk ar M3 sp 20480) by (apply (L5SAR.astk_grows ar M2 M3 sp 20480 ASTK MGM3)).
  assert (ODEF3 : L5.defined M3 ois 272) by (apply (L5.defined_grows M2 M3 _ _ MGM3); exact ODEF).
  (* [comment removed for export] *)
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH3) as ST3. rewrite (L5A.aly_segs L C LYa) in ST3.
  pose proof (L5A.statics_facts L C M3 LYa ST3) as (GOT3 & CSB3 & CUAR3 & _).
  assert (XV : forall a n0, (ois <= a /\ a + n0 <= ois + 272) \/ (sp - 4096 <= a /\ a + n0 <= sp) \/ (0 <= a /\ a + n0 <= 0x696000) -> L5A.avis H a n0).
  { intros a n0 [X|[X|X]]; [eapply L5A.avis_sub; [exact OVIS| lia| lia]| apply VIS; lia| apply VIMG; lia]. }
  assert (Y0 : L5.img_clear M3v 1249280 1282048) by (rewrite <- VIS3; apply L5A.img_clear_mrestrict; exact GOT3).
  assert (Y1 : L5.u64_at RSEGS M3v 1309752 2147450880) by (rewrite <- VIS3; apply (proj2 (L5A.u64_at_vis H M3 1309752 2147450880 (XV 1309752 8 ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB3).
  assert (Y2 : L5.u32_at RSEGS M3v 1309760 1) by (rewrite <- VIS3; apply (proj2 (L5A.u32_at_vis H M3 1309760 1 (XV 1309760 4 ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR3).
  assert (Y3 : L5.writable RSEGS M3v (sp - 4096) 4096).
  { rewrite <- VIS3. apply (proj2 (L5A.writable_vis H M3 (sp - 4096) 4096 (XV (sp - 4096) 4096 ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5SAR.astk_writable ar M3 sp 20480); [exact ASTK3| lia| lia| lia]. }
  assert (YZ : L5KA.zeros_at M3v (ois / 8 + 2147450880) 34).
  { pose proof (PMKA.obj_shadow_vis L ar C HI LYa HIok LB FF LK2 cr Aw2 M3 model3 ois 272 HH3 AO O8 ltac:(lia) ltac:(reflexivity) ACC3) as X.
    rewrite HID3, VIS3 in X. exact X. }
  assert (YW : L5.writable RSEGS M3v ois 272).
  { rewrite <- VIS3. apply (proj2 (L5A.writable_vis H M3 ois 272 (XV ois 272 ltac:(lia)) ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS). exact ODEF3. lia. lia. }
  assert (T23 : forall a v, (sp - 192 <= a /\ a + 8 <= sp) \/ (ois <= a /\ a + 8 <= ois + 80) \/ (ois + 116 <= a /\ a + 8 <= ois + 272) ->
                 L5.u64_at RSEGS M2 a v -> L5.u64_at RSEGS M3v a v).
  { intros a v Ha X. rewrite <- VIS3. apply (proj2 (L5A.u64_at_vis H M3 a v (XV a 8 ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5C.u64_at_agree RSEGS M2 M3); [intros i Hi; apply FR3; [lia| unfold W3; lia]| lia| lia| exact X]. }
  destruct SVI as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80 & S88 & S96 & S104).
  destruct SVB as (T120 & T128 & T136 & T144 & T152 & T160 & T168 & T176 & T184).
  assert (Z8 : L5.u64_at RSEGS M3v (sp - 8) (bv_unsigned (getr R0 (reg 1)))) by (apply T23; [lia| exact S8]).
  assert (Z16 : L5.u64_at RSEGS M3v (sp - 16) (bv_unsigned (getr R0 (reg 8)))) by (apply T23; [lia| exact S16]).
  assert (Z24 : L5.u64_at RSEGS M3v (sp - 24) (bv_unsigned (getr R0 (reg 9)))) by (apply T23; [lia| exact S24]).
  assert (Z32' : L5.u64_at RSEGS M3v (sp - 32) (bv_unsigned (getr R0 (reg 18)))) by (apply T23; [lia| exact S32]).
  assert (Z40 : L5.u64_at RSEGS M3v (sp - 40) (bv_unsigned (getr R0 (reg 19)))) by (apply T23; [lia| exact S40]).
  assert (Z48 : L5.u64_at RSEGS M3v (sp - 48) (bv_unsigned (getr R0 (reg 20)))) by (apply T23; [lia| exact S48]).
  assert (Z56 : L5.u64_at RSEGS M3v (sp - 56) (bv_unsigned (getr R0 (reg 21)))) by (apply T23; [lia| exact S56]).
  assert (Z64 : L5.u64_at RSEGS M3v (sp - 64) (bv_unsigned (getr R0 (reg 22)))) by (apply T23; [lia| exact S64]).
  assert (Z72 : L5.u64_at RSEGS M3v (sp - 72) (bv_unsigned (getr R0 (reg 23)))) by (apply T23; [lia| exact S72]).
  assert (Z80' : L5.u64_at RSEGS M3v (sp - 80) (bv_unsigned (getr R0 (reg 24)))) by (apply T23; [lia| exact S80]).
  assert (Z88 : L5.u64_at RSEGS M3v (sp - 88) (bv_unsigned (getr R0 (reg 25)))) by (apply T23; [lia| exact S88]).
  assert (Z96 : L5.u64_at RSEGS M3v (sp - 96) (bv_unsigned (getr R0 (reg 26)))) by (apply T23; [lia| exact S96]).
  assert (Z104 : L5.u64_at RSEGS M3v (sp - 104) (bv_unsigned (getr R0 (reg 27)))) by (apply T23; [lia| exact S104]).
  assert (Z120 : L5.u64_at RSEGS M3v (sp - 120) 691528) by (apply T23; [lia| exact T120]).
  assert (Z128 : L5.u64_at RSEGS M3v (sp - 128) ois) by (apply T23; [lia| exact T128]).
  assert (Z136 : L5.u64_at RSEGS M3v (sp - 136) (ois + 120)) by (apply T23; [lia| exact T136]).
  assert (Z144 : L5.u64_at RSEGS M3v (sp - 144) 8) by (apply T23; [lia| exact T144]).
  assert (Z152 : L5.u64_at RSEGS M3v (sp - 152) (ois - 64)) by (apply T23; [lia| exact T152]).
  assert (Z160 : L5.u64_at RSEGS M3v (sp - 160) 1266032) by (apply T23; [lia| exact T160]).
  assert (Z168 : L5.u64_at RSEGS M3v (sp - 168) (ois + 16)) by (apply T23; [lia| exact T168]).
  assert (Z176 : L5.u64_at RSEGS M3v (sp - 176) (ois + 120)) by (apply T23; [lia| exact T176]).
  assert (Z184 : L5.u64_at RSEGS M3v (sp - 184) ((ois / 8) + 2147450880)) by (apply T23; [lia| exact T184]).
  assert (U80 : L5.u8_at RSEGS M3v (ois + 80) (2 * n)) by (rewrite <- EW0; apply (PMF.u8_of_u64 RSEGS M3v (ois + 80) w0 Hw0 C80)).
  assert (R3sp : getr R3 (reg 2) = Z_to_bv 64 (sp - 192)) by (rewrite CS3 by inl; exact M2').
  assert (R3s0 : getr R3 (reg 8) = Z_to_bv 64 (ois + 16)) by (rewrite CS3 by inl; exact M8).
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 1))) as UR1. pose proof (bv_unsigned_in_range 64 (getr R0 (reg 8))) as UR8.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 9))) as UR9. pose proof (bv_unsigned_in_range 64 (getr R0 (reg 18))) as UR18.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 19))) as UR19. pose proof (bv_unsigned_in_range 64 (getr R0 (reg 20))) as UR20.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 21))) as UR21. pose proof (bv_unsigned_in_range 64 (getr R0 (reg 22))) as UR22.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 23))) as UR23. pose proof (bv_unsigned_in_range 64 (getr R0 (reg 24))) as UR24.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 25))) as UR25. pose proof (bv_unsigned_in_range 64 (getr R0 (reg 26))) as UR26.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 27))) as UR27. change (bv_modulus 64) with (2 ^ 64) in *.
  LeanFeed.pfeed P (PMAISP.aicCs2_conc as0_icpt_fill as0_icpt_copy as0_icpt_tls fx1 R3 M3v
                (fun j => match j with 2%nat => sp | 33%nat => ois | 38%nat => 2 * n
                          | 43%nat => bv_unsigned (getr R0 (reg 1)) | 44%nat => bv_unsigned (getr R0 (reg 8)) | 45%nat => bv_unsigned (getr R0 (reg 9))
                          | 46%nat => bv_unsigned (getr R0 (reg 18)) | 47%nat => bv_unsigned (getr R0 (reg 19)) | 48%nat => bv_unsigned (getr R0 (reg 20))
                          | 49%nat => bv_unsigned (getr R0 (reg 21)) | 50%nat => bv_unsigned (getr R0 (reg 22)) | 51%nat => bv_unsigned (getr R0 (reg 23))
                          | 52%nat => bv_unsigned (getr R0 (reg 24)) | 53%nat => bv_unsigned (getr R0 (reg 25)) | 54%nat => bv_unsigned (getr R0 (reg 26))
                          | 55%nat => bv_unsigned (getr R0 (reg 27)) | _ => 0 end)) ltac:(first [assumption | unfold PMAISP.aligned; lia | lia]).
  destruct P as (fx4 & R4 & M4v & MG4 & _ & FZ4 & MS4 & KS4 & tR1 & tR2 & tR8 & tR9 & tR10 & tR11 & tR12 & tR13 & tR14 & tR15 & tR16
                 & tR18 & tR19 & tR20 & tR21 & tR22 & tR23 & tR24 & tR25 & tR26 & tR27 & G48 & G40 & G32 & G104).
  assert (R4ra : getr R4 (reg 1) = Z_to_bv 64 r) by (rewrite tR1, Z_to_bv_bv_unsigned; exact Rra).
  pose proof (PMK.ret_to RSEGS fx4 R4 M4v 0xa8d80 W_a8964 r F_a8964 eq_refl D_a8964 R4ra ltac:(lia) Hr2) as MS5.
  set (W5 := fun a => (sp - 272 <= a < sp - 272 + 80) \/ (ois + 32 <= a < ois + 32 + 24) \/ (ois + 104 <= a < ois + 104 + 8)).
  apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK2 cr Aw2 M3 model3 fx1 fx4 R3 0xac320 R4 r M4v W5 K HH3 AM3).
  { rewrite HID3, VIS3. eapply msteps_trans; [exact MS4| exact MS5]. }
  { rewrite HID3, VIS3. exact MG4. }
  { rewrite HID3, VIS3. intros a Ha N. apply FZ4; [exact Ha| | |]; intros X; apply N; unfold W5; tauto. }
  { intros a Ha [Wa|[Wa|Wa]].
    - split; [|lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia].
    - split; [apply (L5SAR.obj_client L ar LB FF 0 0 ois 272 a AOB); lia| lia].
    - split; [apply (L5SAR.obj_client L ar LB FF 0 0 ois 272 a AOB); lia| lia]. }
  intros M5 model5 HH5 AM5 MRT5 HID5 VIS5 MGM5 FR5 VV5.
  assert (EK35 : L5SAR.ek L ar LB FF sp 20480 (PMAIS.WF ois b) M3 M5).
  { apply (L5SAR.ek_piece L ar LB FF sp 20480 (PMAIS.WF ois b) M3 M5 W5 FR5). intros a Ha Hc Ho [X|X].
    - destruct (L5SAR.aclient_cases L ar C HI LYa HIok LB FF LK2 cr Aw2 M2 _ sp 20480 a HH SPT Hc) as [Z1|Z1]; lia.
    - apply (Ho (ois, 272)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]. }
  assert (EK25 : L5SAR.ek L ar LB FF sp 20480 (PMAIS.WF ois b) M2 M5) by (apply (L5SAR.ek_trans L ar LB FF sp 20480 _ M2 M3 M5 EK23 EK35)).
  assert (EK05 : L5SAR.ek L ar LB FF sp 20480 (PMAIS.WF ois b) M0 M5) by (apply (L5SAR.ek_trans L ar LB FF sp 20480 _ M0 M2 M5 EK EK25)).
  assert (ACC5 : PMSPA.accA M5 ois 272) by (apply (PMKA.acc_keepA' L ar LB FF sp 20480 _ M2 M5 EK25 WAPP FRB ois 272 AO ACC)).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK2 cr Aw2 M5 model5 ois 272 sp 20480 HH5 AOB ltac:(lia) ltac:(reflexivity)) as (_ & _ & ODEF5 & _).
  (* [comment removed for export] *)
  assert (A25 : forall a, ois <= a < ois + 272 -> ~ (ois + 80 <= a < ois + 116) -> ~ (ois + 32 <= a < ois + 56) -> ~ (ois + 104 <= a < ois + 112) ->
                M5 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)).
  { intros a Ha N1 N2 N3. rewrite FR5 by (unfold W5; lia). apply FR3; [lia| unfold W3; lia]. }
  assert (A35 : forall a, ois <= a < ois + 272 -> ~ (ois + 32 <= a < ois + 56) -> ~ (ois + 104 <= a < ois + 112) -> M5 (Z_to_bv 64 a) = M3v (Z_to_bv 64 a)).
  { intros a Ha N2 N3. rewrite FR5 by (unfold W5; lia). rewrite <- VIS3. unfold MV in *. symmetry. apply (AsanAcct.mrestrict_visible H M3).
    pose proof (XV a 1 ltac:(lia) 0 ltac:(lia)) as X. rewrite Z.add_0_r in X. exact X. }
  assert (A45 : forall a, (ois <= a < ois + 272) -> M5 (Z_to_bv 64 a) = M4v (Z_to_bv 64 a)).
  { intros a Ha. rewrite <- VIS5. rewrite HID3. symmetry. apply (AsanAcct.mrestrict_visible H M5).
    pose proof (XV a 1 ltac:(lia) 0 ltac:(lia)) as X. rewrite Z.add_0_r in X. exact X. }
  Ltac a64 AG X Ms := apply (L5C.u64_at_agree RSEGS Ms); [intros i Hi; apply AG; (lia || fail 1 "AG")| (lia || fail 1 "B1")| (lia || fail 1 "B2")| exact X].
  Ltac a32 AG X Ms := apply (PMF.u32_at_agree RSEGS Ms); [intros i Hi; apply AG; (lia || fail 1 "AG")| (lia || fail 1 "B1")| (lia || fail 1 "B2")| exact X].
  destruct HC as (H0 & H24 & H120 & H152 & H156 & H160 & H168 & H176).
  assert (E2n : 2 * n / 2 = n) by (rewrite Z.mul_comm; apply Z.div_mul; lia).
  rewrite E2n in G48, G104.
  unfold PMSPA.cfg in KONT.
  apply (KONT fx4 R4 M5 model5 LK2 Aw2 (PM.VShort n) (PM.STRM (ois + 81) (ois + 81 + n) 0) cr).
  - apply L5SAR.preserved_by_index. intros k Hk. unfold L5SAR.cs_all in Hk.
    assert (CH : forall k, In k PMAISP.KS_aicCs2 -> In k L5SAR.cs_all -> In k PMAIS.CSK -> getr R4 (reg k) = getr R0 (reg k)).
    { intros k' H1 H2 H3. rewrite (KS4 k' H1), (CS3 k' H2). apply MCSK. exact H3. }
    destruct Hk as [<-|Hk]; [rewrite tR2, Rsp; reflexivity|].
    destruct Hk as [<-|Hk]; [apply CH; [inl| inl| left; reflexivity]|].
    destruct Hk as [<-|Hk]; [apply CH; [inl| inl| right; left; reflexivity]|].
    destruct Hk as [<-|Hk]; [rewrite tR8; apply Z_to_bv_bv_unsigned|].
    destruct Hk as [<-|Hk]; [rewrite tR9; apply Z_to_bv_bv_unsigned|].
    destruct Hk as [<-|Hk]; [rewrite tR18; apply Z_to_bv_bv_unsigned|].
    destruct Hk as [<-|Hk]; [rewrite tR19; apply Z_to_bv_bv_unsigned|].
    destruct Hk as [<-|Hk]; [rewrite tR20; apply Z_to_bv_bv_unsigned|].
    destruct Hk as [<-|Hk]; [rewrite tR21; apply Z_to_bv_bv_unsigned|].
    destruct Hk as [<-|Hk]; [rewrite tR22; apply Z_to_bv_bv_unsigned|].
    destruct Hk as [<-|Hk]; [rewrite tR23; apply Z_to_bv_bv_unsigned|].
    destruct Hk as [<-|Hk]; [rewrite tR24; apply Z_to_bv_bv_unsigned|].
    destruct Hk as [<-|Hk]; [rewrite tR25; apply Z_to_bv_bv_unsigned|].
    destruct Hk as [<-|Hk]; [rewrite tR26; apply Z_to_bv_bv_unsigned|].
    destruct Hk as [<-|Hk]; [rewrite tR27; apply Z_to_bv_bv_unsigned|].
    destruct Hk.
  - unfold PMAIS.iss_at, PM.iss_at. cbn [PM.vs_data PM.vs_size PM.sm_g PM.sm_eg PM.sm_st pa_vp_iss pa_vp_strbuf pa_classic_imp pa_vp_iss_ios PMA.AD ADDR_A] in *.
    split; [a64 A25 H0 M2|].
    split; [apply (L5.defined_sub M5 ois 272); [exact ODEF5| lia| lia]|].
    split; [intros x Hx; apply ACC5; lia|].
    split; [a64 A25 V16 M2|].
    split; [a64 A25 H24 M2|].
    split; [replace (ois + 80 + 1) with (ois + 81) by lia; a64 A45 G32 M4v|].
    split; [a64 A45 G40 M4v|].
    split; [replace (ois + 81 + n) with (ois + n + 81) by lia; a64 A45 G48 M4v|].
    split; [apply (L5C.u64_at_agree RSEGS M2); [intros i Hi; apply A25; lia| lia| lia|];
            apply (PMCG.u64_of_zeros RSEGS M2 (ois + 64)); [apply (PMCG.zeros_sub M2 (ois + 32) 48); [exact Z32| lia| lia]| lia| lia]|].
    split. { unfold PM.vstr_at. split; [apply (L5.defined_sub M5 ois 272); [exact ODEF5| lia| lia]|].
             split; [intros x Hx; apply ACC5; lia|]. split; [lia|].
             apply (L5C.u8_at_agree RSEGS M3v); [intros i Hi; apply A35; lia| lia| lia| exact U80]. }
    split; [replace (ois + 81 + n) with (ois + n + 81) by lia; a64 A45 G104 M4v|].
    split; [a32 A35 C112 M3v|].
    split. { unfold PM.iosb_at. cbn [pa_classic_imp PMA.AD ADDR_A].
             replace (ois + 120 + 32) with (ois + 152) by lia. replace (ois + 120 + 36) with (ois + 156) by lia.
             replace (ois + 120 + 40) with (ois + 160) by lia. replace (ois + 120 + 48) with (ois + 168) by lia. replace (ois + 120 + 56) with (ois + 176) by lia.
             split; [a64 A25 H120 M2|]. split; [a32 A25 H152 M2|]. split; [a32 A25 H156 M2|]. split; [a64 A25 H160 M2|].
             split; [a64 A25 H168 M2|].
             split; [apply (PMF.zeros_at_agree M2); [intros i Hi; apply A25; lia| exact H176]|].
             split; [apply (L5.defined_sub M5 ois 272); [exact ODEF5| lia| lia]|].
             split; [intros x Hx; apply ACC5; lia| left; reflexivity]. }
    split; lia.
  - reflexivity.
  - cbn [PM.vs_data PM.sm_g]. lia.
  - reflexivity.
  - apply (PMAIS1.loc_ok_agree M2 M5 true); [|exact LOC]. intros a Ha.
    rewrite FR5 by (unfold W5; lia). apply FR3; [lia| unfold W3; lia].
  - change (PMSPA.pm_scr 4) with 20480. apply (L5SAR.ahpres_of L ar LB FF sp 20480 _ M0 M5 EK05).
    + pose proof (L5SAR.astk_grows ar M3 M5 sp 20480 ASTK3 MGM5) as (_ & _ & _ & _ & SD5 & _). exact SD5.
    + apply (L5SAR.dk_trans L ar LB FF sp 20480 M0 M2 M5 DK).
      apply (L5SAR.dk_trans L ar LB FF sp 20480 M2 M3 M5 (L5SAR.dk_grows L ar LB FF sp 20480 M2 M3 MGM3) (L5SAR.dk_grows L ar LB FF sp 20480 M3 M5 MGM5)).
  - destruct (PMA.ly_cost L C LY) as (K1 & K2 & K3).
    unfold PMSPA.credit_keep, PMAIS.cost, PMSPA.scA, PM.cost1, PMSPA.HV, LibIfaceAB.heap_view, PMSPA.cr0. cbn [fst snd HeapIface.hl_k_per_malloc HeapIface.hl_b_overhead PM.vs_size].
    rewrite K1, K2, K3. lia.
  - apply (L5LZ.model_rt_trans model0 model3 model5); [|exact MRT5]. apply (L5LZ.model_rt_trans model0 model2 model3); [exact MRT| exact MRT3].
  - exact INCK.
  - exact INCA.
  - exact AM5.
  - exact HH5.
Qed.

End Stage.
End PMAIS3S.
