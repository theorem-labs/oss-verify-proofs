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
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PnSpecsAa_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgV8 PnModel PnModelFacts. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnSpecsAX_b
     PmModelFactsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnStepA_b PnStepA2_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmCertKitG. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnAIss1_b PnAEmbKit_b PnAAnnV8P_b Ba0_code_ab0c0_ab0c4_b Ba0_code_ab164_ab168_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreB_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnSpecsAXC_b.
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
Module PNAAV8.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).

Section Stage.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis EXT : HAJ.asan_ext_ok L ar SCFG HI PMA.EXT.
Let LYa := PMA.ly_as0 L C LY.

(* [comment removed for export] *)


(* [comment removed for export] *)
Lemma ann_delete_v8_null : forall (fx : FPState) R M model K LBX FF LK Aw cr v sp r,
    ri_inv HI (PGV8.v8_own PGV8.V8Null ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA PMA.AD L ar R M sp r 0 -> PMSPA.ffrsA FF sp ->
    getr R 10%bv = Z_to_bv 64 v -> PMSPA.aobjA FF v 24 -> v mod 8 = 0 -> PMSPA.accA M v 24 ->
    PGV8.v8_at RSEGS PMSPA.accA PMSPA.annA M v PGV8.V8Null ->
    (forall (fx' : FPState) R' M' model' LK' Aw',
        regs_preserved R R' ->
        PNSAX.v8_hdr RSEGS M' v PGV8.V8Null -> PMSPA.accA M' v 24 ->
        (forall b n c, PGV8.V8Null = PGV8.V8Blk b n c -> PMSPA.accA M' b c) ->
        (forall b n c a, PGV8.V8Null = PGV8.V8Blk b n c -> b <= a < b + c -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
        L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr 0) [] M M' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv HI (PGV8.v8_own PGV8.V8Null ++ LBX) FF LK' cr Aw' M' (vml_of model') ->
        srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx' R' r M' model') K) ->
    srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xabb8c M model) K.
Proof.
  intros fx R M model K LBX FF LK Aw cr v sp r HH AM K0 ENT FRS A10 AOV V8 ACCV VEC KONT.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). pose proof RAok as (Hr1 & Hr2).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10.
  change (PMSPA.pm_scr 0) with 12288 in *. change (12288 / 8) with 1536 in STKSH.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof AM as (Mh & MI).
  destruct VEC as (VDEF & VACC & VB & VE & VC). cbn [PGV8.v8_own app] in HH, KONT. set (LB := LBX) in *.
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _ & _ & CB1 & CB2 & STOP & _).
  pose proof (PMKA.aobj_of_aobjA FF v 24 AOV V8) as AOB.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK cr Aw M model v 24 sp 12288 HH AOB ltac:(lia) ltac:(reflexivity)) as (OR & OBIG & ODEF & OVIS & OVSH & OCL & OCLSH).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw M model HH) as (HOFF & VIS & VIMG & VFS & VBLK' & VBSH & VFSSH & VSTSH).
  set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as ST. rewrite (L5A.aly_segs L C LYa) in ST.
  pose proof (L5A.statics_facts L C M LYa ST) as (GOT & CSB & CUAR & _).
  assert (X0 : L5.img_clear MV 1249280 1282048) by (apply L5A.img_clear_mrestrict; exact GOT).
  assert (X1 : L5.u64_at RSEGS MV 1309752 2147450880) by (apply (proj2 (L5A.u64_at_vis H M 1309752 2147450880 (VIMG 1309752 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB).
  assert (X2 : L5.u32_at RSEGS MV 1309760 1) by (apply (proj2 (L5A.u32_at_vis H M 1309760 1 (VIMG 1309760 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR).
  assert (X3 : L5.writable RSEGS MV (sp - 4096) 4096).
  { apply (proj2 (L5A.writable_vis H M (sp - 4096) 4096 (VIS (sp - 4096) 4096 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5SAR.astk_writable ar M sp 12288); [exact ASTK| lia| lia| lia]. }
  assert (X5 : L5KA.zeros_at MV (v / 8 + 2147450880) 3).
  { exact (PMKA.obj_shadow_vis L ar C HI LYa HIok LB FF LK cr Aw M model v 24 HH AOV V8 ltac:(lia) ltac:(reflexivity) ACCV). }
  assert (X6 : L5.u64_at RSEGS MV v 0) by (apply (proj2 (L5A.u64_at_vis H M v 0 ltac:(eapply L5A.avis_sub; [exact OVIS| lia| lia]) ltac:(lia) ltac:(lia))); exact VB).
  assert (X7 : L5.u64_at RSEGS MV (v + 8) 0) by (apply (proj2 (L5A.u64_at_vis H M (v + 8) _ ltac:(eapply L5A.avis_sub; [exact OVIS| lia| lia]) ltac:(lia) ltac:(lia))); exact VE).
  assert (X8 : L5.u64_at RSEGS MV (v + 16) 0) by (apply (proj2 (L5A.u64_at_vis H M (v + 16) _ ltac:(eapply L5A.avis_sub; [exact OVIS| lia| lia]) ltac:(lia) ltac:(lia))); exact VC).
  LeanFeed.pfeed P (PNAAV8P.azudN_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => v | _ => 0 end)) ltac:(first [assumption | unfold PNAAV8P.aligned; lia | lia]).
  destruct P as (fx1 & R1 & M1v & MG1 & _ & FZ1 & MS1 & KS1 & _).
  assert (R1ra : getr R1 (reg 1) = Z_to_bv 64 r) by (rewrite (KS1 1%nat) by inl; exact Rra).
  pose proof (PMK.ret_to RSEGS fx1 R1 M1v 0xabc1c W_ab0c0 r F_ab0c0 eq_refl D_ab0c0 R1ra ltac:(lia) Hr2) as MS2.
  set (W1 := fun a => sp - 24 <= a < sp - 24 + 24).
  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr Aw M model fx fx1 R 0xabb8c R1 r M1v W1 K HH AM ltac:(eapply msteps_trans; [exact MS1| exact MS2]) MG1).
  { intros a Ha N. apply FZ1; [exact Ha| exact N]. }
  { intros a Ha Wa. unfold W1 in Wa. split; [|lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia]. }
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
  assert (TV : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 24 <= a < sp) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) by (intros a Ha N; apply FR1; [exact Ha| unfold W1; lia]).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK cr Aw M1 model1 v 24 sp 12288 HH1 AOB ltac:(lia) ltac:(reflexivity)) as (_ & _ & ODEF1 & _).
  apply (KONT fx1 R1 M1 model1 LK Aw).
  - apply L5SAR.preserved_by_index. intros k0 Hk. apply KS1. revert Hk. unfold L5SAR.cs_all.
    intros Hk. destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]]; inl.
  - split. { intros i Hi. rewrite TV by lia. exact (VDEF i Hi). }
    cbn. split. { apply (L5C.u64_at_agree RSEGS M M1); [intros i Hi; apply TV; lia| lia| lia| exact VB]. }
    split. { apply (L5C.u64_at_agree RSEGS M M1); [intros i Hi; apply TV; lia| lia| lia| exact VE]. }
    apply (L5C.u64_at_agree RSEGS M M1); [intros i Hi; apply TV; lia| lia| lia| exact VC].
  - apply (PMFA.accA_agree M M1 v 24); [| exact ACCV]. intros x Hx. pose proof (PNAEK.S_range x ltac:(lia)) as SRx. apply TV; lia.
  - intros b n c E. discriminate E.
  - intros b n c a E. discriminate E.
  - apply (L5SAR.ahpres_of L ar LBX FF sp 12288 _ M M1).
    + intros a (Ha & Hc & Ho). apply FR1; [exact Ha|]. unfold W1.
      destruct (L5SAR.aclient_cases L ar C HI LYa HIok LB FF LK cr Aw M _ sp 12288 a HH SPT Hc) as [Z1|Z1]; lia.
    + apply (L5.defined_grows M M1 _ _ MGM1). exact SDEF.
    + intros a Ha Hc HM. apply MGM1. exact HM.
  - exact MRT1.
  - intros f Hf. exact Hf.
  - intros q Hq. exact Hq.
  - exact AM1.
  - exact HH1.
Qed.

Theorem ann_delete_v8_ok : PNSAX.ann_delete_v8_spec RSEGS PMA.AD L ar HI 0xabb8c.
Proof.
  unfold PNSAX.ann_delete_v8_spec.
  intros fx R M model K LBX FF LK Aw cr v x sp r HH AM K0 ENT FRS A10 AOV V8 ACCV VEC KONT.
  destruct x as [|b n c].
  { (* [comment removed for export] *)
    apply (ann_delete_v8_null fx R M model K LBX FF LK Aw cr v sp r HH AM K0 ENT FRS A10 AOV V8 ACCV VEC KONT). }
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). pose proof RAok as (Hr1 & Hr2).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10.
  change (PMSPA.pm_scr 0) with 12288 in *. change (12288 / 8) with 1536 in STKSH.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof AM as (Mh & MI).
  destruct VEC as (VDEF & VACC & VB & VE & VC & NC & C27 & B4096 & B16 & BDEF & BACC & BANN).
  cbn [PGV8.v8_own] in HH, KONT. set (LB := [(b, c)] ++ LBX) in *.
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _ & _ & CB1 & CB2 & STOP & _).
  assert (BIN : In (b, c) LB) by (left; reflexivity).
  destruct (PNAEK.blk_facts L ar C HI LY HIok _ FF LK cr Aw M _ b (c) HH BIN) as (Bq0 & Bq1 & Bq2 & Bq3 & _ & Bq5 & Bq6 & _ & Bq8).
  pose proof (PMKA.aobj_of_aobjA FF v 24 AOV V8) as AOB.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK cr Aw M model v 24 sp 12288 HH AOB ltac:(lia) ltac:(reflexivity)) as (OR & OBIG & ODEF & OVIS & OVSH & OCL & OCLSH).
  assert (VBLK : v + 24 <= b \/ b + c <= v).
  { destruct AOV as (f & Hf & Y1 & Y2). destruct (Bq8 f Hf) as [Y|Y]; [right; lia| left; lia]. }
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw M model HH) as (HOFF & VIS & VIMG & VFS & VBLK' & VBSH & VFSSH & VSTSH).
  set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as ST. rewrite (L5A.aly_segs L C LYa) in ST.
  pose proof (L5A.statics_facts L C M LYa ST) as (GOT & CSB & CUAR & _).
  assert (X0 : L5.img_clear MV 1249280 1282048) by (apply L5A.img_clear_mrestrict; exact GOT).
  assert (X1 : L5.u64_at RSEGS MV 1309752 2147450880) by (apply (proj2 (L5A.u64_at_vis H M 1309752 2147450880 (VIMG 1309752 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB).
  assert (X2 : L5.u32_at RSEGS MV 1309760 1) by (apply (proj2 (L5A.u32_at_vis H M 1309760 1 (VIMG 1309760 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR).
  assert (X3 : L5.writable RSEGS MV (sp - 4096) 4096).
  { apply (proj2 (L5A.writable_vis H M (sp - 4096) 4096 (VIS (sp - 4096) 4096 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5SAR.astk_writable ar M sp 12288); [exact ASTK| lia| lia| lia]. }
  assert (X5 : L5KA.zeros_at MV (v / 8 + 2147450880) 3).
  { exact (PMKA.obj_shadow_vis L ar C HI LYa HIok LB FF LK cr Aw M model v 24 HH AOV V8 ltac:(lia) ltac:(reflexivity) ACCV). }
  assert (X6 : L5.u64_at RSEGS MV v b) by (apply (proj2 (L5A.u64_at_vis H M v b ltac:(eapply L5A.avis_sub; [exact OVIS| lia| lia]) ltac:(lia) ltac:(lia))); exact VB).
  assert (X7 : L5.u64_at RSEGS MV (v + 8) (b + n)) by (apply (proj2 (L5A.u64_at_vis H M (v + 8) _ ltac:(eapply L5A.avis_sub; [exact OVIS| lia| lia]) ltac:(lia) ltac:(lia))); exact VE).
  assert (X8 : L5.u64_at RSEGS MV (v + 16) (b + c)) by (apply (proj2 (L5A.u64_at_vis H M (v + 16) _ ltac:(eapply L5A.avis_sub; [exact OVIS| lia| lia]) ltac:(lia) ltac:(lia))); exact VC).
  LeanFeed.pfeed P (PNAAV8P.azudA_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => v | 36%nat => b | 37%nat => n | 41%nat => b + c | _ => 0 end)) ltac:(first [assumption | unfold PNAAV8P.aligned; lia | lia]).
  destruct P as (fx1 & R1 & M1v & MG1 & _ & FZ1 & MS1 & KS1 & fR1 & fR2 & fR10 & fR11 & fR12 & fR13 & fR14 & fR15 & fR16 & T16 & T8).
  set (W1 := fun a => sp - 24 <= a < sp - 24 + 24).
  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr Aw M model fx fx1 R 0xabb8c R1 0x7ba7c M1v W1 K HH AM MS1 MG1).
  { intros a Ha N. apply FZ1; [exact Ha| exact N]. }
  { intros a Ha Wa. unfold W1 in Wa. split; [|lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia]. }
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
  pose proof AM1 as (Mh1 & MI1).
  assert (SH01 : forall x, 0 <= x < 2 ^ 64 -> x < sp - 24 -> M1 (Z_to_bv 64 x) = M (Z_to_bv 64 x)) by (intros x Hx Hx'; apply FR1; [exact Hx| unfold W1; lia]).
  (* [comment removed for export] *)
  pose proof (HAJ.aex_annotate _ _ _ _ _ EXT) as ANN. unfold HAJ.annotate_spec in ANN.
  cbn [PMA.EXT HAJ.ec_ann_pc HAJ.ec_ann_scr paa_annotate PMA.AAD AADDR_A] in ANN. rewrite (L5A.aly_segs L C LYa) in ANN.
  apply (ANN fx1 R1 M1 model1 LB FF LK cr Aw K b (c) (n) (c)); clear ANN.
  { exact HH1. }
  { exact Mh1. }
  { exact MI1. }
  { rewrite L5K.rl10. exact fR10. }
  { rewrite L5K.rl11. exact fR11. }
  { rewrite L5K.rl12. exact fR12. }
  { rewrite L5K.rl13. exact fR13. }
  { exact BIN. }
  { exact B16. }
  { lia. }
  { lia. }
  { apply (PNAEK.ann_agree M M1 b (n) (c)); [| lia| lia| exact BANN].
    intros j Hj. pose proof (PNAEK.shadow_lowU b c j ltac:(lia) ltac:(lia) Hj) as SL. apply SH01; lia. }
  { rewrite L5K.rl4, (KS1 4%nat) by inl. exact Rtp. }
  { rewrite L5K.rl1, fR1. vm_compute. reflexivity. }
  { rewrite L5K.rl2, fR2, L5.unsigned_lit by lia.
    apply (L5SAR.astack_ok_of_astk L ar C LYa M M1 sp 12288 16 2304 ASTK MGM1); [lia| lia| lia|].
    replace (sp - 16) with (sp + (-1) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
  { exact K0. }
  intros fx2 R2 M2 model2 Aw2 RP2 ANN2 KEEP2 DSH2 SCR2 MRT2 INC2 MI2 HH2.
  rewrite L5K.rl2, fR2, L5.unsigned_lit in KEEP2, SCR2 by lia. rewrite L5K.rl1, fR1.
  assert (AM2 : L5CA.amodel_ok Aw2 model2) by (split; [rewrite (L5LZ.model_rt_halted model1 model2 MRT2); exact Mh1| exact MI2]).
  assert (CS2 : forall k0, In k0 L5SAR.cs_all -> getr R2 (reg k0) = getr R1 (reg k0)) by (intros k0 Hk; apply (L5SAR.cs_of_preserved R1 R2 k0 RP2 Hk)).
  assert (T20 : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF 0 0 a -> ~ (sp - 2320 <= a < sp) -> ~ in_shadow_of b (c) a -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha Hc N1 N2. rewrite (KEEP2 a Ha ltac:(apply (L5SAR.aclient_narrow L ar LB FF 0 0); [exact Hc| lia]) N2). apply FR1; [exact Ha| unfold W1; lia]. }
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw2 M2 model2 HH2) as (HOFF2 & VIS2 & VIMG2 & VFS2 & VBLK2 & VBSH2 & VFSSH2 & VSTSH2).
  set (H2 := ahid Aw2 model2) in *. set (MV2 := mrestrict H2 M2) in *.
  assert (ASTK2 : L5CA.astk ar M2 sp 12288).
  { apply (L5SAR.astk_after_eq L ar C HI HIok LB FF LK cr Aw M M1 M2 _ sp 12288 (sp - 16) 2304 HH ASTK MGM1).
    - intros a Ha Hs Hns. apply KEEP2; [exact Ha| apply L5SAR.stack_client; [exact Hs| exact Hns]|].
      intros X. pose proof (PNAEK.in_shadow_range b (c) a ltac:(lia) ltac:(lia) X). lia.
    - exact SCR2.
    - lia. - lia. - lia. }
  assert (Y3 : L5.writable RSEGS MV2 (sp - 4096) 4096).
  { apply (proj2 (L5A.writable_vis H2 M2 (sp - 4096) 4096 (VIS2 (sp - 4096) 4096 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5SAR.astk_writable ar M2 sp 12288); [exact ASTK2| lia| lia| lia]. }
  (* [comment removed for export] *)
  assert (TS : forall a v0, sp - 16 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1v a v0 -> L5.u64_at RSEGS MV2 a v0).
  { intros a v0 Ha Ha' X. apply (proj2 (L5A.u64_at_vis H2 M2 a v0 (VIS2 a 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply KEEP2; [lia| apply L5SAR.stack_client; lia|]| lia| lia|].
    - intros XS. pose proof (PNAEK.in_shadow_range b (c) i ltac:(lia) ltac:(lia) XS). lia.
    - apply (PMAIS1.vis_u64 _ _ _ _ _ VIS1); [apply VIS; lia| lia| lia| exact X]. }
  pose proof (TS (sp - 8) _ ltac:(lia) ltac:(lia) T8) as Z8.
  pose proof (TS (sp - 16) _ ltac:(lia) ltac:(lia) T16) as Z16.
  assert (J2 : getr R2 (reg 2) = Z_to_bv 64 (sp - 16)) by (rewrite CS2 by inl; exact fR2).
  pose proof (PMAIS1.bvu (getr R (reg 1))) as UR1. pose proof (PMAIS1.bvu (getr R (reg 8))) as UR8.
  LeanFeed.pfeed P (PNAAV8P.azudB_conc fx2 R2 MV2 (fun j => match j with 2%nat => sp | 43%nat => bv_unsigned (getr R (reg 1)) | 44%nat => bv_unsigned (getr R (reg 8)) | _ => 0 end)) ltac:(first [assumption | unfold PNAAV8P.aligned; lia | lia]).
  destruct P as (fx3 & R3 & M3v & MG3 & _ & FZ3 & MS3 & KS3 & gR1 & gR2 & gR8).
  assert (R3ra : getr R3 (reg 1) = Z_to_bv 64 r) by (rewrite gR1, Z_to_bv_bv_unsigned; exact Rra).
  pose proof (PMK.ret_to RSEGS fx3 R3 M3v 0xabc1c W_ab0c0 r F_ab0c0 eq_refl D_ab0c0 R3ra ltac:(lia) Hr2) as MS4.
  set (W3 := fun a : Z => False).
  apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr Aw2 M2 model2 fx2 fx3 R2 0xabc10 R3 r M3v W3 K HH2 AM2 ltac:(eapply msteps_trans; [exact MS3| exact MS4]) MG3).
  { intros a Ha N. apply FZ3; exact Ha. }
  { intros a Ha Wa. destruct Wa. }
  intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3.
  assert (TW3 : forall a, 0 <= a < 2 ^ 64 -> M3 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)) by (intros a Ha; apply FR3; [exact Ha| intros []]).
  assert (TB : forall a, b <= a < b + c -> M3 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha. rewrite TW3 by lia. apply T20; [lia| | lia|].
    - unfold aclient, aclient_g. left. exists (b, c). split; [exact BIN| cbn [fst snd]; lia].
    - intros X. pose proof (PNAEK.in_shadow_range b (c) a ltac:(lia) ltac:(lia) X). lia. }
  (* [comment removed for export] *)
  apply (KONT fx3 R3 M3 model3 LK Aw2).
  - apply L5SAR.preserved_by_index. intros k0 Hk.
    assert (CH : forall k', In k' [3; 4; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R3 (reg k') = getr R (reg k')).
    { intros k' Hk'. assert (Y : In k' PNAAV8P.KS_azudB /\ In k' L5SAR.cs_all /\ In k' PNAAV8P.KS_azudA)
        by (destruct Hk' as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]; (split; [inl| split; inl])).
      destruct Y as (Yk1 & Yk2 & Yk3). rewrite (KS3 k' Yk1), (CS2 k' Yk2), (KS1 k' Yk3). reflexivity. }
    unfold L5SAR.cs_all in Hk. destruct Hk as [<-|[<-|[<-|[<-|Hk]]]].
    + rewrite gR2. exact (eq_sym Rsp).
    + apply CH; left; reflexivity.
    + apply CH; right; left; reflexivity.
    + rewrite gR8, Z_to_bv_bv_unsigned; reflexivity.
    + apply CH. destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]; inl.
  - (* [comment removed for export] *)
    assert (TV : forall a, v <= a < v + 24 -> M3 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha. rewrite TW3 by lia. apply T20; [lia| apply (L5SAR.obj_client L ar LB FF 0 0 v 24 a AOB); lia| lia|].
      intros X. pose proof (PNAEK.in_shadow_range b c a ltac:(lia) ltac:(lia) X). lia. }
    split. { intros i Hi. rewrite TV by lia. exact (VDEF i Hi). }
    cbn. split. { apply (L5C.u64_at_agree RSEGS M M3); [intros i Hi; apply TV; lia| lia| lia| exact VB]. }
    split. { apply (L5C.u64_at_agree RSEGS M M3); [intros i Hi; apply TV; lia| lia| lia| exact VE]. }
    split. { apply (L5C.u64_at_agree RSEGS M M3); [intros i Hi; apply TV; lia| lia| lia| exact VC]. }
    split; [lia|]. split; [lia|]. split; [lia|]. split; [exact B16|].
    intros i Hi. rewrite TB by lia. exact (BDEF i Hi).
  - apply (PMFA.accA_agree M M3 v 24); [| exact ACCV]. intros x Hx. pose proof (PNAEK.S_range x ltac:(lia)) as SRx.
    rewrite TW3 by lia. apply T20; [lia| | lia|].
    + exact (PNAEK.frame_sh_client L ar FF v 24 x LB 0 0 AOV Hx).
    + apply (PNAEK.sh_apartU b c x v); lia.
  - intros b' n' c' E. injection E as <- <- <-.
    destruct ANN2 as (ZA2 & PZ2 & _). unfold PMSPA.accA. apply (PMFA.accA_agree M2 M3 b c).
    + intros x Hx. apply TW3. pose proof (PNAEK.S_range x ltac:(lia)). lia.
    + apply (L5CB.aacc_of_blk M2 b c b c (conj ZA2 PZ2)); lia.
  - intros b' n' c' a E Ha. injection E as <- <- <-. apply TB. exact Ha.
  - apply (L5SAR.ahpres_of L ar LBX FF sp 12288 _ M M3).
    + intros a (Ha & Hc & Ho).
      assert (HcB : aclient L ar LB FF sp 12288 a) by (apply (L5SAR.aclient_appb L ar LBX [(b, c)] FF sp 12288 a Hc)).
      assert (NS : ~ in_shadow_of b (c) a) by (exact (PNAEK.own_sh_notclientU L ar C HI LY HIok b (c) LBX FF LK cr Aw M _ HH a sp 12288 Hc)).
      rewrite TW3 by exact Ha. rewrite (KEEP2 a Ha); [| apply (L5SAR.aclient_mono L ar LB FF sp 12288 (sp - 16) 2304 a HcB); intros x Hx; lia| exact NS].
      destruct (L5SAR.aclient_cases L ar C HI LYa HIok LB FF LK cr Aw M _ sp 12288 a HH SPT HcB) as [Z1|Z1];
        (apply FR1; [exact Ha| unfold W1; lia]).
    + pose proof ASTK2 as (_ & _ & _ & _ & SD2 & _). apply (L5.defined_grows M2 M3 _ _ MGM3). exact SD2.
    + intros a Ha Hc HM. apply MGM3.
      assert (HcB : aclient L ar LB FF sp 12288 a) by (apply (L5SAR.aclient_appb L ar LBX [(b, c)] FF sp 12288 a Hc)).
      assert (NS : ~ in_shadow_of b (c) a) by (exact (PNAEK.own_sh_notclientU L ar C HI LY HIok b (c) LBX FF LK cr Aw M _ HH a sp 12288 Hc)).
      rewrite (KEEP2 a Ha); [| apply (L5SAR.aclient_mono L ar LB FF sp 12288 (sp - 16) 2304 a HcB); intros x Hx; lia| exact NS].
      apply MGM1. exact HM.
  - apply (L5LZ.model_rt_trans model model2 model3); [|exact MRT3]. apply (L5LZ.model_rt_trans model model1 model2); [exact MRT1| exact MRT2].
  - intros x Hx. exact Hx.
  - exact INC2.
  - exact AM3.
  - exact HH3.
Qed.


Lemma ann_shrink_v8_null : forall (fx : FPState) R M model K LBX FF LK Aw cr v old sp r,
    ri_inv HI (PGV8.v8_own PGV8.V8Null ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA PMA.AD L ar R M sp r 0 -> PMSPA.ffrsA FF sp ->
    getr R 10%bv = Z_to_bv 64 v -> getr R 11%bv = Z_to_bv 64 old -> PMSPA.aobjA FF v 24 -> v mod 8 = 0 -> PMSPA.accA M v 24 ->
    PNSAX.v8_hdr RSEGS M v PGV8.V8Null -> PGV8.v8_size PGV8.V8Null <= old <= PGV8.v8_cap PGV8.V8Null ->
    (forall (fx' : FPState) R' M' model' LK' Aw',
        regs_preserved R R' -> PGV8.v8_at RSEGS PMSPA.accA PMSPA.annA M' v PGV8.V8Null ->
        (forall b n c a, PGV8.V8Null = PGV8.V8Blk b n c -> b <= a < b + c -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
        L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr 0) [] M M' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv HI (PGV8.v8_own PGV8.V8Null ++ LBX) FF LK' cr Aw' M' (vml_of model') ->
        srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx' R' r M' model') K) ->
    srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xabc48 M model) K.
Proof.
  intros fx R M model K LBX FF LK Aw cr v old sp r HH AM K0 ENT FRS A10 A11 AOV V8 ACCV VEC OLD KONT. cbn [PGV8.v8_size PGV8.v8_cap] in OLD.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). pose proof RAok as (Hr1 & Hr2).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11.
  change (PMSPA.pm_scr 0) with 12288 in *. change (12288 / 8) with 1536 in STKSH.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof AM as (Mh & MI).
  destruct VEC as (VDEF & VB & VE & VC). cbn [PGV8.v8_own app] in HH, KONT. set (LB := LBX) in *.
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _ & _ & CB1 & CB2 & STOP & _).
  pose proof (PMKA.aobj_of_aobjA FF v 24 AOV V8) as AOB.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK cr Aw M model v 24 sp 12288 HH AOB ltac:(lia) ltac:(reflexivity)) as (OR & OBIG & ODEF & OVIS & OVSH & OCL & OCLSH).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw M model HH) as (HOFF & VIS & VIMG & VFS & VBLK' & VBSH & VFSSH & VSTSH).
  set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as ST. rewrite (L5A.aly_segs L C LYa) in ST.
  pose proof (L5A.statics_facts L C M LYa ST) as (GOT & CSB & CUAR & _).
  assert (X0 : L5.img_clear MV 1249280 1282048) by (apply L5A.img_clear_mrestrict; exact GOT).
  assert (X1 : L5.u64_at RSEGS MV 1309752 2147450880) by (apply (proj2 (L5A.u64_at_vis H M 1309752 2147450880 (VIMG 1309752 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB).
  assert (X2 : L5.u32_at RSEGS MV 1309760 1) by (apply (proj2 (L5A.u32_at_vis H M 1309760 1 (VIMG 1309760 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR).
  assert (X3 : L5.writable RSEGS MV (sp - 4096) 4096).
  { apply (proj2 (L5A.writable_vis H M (sp - 4096) 4096 (VIS (sp - 4096) 4096 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5SAR.astk_writable ar M sp 12288); [exact ASTK| lia| lia| lia]. }
  assert (X5 : L5KA.zeros_at MV (v / 8 + 2147450880) 3).
  { exact (PMKA.obj_shadow_vis L ar C HI LYa HIok LB FF LK cr Aw M model v 24 HH AOV V8 ltac:(lia) ltac:(reflexivity) ACCV). }
  assert (X6 : L5.u64_at RSEGS MV v 0) by (apply (proj2 (L5A.u64_at_vis H M v 0 ltac:(eapply L5A.avis_sub; [exact OVIS| lia| lia]) ltac:(lia) ltac:(lia))); exact VB).
  assert (X7 : L5.u64_at RSEGS MV (v + 8) 0) by (apply (proj2 (L5A.u64_at_vis H M (v + 8) _ ltac:(eapply L5A.avis_sub; [exact OVIS| lia| lia]) ltac:(lia) ltac:(lia))); exact VE).
  assert (X8 : L5.u64_at RSEGS MV (v + 16) 0) by (apply (proj2 (L5A.u64_at_vis H M (v + 16) _ ltac:(eapply L5A.avis_sub; [exact OVIS| lia| lia]) ltac:(lia) ltac:(lia))); exact VC).
  LeanFeed.pfeed P (PNAAV8P.azusN_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => v | 34%nat => old | _ => 0 end)) ltac:(first [assumption | unfold PNAAV8P.aligned; lia | lia]).
  destruct P as (fx1 & R1 & M1v & MG1 & _ & FZ1 & MS1 & KS1 & _).
  assert (R1ra : getr R1 (reg 1) = Z_to_bv 64 r) by (rewrite (KS1 1%nat) by inl; exact Rra).
  pose proof (PMK.ret_to RSEGS fx1 R1 M1v 0xabcc4 W_ab164 r F_ab164 eq_refl D_ab164 R1ra ltac:(lia) Hr2) as MS2.
  set (W1 := fun a => sp - 24 <= a < sp - 24 + 24).
  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr Aw M model fx fx1 R 0xabc48 R1 r M1v W1 K HH AM ltac:(eapply msteps_trans; [exact MS1| exact MS2]) MG1).
  { intros a Ha N. apply FZ1; [exact Ha| exact N]. }
  { intros a Ha Wa. unfold W1 in Wa. split; [|lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia]. }
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
  assert (TV : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 24 <= a < sp) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) by (intros a Ha N; apply FR1; [exact Ha| unfold W1; lia]).
  apply (KONT fx1 R1 M1 model1 LK Aw).
  - apply L5SAR.preserved_by_index. intros k0 Hk. apply KS1. revert Hk. unfold L5SAR.cs_all.
    intros Hk. destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]]; inl.
  - split. { intros i Hi. rewrite TV by lia. exact (VDEF i Hi). }
    split. { apply (PMFA.accA_agree M M1 v 24); [| exact ACCV]. intros x Hx. pose proof (PNAEK.S_range x ltac:(lia)) as SRx. apply TV; lia. }
    cbn. split. { apply (L5C.u64_at_agree RSEGS M M1); [intros i Hi; apply TV; lia| lia| lia| exact VB]. }
    split. { apply (L5C.u64_at_agree RSEGS M M1); [intros i Hi; apply TV; lia| lia| lia| exact VE]. }
    apply (L5C.u64_at_agree RSEGS M M1); [intros i Hi; apply TV; lia| lia| lia| exact VC].
  - intros b n c a E. discriminate E.
  - apply (L5SAR.ahpres_of L ar LBX FF sp 12288 _ M M1).
    + intros a (Ha & Hc & Ho). apply FR1; [exact Ha|]. unfold W1.
      destruct (L5SAR.aclient_cases L ar C HI LYa HIok LB FF LK cr Aw M _ sp 12288 a HH SPT Hc) as [Z1|Z1]; lia.
    + apply (L5.defined_grows M M1 _ _ MGM1). exact SDEF.
    + intros a Ha Hc HM. apply MGM1. exact HM.
  - exact MRT1.
  - intros f Hf. exact Hf.
  - intros q Hq. exact Hq.
  - exact AM1.
  - exact HH1.
Qed.

Theorem ann_shrink_v8_ok : PNSAX.ann_shrink_v8_spec RSEGS PMA.AD L ar HI 0xabc48.
Proof.
  unfold PNSAX.ann_shrink_v8_spec.
  intros fx R M model K LBX FF LK Aw cr v old x sp r HH AM K0 ENT FRS A10 A11 AOV V8 ACCV HDR OLD BAN KONT.
  destruct x as [|b n c].
  { (* [comment removed for export] *)
    apply (ann_shrink_v8_null fx R M model K LBX FF LK Aw cr v old sp r HH AM K0 ENT FRS A10 A11 AOV V8 ACCV HDR OLD KONT). }
  destruct HDR as (VDEF & VB & VE & VC & NC & C27 & B4096 & B16 & BDEF). cbn [PGV8.v8_size PGV8.v8_cap] in OLD.
  destruct (BAN b n c eq_refl) as (BACC & BANN). clear BAN. cbn [PGV8.v8_own] in HH, KONT.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). pose proof RAok as (Hr1 & Hr2).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11.
  change (PMSPA.pm_scr 0) with 12288 in *. change (12288 / 8) with 1536 in STKSH.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof AM as (Mh & MI).
  set (LB := [(b, c)] ++ LBX) in *.
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _ & _ & CB1 & CB2 & STOP & _).
  assert (BIN : In (b, c) LB) by (left; reflexivity).
  destruct (PNAEK.blk_facts L ar C HI LY HIok _ FF LK cr Aw M _ b (c) HH BIN) as (Bq0 & Bq1 & Bq2 & Bq3 & _ & Bq5 & Bq6 & _ & Bq8).
  pose proof (PMKA.aobj_of_aobjA FF v 24 AOV V8) as AOB.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK cr Aw M model v 24 sp 12288 HH AOB ltac:(lia) ltac:(reflexivity)) as (OR & OBIG & ODEF & OVIS & OVSH & OCL & OCLSH).
  assert (VBLK : v + 24 <= b \/ b + c <= v).
  { destruct AOV as (f & Hf & Y1 & Y2). destruct (Bq8 f Hf) as [Y|Y]; [right; lia| left; lia]. }
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw M model HH) as (HOFF & VIS & VIMG & VFS & VBLK' & VBSH & VFSSH & VSTSH).
  set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as ST. rewrite (L5A.aly_segs L C LYa) in ST.
  pose proof (L5A.statics_facts L C M LYa ST) as (GOT & CSB & CUAR & _).
  assert (X0 : L5.img_clear MV 1249280 1282048) by (apply L5A.img_clear_mrestrict; exact GOT).
  assert (X1 : L5.u64_at RSEGS MV 1309752 2147450880) by (apply (proj2 (L5A.u64_at_vis H M 1309752 2147450880 (VIMG 1309752 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB).
  assert (X2 : L5.u32_at RSEGS MV 1309760 1) by (apply (proj2 (L5A.u32_at_vis H M 1309760 1 (VIMG 1309760 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR).
  assert (X3 : L5.writable RSEGS MV (sp - 4096) 4096).
  { apply (proj2 (L5A.writable_vis H M (sp - 4096) 4096 (VIS (sp - 4096) 4096 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5SAR.astk_writable ar M sp 12288); [exact ASTK| lia| lia| lia]. }
  assert (X5 : L5KA.zeros_at MV (v / 8 + 2147450880) 3).
  { exact (PMKA.obj_shadow_vis L ar C HI LYa HIok LB FF LK cr Aw M model v 24 HH AOV V8 ltac:(lia) ltac:(reflexivity) ACCV). }
  assert (X6 : L5.u64_at RSEGS MV v b) by (apply (proj2 (L5A.u64_at_vis H M v b ltac:(eapply L5A.avis_sub; [exact OVIS| lia| lia]) ltac:(lia) ltac:(lia))); exact VB).
  assert (X7 : L5.u64_at RSEGS MV (v + 8) (b + n)) by (apply (proj2 (L5A.u64_at_vis H M (v + 8) _ ltac:(eapply L5A.avis_sub; [exact OVIS| lia| lia]) ltac:(lia) ltac:(lia))); exact VE).
  assert (X8 : L5.u64_at RSEGS MV (v + 16) (b + c)) by (apply (proj2 (L5A.u64_at_vis H M (v + 16) _ ltac:(eapply L5A.avis_sub; [exact OVIS| lia| lia]) ltac:(lia) ltac:(lia))); exact VC).
  LeanFeed.pfeed P (PNAAV8P.azusA_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => v | 34%nat => old | 36%nat => b | 37%nat => n | 41%nat => b + c | _ => 0 end)) ltac:(first [assumption | unfold PNAAV8P.aligned; lia | lia]).
  destruct P as (fx1 & R1 & M1v & MG1 & _ & FZ1 & MS1 & KS1 & fR1 & fR2 & fR10 & fR11 & fR12 & fR13 & fR14 & fR15 & fR16 & T16 & T8).
  set (W1 := fun a => sp - 24 <= a < sp - 24 + 24).
  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr Aw M model fx fx1 R 0xabc48 R1 0x7ba7c M1v W1 K HH AM MS1 MG1).
  { intros a Ha N. apply FZ1; [exact Ha| exact N]. }
  { intros a Ha Wa. unfold W1 in Wa. split; [|lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia]. }
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
  pose proof AM1 as (Mh1 & MI1).
  assert (SH01 : forall x, 0 <= x < 2 ^ 64 -> x < sp - 24 -> M1 (Z_to_bv 64 x) = M (Z_to_bv 64 x)) by (intros x Hx Hx'; apply FR1; [exact Hx| unfold W1; lia]).
  (* [comment removed for export] *)
  pose proof (HAJ.aex_annotate _ _ _ _ _ EXT) as ANN. unfold HAJ.annotate_spec in ANN.
  cbn [PMA.EXT HAJ.ec_ann_pc HAJ.ec_ann_scr paa_annotate PMA.AAD AADDR_A] in ANN. rewrite (L5A.aly_segs L C LYa) in ANN.
  apply (ANN fx1 R1 M1 model1 LB FF LK cr Aw K b (c) (old) (n)); clear ANN.
  { exact HH1. }
  { exact Mh1. }
  { exact MI1. }
  { rewrite L5K.rl10. exact fR10. }
  { rewrite L5K.rl11. exact fR11. }
  { rewrite L5K.rl12, fR12. f_equal. lia. }
  { rewrite L5K.rl13. exact fR13. }
  { exact BIN. }
  { exact B16. }
  { lia. }
  { lia. }
  { apply (PNAEK.ann_agree M M1 b (old) (c)); [| lia| lia| exact BANN].
    intros j Hj. pose proof (PNAEK.shadow_lowU b c j ltac:(lia) ltac:(lia) Hj) as SL. apply SH01; lia. }
  { rewrite L5K.rl4, (KS1 4%nat) by inl. exact Rtp. }
  { rewrite L5K.rl1, fR1. vm_compute. reflexivity. }
  { rewrite L5K.rl2, fR2, L5.unsigned_lit by lia.
    apply (L5SAR.astack_ok_of_astk L ar C LYa M M1 sp 12288 16 2304 ASTK MGM1); [lia| lia| lia|].
    replace (sp - 16) with (sp + (-1) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
  { exact K0. }
  intros fx2 R2 M2 model2 Aw2 RP2 ANN2 KEEP2 DSH2 SCR2 MRT2 INC2 MI2 HH2.
  rewrite L5K.rl2, fR2, L5.unsigned_lit in KEEP2, SCR2 by lia. rewrite L5K.rl1, fR1.
  assert (AM2 : L5CA.amodel_ok Aw2 model2) by (split; [rewrite (L5LZ.model_rt_halted model1 model2 MRT2); exact Mh1| exact MI2]).
  assert (CS2 : forall k0, In k0 L5SAR.cs_all -> getr R2 (reg k0) = getr R1 (reg k0)) by (intros k0 Hk; apply (L5SAR.cs_of_preserved R1 R2 k0 RP2 Hk)).
  assert (T20 : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF 0 0 a -> ~ (sp - 2320 <= a < sp) -> ~ in_shadow_of b (c) a -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha Hc N1 N2. rewrite (KEEP2 a Ha ltac:(apply (L5SAR.aclient_narrow L ar LB FF 0 0); [exact Hc| lia]) N2). apply FR1; [exact Ha| unfold W1; lia]. }
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw2 M2 model2 HH2) as (HOFF2 & VIS2 & VIMG2 & VFS2 & VBLK2 & VBSH2 & VFSSH2 & VSTSH2).
  set (H2 := ahid Aw2 model2) in *. set (MV2 := mrestrict H2 M2) in *.
  assert (ASTK2 : L5CA.astk ar M2 sp 12288).
  { apply (L5SAR.astk_after_eq L ar C HI HIok LB FF LK cr Aw M M1 M2 _ sp 12288 (sp - 16) 2304 HH ASTK MGM1).
    - intros a Ha Hs Hns. apply KEEP2; [exact Ha| apply L5SAR.stack_client; [exact Hs| exact Hns]|].
      intros X. pose proof (PNAEK.in_shadow_range b (c) a ltac:(lia) ltac:(lia) X). lia.
    - exact SCR2.
    - lia. - lia. - lia. }
  assert (Y3 : L5.writable RSEGS MV2 (sp - 4096) 4096).
  { apply (proj2 (L5A.writable_vis H2 M2 (sp - 4096) 4096 (VIS2 (sp - 4096) 4096 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5SAR.astk_writable ar M2 sp 12288); [exact ASTK2| lia| lia| lia]. }
  (* [comment removed for export] *)
  assert (TS : forall a v0, sp - 16 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1v a v0 -> L5.u64_at RSEGS MV2 a v0).
  { intros a v0 Ha Ha' X. apply (proj2 (L5A.u64_at_vis H2 M2 a v0 (VIS2 a 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply KEEP2; [lia| apply L5SAR.stack_client; lia|]| lia| lia|].
    - intros XS. pose proof (PNAEK.in_shadow_range b (c) i ltac:(lia) ltac:(lia) XS). lia.
    - apply (PMAIS1.vis_u64 _ _ _ _ _ VIS1); [apply VIS; lia| lia| lia| exact X]. }
  pose proof (TS (sp - 8) _ ltac:(lia) ltac:(lia) T8) as Z8.
  pose proof (TS (sp - 16) _ ltac:(lia) ltac:(lia) T16) as Z16.
  assert (J2 : getr R2 (reg 2) = Z_to_bv 64 (sp - 16)) by (rewrite CS2 by inl; exact fR2).
  pose proof (PMAIS1.bvu (getr R (reg 1))) as UR1. pose proof (PMAIS1.bvu (getr R (reg 8))) as UR8.
  LeanFeed.pfeed P (PNAAV8P.azusB_conc fx2 R2 MV2 (fun j => match j with 2%nat => sp | 43%nat => bv_unsigned (getr R (reg 1)) | 44%nat => bv_unsigned (getr R (reg 8)) | _ => 0 end)) ltac:(first [assumption | unfold PNAAV8P.aligned; lia | lia]).
  destruct P as (fx3 & R3 & M3v & MG3 & _ & FZ3 & MS3 & KS3 & gR1 & gR2 & gR8).
  assert (R3ra : getr R3 (reg 1) = Z_to_bv 64 r) by (rewrite gR1, Z_to_bv_bv_unsigned; exact Rra).
  pose proof (PMK.ret_to RSEGS fx3 R3 M3v 0xabcc4 W_ab164 r F_ab164 eq_refl D_ab164 R3ra ltac:(lia) Hr2) as MS4.
  set (W3 := fun a : Z => False).
  apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr Aw2 M2 model2 fx2 fx3 R2 0xabcb8 R3 r M3v W3 K HH2 AM2 ltac:(eapply msteps_trans; [exact MS3| exact MS4]) MG3).
  { intros a Ha N. apply FZ3; exact Ha. }
  { intros a Ha Wa. destruct Wa. }
  intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3.
  assert (TW3 : forall a, 0 <= a < 2 ^ 64 -> M3 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)) by (intros a Ha; apply FR3; [exact Ha| intros []]).
  assert (TB : forall a, b <= a < b + c -> M3 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha. rewrite TW3 by lia. apply T20; [lia| | lia|].
    - unfold aclient, aclient_g. left. exists (b, c). split; [exact BIN| cbn [fst snd]; lia].
    - intros X. pose proof (PNAEK.in_shadow_range b (c) a ltac:(lia) ltac:(lia) X). lia. }
  (* [comment removed for export] *)
  apply (KONT fx3 R3 M3 model3 LK Aw2).
  - apply L5SAR.preserved_by_index. intros k0 Hk.
    assert (CH : forall k', In k' [3; 4; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R3 (reg k') = getr R (reg k')).
    { intros k' Hk'. assert (Y : In k' PNAAV8P.KS_azusB /\ In k' L5SAR.cs_all /\ In k' PNAAV8P.KS_azusA)
        by (destruct Hk' as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]; (split; [inl| split; inl])).
      destruct Y as (Yk1 & Yk2 & Yk3). rewrite (KS3 k' Yk1), (CS2 k' Yk2), (KS1 k' Yk3). reflexivity. }
    unfold L5SAR.cs_all in Hk. destruct Hk as [<-|[<-|[<-|[<-|Hk]]]].
    + rewrite gR2. exact (eq_sym Rsp).
    + apply CH; left; reflexivity.
    + apply CH; right; left; reflexivity.
    + rewrite gR8, Z_to_bv_bv_unsigned; reflexivity.
    + apply CH. destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]; inl.
  - assert (TV : forall a, v <= a < v + 24 -> M3 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha. rewrite TW3 by lia. apply T20; [lia| apply (L5SAR.obj_client L ar LB FF 0 0 v 24 a AOB); lia| lia|].
      intros X. pose proof (PNAEK.in_shadow_range b (c) a ltac:(lia) ltac:(lia) X). lia. }
    destruct ANN2 as (ZA2 & PM2 & PA2).
    (* [comment removed for export] *)
    split. { intros i Hi. rewrite TV by lia. exact (VDEF i Hi). }
    split. { apply (PMFA.accA_agree M M3 v 24); [| exact ACCV]. intros x Hx. pose proof (PNAEK.S_range x ltac:(lia)) as SRx.
             rewrite TW3 by lia. apply T20; [lia| | lia|].
             + exact (PNAEK.frame_sh_client L ar FF v 24 x LB 0 0 AOV Hx).
             + apply (PNAEK.sh_apartU b c x v); lia. }
    cbn. split. { apply (L5C.u64_at_agree RSEGS M M3); [intros i Hi; apply TV; lia| lia| lia| exact VB]. }
    split. { apply (L5C.u64_at_agree RSEGS M M3); [intros i Hi; apply TV; lia| lia| lia| exact VE]. }
    split. { apply (L5C.u64_at_agree RSEGS M M3); [intros i Hi; apply TV; lia| lia| lia| exact VC]. }
    split; [lia|]. split; [lia|]. split; [lia|]. split; [exact B16|].
    split. { intros i Hi. rewrite TB by lia. exact (BDEF i Hi). }
    split. { unfold PMSPA.accA. apply (PMFA.accA_agree M2 M3 b n).
             - intros x Hx. apply TW3. pose proof (PNAEK.S_range x ltac:(lia)). lia.
             - apply (L5CB.aacc_of_blk M2 b n b n (conj ZA2 PM2)); lia. }
    apply (PNAEK.ann_agree M2 M3 b n c); [| lia| lia| split; [exact ZA2| split; [exact PM2| exact PA2]]].
    intros j Hj. apply TW3. pose proof (PNAEK.shadow_lowU b c j ltac:(lia) ltac:(lia) Hj). lia.
  - intros b' n' c' a E Ha. injection E as <- <- <-. apply TB. exact Ha.
  - apply (L5SAR.ahpres_of L ar LBX FF sp 12288 _ M M3).
    + intros a (Ha & Hc & Ho).
      assert (HcB : aclient L ar LB FF sp 12288 a) by (apply (L5SAR.aclient_appb L ar LBX [(b, c)] FF sp 12288 a Hc)).
      assert (NS : ~ in_shadow_of b (c) a) by (exact (PNAEK.own_sh_notclientU L ar C HI LY HIok b (c) LBX FF LK cr Aw M _ HH a sp 12288 Hc)).
      rewrite TW3 by exact Ha. rewrite (KEEP2 a Ha); [| apply (L5SAR.aclient_mono L ar LB FF sp 12288 (sp - 16) 2304 a HcB); intros x Hx; lia| exact NS].
      destruct (L5SAR.aclient_cases L ar C HI LYa HIok LB FF LK cr Aw M _ sp 12288 a HH SPT HcB) as [Z1|Z1];
        (apply FR1; [exact Ha| unfold W1; lia]).
    + pose proof ASTK2 as (_ & _ & _ & _ & SD2 & _). apply (L5.defined_grows M2 M3 _ _ MGM3). exact SD2.
    + intros a Ha Hc HM. apply MGM3.
      assert (HcB : aclient L ar LB FF sp 12288 a) by (apply (L5SAR.aclient_appb L ar LBX [(b, c)] FF sp 12288 a Hc)).
      assert (NS : ~ in_shadow_of b (c) a) by (exact (PNAEK.own_sh_notclientU L ar C HI LY HIok b (c) LBX FF LK cr Aw M _ HH a sp 12288 Hc)).
      rewrite (KEEP2 a Ha); [| apply (L5SAR.aclient_mono L ar LB FF sp 12288 (sp - 16) 2304 a HcB); intros x Hx; lia| exact NS].
      apply MGM1. exact HM.
  - apply (L5LZ.model_rt_trans model model2 model3); [|exact MRT3]. apply (L5LZ.model_rt_trans model model1 model2); [exact MRT1| exact MRT2].
  - intros x Hx. exact Hx.
  - exact INC2.
  - exact AM3.
  - exact HH3.
Qed.

Lemma clear_v8_fact (b n : Z) : 0 <= b -> 0 <= n <= 2 ^ 27 -> b + n < 2 ^ 64 -> (n = 0 \/ 1 <= b) ->
  134217728 <= ((((((134217728 * (if ((((18446744073709551615 * b) mod 2 ^ 64) + ((18446744073709551615 * n) mod 2 ^ 64)) mod 2 ^ 64) <? ((18446744073709551615 * n) mod 2 ^ 64) then 1 else 0)) mod 2 ^ 64) - n) mod 2 ^ 64) + 134217728) mod 2 ^ 64) <= 268435456.
Proof.
  intros Hb Hn Hbn Hor. destruct (Z.eq_dec n 0) as [->|Hn0].
  - match goal with |- context [if ?t then _ else _] => destruct t end; split; apply Z.leb_le; vm_compute; reflexivity.
  - assert (Hb1 : 1 <= b) by (destruct Hor as [X|X]; [contradiction| exact X]).
    assert (MM : forall y, 1 <= y < 2 ^ 64 -> (18446744073709551615 * y) mod 2 ^ 64 = 2 ^ 64 - y).
    { intros y Hy. replace (18446744073709551615 * y) with ((2 ^ 64 - y) + (y - 1) * 2 ^ 64) by lia.
      rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
    rewrite (MM b) by lia. rewrite (MM n) by lia.
    replace ((2 ^ 64 - b + (2 ^ 64 - n)) mod 2 ^ 64) with (2 ^ 64 - b - n).
    2: { replace (2 ^ 64 - b + (2 ^ 64 - n)) with ((2 ^ 64 - b - n) + 1 * 2 ^ 64) by lia. rewrite Z.mod_add by lia.
         symmetry. apply Z.mod_small. lia. }
    rewrite (proj2 (Z.ltb_lt (2 ^ 64 - b - n) (2 ^ 64 - n))) by lia. change (if true then 1 else 0) with 1.
    rewrite (Z.mod_small (134217728 * 1) (2 ^ 64)) by lia.
    rewrite (Z.mod_small (134217728 * 1 - n) (2 ^ 64)) by lia.
    rewrite (Z.mod_small (134217728 * 1 - n + 134217728) (2 ^ 64)) by lia.
    lia.
Qed.

Theorem clear_v8_ok : PNSAXC.clear_v8_spec RSEGS PMA.AD L ar HI 0xabb00.
Proof.
  unfold PNSAXC.clear_v8_spec.
  intros fx R M model K LBX FF LK Aw cr v x sp r HH AM K0 ENT FRS A10 AOV V8 ACCV VAT KONT.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). pose proof RAok as (Hr1 & Hr2).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10.
  change (PMSPA.pm_scr 0) with 12288 in *. change (12288 / 8) with 1536 in STKSH.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof AM as (Mh & MI).
  pose proof VAT as (VDEF & VACC & _).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _ & _ & CB1 & CB2 & STOP & _).
  pose proof (PMKA.aobj_of_aobjA FF v 24 AOV V8) as AOB.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr Aw M model v 24 sp 12288 HH AOB ltac:(lia) ltac:(reflexivity))
    as ((Ov1 & Ov2 & Ov3 & Ov4 & Ov5) & OBIG & ODEF & OVIS & OVSH & OCL & OCLSH).
  assert (XF : L5.u64_at RSEGS M v (PGV8.v8_data x) /\ L5.u64_at RSEGS M (v + 8) (PGV8.v8_data x + PGV8.v8_size x)
               /\ L5.u64_at RSEGS M (v + 16) (PGV8.v8_data x + PGV8.v8_cap x)
               /\ 0 <= PGV8.v8_data x /\ PGV8.v8_data x + PGV8.v8_cap x < 2 ^ 47 /\ PGV8.v8_data x mod 16 = 0
               /\ 0 <= PGV8.v8_size x <= PGV8.v8_cap x /\ PGV8.v8_cap x <= 2 ^ 27 /\ (PGV8.v8_size x = 0 \/ 4096 <= PGV8.v8_data x)
               /\ (forall a, PGV8.v8_data x <= a < PGV8.v8_data x + PGV8.v8_cap x ->
                     0 <= a < 2 ^ 64 /\ ~ (sp - 16 <= a < sp - 16 + 16) /\ ~ (v + 8 <= a < v + 8 + 8))).
  { destruct x as [|b n c]; destruct VAT as (_ & _ & VX); cbn [PGV8.v8_data PGV8.v8_size PGV8.v8_cap].
    - destruct VX as (Y0 & Y8 & Y16). split; [exact Y0|]. split; [exact Y8|]. split; [exact Y16|].
      split; [lia|]. split; [lia|]. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [left; reflexivity|].
      intros a Ha. lia.
    - destruct VX as (Y0 & Y8 & Y16 & NCb & C27b & B4096 & B16 & _).
      assert (BIN : In (b, c) (PGV8.v8_own (PGV8.V8Blk b n c) ++ LBX)) by (left; reflexivity).
      destruct (PNAEK.blk_facts L ar C HI LY HIok _ FF LK cr Aw M _ b c HH BIN) as (Bq0 & Bq1 & Bq2 & Bq3 & _ & _ & _ & _ & Bq8).
      assert (VB : v + 24 <= b \/ b + c <= v).
      { destruct AOV as (f & Hf & Y1 & Y2). destruct (Bq8 f Hf) as [Y|Y]; [right; lia| left; lia]. }
      split; [exact Y0|]. split; [exact Y8|]. split; [exact Y16|].
      split; [lia|]. split; [lia|]. split; [exact B16|]. split; [lia|]. split; [lia|]. split; [right; lia|].
      intros a Ha. split; [lia|]. split; intros Y; [clear - Ha Y Bq2 SLO; lia| clear - Ha Y VB; lia]. }
  destruct XF as (Y0 & Y8 & Y16 & DB & DC & D16 & NC & C27 & NZ & BLKW).
  assert (OWN : PGV8.v8_own (PGV8.v8_clear x) = PGV8.v8_own x) by (destruct x; reflexivity).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK cr Aw M model HH) as (HOFF & VIS & VIMG & VFS & VBLK' & VBSH & VFSSH & VSTSH).
  set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as ST. rewrite (L5A.aly_segs L C LYa) in ST.
  pose proof (L5A.statics_facts L C M LYa ST) as (GOT & CSB & CUAR & _).
  assert (X0 : L5.img_clear MV 1249280 1282048) by (apply L5A.img_clear_mrestrict; exact GOT).
  assert (X1 : L5.u64_at RSEGS MV 1309752 2147450880) by (apply (proj2 (L5A.u64_at_vis H M 1309752 2147450880 (VIMG 1309752 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB).
  assert (X2 : L5.u32_at RSEGS MV 1309760 1) by (apply (proj2 (L5A.u32_at_vis H M 1309760 1 (VIMG 1309760 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR).
  assert (X3 : L5.writable RSEGS MV (sp - 4096) 4096).
  { apply (proj2 (L5A.writable_vis H M (sp - 4096) 4096 (VIS (sp - 4096) 4096 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5SAR.astk_writable ar M sp 12288); [exact ASTK| lia| lia| lia]. }
  assert (X5 : L5KA.zeros_at MV (v / 8 + 2147450880) 3).
  { exact (PMKA.obj_shadow_vis L ar C HI LYa HIok _ FF LK cr Aw M model v 24 HH AOV V8 ltac:(lia) ltac:(reflexivity) ACCV). }
  assert (X6 : L5.u64_at RSEGS MV v (PGV8.v8_data x))
    by (apply (proj2 (L5A.u64_at_vis H M v _ ltac:(eapply L5A.avis_sub; [exact OVIS| lia| lia]) ltac:(lia) ltac:(lia))); exact Y0).
  assert (X7 : L5.u64_at RSEGS MV (v + 8) (PGV8.v8_data x + PGV8.v8_size x))
    by (apply (proj2 (L5A.u64_at_vis H M (v + 8) _ ltac:(eapply L5A.avis_sub; [exact OVIS| lia| lia]) ltac:(lia) ltac:(lia))); exact Y8).
  assert (X8 : L5.u64_at RSEGS MV (v + 16) (PGV8.v8_data x + PGV8.v8_cap x))
    by (apply (proj2 (L5A.u64_at_vis H M (v + 16) _ ltac:(eapply L5A.avis_sub; [exact OVIS| lia| lia]) ltac:(lia) ltac:(lia))); exact Y16).
  assert (WV8 : L5.writable RSEGS MV (v + 8) 8).
  { apply (proj2 (L5A.writable_vis H M (v + 8) 8 (L5A.avis_sub H v 24 (v + 8) 8 OVIS ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M v 24); [exact VDEF| lia| lia]| lia| lia]. }
  pose proof (PMAIS1.bvu (getr R (reg 11))) as UR11.
  assert (G11 : getr R (reg 11) = Z_to_bv 64 (bv_unsigned (getr R (reg 11)))) by (symmetry; apply Z_to_bv_bv_unsigned).
  pose proof (clear_v8_fact (PGV8.v8_data x) (PGV8.v8_size x) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(destruct NZ as [X|X]; [left; exact X| right; lia])) as FF0.
  LeanFeed.pfeed P (PNAAV8P.azucl_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => v | 34%nat => bv_unsigned (getr R (reg 11))
                                                   | 36%nat => PGV8.v8_data x | 37%nat => PGV8.v8_size x | 41%nat => PGV8.v8_data x + PGV8.v8_cap x | _ => 0 end))
    ltac:(first [assumption | unfold PNAAV8P.aligned; lia | lia]).
  destruct P as (fx1 & R1 & M1v & MG1 & _ & FZ1 & PP).
  assert (POST : msteps RSEGS (st fx R 0xabb00 MV) (st fx1 R1 0xabc48 M1v)
                 /\ (forall k, In k (1%nat :: 10%nat :: L5SAR.cs_all) -> getr R1 (reg k) = getr R (reg k))
                 /\ getr R1 (reg 11) = Z_to_bv 64 (PGV8.v8_size x) /\ L5.u64_at RSEGS M1v (v + 8) (PGV8.v8_data x)).
  { destruct PP as [(MS & KS & Q11 & _ & _ & _ & T8 & N0)|(MS & KS & Q11 & _ & _ & _ & _ & _ & T8 & _ & N1)].
    - split; [exact MS|]. split; [intros k Hk; apply KS; unfold L5SAR.cs_all in Hk; repeat (destruct Hk as [<-|Hk]; [inl|]); destruct Hk|].
      split; [rewrite Q11; f_equal; lia| exact T8].
    - split; [exact MS|]. split; [intros k Hk; apply KS; unfold L5SAR.cs_all in Hk; repeat (destruct Hk as [<-|Hk]; [inl|]); destruct Hk|].
      split; [exact Q11| exact T8]. }
  destruct POST as (MS1 & KP & R11 & T8).
  set (W1 := fun a : Z => (sp - 16 <= a < sp - 16 + 16) \/ (v + 8 <= a < v + 8 + 8)).
  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK cr Aw M model fx fx1 R 0xabb00 R1 0xabc48 M1v W1 K HH AM MS1 MG1).
  { intros a Ha N. unfold W1 in N. apply FZ1; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
  { intros a Ha Wa. unfold W1 in Wa. split.
    - destruct Wa as [X|X]; unfold aclientw, aclient_g.
      + right; left. split; [lia| intros Y; lia].
      + do 3 right; left. destruct AOV as (f & Hf & Y1 & Y2). exists f. split; [exact Hf|]. split; [lia| intros Y; lia].
    - destruct Wa as [X|X]; lia. }
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
  assert (WSH : forall y, BIGSHADOW_LO <= y < BIGSHADOW_HI -> ~ (sp - 16 <= y < sp - 16 + 16) /\ ~ (v + 8 <= y < v + 8 + 8)).
  { intros y Hy. unfold BIGSHADOW_LO, BIGSHADOW_HI in Hy. split; intros Y; [clear - Hy Y SLO SPT; lia| clear - Hy Y OBIG; lia]. }
  assert (SHM1 : forall a m, 0 <= a -> a + m <= 2 ^ 47 -> PMFA.agsh M M1 a m).
  { intros a m Ha Hn y Hy. pose proof (PMKA.S_in_shadow y ltac:(lia)) as SX. destruct (WSH _ SX) as (N1 & N2).
    apply FR1; [unfold BIGSHADOW_LO, BIGSHADOW_HI in SX; lia| unfold W1; tauto]. }
  assert (TVv : forall i, (v <= i < v + 8 \/ v + 16 <= i < v + 24) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
  { intros i Hi. apply FR1; [clear - Hi Ov1 Ov3; lia| unfold W1; clear - Hi Ov2 SLO; lia]. }
  assert (ASTK1 : L5CA.astk ar M1 sp 12288) by exact (L5SAR.astk_grows ar M M1 sp 12288 ASTK MGM1).
  assert (SZ1 : shadow_zero M1 (sp - 12288) 1536).
  { intros j Hj. pose proof (STKSH j Hj) as Z1. red in Z1 |- *.
    assert (SL8 : (sp - 12288) mod 8 = 0)
      by (apply PMKA.mod16_8'; replace (sp - 12288) with (sp + (-768) * 16) by lia; rewrite Z_mod_plus_full; exact A16).
    rewrite (PMFA.S_granule (sp - 12288) j SL8 ltac:(lia)) in Z1 |- *.
    pose proof (PMKA.S_in_shadow (sp - 12288 + 8 * j) ltac:(lia)) as SX. destruct (WSH _ SX) as (N1 & N2).
    rewrite FR1; [exact Z1| unfold BIGSHADOW_LO, BIGSHADOW_HI in SX; lia| unfold W1; tauto]. }
  assert (HH1c : ri_inv HI (PGV8.v8_own (PGV8.v8_clear x) ++ LBX) FF LK cr Aw M1 (vml_of model1)) by (rewrite OWN; exact HH1).
  pose proof ann_shrink_v8_ok as SH. unfold PNSAX.ann_shrink_v8_spec in SH.
  apply (SH fx1 R1 M1 model1 K LBX FF LK Aw cr v (PGV8.v8_size x) (PGV8.v8_clear x) sp r HH1c AM1 K0); clear SH.
  { split; [rewrite L5K.rl1, (KP 1%nat) by inl; exact Rra|]. split; [exact RAok|].
    split; [rewrite L5K.rl2, (KP 2%nat) by inl; exact Rsp|].
    split; [rewrite L5K.rl3, (KP 3%nat) by inl; exact Rgp|].
    split; [rewrite L5K.rl4, (KP 4%nat) by inl; exact Rtp|].
    change (PMSPA.pm_scr 0) with 12288. split; [exact ASTK1|]. change (12288 / 8) with 1536. exact SZ1. }
  { exact FRS. }
  { rewrite L5K.rl10, (KP 10%nat) by inl. exact A10. }
  { rewrite L5K.rl11. exact R11. }
  { exact AOV. }
  { exact V8. }
  { apply (PMFA.accA_agree M M1); [apply SHM1; lia| exact ACCV]. }
  { unfold PNSAX.v8_hdr. split; [intros i Hi; apply MGM1; apply VDEF; exact Hi|].
    pose proof (PMAIS1.vis_u64 _ _ _ _ _ VIS1 (L5A.avis_sub H v 24 (v + 8) 8 OVIS ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia) T8) as T8'.
    assert (U0 : L5.u64_at RSEGS M1 v (PGV8.v8_data x))
      by (apply (L5C.u64_at_agree RSEGS M M1); [intros i Hi; apply TVv; left; lia| lia| lia| exact Y0]).
    assert (U16 : L5.u64_at RSEGS M1 (v + 16) (PGV8.v8_data x + PGV8.v8_cap x))
      by (apply (L5C.u64_at_agree RSEGS M M1); [intros i Hi; apply TVv; right; lia| lia| lia| exact Y16]).
    destruct x as [|b n c].
    - split; [exact U0|]. split; [exact T8'| exact U16].
    - destruct VAT as (_ & _ & _ & _ & _ & NCb & C27b & B4096 & B16 & BDEF & _).
      split; [exact U0|]. split; [rewrite Z.add_0_r; exact T8'|]. split; [exact U16|].
      split; [lia|]. split; [lia|]. split; [lia|]. split; [exact B16|].
      intros i Hi. apply MGM1. apply BDEF. exact Hi. }
  { clear - NC. destruct x; cbn [PGV8.v8_size PGV8.v8_cap PGV8.v8_clear] in *; lia. }
  { intros b' n' c' E. destruct x as [|b n c]; cbn [PGV8.v8_clear] in E; [discriminate E|]. injection E as <- <- <-.
    destruct VAT as (_ & _ & _ & _ & _ & NCb & C27b & B4096 & B16 & _ & BACC & BANN).
    cbn [PGV8.v8_data PGV8.v8_cap PGV8.v8_size] in DC |- *.
    split.
    - apply (PMFA.accA_agree M M1); [apply SHM1; lia| exact BACC].
    - apply (PNAEK.ann_agree M M1 b n c); [| lia| lia| exact BANN]. intros j Hj. rewrite (PNAEK.S_add8 b j).
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      apply (SHM1 b (8 * ((c + 7) / 8))); clear - DC B4096 B16 Hj C27b; Lia.lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  intros fx2 R2 M2 model2 LK2 Aw2 RP2 VAT2 KEPT2 HP2 MRT2 INCLK2 INCAw2 AM2 HH2.
  change (PMSPA.pm_scr 0) with 12288 in HP2.
  apply (KONT fx2 R2 M2 model2 LK2 Aw2).
  - apply (L5SAR.regs_preserved_trans R R1 R2); [| exact RP2].
    apply L5SAR.preserved_by_index. intros k0 Hk. apply KP. right; right; exact Hk.
  - exact VAT2.
  - intros b n c a E Ha. subst x. destruct (BLKW a Ha) as (Z0 & Z1 & Z2).
    rewrite (KEPT2 b 0 c a eq_refl Ha). apply FR1; [exact Z0| unfold W1; tauto].
  - assert (EK01 : L5SAR.ek L ar LBX FF sp 12288 [(v + 8, 8)] M M1).
    { apply (L5SAR.ek_piece L ar LBX FF sp 12288 [(v + 8, 8)] M M1 W1 FR1). intros a Ha Hc Ho [X|X].
      - destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK cr Aw M _ sp 12288 a HH SPT (L5SAR.aclient_appb L ar LBX (PGV8.v8_own x) FF sp 12288 a Hc))
          as [(_ & Z2)|Z2]; [apply Z2; lia| lia].
      - apply (Ho (v + 8, 8)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]. }
    assert (EK12 : L5SAR.ek L ar LBX FF sp 12288 [(v + 8, 8)] M1 M2).
    { apply (L5SAR.ek_callee L ar LBX [] FF [] sp 12288 sp 12288 [(v + 8, 8)] [] M1 M2 HP2); [lia| lia| intros a _ _ r0 []]. }
    pose proof HP2 as (_ & D2 & _).
    apply (L5SAR.ahpres_of L ar LBX FF sp 12288 [(v + 8, 8)] M M2 (L5SAR.ek_trans L ar LBX FF sp 12288 [(v + 8, 8)] M M1 M2 EK01 EK12) D2).
    apply (L5SAR.dk_trans L ar LBX FF sp 12288 M M1 M2); [apply L5SAR.dk_grows; exact MGM1|].
    apply (L5SAR.dk_callee L ar LBX [] FF [] sp 12288 sp 12288 [] M1 M2 HP2); lia.
  - apply (L5LZ.model_rt_trans model model1 model2); [exact MRT1| exact MRT2].
  - exact INCLK2.
  - exact INCAw2.
  - exact AM2.
  - rewrite OWN in HH2. exact HH2.
Qed.


End Stage.
End PNAAV8.
