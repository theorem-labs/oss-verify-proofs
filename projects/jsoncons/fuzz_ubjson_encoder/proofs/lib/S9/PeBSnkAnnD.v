(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim SeqExec StreamSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceAEx IcptIfaceAB0 L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsAB0 L5CoreAB0S9 L5StepARB0S9.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PeLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceAEx PmSpecsA PeSpecsAb PgV8 PnModel PnModelFacts PeSpecsAX PmModelFactsA PmStep PeStepAB0 PeStepB2 PmCertKitG PeBIss1 PeBEmbKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayoutB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PeSnkAnnDefs PeBSnkAnnGP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Eb0_code_rabbd4_abbd8 Eb0_code_rabc7c_abc80.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9.asan Require Import L5CoreBB0S9.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia.
Ltac nodisj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Ltac dlia := first [ solve [ L5FastLia.prune_arith; nodisj; L5FastLia.lia_ne ]
                   | solve [ L5FastLia.prune_arith; match goal with H : _ \/ _ |- _ => L5SAR.clear_disj_but H; destruct H; L5FastLia.lia_ne end ]
                   | solve [ L5FastLia.prune_arith; nodisj; L5FastLia.lia_st ]
                   | solve [ L5FastLia.prune_arith; match goal with H : _ \/ _ |- _ => L5SAR.clear_disj_but H; destruct H; L5FastLia.lia_st end ] ].
Local Ltac lia := dlia.
Module PEBSKAND.

Section Specs.
Context {SCFG_P : ScfgP}.
Variable segs : list Segment.
Variable A : pm_addrs.
Variable L : asan_layout.
Variable ar : asan_run.
Variable HI : asan_iface.
Local Abbreviation bhdr := (PESKAND.bhdr segs).
Local Abbreviation bat := (PESKAND.bat segs).

Definition entryS (R : bvmap 5 word) (M : word -> option byte) (sp r : Z) : Prop :=
  getr R 1%bv = Z_to_bv 64 r /\ L5.ra_ok r /\ getr R 2%bv = Z_to_bv 64 sp /\ getr R 3%bv = Z_to_bv 64 (pa_gp A)
  /\ getr R 4%bv = Z_to_bv 64 (hl_tp L) /\ L5CA.astk ar M sp 4096 /\ shadow_zero M (sp - 4096) 512.

Definition ann_delete_s_spec (pc : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (v b n c : Z) (sp r : Z),
    ri_inv HI ([(b, c)] ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    entryS R M sp r -> PMSPA.ffrsA FF sp ->
    getr R 10%bv = Z_to_bv 64 v -> PMSPA.aobjA FF v 24 -> v mod 8 = 0 -> PMSPA.accA M v 24 ->
    bat M v b n c ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)),
        regs_preserved R R' ->
        bhdr M' v b n c -> PMSPA.accA M' v 24 -> PMSPA.accA M' b c ->
        (forall a, b <= a < b + c -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
        L5CA.ahpres L ar LBX FF sp 4096 [] M M' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv HI ([(b, c)] ++ LBX) FF LK' cr Aw' M' (vml_of model') ->
        srealizes segs SCFG (@PMSPA.cfg segs fx' R' r M' model') K) ->
    srealizes segs SCFG (@PMSPA.cfg segs fx R pc M model) K.

Definition ann_delete_null_s_spec (pc : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (v : Z) (sp r : Z),
    ri_inv HI LBX FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    entryS R M sp r -> PMSPA.ffrsA FF sp ->
    getr R 10%bv = Z_to_bv 64 v -> PMSPA.aobjA FF v 24 -> v mod 8 = 0 -> PMSPA.accA M v 24 ->
    PGV8.v8_at segs PMSPA.accA PMSPA.annA M v PGV8.V8Null ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)),
        regs_preserved R R' ->
        PNSAX.v8_hdr segs M' v PGV8.V8Null -> PMSPA.accA M' v 24 ->
        L5CA.ahpres L ar LBX FF sp 4096 [] M M' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv HI LBX FF LK' cr Aw' M' (vml_of model') ->
        srealizes segs SCFG (@PMSPA.cfg segs fx' R' r M' model') K) ->
    srealizes segs SCFG (@PMSPA.cfg segs fx R pc M model) K.
End Specs.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).

Section Stage.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis EXT : HAJ.asan_ext_ok L ar SCFG HI PMB.EXT.
Let LYa := PMB.ly_as0 L C LY.

Theorem ann_delete_null_s_ok : ann_delete_null_s_spec RSEGS PeCLayoutB.CADDR_B L ar HI 0xab190.
Proof.
  unfold ann_delete_null_s_spec. cbn [PGV8.v8_own app].
  intros fx R M model K LBX FF LK Aw cr v sp r.
  enough (GOAL : forall (_ : unit),
    ri_inv HI (PGV8.v8_own PGV8.V8Null ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    entryS PeCLayoutB.CADDR_B L ar R M sp r -> PMSPA.ffrsA FF sp ->
    getr R 10%bv = Z_to_bv 64 v -> PMSPA.aobjA FF v 24 -> v mod 8 = 0 -> PMSPA.accA M v 24 ->
    PGV8.v8_at RSEGS PMSPA.accA PMSPA.annA M v PGV8.V8Null ->
    (forall (fx' : FPState) R' M' model' LK' Aw',
        regs_preserved R R' ->
        PNSAX.v8_hdr RSEGS M' v PGV8.V8Null -> PMSPA.accA M' v 24 ->
        (forall b n c, PGV8.V8Null = PGV8.V8Blk b n c -> PMSPA.accA M' b c) ->
        (forall b n c a, PGV8.V8Null = PGV8.V8Blk b n c -> b <= a < b + c -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
        L5CA.ahpres L ar LBX FF sp 4096 [] M M' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv HI (PGV8.v8_own PGV8.V8Null ++ LBX) FF LK' cr Aw' M' (vml_of model') ->
        srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx' R' r M' model') K) ->
    srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xab190 M model) K).
  { intros HH AM K0 ENT FRS A10 AOV V8 ACCV VEC KONT. cbn [PGV8.v8_own app] in GOAL.
    apply (GOAL tt HH AM K0 ENT FRS A10 AOV V8 ACCV VEC). intros fx' R' M' model' LK' Aw' RP HD AC _ _. exact (KONT fx' R' M' model' LK' Aw' RP HD AC). }
  intros _ HH AM K0 ENT FRS A10 AOV V8 ACCV VEC KONT.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). pose proof RAok as (Hr1 & Hr2).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof AM as (Mh & MI).
  destruct VEC as (VDEF & VACC & VB & VE & VC). cbn [PGV8.v8_own app] in HH, KONT. set (LB := LBX) in *.
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _ & _ & CB1 & CB2 & STOP & _).
  pose proof (PMKB.aobj_of_aobjA FF v 24 AOV V8) as AOB.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK cr Aw M model v 24 sp 4096 HH AOB ltac:(lia) ltac:(reflexivity)) as (OR & OBIG & ODEF & OVIS & OVSH & OCL & OCLSH).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw M model HH) as (HOFF & VIS & VIMG & VFS & VBLK' & VBSH & VFSSH & VSTSH).
  set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as ST. rewrite (L5A.aly_segs L C LYa) in ST.
  pose proof (L5A.statics_facts L C M LYa ST) as (GOT & CSB & CUAR & _).
  assert (X0 : L5.img_clear MV 1273856 1306624) by (apply L5A.img_clear_mrestrict; exact GOT).
  assert (X1 : L5.u64_at RSEGS MV 1335544 2147450880) by (apply (proj2 (L5A.u64_at_vis H M 1335544 2147450880 (VIMG 1335544 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB).
  assert (X2 : L5.u32_at RSEGS MV 1335552 1) by (apply (proj2 (L5A.u32_at_vis H M 1335552 1 (VIMG 1335552 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR).
  assert (X3 : L5.writable RSEGS MV (sp - 4096) 4096).
  { apply (proj2 (L5A.writable_vis H M (sp - 4096) 4096 (VIS (sp - 4096) 4096 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5SAR.astk_writable ar M sp 4096); [exact ASTK| lia| lia| lia]. }
  assert (X5 : L5KA.zeros_at MV (v / 8 + 2147450880) 3).
  { exact (PMKB.obj_shadow_vis L ar C HI LYa HIok LB FF LK cr Aw M model v 24 HH AOV V8 ltac:(lia) ltac:(reflexivity) ACCV). }
  assert (X6 : L5.u64_at RSEGS MV v 0) by (apply (proj2 (L5A.u64_at_vis H M v 0 ltac:(eapply L5A.avis_sub; [exact OVIS| lia| lia]) ltac:(lia) ltac:(lia))); exact VB).
  assert (X7 : L5.u64_at RSEGS MV (v + 8) 0) by (apply (proj2 (L5A.u64_at_vis H M (v + 8) _ ltac:(eapply L5A.avis_sub; [exact OVIS| lia| lia]) ltac:(lia) ltac:(lia))); exact VE).
  assert (X8 : L5.u64_at RSEGS MV (v + 16) 0) by (apply (proj2 (L5A.u64_at_vis H M (v + 16) _ ltac:(eapply L5A.avis_sub; [exact OVIS| lia| lia]) ltac:(lia) ltac:(lia))); exact VC).

  pose proof (PEBSKANGP.hkvN_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => v | _ => 0 end)) as P.
  cbn beta iota in P.
  L5SAR.feed P ltac:(first [assumption | unfold PEBSKANGP.aligned; lia | lia]).
  destruct P as (fx1 & R1 & M1v & MG1 & _ & FZ1 & MS1 & KS1 & _).
  assert (R1ra : getr R1 (reg 1) = Z_to_bv 64 r) by (rewrite (KS1 1%nat) by inl; exact Rra).
  pose proof (PMK.ret_to RSEGS fx1 R1 M1v 0xab220 W_ab1d0 r F_ab1d0 eq_refl D_ab1d0 R1ra ltac:(lia) Hr2) as MS2.
  set (W1 := fun a => sp - 32 <= a < sp - 32 + 32).
  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr Aw M model fx fx1 R 0xab190 R1 r M1v W1 K HH AM ltac:(eapply msteps_trans; [exact MS1| exact MS2]) MG1).
  { intros a Ha N. apply FZ1; [exact Ha| exact N]. }
  { intros a Ha Wa. unfold W1 in Wa. split; [|lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia]. }
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
  assert (TV : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 32 <= a < sp) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) by (intros a Ha N; apply FR1; [exact Ha| unfold W1; lia]).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK cr Aw M1 model1 v 24 sp 4096 HH1 AOB ltac:(lia) ltac:(reflexivity)) as (_ & _ & ODEF1 & _).
  apply (KONT fx1 R1 M1 model1 LK Aw).
  - apply L5SAR.preserved_by_index. intros k0 Hk. apply KS1. revert Hk. unfold L5SAR.cs_all.
    intros Hk. destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]]; inl.
  - split. { intros i Hi. rewrite TV by lia. exact (VDEF i Hi). }
    cbn. split. { apply (L5C.u64_at_agree RSEGS M M1); [intros i Hi; apply TV; lia| lia| lia| exact VB]. }
    split. { apply (L5C.u64_at_agree RSEGS M M1); [intros i Hi; apply TV; lia| lia| lia| exact VE]. }
    apply (L5C.u64_at_agree RSEGS M M1); [intros i Hi; apply TV; lia| lia| lia| exact VC].
  - apply (PMFA.accA_agree M M1 v 24); [| exact ACCV]. intros x Hx. pose proof (PNBEK.S_range x ltac:(lia)) as SRx. apply TV; lia.
  - intros b n c E. discriminate E.
  - intros b n c a E. discriminate E.
  - apply (L5SAR.ahpres_of L ar LBX FF sp 4096 _ M M1).
    + intros a (Ha & Hc & Ho). apply FR1; [exact Ha|]. unfold W1.
      destruct (L5SAR.aclient_cases L ar C HI LYa HIok LB FF LK cr Aw M _ sp 4096 a HH SPT Hc) as [Z1|Z1]; lia.
    + apply (L5.defined_grows M M1 _ _ MGM1). exact SDEF.
    + intros a Ha Hc HM. apply MGM1. exact HM.
  - exact MRT1.
  - intros f Hf. exact Hf.
  - intros q Hq. exact Hq.
  - exact AM1.
  - exact HH1.
Qed.

Theorem ann_delete_s_ok : ann_delete_s_spec RSEGS PeCLayoutB.CADDR_B L ar HI 0xab190.
Proof.
  unfold ann_delete_s_spec.
  intros fx R M model K LBX FF LK Aw cr v b n c sp r HH AM K0 ENT FRS A10 AOV V8 ACCV VEC KONT.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). pose proof RAok as (Hr1 & Hr2).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof AM as (Mh & MI).
  destruct VEC as (VDEF & VACC & VB & VE & VC & NC & C27 & B4096 & B16 & BDEF & BACC & BANN).
  set (LB := [(b, c)] ++ LBX) in *.
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _ & _ & CB1 & CB2 & STOP & _).
  assert (BIN : In (b, c) LB) by (left; reflexivity).
  destruct (PNBEK.blk_facts L ar C HI LY HIok _ FF LK cr Aw M _ b (c) HH BIN) as (Bq0 & Bq1 & Bq2 & Bq3 & _ & Bq5 & Bq6 & _ & Bq8).
  pose proof (PMKB.aobj_of_aobjA FF v 24 AOV V8) as AOB.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK cr Aw M model v 24 sp 4096 HH AOB ltac:(lia) ltac:(reflexivity)) as (OR & OBIG & ODEF & OVIS & OVSH & OCL & OCLSH).
  assert (VBLK : v + 24 <= b \/ b + c <= v).
  { destruct AOV as (f & Hf & Y1 & Y2). destruct (Bq8 f Hf) as [Y|Y]; [right; lia| left; lia]. }
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw M model HH) as (HOFF & VIS & VIMG & VFS & VBLK' & VBSH & VFSSH & VSTSH).
  set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as ST. rewrite (L5A.aly_segs L C LYa) in ST.
  pose proof (L5A.statics_facts L C M LYa ST) as (GOT & CSB & CUAR & _).
  assert (X0 : L5.img_clear MV 1273856 1306624) by (apply L5A.img_clear_mrestrict; exact GOT).
  assert (X1 : L5.u64_at RSEGS MV 1335544 2147450880) by (apply (proj2 (L5A.u64_at_vis H M 1335544 2147450880 (VIMG 1335544 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB).
  assert (X2 : L5.u32_at RSEGS MV 1335552 1) by (apply (proj2 (L5A.u32_at_vis H M 1335552 1 (VIMG 1335552 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR).
  assert (X3 : L5.writable RSEGS MV (sp - 4096) 4096).
  { apply (proj2 (L5A.writable_vis H M (sp - 4096) 4096 (VIS (sp - 4096) 4096 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5SAR.astk_writable ar M sp 4096); [exact ASTK| lia| lia| lia]. }
  assert (X5 : L5KA.zeros_at MV (v / 8 + 2147450880) 3).
  { exact (PMKB.obj_shadow_vis L ar C HI LYa HIok LB FF LK cr Aw M model v 24 HH AOV V8 ltac:(lia) ltac:(reflexivity) ACCV). }
  assert (X6 : L5.u64_at RSEGS MV v b) by (apply (proj2 (L5A.u64_at_vis H M v b ltac:(eapply L5A.avis_sub; [exact OVIS| lia| lia]) ltac:(lia) ltac:(lia))); exact VB).
  assert (X7 : L5.u64_at RSEGS MV (v + 8) (b + n)) by (apply (proj2 (L5A.u64_at_vis H M (v + 8) _ ltac:(eapply L5A.avis_sub; [exact OVIS| lia| lia]) ltac:(lia) ltac:(lia))); exact VE).
  assert (X8 : L5.u64_at RSEGS MV (v + 16) (b + c)) by (apply (proj2 (L5A.u64_at_vis H M (v + 16) _ ltac:(eapply L5A.avis_sub; [exact OVIS| lia| lia]) ltac:(lia) ltac:(lia))); exact VC).

  pose proof (PEBSKANGP.hkvA_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => v | 36%nat => b | 37%nat => n | 41%nat => c | _ => 0 end)) as P.
  cbn beta iota in P.
  L5SAR.feed P ltac:(first [assumption | unfold PEBSKANGP.aligned; lia | lia]).
  destruct P as (fx1 & R1 & M1v & MG1 & _ & FZ1 & MS1 & KS1 & fR1 & fR2 & fR10 & fR11 & fR12 & fR13 & fR14 & fR15 & fR16 & T16 & T8).
  set (W1 := fun a => sp - 32 <= a < sp - 32 + 32).
  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr Aw M model fx fx1 R 0xab190 R1 0x7cc28 M1v W1 K HH AM MS1 MG1).
  { intros a Ha N. apply FZ1; [exact Ha| exact N]. }
  { intros a Ha Wa. unfold W1 in Wa. split; [|lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia]. }
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
  pose proof AM1 as (Mh1 & MI1).
  assert (SH01 : forall x, 0 <= x < 2 ^ 64 -> x < sp - 32 -> M1 (Z_to_bv 64 x) = M (Z_to_bv 64 x)) by (intros x Hx Hx'; apply FR1; [exact Hx| unfold W1; lia]).

  pose proof (HAJ.aex_annotate _ _ _ _ _ EXT) as ANN. unfold HAJ.annotate_spec in ANN.
  cbn [PMB.EXT HAJ.ec_ann_pc HAJ.ec_ann_scr paa_annotate PMB.AAD AADDR_A] in ANN. rewrite (L5A.aly_segs L C LYa) in ANN.
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
  { apply (PNBEK.ann_agree M M1 b (n) (c)); [| lia| lia| exact BANN].
    intros j Hj. pose proof (PNBEK.shadow_lowU b c j ltac:(lia) ltac:(lia) Hj) as SL. apply SH01; lia. }
  { rewrite L5K.rl4, (KS1 4%nat) by inl. exact Rtp. }
  { rewrite L5K.rl1, fR1. vm_compute. reflexivity. }
  { rewrite L5K.rl2, fR2, L5.unsigned_lit by lia.
    apply (L5SAR.astack_ok_of_astk L ar C LYa M M1 sp 4096 16 2304 ASTK MGM1); [lia| lia| lia|].
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
  assert (ASTK2 : L5CA.astk ar M2 sp 4096).
  { apply (L5SAR.astk_after_eq L ar C HI HIok LB FF LK cr Aw M M1 M2 _ sp 4096 (sp - 16) 2304 HH ASTK MGM1).
    - intros a Ha Hs Hns. apply KEEP2; [exact Ha| apply L5SAR.stack_client; [exact Hs| exact Hns]|].
      intros X. pose proof (PNBEK.in_shadow_range b (c) a ltac:(lia) ltac:(lia) X). lia.
    - exact SCR2.
    - lia. - lia. - lia. }
  assert (Y3 : L5.writable RSEGS MV2 (sp - 4096) 4096).
  { apply (proj2 (L5A.writable_vis H2 M2 (sp - 4096) 4096 (VIS2 (sp - 4096) 4096 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5SAR.astk_writable ar M2 sp 4096); [exact ASTK2| lia| lia| lia]. }

  assert (TS : forall a v0, sp - 16 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1v a v0 -> L5.u64_at RSEGS MV2 a v0).
  { intros a v0 Ha Ha' X. apply (proj2 (L5A.u64_at_vis H2 M2 a v0 (VIS2 a 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply KEEP2; [lia| apply L5SAR.stack_client; lia|]| lia| lia|].
    - intros XS. pose proof (PNBEK.in_shadow_range b (c) i ltac:(lia) ltac:(lia) XS). lia.
    - apply (PMBIS1.vis_u64 _ _ _ _ _ VIS1); [apply VIS; lia| lia| lia| exact X]. }
  pose proof (TS (sp - 8) _ ltac:(lia) ltac:(lia) T8) as Z8.
  pose proof (TS (sp - 16) _ ltac:(lia) ltac:(lia) T16) as Z16.
  assert (J2 : getr R2 (reg 2) = Z_to_bv 64 (sp - 16)) by (rewrite CS2 by inl; exact fR2).
  pose proof (PMBIS1.bvu (getr R (reg 1))) as UR1. pose proof (PMBIS1.bvu (getr R (reg 8))) as UR8.

  pose proof (PEBSKANGP.hkvB_conc fx2 R2 MV2 (fun j => match j with 2%nat => sp | 43%nat => bv_unsigned (getr R (reg 1)) | 44%nat => bv_unsigned (getr R (reg 8)) | _ => 0 end)) as P.
  cbn beta iota in P.
  L5SAR.feed P ltac:(first [assumption | unfold PEBSKANGP.aligned; lia | lia]).
  destruct P as (fx3 & R3 & M3v & MG3 & _ & FZ3 & MS3 & KS3 & gR1 & gR2 & gR8).
  assert (R3ra : getr R3 (reg 1) = Z_to_bv 64 r) by (rewrite gR1, Z_to_bv_bv_unsigned; exact Rra).
  pose proof (PMK.ret_to RSEGS fx3 R3 M3v 0xab220 W_ab1d0 r F_ab1d0 eq_refl D_ab1d0 R3ra ltac:(lia) Hr2) as MS4.
  set (W3 := fun a : Z => False).
  apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr Aw2 M2 model2 fx2 fx3 R2 0xab214 R3 r M3v W3 K HH2 AM2 ltac:(eapply msteps_trans; [exact MS3| exact MS4]) MG3).
  { intros a Ha N. apply FZ3; exact Ha. }
  { intros a Ha Wa. destruct Wa. }
  intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3.
  assert (TW3 : forall a, 0 <= a < 2 ^ 64 -> M3 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)) by (intros a Ha; apply FR3; [exact Ha| intros []]).
  assert (TB : forall a, b <= a < b + c -> M3 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha. rewrite TW3 by lia. apply T20; [lia| | lia|].
    - unfold aclient, aclient_g. left. exists (b, c). split; [exact BIN| cbn [fst snd]; lia].
    - intros X. pose proof (PNBEK.in_shadow_range b (c) a ltac:(lia) ltac:(lia) X). lia. }

  apply (KONT fx3 R3 M3 model3 LK Aw2).
  - apply L5SAR.preserved_by_index. intros k0 Hk.
    assert (CH : forall k', In k' [3; 4; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R3 (reg k') = getr R (reg k')).
    { intros k' Hk'. assert (Y : In k' PEBSKANGP.KS_hkvB /\ In k' L5SAR.cs_all /\ In k' PEBSKANGP.KS_hkvA)
        by (destruct Hk' as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]; (split; [inl| split; inl])).
      destruct Y as (Yk1 & Yk2 & Yk3). rewrite (KS3 k' Yk1), (CS2 k' Yk2), (KS1 k' Yk3). reflexivity. }
    unfold L5SAR.cs_all in Hk. destruct Hk as [<-|[<-|[<-|[<-|Hk]]]].
    + rewrite gR2. exact (eq_sym Rsp).
    + apply CH; left; reflexivity.
    + apply CH; right; left; reflexivity.
    + rewrite gR8, Z_to_bv_bv_unsigned; reflexivity.
    + apply CH. destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]; inl.
  -
    assert (TV : forall a, v <= a < v + 24 -> M3 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha. rewrite TW3 by lia. apply T20; [lia| apply (L5SAR.obj_client L ar LB FF 0 0 v 24 a AOB); lia| lia|].
      intros X. pose proof (PNBEK.in_shadow_range b c a ltac:(lia) ltac:(lia) X). lia. }
    split. { intros i Hi. rewrite TV by lia. exact (VDEF i Hi). }
    split. { apply (L5C.u64_at_agree RSEGS M M3); [intros i Hi; apply TV; lia| lia| lia| exact VB]. }
    split. { apply (L5C.u64_at_agree RSEGS M M3); [intros i Hi; apply TV; lia| lia| lia| exact VE]. }
    split. { apply (L5C.u64_at_agree RSEGS M M3); [intros i Hi; apply TV; lia| lia| lia| exact VC]. }
    split; [lia|]. split; [lia|]. split; [lia|]. split; [exact B16|].
    intros i Hi. rewrite TB by lia. exact (BDEF i Hi).
  - apply (PMFA.accA_agree M M3 v 24); [| exact ACCV]. intros x Hx. pose proof (PNBEK.S_range x ltac:(lia)) as SRx.
    rewrite TW3 by lia. apply T20; [lia| | lia|].
    + exact (PNBEK.frame_sh_client L ar FF v 24 x LB 0 0 AOV Hx).
    + apply (PNBEK.sh_apartU b c x v); lia.
  -     destruct ANN2 as (ZA2 & PZ2 & _). unfold PMSPA.accA. apply (PMFA.accA_agree M2 M3 b c).
    + intros x Hx. apply TW3. pose proof (PNBEK.S_range x ltac:(lia)). lia.
    + apply (L5CB.aacc_of_blk M2 b c b c (conj ZA2 PZ2)); lia.
  - intros a Ha. apply TB. exact Ha.
  - apply (L5SAR.ahpres_of L ar LBX FF sp 4096 _ M M3).
    + intros a (Ha & Hc & Ho).
      assert (HcB : aclient L ar LB FF sp 4096 a) by (apply (L5SAR.aclient_appb L ar LBX [(b, c)] FF sp 4096 a Hc)).
      assert (NS : ~ in_shadow_of b (c) a) by (exact (PNBEK.own_sh_notclientU L ar C HI LY HIok b (c) LBX FF LK cr Aw M _ HH a sp 4096 Hc)).
      rewrite TW3 by exact Ha. rewrite (KEEP2 a Ha); [| apply (L5SAR.aclient_mono L ar LB FF sp 4096 (sp - 16) 2304 a HcB); intros x Hx; lia| exact NS].
      destruct (L5SAR.aclient_cases L ar C HI LYa HIok LB FF LK cr Aw M _ sp 4096 a HH SPT HcB) as [Z1|Z1];
        (apply FR1; [exact Ha| unfold W1; lia]).
    + pose proof ASTK2 as (_ & _ & _ & _ & SD2 & _). apply (L5.defined_grows M2 M3 _ _ MGM3). exact SD2.
    + intros a Ha Hc HM. apply MGM3.
      assert (HcB : aclient L ar LB FF sp 4096 a) by (apply (L5SAR.aclient_appb L ar LBX [(b, c)] FF sp 4096 a Hc)).
      assert (NS : ~ in_shadow_of b (c) a) by (exact (PNBEK.own_sh_notclientU L ar C HI LY HIok b (c) LBX FF LK cr Aw M _ HH a sp 4096 Hc)).
      rewrite (KEEP2 a Ha); [| apply (L5SAR.aclient_mono L ar LB FF sp 4096 (sp - 16) 2304 a HcB); intros x Hx; lia| exact NS].
      apply MGM1. exact HM.
  - apply (L5LZ.model_rt_trans model model2 model3); [|exact MRT3]. apply (L5LZ.model_rt_trans model model1 model2); [exact MRT1| exact MRT2].
  - intros x Hx. exact Hx.
  - exact INC2.
  - exact AM3.
  - exact HH3.
Qed.

End Stage.
End PEBSKAND.
