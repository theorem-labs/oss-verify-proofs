(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality Permutation.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs PmParSpecs PmTxtSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PmSpecsAX_b PnSpecsAa_b
     PmModelFactsA_b PnStepA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnASrcKit_b PnASrcReadK_b PnAReset1_b PnAEmbKit_b PnAVu8Dtor_b PnAVu8GrowP_b Ba0_code_b404c_b4050_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgV8A_b PgV8KitA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b PnSpecsAX_b PnSpecsAX8_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0PgVu8ApK_b.

Module PGVAPG.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation AD := PMA.AD.
Abbreviation v8_atA := (PGV8.v8_at RSEGS PMSPA.accA PGV8A.annA).

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMA.ly_as0 L C LY.

Section Call.
Variables (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet) (LB : list (Z * Z)) (FF LK0 : list fframe) (Aw0 : list (Z * Z)) (cr0 : credit).
Variables (v S r g k : Z) (x : PGV8.v8).
Hypothesis Rra0 : getr R0 (reg 1) = Z_to_bv 64 r.
Hypothesis RAok : L5.ra_ok r.
Hypothesis Rsp0 : getr R0 (reg 2) = Z_to_bv 64 S.
Hypothesis Rgp0 : getr R0 (reg 3) = Z_to_bv 64 (pa_gp AD).
Hypothesis Rtp0 : getr R0 (reg 4) = Z_to_bv 64 (hl_tp L).
Hypothesis K0 : K [].
Hypothesis FRS : PMSPA.ffrsA FF S.
Hypothesis AO : PMSPA.aobjA FF v 24.
Hypothesis V8 : v mod 8 = 0.
Hypothesis OK0 : PGV8.v8_ok x g.
Hypothesis Hk : 1 <= k.
Hypothesis GROK : PGV8.v8_grow_ok x (PGV8.v8_size x + k).
Hypothesis CRL0 : PMSP.credit_le (PMSPA.scA L (PGV8.pot_v8 (PMSPA.HV L ar) x g)) cr0.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (x' : PGV8.v8) (g' : Z) (cr' : credit),
  regs_preserved R0 R' -> v8_atA M' v x' -> PGV8.v8_size x' = PGV8.v8_size x + k -> PGV8.v8_ok x' g' ->
  PGV8.v8_cap x <= PGV8.v8_cap x' ->
  (PGV8.v8_size x' <= PGV8.v8_cap x -> PGV8.v8_own x' = PGV8.v8_own x /\ PGV8.v8_cap x' = PGV8.v8_cap x /\ g' = g) ->
  (PGV8.v8_cap x' = PGV8.v8_cap x \/ PGV8.v8_cap x' = Z.max (2 * PGV8.v8_cap x) (PGV8.v8_size x + k)) ->
  L5CA.ahpres L ar LB FF S (PMSPA.pm_scr 1) [(v, 24)] M0 M' ->
  PMSP.credit_keep cr0 cr' (PMSPA.scA L (PGV8.pot_v8 (PMSPA.HV L ar) x g)) (PMSPA.scA L (PGV8.pot_v8 (PMSPA.HV L ar) x' g')) ->
  model_rt model0 model' -> incl LK' LK0 -> incl Aw0 Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (PGV8.v8_own x' ++ LB) FF LK' cr' Aw' M' (vml_of model') ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K.
(* [comment removed for export] *)
Hypothesis OPN : PMA.opnew_spec L ar HI.
Hypothesis OPD : PMA.opdel_spec L ar HI.
Hypothesis ANNI : PNSAX8.ann_increase_v8_spec RSEGS AD L ar HI 0xb609c.
Hypothesis ANNN : PNSAX8.ann_new_v8_spec RSEGS AD L ar HI 0xb615c.
Hypothesis ANND : PNSAX.ann_delete_v8_spec RSEGS AD L ar HI 0xabb8c.
(* [comment removed for export] *)
Hypothesis VS0 : v8_atA M0 v x.
Hypothesis HH0 : ri_inv HI (PGV8.v8_own x ++ LB) FF LK0 cr0 Aw0 M0 (vml_of model0).
(* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis Ra0 : getr R0 (reg 10) = Z_to_bv 64 v.
Hypothesis Ra1 : getr R0 (reg 11) = Z_to_bv 64 k.
Hypothesis AM0 : L5CA.amodel_ok Aw0 model0.
Hypothesis STK0 : L5CA.astk ar M0 S 14336.
Hypothesis STKSH0 : shadow_zero M0 (S - 14336) 1792.

#[local] Abbreviation U := (PGVAPK.U R0).
#[local] Abbreviation saves := (PGVAPK.saves R0 S).
#[local] Abbreviation kept0 := (PGVAPK.kept0 R0).
#[local] Abbreviation stok := (PGVAPK.stok model0 LK0 Aw0).
#[local] Abbreviation mem_ok := (PGVAPK.mem_ok L ar M0 LB FF v S).
#[local] Abbreviation post_ok := (PGVAPK.post_ok L ar cr0 g k x).
#[local] Abbreviation gbuf := (PGVAPK.gbuf S).
#[local] Abbreviation hdr := (PGVAPK.hdr v).
#[local] Abbreviation finish_p := (PGVAPK.finish_p L ar C HI LY HIok R0 M0 model0 K LB FF LK0 Aw0 cr0 v S r g k x Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRS AO V8 OK0 Hk GROK CRL0 KONT OPN OPD ANNI ANNN ANND VS0 HH0 Ra0 Ra1 AM0 STK0 STKSH0).
#[local] Abbreviation piece_step := (PGVAPK.piece_step L ar C HI LY HIok R0 M0 model0 K LB FF LK0 Aw0 cr0 v S r g k x Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRS AO V8 OK0 Hk GROK CRL0 KONT OPN OPD ANNI ANNN ANND VS0 HH0 Ra0 Ra1 AM0 STK0 STKSH0).
#[local] Abbreviation piece_ro := (PGVAPK.piece_ro L ar C HI LY HIok R0 M0 model0 K LB FF LK0 Aw0 cr0 v S r g k x Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRS AO V8 OK0 Hk GROK CRL0 KONT OPN OPD ANNI ANNN ANND VS0 HH0 Ra0 Ra1 AM0 STK0 STKSH0).
#[local] Abbreviation nfacts := (PGVAPK.nfacts L ar C HI LY HIok R0 M0 model0 K LB FF LK0 Aw0 cr0 v S r g k x Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRS AO V8 OK0 Hk GROK CRL0 KONT OPN OPD ANNI ANNN ANND VS0 HH0 Ra0 Ra1 AM0 STK0 STKSH0).
#[local] Abbreviation vfacts := (PGVAPK.vfacts L ar C HI LY HIok R0 M0 model0 K LB FF LK0 Aw0 cr0 v S r g k x Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRS AO V8 OK0 Hk GROK CRL0 KONT OPN OPD ANNI ANNN ANND VS0 HH0 Ra0 Ra1 AM0 STK0 STKSH0).
#[local] Abbreviation cell_callee := (PGVAPK.cell_callee L ar C HI LY HIok R0 M0 model0 K LB FF LK0 Aw0 cr0 v S r g k x Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRS AO V8 OK0 Hk GROK CRL0 KONT OPN OPD ANNI ANNN ANND VS0 HH0 Ra0 Ra1 AM0 STK0 STKSH0).
#[local] Abbreviation saves_callee := (PGVAPK.saves_callee L ar C HI LY HIok R0 M0 model0 K LB FF LK0 Aw0 cr0 v S r g k x Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRS AO V8 OK0 Hk GROK CRL0 KONT OPN OPD ANNI ANNN ANND VS0 HH0 Ra0 Ra1 AM0 STK0 STKSH0).
#[local] Abbreviation mem_ok_callee := (PGVAPK.mem_ok_callee L ar C HI LY HIok R0 M0 model0 K LB FF LK0 Aw0 cr0 v S r g k x Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRS AO V8 OK0 Hk GROK CRL0 KONT OPN OPD ANNI ANNN ANND VS0 HH0 Ra0 Ra1 AM0 STK0 STKSH0).
#[local] Abbreviation cstk := (PGVAPK.cstk L ar C HI LY HIok R0 M0 model0 K LB FF LK0 Aw0 cr0 v S r g k x Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRS AO V8 OK0 Hk GROK CRL0 KONT OPN OPD ANNI ANNN ANND VS0 HH0 Ra0 Ra1 AM0 STK0 STKSH0).
#[local] Abbreviation xnum := (PGVAPK.xnum L ar C HI LY HIok R0 M0 model0 K LB FF LK0 Aw0 cr0 v S r g k x Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRS AO V8 OK0 Hk GROK CRL0 KONT OPN OPD ANNI ANNN ANND VS0 HH0 Ra0 Ra1 AM0 STK0 STKSH0).
#[local] Abbreviation xr := (PGVAPK.xr L ar C HI LY HIok R0 M0 model0 K LB FF LK0 Aw0 cr0 v S r g k x Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRS AO V8 OK0 Hk GROK CRL0 KONT OPN OPD ANNI ANNN ANND VS0 HH0 Ra0 Ra1 AM0 STK0 STKSH0).
#[local] Abbreviation v8_at_agree := (PGVAPK.v8_at_agree L ar C HI LY HIok R0 M0 model0 K LB FF LK0 Aw0 cr0 v S r g k x Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRS AO V8 OK0 Hk GROK CRL0 KONT OPN OPD ANNI ANNN ANND VS0 HH0 Ra0 Ra1 AM0 STK0 STKSH0).
#[local] Abbreviation v8_case := (PGVAPK.v8_case L ar C HI LY HIok R0 M0 model0 K LB FF LK0 Aw0 cr0 v S r g k x Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRS AO V8 OK0 Hk GROK CRL0 KONT OPN OPD ANNI ANNN ANND VS0 HH0 Ra0 Ra1 AM0 STK0 STKSH0).
#[local] Abbreviation kept0_of := (PGVAPK.kept0_of L ar C HI LY HIok R0 M0 model0 K LB FF LK0 Aw0 cr0 v S r g k x Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRS AO V8 OK0 Hk GROK CRL0 KONT OPN OPD ANNI ANNN ANND VS0 HH0 Ra0 Ra1 AM0 STK0 STKSH0).
#[local] Abbreviation kept0_pres := (PGVAPK.kept0_pres L ar C HI LY HIok R0 M0 model0 K LB FF LK0 Aw0 cr0 v S r g k x Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRS AO V8 OK0 Hk GROK CRL0 KONT OPN OPD ANNI ANNN ANND VS0 HH0 Ra0 Ra1 AM0 STK0 STKSH0).
#[local] Abbreviation stok_step := (PGVAPK.stok_step L ar C HI LY HIok R0 M0 model0 K LB FF LK0 Aw0 cr0 v S r g k x Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRS AO V8 OK0 Hk GROK CRL0 KONT OPN OPD ANNI ANNN ANND VS0 HH0 Ra0 Ra1 AM0 STK0 STKSH0).
#[local] Abbreviation centry0 := (PGVAPK.centry0 L ar C HI LY HIok R0 M0 model0 K LB FF LK0 Aw0 cr0 v S r g k x Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRS AO V8 OK0 Hk GROK CRL0 KONT OPN OPD ANNI ANNN ANND VS0 HH0 Ra0 Ra1 AM0 STK0 STKSH0).
#[local] Abbreviation cell_piece := (PGVAPK.cell_piece L ar C HI LY HIok R0 M0 model0 K LB FF LK0 Aw0 cr0 v S r g k x Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRS AO V8 OK0 Hk GROK CRL0 KONT OPN OPD ANNI ANNN ANND VS0 HH0 Ra0 Ra1 AM0 STK0 STKSH0).
#[local] Abbreviation saves_piece := (PGVAPK.saves_piece L ar C HI LY HIok R0 M0 model0 K LB FF LK0 Aw0 cr0 v S r g k x Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRS AO V8 OK0 Hk GROK CRL0 KONT OPN OPD ANNI ANNN ANND VS0 HH0 Ra0 Ra1 AM0 STK0 STKSH0).
#[local] Abbreviation wob := (PGVAPK.wob L ar C HI LY HIok R0 M0 model0 K LB FF LK0 Aw0 cr0 v S r g k x Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRS AO V8 OK0 Hk GROK CRL0 KONT OPN OPD ANNI ANNN ANND VS0 HH0 Ra0 Ra1 AM0 STK0 STKSH0).

Ltac pfeed XW XSZ XAV :=
  first [ assumption
        | lazymatch goal with
          | |- L5.u64_at _ (mrestrict ?H ?M) ?a ?val => apply (proj2 (L5A.u64_at_vis H M a val (XAV a 8 ltac:(lia)) ltac:(lia) ltac:(lia))); assumption
          | |- L5.writable _ _ _ _ => apply XW; lia
          | |- L5KA.zeros_at _ (?s / 8 + ?c) ?n => first [apply XSZ; lia
              | let Z := fresh in pose proof (XSZ (s - 8 * n) n ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Z;
                lazymatch type of Z with L5KA.zeros_at _ ?e _ => replace (s / 8 + c) with e by lia; exact Z end]
          | |- L5KA.zeros_at _ _ _ => apply XSZ; lia
          | |- PMAVGP.aligned _ _ => unfold PMAVGP.aligned; lia
          | |- _ => lia
          end ].

Definition sw_pcB : Z := 0xb5cfc.
Definition sw_pcC : Z := 0xb5d74.

Definition ssaves (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M (S - 72) 0xb58c0 /\ L5.u64_at RSEGS M (S - 80) v /\ L5.u64_at RSEGS M (S - 88) k /\ L5.u64_at RSEGS M (S - 96) (U 18)
  /\ L5.u64_at RSEGS M (S - 104) (U 19) /\ L5.u64_at RSEGS M (S - 112) (U 20) /\ L5.u64_at RSEGS M (S - 120) (U 21)
  /\ L5.u64_at RSEGS M (S - 128) (U 22) /\ L5.u64_at RSEGS M (S - 136) (U 23) /\ L5.u64_at RSEGS M (S - 144) (U 24).

Lemma tail_J (fx : FPState) R M model LK Aw x' g' cr' :
  getr R (reg 2) = Z_to_bv 64 (S - 64) -> getr R (reg 8) = Z_to_bv 64 v -> getr R (reg 9) = Z_to_bv 64 k ->
  (forall i, In i [18; 19; 20; 21]%nat -> getr R (reg i) = Z_to_bv 64 (U i)) -> kept0 R ->
  stok model LK Aw -> mem_ok M -> saves M -> L5.u64_at RSEGS M (S - 32) v ->
  gbuf M (PGV8.v8_data x) (PGV8.v8_data x) (PGV8.v8_data x) (PGV8.v8_data x + PGV8.v8_cap x) ->
  ri_inv HI (PGV8.v8_own x' ++ LB) FF LK cr' Aw M (vml_of model) -> v8_atA M v x' -> post_ok x' g' cr' ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0xb58c8 M model) K.
Proof using All.
  intros E2 E8 E9 ER KP SO MO SV S32 (G64 & G56 & G48 & G40) HH VS PO.
  destruct (nfacts _ LK cr' Aw M model HH MO) as ((A16 & SLO & SHI & SPT & C0) & (O1 & O2 & O5 & ODEF) & BF). unfold PGVAPK.nsh in O5.
  destruct (vfacts _ LK cr' Aw M model HH MO) as (X0 & X1 & X2 & XW & XZ & XWV & XSZ & XAV).
  pose proof SV as (S8 & S16 & S24). pose proof xnum as (XD & XS & XC & K27 & XSK & XDC).
  assert (UB : forall i, 0 <= U i < 2 ^ 64) by (intros i; unfold U; apply bv_unsigned_in_range).
  pose proof (UB 1%nat) as UB1. pose proof (UB 8%nat) as UB8. pose proof (UB 9%nat) as UB9.
  pose proof (UB 18%nat) as UB18. pose proof (UB 19%nat) as UB19. pose proof (UB 20%nat) as UB20. pose proof (UB 21%nat) as UB21.
  pose proof (ER 18%nat ltac:(inl)) as R18. pose proof (ER 19%nat ltac:(inl)) as R19. pose proof (ER 20%nat ltac:(inl)) as R20. pose proof (ER 21%nat ltac:(inl)) as R21.
  LeanFeed.pfeed PP (PMAVGP.avaJ_conc fx R (mrestrict (ahid Aw model) M) (fun j => match j with 2%nat => S | 37%nat => v | 40%nat => PGV8.v8_data x | 42%nat => PGV8.v8_cap x | 43%nat => k
     | 48%nat => U 1 | 49%nat => U 8 | 50%nat => U 9 | 51%nat => U 18 | 52%nat => U 19 | 53%nat => U 20 | 54%nat => U 21 | _ => 0 end)) ltac:(pfeed XW XSZ XAV).
  destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & A1 & A2 & A8 & A9).
  apply (piece_ro fx fx1 R 0xb58c8 R1 0xb58d8 _ M model cr' LK Aw M1v HH SO MO MS1 MG1 FRZ1). intros model1 HH1 SO1.
  apply (finish_p fx1 R1 M model1 LK Aw x' g' cr' 0xb58d8 W_b404c F_b404c eq_refl D_b404c A1 A2); try assumption.
  - intros i Hi. cbn in Hi. destruct Hi as [<-|[<-|Hi]]; [exact A8| exact A9|].
    rewrite KS1 by (clear - Hi; cbn in Hi; repeat (destruct Hi as [<-|Hi]; [inl|]); destruct Hi). apply ER. exact Hi.
  - apply (kept0_of R R1 KP). intros i Hi. apply KS1. clear - Hi. cbn in Hi. repeat (destruct Hi as [<-|Hi]; [inl|]). destruct Hi.
Qed.

Lemma tail_I (fx : FPState) R M model LK Aw cr B A g' :
  getr R (reg 2) = Z_to_bv 64 (S - 64) -> getr R (reg 8) = Z_to_bv 64 v -> getr R (reg 9) = Z_to_bv 64 k ->
  (forall i, In i [18; 19; 20; 21]%nat -> getr R (reg i) = Z_to_bv 64 (U i)) -> kept0 R ->
  stok model LK Aw -> mem_ok M -> saves M -> L5.u64_at RSEGS M (S - 32) v ->
  ri_inv HI (((B, A) :: PGV8.v8_own x) ++ LB) FF LK cr Aw M (vml_of model) ->
  v8_atA M v (PGV8.V8Blk B (PGV8.v8_size x + k) A) ->
  gbuf M (PGV8.v8_data x) (PGV8.v8_data x) (PGV8.v8_data x) (PGV8.v8_data x + PGV8.v8_cap x) ->
  post_ok (PGV8.V8Blk B (PGV8.v8_size x + k) A) g' cr ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0xb58c0 M model) K.
Proof using All.
  intros E2 E8 E9 ER KP SO MO SV S32 HH VS (G64 & G56 & G48 & G40) PO.
  destruct (nfacts _ LK cr Aw M model HH MO) as ((A16 & SLO & SHI & SPT & C0) & (O1 & O2 & O5 & ODEF) & BF). unfold PGVAPK.nsh in O5.
  destruct (vfacts _ LK cr Aw M model HH MO) as (X0 & X1 & X2 & XW & XZ & XWV & XSZ & XAV).
  destruct (BF B A ltac:(left; reflexivity)) as (QB0 & QB1 & QB2 & QB4 & QB5 & QB6 & QBD).
  pose proof SV as (S8 & S16 & S24). pose proof xnum as (XD & XS & XC & K27 & XSK & XDC). pose proof xr as XR.
  assert (UB : forall i, 0 <= U i < 2 ^ 64) by (intros i; unfold U; apply bv_unsigned_in_range).
  pose proof (UB 1%nat) as UB1. pose proof (UB 8%nat) as UB8. pose proof (UB 9%nat) as UB9.
  pose proof (UB 18%nat) as UB18. pose proof (UB 19%nat) as UB19. pose proof (UB 20%nat) as UB20. pose proof (UB 21%nat) as UB21.
  pose proof (ER 18%nat ltac:(inl)) as R18. pose proof (ER 19%nat ltac:(inl)) as R19. pose proof (ER 20%nat ltac:(inl)) as R20. pose proof (ER 21%nat ltac:(inl)) as R21.
  LeanFeed.pfeed PP (PMAVGP.avaI_conc fx R (mrestrict (ahid Aw model) M) (fun j => match j with 2%nat => S | 37%nat => v | 40%nat => PGV8.v8_data x | 42%nat => PGV8.v8_cap x | 43%nat => k
     | 48%nat => U 1 | 49%nat => U 8 | 50%nat => U 9 | 51%nat => U 18 | 52%nat => U 19 | 53%nat => U 20 | 54%nat => U 21 | _ => 0 end)) ltac:(pfeed XW XSZ XAV).
  destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & [(MS1 & KS1 & A1 & A10 & A11 & _ & _ & _ & _ & _ & _ & NZ & _ & C8 & C16 & C24 & C32 & C40 & C48 & C56 & C64)
    |(MS1 & KS1 & A1 & A2 & A8 & A9 & _ & _ & _ & _ & _ & _ & _ & _ & ZZ & _ & C8 & C16 & C24 & C32 & C40 & C48 & C56 & C64)]).
  - apply (piece_step fx fx1 R 0xb58c0 R1 0xd39ac _ M model cr LK Aw M1v (fun a => S - 128 <= a < S - 128 + 128) HH SO MO MS1 MG1 FRZ1);
      [intros a Pa; cbv beta in Pa; left; lia|].
    intros M1 model1 HH1 SO1 MO1 FR1 VUP AGS.
    pose proof (VUP (S - 8) (U 1) ltac:(left; lia) C8) as S8'. pose proof (VUP (S - 16) (U 8) ltac:(left; lia) C16) as S16'.
    pose proof (VUP (S - 24) (U 9) ltac:(left; lia) C24) as S24'. pose proof (VUP (S - 32) v ltac:(left; lia) C32) as S32'.
    pose proof (VUP (S - 40) (PGV8.v8_data x + PGV8.v8_cap x) ltac:(left; lia) C40) as G40'.
    pose proof (VUP (S - 48) (PGV8.v8_data x) ltac:(left; lia) C48) as G48'.
    pose proof (VUP (S - 56) (PGV8.v8_data x) ltac:(left; lia) C56) as G56'.
    pose proof (VUP (S - 64) (PGV8.v8_data x) ltac:(left; lia) C64) as G64'.
    assert (SV1 : saves M1) by (split; [exact S8'|]; split; [exact S16'| exact S24']).
    destruct (nfacts _ LK cr Aw M1 model1 HH1 MO1) as (_ & (_ & _ & _ & ODEF1) & BF1).
    assert (VS1 : v8_atA M1 v (PGV8.V8Blk B (PGV8.v8_size x + k) A)).
    { apply (v8_at_agree M M1 _ VS ODEF1); [| | lia| lia|].
      - intros i Hi. apply FR1; cbv beta; lia.
      - apply AGS; lia.
      - intros b' n' c' E. injection E as <- <- <-. destruct (BF1 B A ltac:(left; reflexivity)) as (_ & _ & _ & _ & _ & _ & QBD1).
        split; [exact QBD1| apply AGS; lia]. }
    destruct (v8_case x) as [EX|(b & n & c & EX)].
    { exfalso. rewrite EX in NZ. cbn [PGV8.v8_data] in NZ. rewrite Z.sub_0_r, Z.mod_0_l in NZ by lia. lia. }
    rewrite EX in XR, NZ, HH1, A10. cbn [PGV8.v8_data PGV8.v8_cap PGV8.v8_size PGV8.v8_own] in XR, NZ, HH1, A10.
    destruct XR as (Hn & Hc & Hb & Hb16 & Hbc).
    pose proof SO1 as (AM1 & MRT1 & ILK1 & IAW1).
    destruct (cstk _ LK cr Aw M1 model1 64 4096 HH1 MO1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(reflexivity)) as (STKc & _).
    destruct (PNAEK.own_facts L ar C HI HIok B A _ FF LK cr Aw M1 _ HH1) as (BAp & _). pose proof (BAp b c ltac:(left; reflexivity)) as BNE.
    assert (NEQ : (B =? b) = false) by (apply Z.eqb_neq; clear - BNE QB1 Hc; lia).
    assert (KS2 : forall i, In i [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R1 (reg i) = getr R (reg i)).
    { intros i Hi. apply KS1. clear - Hi. cbn in Hi. repeat (destruct Hi as [<-|Hi]; [inl|]). destruct Hi. }
    pose proof OPD as OD. unfold PMA.opdel_spec, PMSPA.opdel_spec, PMSPA.opdel_spec_at in OD. cbn [pa_opdel PMA.AD ADDR_A] in OD.
    assert (E10 : getr R1 10%bv = Z_to_bv 64 b) by (rewrite L5K.rl10; exact A10).
    assert (E1 : getr R1 1%bv = Z_to_bv 64 0xb58c8) by (rewrite L5K.rl1; exact A1).
    assert (E2' : getr R1 2%bv = Z_to_bv 64 (S - 64)) by (rewrite L5K.rl2, (KS2 2%nat) by inl; exact E2).
    assert (E4 : getr R1 4%bv = Z_to_bv 64 (hl_tp L)) by (rewrite L5K.rl4, (KS2 4%nat) by inl; rewrite (KP 4%nat) by inl; exact Rtp0).
    unfold PMSP.cfg.
    apply (OD fx1 R1 M1 model1 K _ FF LK Aw cr b c (S - 64) 0xb58c8 HH1 AM1 K0 ltac:(right; left; reflexivity) E10 E1 ltac:(split; [lia| reflexivity]) E2' E4 STKc).
    intros fx2 R2 M2 model2 Aw2 RP2 HP2 MRT2 IAW2 AM2 HH2.
    cbn [app lb_remove fst] in HP2, HH2. rewrite NEQ, Z.eqb_refl in HP2, HH2. unfold PMSPA.OPDEL_SCR, PMSPA.MALLOC_SCR in HP2.
    assert (WIN : forall rg, In rg (@nil L5.range) -> exists q m, In (q, m) [(B, A); (b, c)] /\ q <= fst rg /\ fst rg + snd rg <= q + m) by (intros rg []).
    pose proof (mem_ok_callee [(B, A); (b, c)] [(B, A)] LK cr Aw M1 model1 M2 (S - 64) 4096 _ HH1 MO1 HP2 ltac:(lia) ltac:(lia) ltac:(lia) WIN) as MO2.
    pose proof (saves_callee [(B, A); (b, c)] LK cr Aw M1 model1 M2 [(B, A)] (S - 64) 4096 _ HH1 MO1 HP2 ltac:(lia) ltac:(lia) ltac:(lia) WIN SV1) as SV2.
    pose proof (cell_callee [(B, A); (b, c)] LK cr Aw M1 model1 M2 [(B, A)] (S - 64) 4096 _ (S - 32) v HH1 MO1 HP2 ltac:(lia) ltac:(lia) ltac:(lia) WIN ltac:(left; lia) S32') as S32''.
    pose proof (cell_callee [(B, A); (b, c)] LK cr Aw M1 model1 M2 [(B, A)] (S - 64) 4096 _ (S - 40) _ HH1 MO1 HP2 ltac:(lia) ltac:(lia) ltac:(lia) WIN ltac:(left; lia) G40') as G40''.
    pose proof (cell_callee [(B, A); (b, c)] LK cr Aw M1 model1 M2 [(B, A)] (S - 64) 4096 _ (S - 48) _ HH1 MO1 HP2 ltac:(lia) ltac:(lia) ltac:(lia) WIN ltac:(left; lia) G48') as G48''.
    pose proof (cell_callee [(B, A); (b, c)] LK cr Aw M1 model1 M2 [(B, A)] (S - 64) 4096 _ (S - 56) _ HH1 MO1 HP2 ltac:(lia) ltac:(lia) ltac:(lia) WIN ltac:(left; lia) G56') as G56''.
    pose proof (cell_callee [(B, A); (b, c)] LK cr Aw M1 model1 M2 [(B, A)] (S - 64) 4096 _ (S - 64) _ HH1 MO1 HP2 ltac:(lia) ltac:(lia) ltac:(lia) WIN ltac:(left; lia) G64') as G64''.
    destruct (nfacts [(B, A)] LK cr Aw2 M2 model2 HH2 MO2) as (_ & (_ & _ & _ & ODEF2) & BF2).
    destruct (BF2 B A ltac:(left; reflexivity)) as (_ & _ & _ & _ & _ & _ & QBD2).
    pose proof HP2 as (EK2 & _).
    apply (tail_J fx2 R2 M2 model2 LK Aw2 (PGV8.V8Blk B (PGV8.v8_size x + k) A) g' cr).
    + rewrite (L5SAR.cs_of_preserved R1 R2 2%nat RP2) by inl. rewrite (KS2 2%nat) by inl. exact E2.
    + rewrite (L5SAR.cs_of_preserved R1 R2 8%nat RP2) by inl. rewrite (KS2 8%nat) by inl. exact E8.
    + rewrite (L5SAR.cs_of_preserved R1 R2 9%nat RP2) by inl. rewrite (KS2 9%nat) by inl. exact E9.
    + intros i Hi. rewrite (L5SAR.cs_of_preserved R1 R2 i RP2) by (unfold L5SAR.cs_all; clear - Hi; cbn in Hi |- *; tauto).
      rewrite KS2 by (clear - Hi; cbn in Hi |- *; tauto). apply ER. exact Hi.
    + apply (kept0_pres R1 R2); [| exact RP2]. apply (kept0_of R R1 KP). intros i Hi. apply KS2. clear - Hi. cbn in Hi |- *. tauto.
    + exact (stok_step model1 LK Aw model2 LK Aw2 SO1 AM2 MRT2 (incl_refl _) IAW2).
    + exact MO2.
    + exact SV2.
    + exact S32''.
    + split; [exact G64''|]. split; [exact G56''|]. split; [exact G48''| exact G40''].
    + exact HH2.
    + apply (v8_at_agree M1 M2 _ VS1 ODEF2); [| | lia| lia|].
      * apply (PGVAPK.obj_ek L ar C HI LY HIok _ FF (S - 64) 4096 [] M1 M2 v 24 v 24 EK2 AO V8); [lia| lia| lia| lia| intros i _ rg []].
      * apply (PGVAPK.objsh_ek L ar C HI LY HIok _ FF (S - 64) 4096 [] M1 M2 v 24 EK2 ltac:(intros rg []) AO); lia.
      * intros b' n' c' E. injection E as <- <- <-. split; [exact QBD2|].
        apply (PGVAPK.blksh_ek L ar C HI LY HIok _ FF (S - 64) 4096 [] M1 M2 B A EK2 ltac:(intros rg []) ltac:(left; reflexivity)); lia.
    + exact PO.
  - apply (piece_step fx fx1 R 0xb58c0 R1 0xb58d8 _ M model cr LK Aw M1v (fun a => S - 128 <= a < S - 128 + 128) HH SO MO MS1 MG1 FRZ1);
      [intros a Pa; cbv beta in Pa; left; lia|].
    intros M1 model1 HH1 SO1 MO1 FR1 VUP AGS.
    destruct (nfacts _ LK cr Aw M1 model1 HH1 MO1) as (_ & (_ & _ & _ & ODEF1) & BF1).
    assert (VS1 : v8_atA M1 v (PGV8.V8Blk B (PGV8.v8_size x + k) A)).
    { apply (v8_at_agree M M1 _ VS ODEF1); [| | lia| lia|].
      - intros i Hi. apply FR1; cbv beta; lia.
      - apply AGS; lia.
      - intros b' n' c' E. injection E as <- <- <-. destruct (BF1 B A ltac:(left; reflexivity)) as (_ & _ & _ & _ & _ & _ & QBD1).
        split; [exact QBD1| apply AGS; lia]. }
    destruct (v8_case x) as [EX|(b & n & c & EX)].
    2: { exfalso. rewrite EX in XR, ZZ. cbn [PGV8.v8_data] in ZZ. destruct XR as (Hn & Hc & Hb & Hb16 & Hbc). clear - ZZ Hb Hbc Hc. rewrite Z.sub_0_r, Z.mod_small in ZZ by lia. lia. }
    rewrite EX in HH1. cbn [PGV8.v8_own app] in HH1.
    apply (finish_p fx1 R1 M1 model1 LK Aw (PGV8.V8Blk B (PGV8.v8_size x + k) A) g' cr 0xb58d8 W_b404c F_b404c eq_refl D_b404c A1 A2); try assumption.
    + intros i Hi. cbn in Hi. destruct Hi as [<-|[<-|Hi]]; [exact A8| exact A9|].
      rewrite KS1 by (clear - Hi; cbn in Hi; repeat (destruct Hi as [<-|Hi]; [inl|]); destruct Hi). apply ER. exact Hi.
    + apply (kept0_of R R1 KP). intros i Hi. apply KS1. clear - Hi. cbn in Hi. repeat (destruct Hi as [<-|Hi]; [inl|]). destruct Hi.
Qed.


Lemma sw_C (fx : FPState) R M model LK Aw cr B A g' :
  getr R (reg 2) = Z_to_bv 64 (S - 144) -> getr R (reg 8) = Z_to_bv 64 (S - 64) -> getr R (reg 9) = Z_to_bv 64 v ->
  getr R (reg 18) = Z_to_bv 64 (v + 8) -> getr R (reg 19) = Z_to_bv 64 (S - 56) -> getr R (reg 20) = Z_to_bv 64 B ->
  getr R (reg 21) = Z_to_bv 64 HeapIfaceA.SB -> getr R (reg 22) = Z_to_bv 64 (HeapIfaceA.S (v + 8)) ->
  getr R (reg 23) = Z_to_bv 64 (HeapIfaceA.S (S - 56)) -> getr R (reg 24) = Z_to_bv 64 (HeapIfaceA.S v) ->
  (forall i, In i [3; 4; 25; 26; 27]%nat -> getr R (reg i) = getr R0 (reg i)) ->
  stok model LK Aw -> mem_ok M -> saves M -> L5.u64_at RSEGS M (S - 32) v -> ssaves M ->
  ri_inv HI (((B, A) :: PGV8.v8_own x) ++ LB) FF LK cr Aw M (vml_of model) ->
  hdr M (PGV8.v8_data x) (PGV8.v8_data x + PGV8.v8_size x) (PGV8.v8_data x + PGV8.v8_cap x) ->
  gbuf M B (B + PGV8.v8_size x) ((B + PGV8.v8_size x) + k) (B + A) ->
  A <= 2 ^ 27 -> PGV8.v8_size x + k <= A -> shadow_blk M B A ->
  post_ok (PGV8.V8Blk B (PGV8.v8_size x + k) A) g' cr ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R sw_pcC M model) K.
Proof using All.
  intros E2 E8 E9 E18 E19 E20 E21 E22 E23 E24 KQ SO MO SV S32 SSV HH HD GB HA HnkA SHB PO.
  destruct (nfacts _ LK cr Aw M model HH MO) as ((A16 & SLO & SHI & SPT & C0) & (O1 & O2 & O5 & ODEF) & BF). unfold PGVAPK.nsh in O5.
  destruct (BF B A ltac:(left; reflexivity)) as (QB0 & QB1 & QB2 & QB4 & QB5 & QB6 & QBD). unfold PGVAPK.nsh in QB5.
  destruct (vfacts _ LK cr Aw M model HH MO) as (X0 & X1 & X2 & XW & XZ & XWV & XSZ & XAV).
  pose proof SSV as (T72 & T80 & T88 & T96 & T104 & T112 & T120 & T128 & T136 & T144). pose proof HD as (W0 & W8 & W16). pose proof GB as (B1 & B2 & B3 & B4).
  pose proof xnum as (XD & XS & XC & K27 & XSK & XDC).
  assert (UB : forall i, 0 <= U i < 2 ^ 64) by (intros i; unfold PGVAPK.U; apply bv_unsigned_in_range).
  pose proof (UB 18%nat) as UB18. pose proof (UB 19%nat) as UB19. pose proof (UB 20%nat) as UB20. pose proof (UB 21%nat) as UB21.
  pose proof (UB 22%nat) as UB22. pose proof (UB 23%nat) as UB23. pose proof (UB 24%nat) as UB24.
  pose proof (PMAVGP.avsC_conc fx R (mrestrict (ahid Aw model) M) (fun j => match j with 2%nat => S - 64 | 37%nat => v | 40%nat => PGV8.v8_data x | 41%nat => PGV8.v8_size x
     | 42%nat => PGV8.v8_cap x | 43%nat => k | 44%nat => B | 46%nat => A
     | 48%nat => 0xb58c0 | 49%nat => v | 50%nat => k | 51%nat => U 18 | 52%nat => U 19 | 53%nat => U 20 | 54%nat => U 21
     | 55%nat => U 22 | 56%nat => U 23 | 57%nat => U 24 | _ => 0 end)) as PP.
  cbn beta iota in PP.
  replace (S - 64 - 80) with (S - 144) in PP by lia. replace (S - 64 - 8) with (S - 72) in PP by lia. replace (S - 64 - 16) with (S - 80) in PP by lia.
  replace (S - 64 - 24) with (S - 88) in PP by lia. replace (S - 64 - 32) with (S - 96) in PP by lia. replace (S - 64 - 40) with (S - 104) in PP by lia.
  replace (S - 64 - 48) with (S - 112) in PP by lia. replace (S - 64 - 56) with (S - 120) in PP by lia. replace (S - 64 - 64) with (S - 128) in PP by lia.
  replace (S - 64 - 72) with (S - 136) in PP by lia. replace (S - 64 + 8) with (S - 56) in PP by lia. replace (S - 64 + 16) with (S - 48) in PP by lia.
  replace (S - 64 + 24) with (S - 40) in PP by lia. replace (S - 64 + 0) with (S - 64) in PP by lia. replace (v + 0) with v in PP by lia.
  L5SAR.feed PP ltac:(pfeed XW XSZ XAV).
  destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & A1 & A2 & A8 & A9 & A10 & A11 & A12 & A18 & A19 & A20 & A21 & A22 & A23 & A24
    & C1 & C2 & C3 & C4 & C5 & C6 & C7).
  apply (piece_step fx fx1 R _ R1 _ _ M model cr LK Aw M1v (fun a => v <= a < v + 24 \/ S - 64 <= a < S - 64 + 32) HH SO MO MS1 MG1).
  { intros a Ha N. apply FRZ1; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
  { intros a [Pa|Pa]; [right; left; exact Pa| left; lia]. }
  intros M1 model1 HH1 SO1 MO1 FR1 VUP AGS.
  pose proof (saves_piece _ LK cr Aw M model M1 _ HH MO FR1 ltac:(intros i [X|X]; lia) SV) as SV1.
  assert (S32a : L5.u64_at RSEGS M1 (S - 32) v).
  { apply (cell_piece M M1 _ (S - 32) v FR1); [intros i Hi [X|X]; lia| lia| lia| exact S32]. }
  destruct (nfacts _ LK cr Aw M1 model1 HH1 MO1) as (_ & (_ & _ & _ & ODEF1) & BF1).
  destruct (BF1 B A ltac:(left; reflexivity)) as (_ & _ & _ & _ & _ & _ & QBD1).
  pose proof MO1 as (_ & _ & _ & ACC1 & _). pose proof SO1 as (AM1 & MRT1 & ILK1 & IAW1).
  assert (KS2 : forall i, In i [3; 4; 25; 26; 27]%nat -> getr R1 (reg i) = getr R (reg i)).
  { intros i Hi. apply KS1. clear - Hi. cbn in Hi. repeat (destruct Hi as [<-|Hi]; [inl|]). destruct Hi. }
  assert (KP1 : kept0 R1).
  { intros i Hi. cbn in Hi. destruct Hi as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]].
    - rewrite KS2 by inl. apply (KQ _). inl.
    - rewrite KS2 by inl. apply (KQ _). inl.
    - rewrite A22. unfold PGVAPK.U. apply Z_to_bv_bv_unsigned.
    - rewrite A23. unfold PGVAPK.U. apply Z_to_bv_bv_unsigned.
    - rewrite A24. unfold PGVAPK.U. apply Z_to_bv_bv_unsigned.
    - rewrite KS2 by inl. apply (KQ _). inl.
    - rewrite KS2 by inl. apply (KQ _). inl.
    - rewrite KS2 by inl. apply (KQ _). inl. }
  destruct (centry0 R1 _ LK cr Aw M1 model1 64 0xb58c0 HH1 MO1 KP1 A1 ltac:(split; [lia| reflexivity]) A2 ltac:(lia) ltac:(reflexivity)) as (ENT & FRSc).
  set (x' := PGV8.V8Blk B (PGV8.v8_size x + k) A) in *.
  assert (HD1 : PNSAX.v8_hdr RSEGS M1 v x').
  { split; [exact ODEF1|]. unfold x'. split; [apply VUP; [right; lia| exact C7]|].
    split; [apply VUP; [right; lia| replace (B + (PGV8.v8_size x + k)) with (B + PGV8.v8_size x + k) by lia; exact C5]|].
    split; [apply VUP; [right; lia| exact C3]|].
    split; [lia|]. split; [lia|]. split; [lia|]. split; [exact QB4| exact QBD1]. }
  assert (SHB1 : forall b n c, x' = PGV8.V8Blk b n c -> PMSPA.annA M1 b c c).
  { intros b n c E. unfold x' in E. injection E as <- <- <-. apply PNSAX8.ann_full_of_blk.
    apply (PGVAPK.shblk_agree L ar C HI LY HIok M M1 B A); [apply PMKA.mod16_8'; exact QB4| lia| apply AGS; lia| exact SHB]. }
  assert (HHx : ri_inv HI (PGV8.v8_own x' ++ (PGV8.v8_own x ++ LB)) FF LK cr Aw M1 (vml_of model1)) by exact HH1.
  pose proof ANNN as AN. unfold PNSAX8.ann_new_v8_spec in AN.
  assert (E10 : getr R1 10%bv = Z_to_bv 64 v) by (rewrite L5K.rl10; exact A10).
  assert (E11 : getr R1 11%bv = Z_to_bv 64 (PGV8.v8_size x + k)) by (rewrite L5SAR.r11; exact A11).
  unfold PMSP.cfg.
  apply (AN fx1 R1 M1 model1 K (PGV8.v8_own x ++ LB) FF LK Aw cr v (PGV8.v8_size x + k) x' (S - 64) 0xb58c0 HHx AM1 K0 ENT FRSc E10 E11 AO V8
    ACC1 HD1 eq_refl SHB1).
  intros fx2 R2 M2 model2 LK2 Aw2 RP2 VS2 KEPT2 HP2 MRT2 ILK2 IAW2 AM2 HH2.
  change (PMSPA.pm_scr 0) with 12288 in HP2.
  assert (WIN : forall rg, In rg (@nil L5.range) -> exists q m, In (q, m) ((B, A) :: PGV8.v8_own x) /\ q <= fst rg /\ fst rg + snd rg <= q + m)
    by (intros rg []).
  pose proof (mem_ok_callee _ (PGV8.v8_own x) LK cr Aw M1 model1 M2 (S - 64) 12288 _ HH1 MO1 HP2 ltac:(lia) ltac:(lia) ltac:(lia) WIN) as MO2.
  pose proof (saves_callee _ LK cr Aw M1 model1 M2 (PGV8.v8_own x) (S - 64) 12288 _ HH1 MO1 HP2 ltac:(lia) ltac:(lia) ltac:(lia) WIN SV1) as SV2.
  assert (CK : forall a val, (S - 64 <= a /\ a + 8 <= S) \/ (v <= a /\ a + 8 <= v + 24) -> L5.u64_at RSEGS M1 a val -> L5.u64_at RSEGS M2 a val).
  { intros a val Ha X. exact (cell_callee _ LK cr Aw M1 model1 M2 (PGV8.v8_own x) (S - 64) 12288 _ a val HH1 MO1 HP2 ltac:(lia) ltac:(lia) ltac:(lia) WIN Ha X). }
  assert (CS2 : forall i, In i L5SAR.cs_all -> getr R2 (reg i) = getr R1 (reg i)) by (intros i Hi; exact (L5SAR.cs_of_preserved R1 R2 i RP2 Hi)).
  apply (tail_I fx2 R2 M2 model2 LK2 Aw2 cr B A g').
  - rewrite CS2 by inl. exact A2.
  - rewrite CS2 by inl. exact A8.
  - rewrite CS2 by inl. exact A9.
  - intros i Hi. cbn in Hi. destruct Hi as [<-|[<-|[<-|[<-|[]]]]]; rewrite CS2 by inl; assumption.
  - exact (kept0_pres R1 R2 KP1 RP2).
  - exact (stok_step model1 LK Aw model2 LK2 Aw2 SO1 AM2 MRT2 ILK2 IAW2).
  - exact MO2.
  - exact SV2.
  - apply CK; [left; lia| exact S32a].
  - exact HH2.
  - exact VS2.
  - split; [apply CK; [left; lia|]; apply VUP; [left; lia| exact C1]|]. split; [apply CK; [left; lia|]; apply VUP; [left; lia| exact C6]|].
    split; [apply CK; [left; lia|]; apply VUP; [left; lia| exact C4]| apply CK; [left; lia|]; apply VUP; [left; lia| exact C2]].
  - exact PO.
Qed.

Lemma aacc_of_block (M : word -> option byte) u m p n : shadow_blk M u m -> u mod 8 = 0 -> 0 <= u -> u <= p -> p + n <= u + m -> aacc M p n.
Proof.
  intros [SZ SP] U8 U0 H1 H2 a Ha. clear - SZ SP U8 U0 H1 H2 Ha. unfold shadow_zero, byte_at in SZ, SP |- *.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (E : HeapIfaceA.S a = HeapIfaceA.S u + (a / 8 - u / 8)) by (unfold HeapIfaceA.S; Lia.lia).
  destruct (Z_lt_le_dec (a / 8 - u / 8) (m / 8)) as [LT|GE].
  - left. rewrite E. apply SZ. Lia.lia.
  - right. exists (m mod 8). assert (NZ : m mod 8 <> 0) by Lia.lia. assert (G : a / 8 - u / 8 = m / 8) by Lia.lia.
    split. rewrite E, G. apply SP. exact NZ. Lia.lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma src_facts B A LK cr Aw M model :
  ri_inv HI (((B, A) :: PGV8.v8_own x) ++ LB) FF LK cr Aw M (vml_of model) -> mem_ok M ->
  (forall b n c, x = PGV8.V8Blk b n c -> PMSPA.accA M b n) -> PGV8.v8_size x <= A ->
  aacc M (PGV8.v8_data x) (PGV8.v8_size x) /\ app_rng ar (PGV8.v8_data x) (PGV8.v8_size x)
  /\ (forall i sp' scr', 0 <= i < PGV8.v8_size x -> aclient L ar (((B, A) :: PGV8.v8_own x) ++ LB) FF sp' scr' (PGV8.v8_data x + i))
  /\ L5.defined M (PGV8.v8_data x) (PGV8.v8_size x)
  /\ (B + PGV8.v8_size x <= PGV8.v8_data x \/ PGV8.v8_data x + PGV8.v8_size x <= B).
Proof using All.
  intros HH MO ACX HsA. destruct (nfacts _ LK cr Aw M model HH MO) as ((A16 & SLO & SHI & SPT & C0) & _ & BF).
  destruct (BF B A ltac:(left; reflexivity)) as (QB0 & QB1 & QB2 & QB4 & QB5 & QB6 & QBD).
  pose proof xr as XR. destruct (v8_case x) as [EX|(b & n & c & EX)]; rewrite EX in XR, HH, BF, HsA |- *; cbn [PGV8.v8_data PGV8.v8_size PGV8.v8_own] in *.
  - split; [intros a Ha; lia|]. split; [unfold app_rng, BIGSHADOW_LO, BIGSHADOW_HI; lia|]. split; [intros i sp' scr' Hi; lia|]. split; [intros i Hi; lia| right; lia].
  - destruct XR as (Hn & Hc & Hb & Hb16 & Hbc). destruct (BF b c ltac:(right; left; reflexivity)) as (Q0 & Q1 & Q2 & Q4 & Q5 & Q6 & QD). unfold PGVAPK.nsh in Q5.
    destruct (PNAEK.own_facts L ar C HI HIok B A _ FF LK cr Aw M _ HH) as (BAp & _). pose proof (BAp b c ltac:(left; reflexivity)) as BNE.
    split; [exact (ACX b n c EX)|]. split; [unfold app_rng, BIGSHADOW_LO, BIGSHADOW_HI; lia|].
    split; [intros i sp' scr' Hi; unfold aclient, aclient_g; left; exists (b, c); split; [right; left; reflexivity| cbn [fst snd]; lia]|].
    split; [intros i Hi; apply QD; lia| lia].
Qed.

Lemma ri_swap B A LK cr Aw M V :
  ri_inv HI (((B, A) :: PGV8.v8_own x) ++ LB) FF LK cr Aw M V <-> ri_inv HI (PGV8.v8_own x ++ ((B, A) :: LB)) FF LK cr Aw M V.
Proof using All.
  assert (G : forall (l1 l2 : list (Z * Z)), (forall y, In y l1 <-> In y l2) -> (NoDup (map fst l1) -> NoDup (map fst l2)) ->
            ri_inv HI l1 FF LK cr Aw M V -> ri_inv HI l2 FF LK cr Aw M V).
  { intros l1 l2 IFF ND HH. pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND1 & NDF & _).
    apply (HAJ.aior_perm _ _ _ _ _ HIok l1 l2 FF FF LK cr Aw M V HH IFF (ND ND1)); [intros f; tauto|].
    rewrite map_app in NDF. apply stdpp.list_relations.list.NoDup_app in NDF. exact (proj1 NDF). }
  destruct (v8_case x) as [EX|(b & n & c & EX)]; rewrite EX; cbn [PGV8.v8_own app]; [tauto|].
  assert (SW : forall (p q : Z * Z) l, NoDup (map fst (p :: q :: l)) -> NoDup (map fst (q :: p :: l))).
  { intros p q l ND. cbn [map] in *. apply stdpp.list_relations.list.NoDup_cons in ND as (N1 & ND). apply stdpp.list_relations.list.NoDup_cons in ND as (N2 & ND).
    apply stdpp.list_relations.list.NoDup_cons. split.
    - intros X. apply stdpp.list_basics.list.elem_of_cons in X as [X|X]; [apply N1; rewrite X; apply stdpp.list_basics.list.elem_of_cons; left; reflexivity| exact (N2 X)].
    - apply stdpp.list_relations.list.NoDup_cons. split; [| exact ND]. intros X. apply N1. apply stdpp.list_basics.list.elem_of_cons. right. exact X. }
  split; apply G; try apply SW; intros y; cbn [In]; tauto.
Qed.

Lemma sw_B (fx : FPState) R M model LK Aw cr B A g' :
  getr R (reg 2) = Z_to_bv 64 (S - 144) -> getr R (reg 8) = Z_to_bv 64 (S - 64) -> getr R (reg 9) = Z_to_bv 64 v ->
  getr R (reg 21) = Z_to_bv 64 HeapIfaceA.SB -> kept0 R ->
  stok model LK Aw -> mem_ok M -> saves M -> L5.u64_at RSEGS M (S - 32) v -> ssaves M ->
  ri_inv HI (((B, A) :: PGV8.v8_own x) ++ LB) FF LK cr Aw M (vml_of model) ->
  hdr M (PGV8.v8_data x) (PGV8.v8_data x + PGV8.v8_size x) (PGV8.v8_data x + PGV8.v8_cap x) ->
  gbuf M B (B + PGV8.v8_size x) ((B + PGV8.v8_size x) + k) (B + A) ->
  A <= 2 ^ 27 -> PGV8.v8_size x + k <= A -> shadow_blk M B A ->
  (forall b n c, x = PGV8.V8Blk b n c -> PMSPA.accA M b n) ->
  post_ok (PGV8.V8Blk B (PGV8.v8_size x + k) A) g' cr ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R sw_pcB M model) K.
Proof using All.
  intros E2 E8 E9 E21 KP SO MO SV S32 SSV HH HD GB HA HnkA SHB ACX PO.
  destruct (nfacts _ LK cr Aw M model HH MO) as ((A16 & SLO & SHI & SPT & C0) & (O1 & O2 & O5 & ODEF) & BF). unfold PGVAPK.nsh in O5.
  destruct (BF B A ltac:(left; reflexivity)) as (QB0 & QB1 & QB2 & QB4 & QB5 & QB6 & QBD). unfold PGVAPK.nsh in QB5.
  destruct (vfacts _ LK cr Aw M model HH MO) as (X0 & X1 & X2 & XW & XZ & XWV & XSZ & XAV).
  pose proof SSV as (T72 & T80 & T88 & T96 & T104 & T112 & T120 & T128 & T136 & T144). pose proof HD as (W0 & W8 & W16). pose proof GB as (B1 & B2 & B3 & B4).
  pose proof xnum as (XD & XS & XC & K27 & XSK & XDC).
  assert (UB : forall i, 0 <= U i < 2 ^ 64) by (intros i; unfold PGVAPK.U; apply bv_unsigned_in_range).
  pose proof (UB 18%nat) as UB18. pose proof (UB 19%nat) as UB19. pose proof (UB 20%nat) as UB20. pose proof (UB 21%nat) as UB21.
  pose proof (UB 22%nat) as UB22. pose proof (UB 23%nat) as UB23. pose proof (UB 24%nat) as UB24.
  pose proof (PMAVGP.avsB_conc fx R (mrestrict (ahid Aw model) M) (fun j => match j with 2%nat => S - 64 | 37%nat => v | 40%nat => PGV8.v8_data x | 41%nat => PGV8.v8_size x
     | 44%nat => B | 48%nat => 0xb58c0 | 49%nat => v | 50%nat => k | 51%nat => U 18 | 52%nat => U 19 | 53%nat => U 20 | 54%nat => U 21
     | 55%nat => U 22 | 56%nat => U 23 | 57%nat => U 24 | _ => 0 end)) as PP.
  cbn beta iota in PP.
  replace (S - 64 - 80) with (S - 144) in PP by lia. replace (S - 64 - 8) with (S - 72) in PP by lia. replace (S - 64 - 16) with (S - 80) in PP by lia.
  replace (S - 64 - 24) with (S - 88) in PP by lia. replace (S - 64 - 32) with (S - 96) in PP by lia. replace (S - 64 - 40) with (S - 104) in PP by lia.
  replace (S - 64 - 48) with (S - 112) in PP by lia. replace (S - 64 - 56) with (S - 120) in PP by lia. replace (S - 64 - 64) with (S - 128) in PP by lia.
  replace (S - 64 - 72) with (S - 136) in PP by lia. replace (S - 64 + 8) with (S - 56) in PP by lia.
  L5SAR.feed PP ltac:(pfeed XW XSZ XAV).
  destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & A1 & A10 & A11 & A12 & A14 & A15 & A18 & A19 & A20 & A22 & A23 & A24).
  apply (piece_ro fx fx1 R _ R1 _ _ M model cr LK Aw M1v HH SO MO MS1 MG1 FRZ1). intros model1 HH1 SO1.
  pose proof SO1 as (AM1 & MRT1 & ILK1 & IAW1).
  assert (KS2 : forall i, In i [2; 3; 4; 8; 9; 21; 25; 26; 27]%nat -> getr R1 (reg i) = getr R (reg i)).
  { intros i Hi. apply KS1. clear - Hi. cbn in Hi. repeat (destruct Hi as [<-|Hi]; [inl|]). destruct Hi. }
  destruct (cstk _ LK cr Aw M model1 144 2560 HH1 MO ltac:(lia) ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(reflexivity)) as (STKc & _).
  destruct (src_facts B A LK cr Aw M model1 HH1 MO ACX ltac:(lia)) as (SAC & SAP & SCL & SDF & SNO).
  assert (E2' : getr R1 (reg 2) = Z_to_bv 64 (S - 144)) by (rewrite (KS2 2%nat) by inl; exact E2).
  assert (E4 : getr R1 (reg 4) = Z_to_bv 64 (hl_tp L)) by (rewrite (KS2 4%nat) by inl; rewrite (KP 4%nat) by inl; exact Rtp0).
  apply (PGVAPK.memcpy_call27 L ar C HI LY HIok fx1 R1 M model1 K _ FF LK cr Aw (S - 144) _ B (PGV8.v8_data x) (PGV8.v8_size x) HH1 AM1 K0 A1
    ltac:(split; [lia| reflexivity]) E2' E4 A10 A11 A12 ltac:(lia) STKc).
  { apply (aacc_of_block M B A B (PGV8.v8_size x) SHB); [apply PMKA.mod16_8'; exact QB4| lia| lia| lia]. }
  { intros i Hi. unfold aclientw, aclient_g. left. exists (B, A). split; [left; reflexivity|]. cbn [fst snd]. lia. }
  { intros i Hi. apply QBD. lia. }
  { lia. } { lia. }
  { unfold app_rng, BIGSHADOW_LO, BIGSHADOW_HI. lia. }
  { exact SAC. } { lia. } { lia. } { exact SAP. }
  { intros i Hi. exact (SCL i (S - 144) 2560 Hi). }
  { exact SDF. } { exact SNO. }
  intros fx2 R2 M2 model2 RP2 DD2 HP2 MRT2 AM2 HH2.
  assert (WIN : forall rg, In rg [(B, PGV8.v8_size x)] -> exists q m, In (q, m) ((B, A) :: PGV8.v8_own x) /\ q <= fst rg /\ fst rg + snd rg <= q + m).
  { intros rg [<-|[]]. exists B, A. split; [left; reflexivity|]. cbn [fst snd]. lia. }
  pose proof (mem_ok_callee _ _ LK cr Aw M model1 M2 (S - 144) 2560 _ HH1 MO HP2 ltac:(lia) ltac:(lia) ltac:(lia) WIN) as MO2.
  pose proof (saves_callee _ LK cr Aw M model1 M2 _ (S - 144) 2560 _ HH1 MO HP2 ltac:(lia) ltac:(lia) ltac:(lia) WIN SV) as SV2.
  assert (CK : forall a val, (S - 144 <= a /\ a + 8 <= S) \/ (v <= a /\ a + 8 <= v + 24) -> L5.u64_at RSEGS M a val -> L5.u64_at RSEGS M2 a val).
  { intros a val Ha X. exact (cell_callee _ LK cr Aw M model1 M2 _ (S - 144) 2560 _ a val HH1 MO HP2 ltac:(lia) ltac:(lia) ltac:(lia) WIN Ha X). }
  assert (WA : PMKA.wapp [(B, PGV8.v8_size x)]) by (apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; lia| intros rg []]).
  pose proof (PGVAPK.blksh_ek L ar C HI LY HIok _ FF (S - 144) 2560 _ M M2 B A (proj1 HP2) WA ltac:(left; reflexivity) ltac:(lia) ltac:(lia)) as AGB.
  assert (CS2 : forall i, In i L5SAR.cs_all -> getr R2 (reg i) = getr R1 (reg i)) by (intros i Hi; exact (L5SAR.cs_of_preserved R1 R2 i RP2 Hi)).
  apply (sw_C fx2 R2 M2 model2 LK Aw cr B A g').
  - rewrite CS2 by inl. exact E2'.
  - rewrite CS2 by inl. rewrite (KS2 8%nat) by inl. exact E8.
  - rewrite CS2 by inl. rewrite (KS2 9%nat) by inl. exact E9.
  - rewrite CS2 by inl. exact A18.
  - rewrite CS2 by inl. exact A19.
  - rewrite CS2 by inl. exact A20.
  - rewrite CS2 by inl. rewrite (KS2 21%nat) by inl. exact E21.
  - rewrite CS2 by inl. exact A22.
  - rewrite CS2 by inl. exact A23.
  - rewrite CS2 by inl. exact A24.
  - intros i Hi. cbn in Hi. destruct Hi as [<-|[<-|[<-|[<-|[<-|[]]]]]]; rewrite CS2 by inl; rewrite KS2 by inl; apply (KP _); inl.
  - exact (stok_step model1 LK Aw model2 LK Aw SO1 AM2 MRT2 (incl_refl _) (incl_refl _)).
  - exact MO2.
  - exact SV2.
  - apply CK; [left; lia| exact S32].
  - unfold ssaves. repeat split; (apply CK; [left; lia| assumption]).
  - exact HH2.
  - split; [apply CK; [right; lia| exact W0]|]. split; [apply CK; [right; lia| exact W8]| apply CK; [right; lia| exact W16]].
  - split; [apply CK; [left; lia| exact B1]|]. split; [apply CK; [left; lia| exact B2]|]. split; [apply CK; [left; lia| exact B3]| apply CK; [left; lia| exact B4]].
  - exact HA.
  - exact HnkA.
  - apply (PGVAPK.shblk_agree L ar C HI LY HIok M M2 B A); [apply PMKA.mod16_8'; exact QB4| lia| exact AGB| exact SHB].
  - exact PO.
Qed.

Lemma sw_A (fx : FPState) R M model LK Aw cr B A g' :
  getr R (reg 1) = Z_to_bv 64 0xb58c0 -> getr R (reg 2) = Z_to_bv 64 (S - 64) -> getr R (reg 8) = Z_to_bv 64 v ->
  getr R (reg 9) = Z_to_bv 64 k -> getr R (reg 10) = Z_to_bv 64 v -> getr R (reg 11) = Z_to_bv 64 (S - 64) ->
  (forall i, In i [18; 19; 20; 21]%nat -> getr R (reg i) = Z_to_bv 64 (U i)) -> kept0 R ->
  stok model LK Aw -> mem_ok M -> saves M -> L5.u64_at RSEGS M (S - 32) v ->
  ri_inv HI (((B, A) :: PGV8.v8_own x) ++ LB) FF LK cr Aw M (vml_of model) -> v8_atA M v x ->
  gbuf M B (B + PGV8.v8_size x) ((B + PGV8.v8_size x) + k) (B + A) ->
  A <= 2 ^ 27 -> PGV8.v8_size x + k <= A -> shadow_blk M B A ->
  post_ok (PGV8.V8Blk B (PGV8.v8_size x + k) A) g' cr ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0xb5cb8 M model) K.
Proof using All.
  intros E1 E2 E8 E9 E10 E11 ER KP SO MO SV S32 HH VS GB HA HnkA SHB PO.
  destruct (nfacts _ LK cr Aw M model HH MO) as ((A16 & SLO & SHI & SPT & C0) & (O1 & O2 & O5 & ODEF) & BF). unfold PGVAPK.nsh in O5.
  destruct (BF B A ltac:(left; reflexivity)) as (QB0 & QB1 & QB2 & QB4 & QB5 & QB6 & QBD). unfold PGVAPK.nsh in QB5.
  destruct (vfacts _ LK cr Aw M model HH MO) as (X0 & X1 & X2 & XW & XZ & XWV & XSZ & XAV).
  pose proof xnum as (XD & XS & XC & K27 & XSK & XDC).
  pose proof (PMAVGP.avsA_conc fx R (mrestrict (ahid Aw model) M) (fun j => match j with 2%nat => S - 64 | 37%nat => v | _ => 0 end)) as PP.
  cbn beta iota in PP.
  replace (S - 64 - 80) with (S - 144) in PP by lia. replace (S - 64 - 8) with (S - 72) in PP by lia. replace (S - 64 - 16) with (S - 80) in PP by lia.
  replace (S - 64 - 24) with (S - 88) in PP by lia. replace (S - 64 - 32) with (S - 96) in PP by lia. replace (S - 64 - 40) with (S - 104) in PP by lia.
  replace (S - 64 - 48) with (S - 112) in PP by lia. replace (S - 64 - 56) with (S - 120) in PP by lia. replace (S - 64 - 64) with (S - 128) in PP by lia.
  replace (S - 64 - 72) with (S - 136) in PP by lia.
  L5SAR.feed PP ltac:(pfeed XW XSZ XAV).
  destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & A1 & A2 & A8 & A9 & A11 & A21 & C144 & C136 & C128 & C120 & C112 & C104 & C96 & C88 & C80 & C72).
  assert (U1 : bv_unsigned (getr R (reg 1)) = 0xb58c0) by (rewrite E1; apply L5.unsigned_lit; lia).
  assert (U8 : bv_unsigned (getr R (reg 8)) = v) by (rewrite E8; apply L5.unsigned_lit; lia).
  assert (U9 : bv_unsigned (getr R (reg 9)) = k) by (rewrite E9; apply L5.unsigned_lit; lia).
  assert (UR : forall i, In i [18; 19; 20; 21]%nat -> bv_unsigned (getr R (reg i)) = U i).
  { intros i Hi. rewrite (ER i Hi). unfold PGVAPK.U. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  assert (UK : forall i, In i [22; 23; 24]%nat -> bv_unsigned (getr R (reg i)) = U i).
  { intros i Hi. unfold PGVAPK.U. rewrite (KP i) by (clear - Hi; cbn in Hi |- *; tauto). reflexivity. }
  rewrite U1 in C72. rewrite U8 in C80. rewrite U9 in C88.
  rewrite (UR 18%nat) in C96 by inl. rewrite (UR 19%nat) in C104 by inl. rewrite (UR 20%nat) in C112 by inl. rewrite (UR 21%nat) in C120 by inl.
  rewrite (UK 22%nat) in C128 by inl. rewrite (UK 23%nat) in C136 by inl. rewrite (UK 24%nat) in C144 by inl.
  apply (piece_step fx fx1 R _ R1 _ _ M model cr LK Aw M1v (fun a => S - 144 <= a < S - 144 + 80) HH SO MO MS1 MG1 FRZ1); [intros a Pa; cbv beta in Pa; left; lia|].
  intros M1 model1 HH1 SO1 MO1 FR1 VUP AGS.
  pose proof (saves_piece _ LK cr Aw M model M1 (fun a => S - 144 <= a < S - 144 + 80) HH MO FR1 ltac:(intros i X; cbv beta in X; lia) SV) as SV1.
  assert (S32a : L5.u64_at RSEGS M1 (S - 32) v).
  { apply (cell_piece M M1 (fun a => S - 144 <= a < S - 144 + 80) (S - 32) v FR1); [intros i Hi X; cbv beta in X; lia| lia| lia| exact S32]. }
  destruct (nfacts _ LK cr Aw M1 model1 HH1 MO1) as (_ & (_ & _ & _ & ODEF1) & BF1).
  destruct (BF1 B A ltac:(left; reflexivity)) as (_ & _ & _ & _ & _ & _ & QBD1).
  pose proof MO1 as (_ & _ & _ & ACC1 & _). pose proof SO1 as (AM1 & MRT1 & ILK1 & IAW1).
  assert (KS2 : forall i, In i [3; 4; 10; 22; 23; 24; 25; 26; 27]%nat -> getr R1 (reg i) = getr R (reg i)).
  { intros i Hi. apply KS1. clear - Hi. cbn in Hi. repeat (destruct Hi as [<-|Hi]; [inl|]). destruct Hi. }
  assert (KP1 : kept0 R1) by (apply (kept0_of R R1 KP); intros i Hi; apply KS2; clear - Hi; cbn in Hi |- *; tauto).
  destruct (centry0 R1 _ LK cr Aw M1 model1 144 _ HH1 MO1 KP1 A1 ltac:(split; [lia| reflexivity]) A2 ltac:(lia) ltac:(reflexivity)) as (ENT & FRSc).
  assert (VS1 : v8_atA M1 v x).
  { apply (v8_at_agree M M1 x VS ODEF1); [intros i Hi; apply FR1; cbv beta; lia| apply AGS; lia| lia| lia|].
    intros b n c EX. destruct (BF1 b c ltac:(rewrite EX; right; left; reflexivity)) as (Q0 & Q1 & Q2 & Q4 & Q5 & Q6 & QD). unfold PGVAPK.nsh in Q5.
    split; [exact QD| apply AGS; lia]. }
  assert (GB1 : gbuf M1 B (B + PGV8.v8_size x) ((B + PGV8.v8_size x) + k) (B + A)).
  { pose proof GB as (B1 & B2 & B3 & B4).
    repeat split; (eapply (cell_piece M M1 _ _ _ FR1); [intros i Hi X; cbv beta in X; lia| lia| lia| eassumption]). }
  assert (SHB1 : shadow_blk M1 B A) by (apply (PGVAPK.shblk_agree L ar C HI LY HIok M M1 B A); [apply PMKA.mod16_8'; exact QB4| lia| apply AGS; lia| exact SHB]).
  pose proof (proj1 (ri_swap B A LK cr Aw M1 _) HH1) as HHx.
  pose proof ANND as AD'. unfold PNSAX.ann_delete_v8_spec in AD'.
  assert (E10' : getr R1 10%bv = Z_to_bv 64 v) by (rewrite L5K.rl10, (KS2 10%nat) by inl; exact E10).
  unfold PMSP.cfg.
  apply (AD' fx1 R1 M1 model1 K ((B, A) :: LB) FF LK Aw cr v x (S - 144) _ HHx AM1 K0 ENT FRSc E10' AO V8 ACC1 VS1).
  intros fx2 R2 M2 model2 LK2 Aw2 RP2 HD2 ACC2 ACX2 KEPT2 HP2 MRT2 ILK2 IAW2 AM2 HH2.
  change (PMSPA.pm_scr 0) with 12288 in HP2.
  pose proof (proj2 (ri_swap B A LK2 cr Aw2 M2 _) HH2) as HH2s.
  assert (WIN : forall rg, In rg (@nil L5.range) -> exists q m, In (q, m) ((B, A) :: PGV8.v8_own x) /\ q <= fst rg /\ fst rg + snd rg <= q + m)
    by (intros rg []).
  pose proof (mem_ok_callee _ [(B, A)] LK cr Aw M1 model1 M2 (S - 144) 12288 _ HH1 MO1 HP2 ltac:(lia) ltac:(lia) ltac:(lia) WIN) as MO2.
  pose proof (saves_callee _ LK cr Aw M1 model1 M2 [(B, A)] (S - 144) 12288 _ HH1 MO1 HP2 ltac:(lia) ltac:(lia) ltac:(lia) WIN SV1) as SV2.
  assert (CK : forall a val, (S - 144 <= a /\ a + 8 <= S) \/ (v <= a /\ a + 8 <= v + 24) -> L5.u64_at RSEGS M1 a val -> L5.u64_at RSEGS M2 a val).
  { intros a val Ha X. exact (cell_callee _ LK cr Aw M1 model1 M2 [(B, A)] (S - 144) 12288 _ a val HH1 MO1 HP2 ltac:(lia) ltac:(lia) ltac:(lia) WIN Ha X). }
  pose proof (PGVAPK.blksh_ek L ar C HI LY HIok _ FF (S - 144) 12288 _ M1 M2 B A (proj1 HP2) ltac:(intros rg []) ltac:(left; reflexivity) ltac:(lia) ltac:(lia)) as AGB.
  assert (CS2 : forall i, In i L5SAR.cs_all -> getr R2 (reg i) = getr R1 (reg i)) by (intros i Hi; exact (L5SAR.cs_of_preserved R1 R2 i RP2 Hi)).
  destruct GB1 as (B1' & B2' & B3' & B4').
  apply (sw_B fx2 R2 M2 model2 LK2 Aw2 cr B A g').
  - rewrite CS2 by inl. exact A2.
  - rewrite CS2 by inl. exact A8.
  - rewrite CS2 by inl. exact A9.
  - rewrite CS2 by inl. exact A21.
  - exact (kept0_pres R1 R2 KP1 RP2).
  - exact (stok_step model1 LK Aw model2 LK2 Aw2 SO1 AM2 MRT2 ILK2 IAW2).
  - exact MO2.
  - exact SV2.
  - apply CK; [left; lia| exact S32a].
  - unfold ssaves. repeat split; (apply CK; [left; lia|]; apply VUP; [left; lia| assumption]).
  - exact HH2s.
  - destruct HD2 as (_ & HR). destruct (v8_case x) as [EX|(b & n & c & EX)]; rewrite EX in HR |- *; cbn [PGV8.v8_data PGV8.v8_size PGV8.v8_cap].
    + destruct HR as (H0 & H8 & H16). split; [exact H0|]. split; [exact H8| exact H16].
    + destruct HR as (H0 & H8 & H16 & _). split; [exact H0|]. split; [exact H8| exact H16].
  - split; [apply CK; [left; lia| exact B1']|]. split; [apply CK; [left; lia| exact B2']|]. split; [apply CK; [left; lia| exact B3']| apply CK; [left; lia| exact B4']].
  - exact HA.
  - exact HnkA.
  - apply (PGVAPK.shblk_agree L ar C HI LY HIok M1 M2 B A); [apply PMKA.mod16_8'; exact QB4| lia| exact AGB| exact SHB1].
  - intros b n c EX. pose proof xr as XR. rewrite EX in XR. cbv beta iota in XR.
    apply (PGVAPK.aacc_sub L ar C HI LY HIok M2 b c); [exact (ACX2 b n c EX)| lia| lia].
  - exact PO.
Qed.

Lemma gtail_ok : PGVAPK.gtail L ar HI R0 M0 model0 K LB FF LK0 Aw0 cr0 v S g k x.
Proof using All.
  exact sw_A.
Qed.

End Call.

End WithHeap.
End PGVAPG.
