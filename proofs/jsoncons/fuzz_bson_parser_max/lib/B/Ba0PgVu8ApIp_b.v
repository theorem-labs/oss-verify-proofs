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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require PnAVu8LoopP_b.

Module PGVAPI.
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
#[local] Abbreviation SA f := (f L ar C HI LY HIok R0 M0 model0 K LB FF LK0 Aw0 cr0 v S r g k x Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRS AO V8 OK0 Hk GROK CRL0 KONT OPN OPD ANNI ANNN ANND VS0 HH0 Ra0 Ra1 AM0 STK0 STKSH0).

Lemma u8b (M : word -> option byte) a w : byte_at M a w -> L5.u8_at RSEGS M a w.
Proof using All. intros B. unfold L5.u8_at. cbn [rdn]. unfold byte_at in B. rewrite B. reflexivity. Qed.

Lemma wblk HL LK cr Aw M model q m : ri_inv HI (HL ++ LB) FF LK cr Aw M (vml_of model) -> In (q, m) HL ->
  L5.writable RSEGS (mrestrict (ahid Aw model) M) q m.
Proof using All.
  intros HH Hin. assert (Hin' : In (q, m) (HL ++ LB)) by (apply in_or_app; left; exact Hin).
  pose proof (L5SAR.vis_pack L ar C HI (PMA.ly_as0 L C LY) HIok _ FF LK cr Aw M model HH) as (_ & _ & _ & _ & VB & _).
  destruct (PNAEK.blk_facts L ar C HI LY HIok _ FF LK cr Aw M _ q m HH Hin') as (Q0 & Q1 & Q2 & Q3 & _ & _ & _ & QD & _).
  apply (proj2 (L5A.writable_vis (ahid Aw model) M q m (VB q m q m Hin' ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
  apply (L5C.writable_of_defined RSEGS M q m QD); lia.
Qed.

Lemma sdwf HL LK cr Aw M model q m p e : ri_inv HI (HL ++ LB) FF LK cr Aw M (vml_of model) -> In (q, m) HL ->
  q <= p -> p + e <= q + m -> PMSPA.accA M p e ->
  forall i, 0 <= i < e -> exists s, L5.u8_at RSEGS (mrestrict (ahid Aw model) M) ((p + i) / 8 + HeapIfaceA.SB) s
    /\ (s = 0 \/ (1 <= s <= 7 /\ 1 <= s - Z.land (p + i) 7)).
Proof using All.
  intros HH Hin H1 H2 ACC i Hi. assert (Hin' : In (q, m) (HL ++ LB)) by (apply in_or_app; left; exact Hin).
  pose proof (L5SAR.vis_pack L ar C HI (PMA.ly_as0 L C LY) HIok _ FF LK cr Aw M model HH) as (_ & _ & _ & _ & _ & VBS & _).
  destruct (PNAEK.blk_facts L ar C HI LY HIok _ FF LK cr Aw M _ q m HH Hin') as (Q0 & Q1 & Q2 & Q3 & _).
  unfold PMSPA.accA, aacc in ACC.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (SR : 0 <= HeapIfaceA.S (p + i) /\ HeapIfaceA.S (p + i) + 1 <= 2 ^ 64).
  { clear - Q0 Q3 H1 H2 Hi. unfold HeapIfaceA.S, HeapIfaceA.SB. Lia.lia. }
  assert (AV : L5A.avis (ahid Aw model) (HeapIfaceA.S (p + i)) 1).
  { apply (VBS q m _ _ Hin'). intros t Ht. replace (HeapIfaceA.S (p + i) + t) with (HeapIfaceA.S (p + i)) by (clear - Ht; Lia.lia).
    unfold in_shadow_of. split; apply PMKA.S_mono; clear - H1 H2 Hi; Lia.lia. }
  assert (LA : Z.land (p + i) 7 = (p + i) mod 8).
  { change 7 with (Z.ones 3). rewrite Z.land_ones by (clear; Lia.lia). reflexivity. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  change ((p + i) / 8 + HeapIfaceA.SB) with (HeapIfaceA.S (p + i)).
  destruct (ACC (p + i) ltac:(lia)) as [Z0|(s & Bs & Hs1 & Hs2)].
  - exists 0. split; [| left; reflexivity].
    apply (proj2 (L5A.u8_at_vis (ahid Aw model) M _ 0 AV ltac:(lia) ltac:(lia))). exact (u8b M _ 0 Z0).
  - exists s. split.
    + apply (proj2 (L5A.u8_at_vis (ahid Aw model) M _ s AV ltac:(lia) ltac:(lia))). exact (u8b M _ s Bs).
    + right. rewrite LA. lia.
Qed.

Ltac pfb XW XSZ XAV SDF :=
  first [ assumption
        | lazymatch goal with
          | |- L5.u64_at _ (mrestrict ?H ?M) ?a ?val => apply (proj2 (L5A.u64_at_vis H M a val (XAV a 8 ltac:(lia)) ltac:(lia) ltac:(lia))); assumption
          | |- L5.writable _ _ _ _ => apply XW; lia
          | |- L5KA.zeros_at _ (?a / 8 + ?c) ?m =>
              replace (a / 8 + c) with ((a + (- m) * 8) / 8 + HeapIfaceA.SB) by (rewrite Z_div_plus_full by lia; unfold HeapIfaceA.SB; lia);
              apply XSZ; [lia| lia| rewrite Z_mod_plus_full; apply PMKA.mod16_8'; assumption| lia]
          | |- PMAVGP.aligned _ _ => unfold PMAVGP.aligned; lia
          | |- forall _ : Z, _ => let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi; first [ apply SDF; lia | split; [lia| split; lia] ]
          | |- _ => lia
          end ].


Lemma ip_inc_b (fx : FPState) R M model LK Aw b n c :
  x = PGV8.V8Blk b n c -> n + k <= c ->
  getr R (reg 1) = Z_to_bv 64 0xb5a18 -> getr R (reg 2) = Z_to_bv 64 (S - 48) -> getr R (reg 8) = Z_to_bv 64 2147450880 ->
  getr R (reg 9) = Z_to_bv 64 (b + (n + k)) -> getr R (reg 10) = Z_to_bv 64 v -> getr R (reg 11) = Z_to_bv 64 k ->
  (forall i, In i [18; 19; 20; 21]%nat -> getr R (reg i) = Z_to_bv 64 (U i)) -> kept0 R ->
  stok model LK Aw -> mem_ok M -> saves M -> ri_inv HI ([(b, c)] ++ LB) FF LK cr0 Aw M (vml_of model) -> v8_atA M v x ->
  L5.u64_at RSEGS M (S - 32) (b + (n + k)) -> L5.u64_at RSEGS M (S - 40) (b + n) -> L5.u64_at RSEGS M (S - 48) v ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0xb609c M model) K.
Proof using All.
  intros EX Hnk E1 E2 E8 E9 E10 E11 EU KP SO MO SV HH VS C32 C40 C48.
  pose proof (SA PGVAPK.xr) as XR. rewrite EX in XR. destruct XR as (Hn & Hc & Hb & Hb16 & Hbc).
  pose proof (SA PGVAPK.xnum) as XN. rewrite EX in XN. cbn [PGV8.v8_data PGV8.v8_size PGV8.v8_cap] in XN.
  destruct XN as (_ & _ & _ & Hk27 & Hnk27 & _).
  pose proof (SA PGVAPK.centry0 R [(b, c)] LK cr0 Aw M model 48 _ HH MO KP E1) as CE.
  destruct (CE ltac:(split; [lia| reflexivity]) E2 ltac:(lia) ltac:(reflexivity)) as (ENT & FRSc). clear CE.
  pose proof SO as (AM & MRT & ILK & IAW). pose proof MO as (_ & _ & _ & ACC & _).
  pose proof ANNI as AI. unfold PNSAX8.ann_increase_v8_spec in AI.
  assert (HHx : ri_inv HI (PGV8.v8_own x ++ LB) FF LK cr0 Aw M (vml_of model)) by (rewrite EX; exact HH).
  assert (A10 : getr R 10%bv = Z_to_bv 64 v) by (rewrite L5K.rl10; exact E10).
  assert (A11 : getr R 11%bv = Z_to_bv 64 k) by (rewrite L5SAR.r11; exact E11).
  assert (Hsz : PGV8.v8_size x + k <= PGV8.v8_cap x) by (rewrite EX; cbn [PGV8.v8_size PGV8.v8_cap]; lia).
  unfold PMSP.cfg.
  apply (AI fx R M model K LB FF LK Aw cr0 v k x (S - 48) _ HHx AM K0 ENT FRSc A10 A11 AO V8 ACC VS ltac:(lia) Hsz).
  clear AI HHx A10 A11 Hsz ENT FRSc.
  intros fx1 R1 M1 model1 LK1 Aw1 RP1 HD1 ACC1 BLK1 KEPT1 HP1 MRT1 ILK1 IAW1 AM1 HH1.
  change (PMSPA.pm_scr 0) with 12288 in HP1.
  rewrite EX in HH1, HD1. cbn [PGV8.v8_own] in HH1.
  assert (WIN : forall rg, In rg (@nil L5.range) -> exists q m, In (q, m) [(b, c)] /\ q <= fst rg /\ fst rg + snd rg <= q + m) by (intros rg []).
  pose proof (SA PGVAPK.mem_ok_callee _ [] LK cr0 Aw M model M1 (S - 48) 12288 _ HH MO HP1 ltac:(lia) ltac:(lia) ltac:(lia) WIN) as MO1.
  pose proof (SA PGVAPK.saves_callee _ LK cr0 Aw M model M1 [] (S - 48) 12288 _ HH MO HP1 ltac:(lia) ltac:(lia) ltac:(lia) WIN SV) as SV1.
  pose proof (SA PGVAPK.cell_callee _ LK cr0 Aw M model M1 [] (S - 48) 12288 _ (S - 32) _ HH MO HP1 ltac:(lia) ltac:(lia) ltac:(lia) WIN ltac:(left; lia) C32) as C32a.
  pose proof (SA PGVAPK.cell_callee _ LK cr0 Aw M model M1 [] (S - 48) 12288 _ (S - 40) _ HH MO HP1 ltac:(lia) ltac:(lia) ltac:(lia) WIN ltac:(left; lia) C40) as C40a.
  pose proof (SA PGVAPK.cell_callee _ LK cr0 Aw M model M1 [] (S - 48) 12288 _ (S - 48) _ HH MO HP1 ltac:(lia) ltac:(lia) ltac:(lia) WIN ltac:(left; lia) C48) as C48a.
  destruct HD1 as (_ & W0 & W8 & W16 & _).
  destruct (BLK1 b n c EX) as (ACB & ANB).
  assert (CS1 : forall i, In i L5SAR.cs_all -> getr R1 (reg i) = getr R (reg i)) by (intros i Hi; exact (L5SAR.cs_of_preserved R R1 i RP1 Hi)).
  assert (SO1 : stok model1 LK1 Aw1) by exact (SA PGVAPK.stok_step model LK Aw model1 LK1 Aw1 SO AM1 MRT1 ILK1 IAW1).
  assert (KP1 : kept0 R1) by exact (SA PGVAPK.kept0_pres R R1 KP RP1).
  pose proof (eq_trans (CS1 2%nat ltac:(inl)) E2) as E2a.
  pose proof (eq_trans (CS1 8%nat ltac:(inl)) E8) as E8a.
  pose proof (eq_trans (CS1 9%nat ltac:(inl)) E9) as E9a.
  assert (EUa : forall i, In i [18; 19; 20; 21]%nat -> getr R1 (reg i) = Z_to_bv 64 (U i)).
  { intros i Hi. rewrite CS1 by (unfold L5SAR.cs_all; cbn in Hi |- *; tauto). exact (EU i Hi). }
  clear CS1 RP1 MRT1 ILK1 IAW1 AM1 HP1 BLK1 KEPT1 ACC1 WIN E1 E2 E8 E9 E10 E11 EU KP SO MO SV HH VS C32 C40 C48 AM MRT ILK IAW ACC.
  pose proof SV1 as (S8a & S16a & S24a).
  destruct (SA PGVAPK.nfacts _ LK1 cr0 Aw1 M1 model1 HH1 MO1) as ((A16 & SLO & SHI & SPT & C0) & (O1 & O2 & O5 & _) & BF).
  destruct (BF b c ltac:(left; reflexivity)) as (_ & _ & _ & _ & _ & BV & _). clear BF.
  unfold PGVAPK.nsh in O5.
  destruct (PNAEK.blk_facts L ar C HI LY HIok _ FF LK1 cr0 Aw1 M1 _ b c HH1 ltac:(left; reflexivity)) as (Q0 & Q1 & Q2 & Q3 & Q4 & QIMG & QNSH & _ & _).
  assert (UB : forall i, 0 <= U i < 2 ^ 64) by (intros i; unfold PGVAPK.U; apply bv_unsigned_in_range).
  pose proof (UB 1%nat) as UB1. pose proof (UB 8%nat) as UB8. pose proof (UB 9%nat) as UB9. clear UB.
  destruct (SA PGVAPK.vfacts _ LK1 cr0 Aw1 M1 model1 HH1 MO1) as (X0 & X1 & X2 & XW & XZ & XWV & XSZ & XAV).
  pose proof (wblk _ LK1 cr0 Aw1 M1 model1 b c HH1 ltac:(left; reflexivity)) as XWB.
  LeanFeed.pfeed PB (PMAVGP.avaB_conc fx1 R1 (mrestrict (ahid Aw1 model1) M1) (fun j => match j with 2%nat => S | 37%nat => v | 40%nat => b | 41%nat => n | 42%nat => c | 43%nat => k
     | 48%nat => U 1 | 49%nat => U 8 | 50%nat => U 9 | _ => 0 end)) ltac:(pfb XW XSZ XAV I).
  destruct PB as (fx2 & R2 & M2v & MG2 & _ & FZ2 & MS2 & KS2 & B10 & B11 & B12 & B13 & D8 & D16 & D24 & D32 & D40 & D48).
  clear X0 X1 X2 XW XZ XWV XSZ XAV XWB.
  apply (SA PGVAPK.piece_step fx1 fx2 R1 _ R2 _ [(b, c)] M1 model1 cr0 LK1 Aw1 M2v (fun a => S - 128 <= a < S - 128 + 128) HH1 SO1 MO1 MS2 MG2 FZ2).
  { intros a Pa. cbv beta in Pa. left. lia. }
  intros M2 model2 HH2 SO2 MO2 FR2 VUP2 AGS2.
  pose proof (eq_trans (KS2 2%nat ltac:(inl)) E2a) as E2b.
  pose proof (eq_trans (KS2 8%nat ltac:(inl)) E8a) as E8b.
  pose proof (eq_trans (KS2 9%nat ltac:(inl)) E9a) as E9b.
  assert (EUb : forall i, In i [18; 19; 20; 21]%nat -> getr R2 (reg i) = Z_to_bv 64 (U i)).
  { intros i Hi. rewrite KS2 by (cbn in Hi; repeat (destruct Hi as [<-|Hi]; [inl|]); destruct Hi). exact (EUa i Hi). }
  assert (KP2 : kept0 R2).
  { apply (SA PGVAPK.kept0_of R1 R2 KP1). intros i Hi. apply KS2. cbn in Hi. repeat (destruct Hi as [<-|Hi]; [inl|]). destruct Hi. }
  pose proof (VUP2 (S - 8) (U 1) ltac:(left; lia) D8) as S8b.
  pose proof (VUP2 (S - 16) (U 8) ltac:(left; lia) D16) as S16b.
  pose proof (VUP2 (S - 24) (U 9) ltac:(left; lia) D24) as S24b.
  pose proof (VUP2 (S - 32) _ ltac:(left; lia) D32) as C32b.
  pose proof (VUP2 (S - 40) _ ltac:(left; lia) D40) as C40b.
  pose proof (VUP2 (S - 48) _ ltac:(left; lia) D48) as C48b.
  pose proof (SA PGVAPK.cell_piece M1 M2 _ v b FR2 ltac:(intros i Hi Pi; cbv beta in Pi; lia) ltac:(lia) ltac:(lia) W0) as W0b.
  pose proof (SA PGVAPK.cell_piece M1 M2 _ (v + 8) _ FR2 ltac:(intros i Hi Pi; cbv beta in Pi; lia) ltac:(lia) ltac:(lia) W8) as W8b.
  pose proof (SA PGVAPK.cell_piece M1 M2 _ (v + 16) _ FR2 ltac:(intros i Hi Pi; cbv beta in Pi; lia) ltac:(lia) ltac:(lia) W16) as W16b.
  pose proof (PMFA.accA_agree M1 M2 b (n + k) (AGS2 b (n + k) ltac:(lia) ltac:(lia)) ACB) as ACB2.
  pose proof (PGV8KA.annA_agree M1 M2 b (n + k) c ltac:(lia) (PMKA.mod16_8' _ Hb16) (AGS2 b c ltac:(lia) ltac:(lia)) ANB) as ANB2.
  clear KS2 E2a E8a E9a EUa KP1 D8 D16 D24 D32 D40 D48 S8a S16a S24a C32a C40a C48a W0 W8 W16 ACB ANB FR2 VUP2 AGS2 MS2 MG2 FZ2 HH1 SO1 MO1 SV1.
  destruct (SA PGVAPK.vfacts _ LK1 cr0 Aw1 M2 model2 HH2 MO2) as (X0 & X1 & X2 & XW & XZ & XWV & XSZ & XAV).
  pose proof (wblk _ LK1 cr0 Aw1 M2 model2 b c HH2 ltac:(left; reflexivity)) as XWB.
  pose proof (sdwf _ LK1 cr0 Aw1 M2 model2 b c b (n + k) HH2 ltac:(left; reflexivity) ltac:(lia) ltac:(lia) ACB2) as SDF.
  LeanFeed.pfeed PL (PnAVu8LoopP_b.PMAVLP.avaBLoop_conc fx2 R2 (mrestrict (ahid Aw1 model2) M2) (fun j => match j with 2%nat => S | 37%nat => v | 40%nat => b | 41%nat => n | 42%nat => c | 43%nat => k
     | 48%nat => U 1 | 49%nat => U 8 | 50%nat => U 9 | 56%nat => n | _ => 0 end)) ltac:(pfb XW XSZ XAV SDF).
  destruct PL as (fx3 & R3 & M3v & MG3 & _ & FZ3 & MS3 & KS3 & L1 & L10 & L11 & F8 & F16 & F24 & F32 & F40 & F48 & _).
  clear X0 X1 X2 XW XZ XWV XSZ XAV XWB SDF.
  apply (SA PGVAPK.piece_step fx2 fx3 R2 _ R3 _ [(b, c)] M2 model2 cr0 LK1 Aw1 M3v (fun a => S - 128 <= a < S - 128 + 128 \/ b + n <= a < b + (n + k)) HH2 SO2 MO2 MS3 MG3).
  { intros a Ha NP. apply FZ3; [exact Ha| intros X; apply NP; left; exact X| intros X; apply NP; right; exact X]. }
  { intros a Pa. cbv beta in Pa. destruct Pa as [Pa|Pa]; [left; lia| right; right; exists b, c; split; [left; reflexivity| lia]]. }
  intros M3 model3 HH3 SO3 MO3 FR3 VUP3 AGS3.
  pose proof (eq_trans (KS3 2%nat ltac:(inl)) E2b) as E2c.
  pose proof (eq_trans (KS3 8%nat ltac:(inl)) E8b) as E8c.
  pose proof (eq_trans (KS3 9%nat ltac:(inl)) E9b) as E9c.
  pose proof (eq_trans (KS3 12%nat ltac:(inl)) B12) as B12c.
  assert (EUc : forall i, In i [18; 19; 20; 21]%nat -> getr R3 (reg i) = Z_to_bv 64 (U i)).
  { intros i Hi. rewrite KS3 by (cbn in Hi; repeat (destruct Hi as [<-|Hi]; [inl|]); destruct Hi). exact (EUb i Hi). }
  assert (KP3 : kept0 R3).
  { apply (SA PGVAPK.kept0_of R2 R3 KP2). intros i Hi. apply KS3. cbn in Hi. repeat (destruct Hi as [<-|Hi]; [inl|]). destruct Hi. }
  pose proof (VUP3 (S - 8) (U 1) ltac:(left; lia) F8) as S8c.
  pose proof (VUP3 (S - 16) (U 8) ltac:(left; lia) F16) as S16c.
  pose proof (VUP3 (S - 24) (U 9) ltac:(left; lia) F24) as S24c.
  pose proof (VUP3 (S - 32) _ ltac:(left; lia) F32) as C32c.
  pose proof (VUP3 (S - 40) _ ltac:(left; lia) F40) as C40c.
  pose proof (VUP3 (S - 48) _ ltac:(left; lia) F48) as C48c.
  pose proof (SA PGVAPK.cell_piece M2 M3 _ v b FR3 ltac:(intros i Hi Pi; cbv beta in Pi; lia) ltac:(lia) ltac:(lia) W0b) as W0c.
  pose proof (SA PGVAPK.cell_piece M2 M3 _ (v + 16) _ FR3 ltac:(intros i Hi Pi; cbv beta in Pi; lia) ltac:(lia) ltac:(lia) W16b) as W16c.
  pose proof (PMFA.accA_agree M2 M3 b (n + k) (AGS3 b (n + k) ltac:(lia) ltac:(lia)) ACB2) as ACB3.
  pose proof (PGV8KA.annA_agree M2 M3 b (n + k) c ltac:(lia) (PMKA.mod16_8' _ Hb16) (AGS3 b c ltac:(lia) ltac:(lia)) ANB2) as ANB3.
  clear KS3 E2b E8b E9b EUb KP2 B10 B11 B12 B13 F8 F16 F24 F32 F40 F48 S8b S16b S24b C32b C40b C48b W0b W8b W16b ACB2 ANB2 FR3 VUP3 AGS3 MS3 MG3 FZ3 HH2 SO2 MO2.
  destruct (SA PGVAPK.vfacts _ LK1 cr0 Aw1 M3 model3 HH3 MO3) as (X0 & X1 & X2 & XW & XZ & XWV & XSZ & XAV).
  pose proof (wblk _ LK1 cr0 Aw1 M3 model3 b c HH3 ltac:(left; reflexivity)) as XWB.
  LeanFeed.pfeed PC (PMAVGP.avaC_conc fx3 R3 (mrestrict (ahid Aw1 model3) M3) (fun j => match j with 2%nat => S | 37%nat => v | 40%nat => b | 41%nat => n | 42%nat => c | 43%nat => k
     | 48%nat => U 1 | 49%nat => U 8 | 50%nat => U 9 | _ => 0 end)) ltac:(pfb XW XSZ XAV I).
  destruct PC as (fx4 & R4 & M4v & MG4 & _ & FZ4 & MS4 & KS4 & G1 & G2 & G8 & G9 & _ & _ & _ & _ & _ & G8c & _).
  clear X0 X1 X2 XW XZ XWV XSZ XAV XWB.
  apply (SA PGVAPK.piece_step fx3 fx4 R3 _ R4 _ [(b, c)] M3 model3 cr0 LK1 Aw1 M4v (fun a => S - 128 <= a < S - 128 + 128 \/ v + 8 <= a < v + 8 + 8) HH3 SO3 MO3 MS4 MG4).
  { intros a Ha NP. apply FZ4; [exact Ha| intros X; apply NP; left; exact X| intros X; apply NP; right; exact X]. }
  { intros a Pa. cbv beta in Pa. destruct Pa as [Pa|Pa]; [left; lia| right; left; lia]. }
  intros M4 model4 HH4 SO4 MO4 FR4 VUP4 AGS4.
  pose proof (VUP4 (v + 8) _ ltac:(right; lia) G8c) as W8d.
  pose proof (SA PGVAPK.cell_piece M3 M4 _ v b FR4 ltac:(intros i Hi Pi; cbv beta in Pi; lia) ltac:(lia) ltac:(lia) W0c) as W0d.
  pose proof (SA PGVAPK.cell_piece M3 M4 _ (v + 16) _ FR4 ltac:(intros i Hi Pi; cbv beta in Pi; lia) ltac:(lia) ltac:(lia) W16c) as W16d.
  pose proof (PMFA.accA_agree M3 M4 b (n + k) (AGS4 b (n + k) ltac:(lia) ltac:(lia)) ACB3) as ACB4.
  pose proof (PGV8KA.annA_agree M3 M4 b (n + k) c ltac:(lia) (PMKA.mod16_8' _ Hb16) (AGS4 b c ltac:(lia) ltac:(lia)) ANB3) as ANB4.
  destruct (SA PGVAPK.nfacts _ LK1 cr0 Aw1 M4 model4 HH4 MO4) as (_ & (_ & _ & _ & ODEF4) & BF4).
  destruct (BF4 b c ltac:(left; reflexivity)) as (_ & _ & _ & _ & _ & _ & QD4). clear BF4.
  pose proof MO4 as (_ & _ & _ & ACC4 & _).
  apply (SA PGVAPK.finish_p fx4 R4 M4 model4 LK1 Aw1 (PGV8.V8Blk b (n + k) c) g cr0 0xb5a7c W_b5a7c F_b5a7c eq_refl D_b5a7c).
  - exact G1.
  - exact G2.
  - intros i Hi. cbn in Hi. destruct Hi as [<-|[<-|Hi]]; [exact G8| exact G9|].
    rewrite KS4 by (repeat (destruct Hi as [<-|Hi]; [inl|]); destruct Hi). exact (EUc i Hi).
  - apply (SA PGVAPK.kept0_of R3 R4 KP3). intros i Hi. apply KS4. cbn in Hi. repeat (destruct Hi as [<-|Hi]; [inl|]). destruct Hi.
  - exact SO4.
  - exact MO4.
  - exact HH4.
  - split; [exact ODEF4|]. split; [exact ACC4|]. split; [exact W0d|]. split; [exact W8d|]. split; [exact W16d|].
    split; [lia|]. split; [lia|]. split; [exact Hb|]. split; [exact Hb16|]. split; [exact QD4|]. split; [exact ACB4| exact ANB4].
  - unfold PGVAPK.post_ok. pose proof OK0 as OK1. rewrite EX in OK1 |- *.
    cbn [PGV8.v8_size PGV8.v8_cap PGV8.v8_own].
    split; [lia|]. split; [exact OK1|]. split; [lia|]. split; [intros _; split; [reflexivity| split; reflexivity]|]. split; [left; reflexivity|].
    unfold PMSP.credit_keep, PMSPA.scA, PGV8.pot_v8. cbn [fst snd PGV8.v8_cap]. lia.
Qed.

End Call.

End WithHeap.
End PGVAPI.
