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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require PnAVu8LoopP_b Ba0PgVu8ApIp_b Ba0PgVu8ApG_b.

Module PGVAPA.
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

(* [comment removed for export] *)
(* [comment removed for export] *)
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

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac pfeed XW XSZ XAV :=
  first [ assumption
        | lazymatch goal with
          | |- L5.u64_at _ (mrestrict ?H ?M) ?a ?val => apply (proj2 (L5A.u64_at_vis H M a val (XAV a 8 ltac:(lia)) ltac:(lia) ltac:(lia))); assumption
          | |- L5.writable _ _ _ _ => apply XW; lia
          | |- L5KA.zeros_at _ _ _ => apply XSZ; lia
          | |- PMAVGP.aligned _ _ => unfold PMAVGP.aligned; lia
          | |- _ => lia
          end ].

#[local] Abbreviation blksh_ek := (PGVAPK.blksh_ek L ar C HI LY HIok).
#[local] Abbreviation objsh_ek := (PGVAPK.objsh_ek L ar C HI LY HIok).
#[local] Abbreviation obj_ek := (PGVAPK.obj_ek L ar C HI LY HIok).
#[local] Abbreviation shblk_agree := (PGVAPK.shblk_agree L ar C HI LY HIok).
#[local] Abbreviation U := (PGVAPK.U R0).
#[local] Abbreviation saves := (PGVAPK.saves R0 S).
#[local] Abbreviation kept0 := (PGVAPK.kept0 R0).
#[local] Abbreviation stok := (PGVAPK.stok model0 LK0 Aw0).
#[local] Abbreviation mem_ok := (PGVAPK.mem_ok L ar M0 LB FF v S).
#[local] Abbreviation kept0_of := (PGVAPK.kept0_of L ar C HI LY HIok R0 M0 model0 K LB FF LK0 Aw0 cr0 v S r g k x Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRS AO V8 OK0 Hk GROK CRL0 KONT OPN OPD ANNI ANNN ANND VS0 HH0 Ra0 Ra1 AM0 STK0 STKSH0).
#[local] Abbreviation kept0_pres := (PGVAPK.kept0_pres L ar C HI LY HIok R0 M0 model0 K LB FF LK0 Aw0 cr0 v S r g k x Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRS AO V8 OK0 Hk GROK CRL0 KONT OPN OPD ANNI ANNN ANND VS0 HH0 Ra0 Ra1 AM0 STK0 STKSH0).
#[local] Abbreviation stok_step := (PGVAPK.stok_step L ar C HI LY HIok R0 M0 model0 K LB FF LK0 Aw0 cr0 v S r g k x Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRS AO V8 OK0 Hk GROK CRL0 KONT OPN OPD ANNI ANNN ANND VS0 HH0 Ra0 Ra1 AM0 STK0 STKSH0).
#[local] Abbreviation nfacts := (PGVAPK.nfacts L ar C HI LY HIok R0 M0 model0 K LB FF LK0 Aw0 cr0 v S r g k x Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRS AO V8 OK0 Hk GROK CRL0 KONT OPN OPD ANNI ANNN ANND VS0 HH0 Ra0 Ra1 AM0 STK0 STKSH0).
#[local] Abbreviation vfacts := (PGVAPK.vfacts L ar C HI LY HIok R0 M0 model0 K LB FF LK0 Aw0 cr0 v S r g k x Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRS AO V8 OK0 Hk GROK CRL0 KONT OPN OPD ANNI ANNN ANND VS0 HH0 Ra0 Ra1 AM0 STK0 STKSH0).
#[local] Abbreviation mem_ok_callee := (PGVAPK.mem_ok_callee L ar C HI LY HIok R0 M0 model0 K LB FF LK0 Aw0 cr0 v S r g k x Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRS AO V8 OK0 Hk GROK CRL0 KONT OPN OPD ANNI ANNN ANND VS0 HH0 Ra0 Ra1 AM0 STK0 STKSH0).
#[local] Abbreviation cell_callee := (PGVAPK.cell_callee L ar C HI LY HIok R0 M0 model0 K LB FF LK0 Aw0 cr0 v S r g k x Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRS AO V8 OK0 Hk GROK CRL0 KONT OPN OPD ANNI ANNN ANND VS0 HH0 Ra0 Ra1 AM0 STK0 STKSH0).
#[local] Abbreviation grow_credit := (PGVAPK.grow_credit L ar C HI LY HIok R0 M0 model0 K LB FF LK0 Aw0 cr0 v S r g k x Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRS AO V8 OK0 Hk GROK CRL0 KONT OPN OPD ANNI ANNN ANND VS0 HH0 Ra0 Ra1 AM0 STK0 STKSH0).
#[local] Abbreviation piece_step := (PGVAPK.piece_step L ar C HI LY HIok R0 M0 model0 K LB FF LK0 Aw0 cr0 v S r g k x Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRS AO V8 OK0 Hk GROK CRL0 KONT OPN OPD ANNI ANNN ANND VS0 HH0 Ra0 Ra1 AM0 STK0 STKSH0).
#[local] Abbreviation saves_callee := (PGVAPK.saves_callee L ar C HI LY HIok R0 M0 model0 K LB FF LK0 Aw0 cr0 v S r g k x Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRS AO V8 OK0 Hk GROK CRL0 KONT OPN OPD ANNI ANNN ANND VS0 HH0 Ra0 Ra1 AM0 STK0 STKSH0).
#[local] Abbreviation cstk := (PGVAPK.cstk L ar C HI LY HIok R0 M0 model0 K LB FF LK0 Aw0 cr0 v S r g k x Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRS AO V8 OK0 Hk GROK CRL0 KONT OPN OPD ANNI ANNN ANND VS0 HH0 Ra0 Ra1 AM0 STK0 STKSH0).
#[local] Abbreviation xr := (PGVAPK.xr L ar C HI LY HIok R0 M0 model0 K LB FF LK0 Aw0 cr0 v S r g k x Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRS AO V8 OK0 Hk GROK CRL0 KONT OPN OPD ANNI ANNN ANND VS0 HH0 Ra0 Ra1 AM0 STK0 STKSH0).
#[local] Abbreviation xnum := (PGVAPK.xnum L ar C HI LY HIok R0 M0 model0 K LB FF LK0 Aw0 cr0 v S r g k x Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRS AO V8 OK0 Hk GROK CRL0 KONT OPN OPD ANNI ANNN ANND VS0 HH0 Ra0 Ra1 AM0 STK0 STKSH0).
#[local] Abbreviation post_ok := (PGVAPK.post_ok L ar cr0 g k x).
#[local] Abbreviation gbuf := (PGVAPK.gbuf S).
#[local] Abbreviation v8_at_agree := (PGVAPK.v8_at_agree L ar C HI LY HIok R0 M0 model0 K LB FF LK0 Aw0 cr0 v S r g k x Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRS AO V8 OK0 Hk GROK CRL0 KONT OPN OPD ANNI ANNN ANND VS0 HH0 Ra0 Ra1 AM0 STK0 STKSH0).
#[local] Abbreviation v8_case := (PGVAPK.v8_case L ar C HI LY HIok R0 M0 model0 K LB FF LK0 Aw0 cr0 v S r g k x Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRS AO V8 OK0 Hk GROK CRL0 KONT OPN OPD ANNI ANNN ANND VS0 HH0 Ra0 Ra1 AM0 STK0 STKSH0).
#[local] Abbreviation ip_inc_b := (Ba0PgVu8ApIp_b.PGVAPI.ip_inc_b L ar C HI LY HIok R0 M0 model0 K LB FF LK0 Aw0 cr0 v S r g k x Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRS AO V8 OK0 Hk GROK CRL0 KONT OPN OPD ANNI ANNN ANND VS0 HH0 Ra0 Ra1 AM0 STK0 STKSH0).
#[local] Abbreviation gtail_ok := (Ba0PgVu8ApG_b.PGVAPG.gtail_ok L ar C HI LY HIok R0 M0 model0 K LB FF LK0 Aw0 cr0 v S r g k x Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRS AO V8 OK0 Hk GROK CRL0 KONT OPN OPD ANNI ANNN ANND VS0 HH0 Ra0 Ra1 AM0 STK0 STKSH0).

Lemma room_mod n c : 0 <= n <= c -> c <= 2 ^ 27 -> ((18446744073709551615 * n) mod 2 ^ 64 + c) mod 2 ^ 64 = c - n.
Proof.
  intros H1 H2. rewrite Zplus_mod_idemp_l. replace (18446744073709551615 * n + c) with ((c - n) + n * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma model_rt_refl (m : Model) : model_rt m m.
Proof. destruct m; reflexivity. Qed.
Lemma stok0 : stok model0 LK0 Aw0.
Proof using All. split; [exact AM0|]. split; [apply model_rt_refl|]. split; apply incl_refl. Qed.
Lemma mem_ok0 : mem_ok M0.
Proof using All.
  split; [intros a _; reflexivity|]. split; [intros a _ _ X; exact X|]. split; [exact STK0|]. split; [destruct VS0 as (_ & X & _); exact X| exact STKSH0].
Qed.

Definition gsv (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M (S - 96) (U 18) /\ L5.u64_at RSEGS M (S - 104) (U 19) /\ L5.u64_at RSEGS M (S - 112) (U 20)
  /\ L5.u64_at RSEGS M (S - 120) (U 21).

Lemma zs512 (Mx : word -> option byte) H :
  (forall a n, S - 14336 <= a -> a + 8 * n <= S -> a mod 8 = 0 -> 0 <= n -> L5KA.zeros_at (mrestrict H Mx) (a / 8 + 2147450880) n) ->
  S mod 16 = 0 -> L5KA.zeros_at (mrestrict H Mx) (S / 8 + 2147450368) 512.
Proof using All.
  intros XSZ A16. replace (S / 8 + 2147450368) with ((S - 4096) / 8 + 2147450880).
  - apply XSZ; [lia| lia| | lia]. replace (S - 4096) with (S + (-512) * 8) by lia. rewrite Z_mod_plus_full. apply PMKA.mod16_8'. exact A16.
  - replace (S - 4096) with (S + (-512) * 8) by lia. rewrite Z_div_plus_full by lia. lia.
Qed.
Lemma u8_of_byte (Mx : word -> option byte) a w : byte_at Mx a w -> L5.u8_at RSEGS Mx a w.
Proof. intros Hb. unfold L5.u8_at. cbn [rdn]. unfold byte_at in Hb. rewrite Hb. reflexivity. Qed.
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

(* [comment removed for export] *)
Lemma gr_G (fx : FPState) R M model LK Aw cr B A g' :
  getr R (reg 2) = Z_to_bv 64 (S - 128) -> getr R (reg 8) = Z_to_bv 64 (S - 40) -> getr R (reg 9) = Z_to_bv 64 A ->
  getr R (reg 10) = Z_to_bv 64 B -> getr R (reg 18) = Z_to_bv 64 (S - 64) -> getr R (reg 19) = Z_to_bv 64 (PGV8.v8_size x) ->
  getr R (reg 20) = Z_to_bv 64 ((S - 40) / 8 + 2147450880) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> kept0 R ->
  stok model LK Aw -> mem_ok M -> saves M -> gsv M -> L5.u64_at RSEGS M (S - 32) v -> L5.u64_at RSEGS M (S - 40) 0 ->
  L5.u64_at RSEGS M (S - 72) 743592 -> L5.u64_at RSEGS M (S - 80) v -> L5.u64_at RSEGS M (S - 88) k ->
  ri_inv HI (((B, A) :: PGV8.v8_own x) ++ LB) FF LK cr Aw M (vml_of model) -> v8_atA M v x ->
  1 <= A <= 2 ^ 27 -> PGV8.v8_size x + k <= A -> shadow_blk M B A ->
  post_ok (PGV8.V8Blk B (PGV8.v8_size x + k) A) g' cr ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0xb5b00 M model) K.
Proof using All.
  intros E2 E8 E9 E10 E18 E19 E20 E21 KP SO MO SV GV C32 C40 C72 C80 C88 HH VS HA HnkA SHB PO.
  destruct (nfacts _ LK cr Aw M model HH MO) as ((A16 & SLO & SHI & SPT & C0) & (O1 & O2 & O5 & ODEF) & BF). unfold PGVAPK.nsh in O5.
  destruct (BF B A ltac:(left; reflexivity)) as (QB0 & QB1 & QB2 & QB4 & QB5 & QB6 & QBD). unfold PGVAPK.nsh in QB5.
  destruct (vfacts _ LK cr Aw M model HH MO) as (X0 & X1 & X2 & XW & XZ & XWV & XSZ & XAV).
  pose proof (zs512 _ _ XSZ A16) as ZS.
  pose proof SV as (S8 & S16 & S24). pose proof GV as (G96 & G104 & G112 & G120). pose proof xnum as (XD & XS & XC & K27 & XSK & XDC).
  assert (UB : forall i, 0 <= U i < 2 ^ 64) by (intros i; unfold PGVAPK.U; apply bv_unsigned_in_range).
  pose proof (UB 1%nat) as UB1. pose proof (UB 8%nat) as UB8. pose proof (UB 9%nat) as UB9. pose proof (UB 18%nat) as UB18.
  pose proof (UB 19%nat) as UB19. pose proof (UB 20%nat) as UB20. pose proof (UB 21%nat) as UB21.
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK cr Aw M model HH) as (_ & _ & _ & _ & VBLK & _ & _ & _).
  assert (WB : L5.writable RSEGS (mrestrict (ahid Aw model) M) B A).
  { apply (proj2 (L5A.writable_vis (ahid Aw model) M B A (VBLK B A B A ltac:(apply in_or_app; left; left; reflexivity) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5C.writable_of_defined RSEGS M B A QBD); lia. }
  LeanFeed.pfeed PP (PMAVGP.avaG_conc fx R (mrestrict (ahid Aw model) M) (fun j => match j with 2%nat => S | 37%nat => v | 41%nat => PGV8.v8_size x
     | 43%nat => k | 44%nat => B | 46%nat => A | 48%nat => U 1 | 49%nat => U 8 | 50%nat => U 9 | 51%nat => U 18 | 52%nat => U 19
     | 53%nat => U 20 | 54%nat => U 21 | _ => 0 end)) ltac:(pfeed XW XSZ XAV).
  destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & A1 & A2 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16' & A17
                  & A18 & A19 & A20 & A21 & D72 & D40 & D56 & D48 & D64 & D8 & D16 & D24 & D32 & D80 & D88 & D96 & D104 & D112 & D120).
  apply (piece_step fx fx1 R 0xb5b00 R1 0xb5c54 _ M model cr LK Aw M1v (fun a => (S - 128 <= a < S - 128 + 128) \/ (B + 0 <= a < B + 0 + A)) HH SO MO MS1 MG1
           (fun a Ha NP => FRZ1 a Ha (fun X => NP (or_introl X)) (fun X => NP (or_intror X))));
    [intros a [Pa|Pa]; [left; lia| right; right; exists B, A; split; [left; reflexivity| lia]]|].
  intros M1 model1 HH1 SO1 MO1 FR1 VUP AGS.
  destruct (nfacts _ LK cr Aw M1 model1 HH1 MO1) as (_ & (_ & _ & _ & ODEF1) & BF1).
  destruct (BF1 B A ltac:(left; reflexivity)) as (_ & _ & _ & _ & _ & _ & QBD1).
  destruct (vfacts _ LK cr Aw M1 model1 HH1 MO1) as (Y0 & Y1 & Y2 & YW & YZ & YWV & YSZ & YAV).
  pose proof (zs512 _ _ YSZ A16) as ZS1.
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK cr Aw M1 model1 HH1) as (_ & _ & _ & _ & VBLK1 & VBSH1 & _ & _).
  assert (WB1 : L5.writable RSEGS (mrestrict (ahid Aw model1) M1) B A).
  { apply (proj2 (L5A.writable_vis (ahid Aw model1) M1 B A (VBLK1 B A B A ltac:(apply in_or_app; left; left; reflexivity) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5C.writable_of_defined RSEGS M1 B A QBD1); lia. }
  assert (VS1 : v8_atA M1 v x).
  { apply (v8_at_agree M M1 x VS ODEF1); [intros i Hi; apply FR1; lia| apply AGS; lia| lia| lia|].
    intros b n c EX. destruct (BF1 b c ltac:(rewrite EX; right; left; reflexivity)) as (Q0 & Q1 & Q2 & Q4 & Q5 & Q6 & QD). unfold PGVAPK.nsh in Q5. split; [exact QD| apply AGS; lia]. }
  assert (SHB1 : shadow_blk M1 B A) by (apply (shblk_agree M M1 B A); [apply PMKA.mod16_8'; exact QB4| lia| apply AGS; lia| exact SHB]).
  assert (KP1 : kept0 R1) by (apply (kept0_of R R1 KP); intros i Hi; apply KS1; clear - Hi; cbn in Hi; repeat (destruct Hi as [<-|Hi]; [inl|]); destruct Hi).
  pose proof (VUP (S - 72) _ ltac:(left; lia) D72) as F72. pose proof (VUP (S - 40) _ ltac:(left; lia) D40) as F40.
  pose proof (VUP (S - 56) _ ltac:(left; lia) D56) as F56. pose proof (VUP (S - 48) _ ltac:(left; lia) D48) as F48.
  pose proof (VUP (S - 64) _ ltac:(left; lia) D64) as F64. pose proof (VUP (S - 8) _ ltac:(left; lia) D8) as F8.
  pose proof (VUP (S - 16) _ ltac:(left; lia) D16) as F16. pose proof (VUP (S - 24) _ ltac:(left; lia) D24) as F24.
  pose proof (VUP (S - 32) _ ltac:(left; lia) D32) as F32. pose proof (VUP (S - 80) _ ltac:(left; lia) D80) as F80.
  pose proof (VUP (S - 88) _ ltac:(left; lia) D88) as F88. pose proof (VUP (S - 96) _ ltac:(left; lia) D96) as F96.
  pose proof (VUP (S - 104) _ ltac:(left; lia) D104) as F104. pose proof (VUP (S - 112) _ ltac:(left; lia) D112) as F112.
  pose proof (VUP (S - 120) _ ltac:(left; lia) D120) as F120.
  rewrite (Z.add_comm (PGV8.v8_size x) B) in A7, A13, A16'.
  assert (A11' : getr R1 (reg 11) = Z_to_bv 64 (PGV8.v8_size x + k - PGV8.v8_size x)) by (replace (PGV8.v8_size x + k - PGV8.v8_size x) with k by lia; exact A11).
  assert (LB8 : forall i, PGV8.v8_size x <= i < PGV8.v8_size x + k -> exists s, L5.u8_at RSEGS (mrestrict (ahid Aw model1) M1) ((B + i) / 8 + 2147450880) s
      /\ (s = 0 \/ (1 <= s <= 7 /\ 1 <= s - Z.land (B + i) 7))).
  { intros i Hi.
    pose proof (aacc_of_block M1 B A (B + PGV8.v8_size x) k SHB1 ltac:(apply PMKA.mod16_8'; exact QB4) ltac:(lia) ltac:(lia) ltac:(lia) (B + i) ltac:(lia)) as AC.
    assert (AV : L5A.avis (ahid Aw model1) ((B + i) / 8 + 2147450880) 1).
    { apply (VBSH1 B A); [apply in_or_app; left; left; reflexivity|]. intros j Hj. assert (Ej : j = 0) by lia. subst j. rewrite Z.add_0_r. change ((B + i) / 8 + 2147450880) with (HeapIfaceA.S (B + i)).
      unfold in_shadow_of. split; apply PMKA.S_mono; lia. }
    assert (LND : Z.land (B + i) 7 = (B + i) mod 8) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity).
    change (HeapIfaceA.S (B + i)) with ((B + i) / 8 + 2147450880) in AC. rewrite LND.
    destruct AC as [Z0|(s & Hs & S1 & S2)].
    - exists 0. split; [| left; reflexivity]. apply (proj2 (L5A.u8_at_vis (ahid Aw model1) M1 _ 0 AV ltac:(lia) ltac:(lia))). apply u8_of_byte. exact Z0.
    - exists s. split; [| right; lia]. apply (proj2 (L5A.u8_at_vis (ahid Aw model1) M1 _ s AV ltac:(lia) ltac:(lia))). apply u8_of_byte. exact Hs. }
  destruct (PNAEK.blk_facts L ar C HI LY HIok _ FF LK cr Aw M1 _ B A HH1 ltac:(apply in_or_app; left; left; reflexivity)) as (_ & _ & _ & _ & _ & IMG & _).
  assert (LIM : forall i, PGV8.v8_size x <= i < PGV8.v8_size x + k -> ~ (1249280 <= B + i < 1282048) /\ ~ (1309752 <= B + i < 1309752 + 8) /\ ~ (1309760 <= B + i < 1309760 + 4)).
  { intros i Hi. lia. }
  LeanFeed.pfeed PQ (PnAVu8LoopP_b.PMAVLP.avaGLoop_conc fx1 R1 (mrestrict (ahid Aw model1) M1) (fun j => match j with 2%nat => S | 37%nat => v
     | 41%nat => PGV8.v8_size x | 43%nat => k | 44%nat => B | 46%nat => A | 48%nat => U 1 | 49%nat => U 8 | 50%nat => U 9 | 51%nat => U 18
     | 52%nat => U 19 | 53%nat => U 20 | 54%nat => U 21 | 56%nat => PGV8.v8_size x | _ => 0 end)) ltac:(pfeed YW YSZ YAV).
  destruct PQ as (fx2 & R2 & M2v & MG2 & _ & FRZ2 & MS2 & KS2 & B1 & B2 & B10 & B11 & B13 & B16 & J48 & J72 & J40 & J56 & J64 & J8 & J16 & J24 & J32
                  & J80 & J88 & J96 & J104 & J112 & J120 & _).
  apply (piece_step fx1 fx2 R1 0xb5c54 R2 0xb5cb8 _ M1 model1 cr LK Aw M2v
           (fun a => (S - 128 <= a < S - 128 + 128) \/ (B + PGV8.v8_size x <= a < B + (PGV8.v8_size x + k))) HH1 SO1 MO1 MS2 MG2
           (fun a Ha NP => FRZ2 a Ha (fun X => NP (or_introl X)) (fun X => NP (or_intror X))));
    [intros a [Pa|Pa]; [left; lia| right; right; exists B, A; split; [left; reflexivity| lia]]|].
  intros M2 model2 HH2 SO2 MO2 FR2 VUP2 AGS2.
  destruct (nfacts _ LK cr Aw M2 model2 HH2 MO2) as (_ & (_ & _ & _ & ODEF2) & BF2).
  assert (VS2 : v8_atA M2 v x).
  { apply (v8_at_agree M1 M2 x VS1 ODEF2); [intros i Hi; apply FR2; lia| apply AGS2; lia| lia| lia|].
    intros b n c EX. destruct (BF2 b c ltac:(rewrite EX; right; left; reflexivity)) as (Q0 & Q1 & Q2 & Q4 & Q5 & Q6 & QD). unfold PGVAPK.nsh in Q5. split; [exact QD| apply AGS2; lia]. }
  assert (SHB2 : shadow_blk M2 B A) by (apply (shblk_agree M1 M2 B A); [apply PMKA.mod16_8'; exact QB4| lia| apply AGS2; lia| exact SHB1]).
  assert (KS21 : forall i, In i [3; 4; 22; 23; 24; 25; 26; 27]%nat -> getr R2 (reg i) = getr R1 (reg i)).
  { intros i Hi. apply KS2. clear - Hi. cbn in Hi. repeat (destruct Hi as [<-|Hi]; [inl|]). destruct Hi. }
  assert (KP2 : kept0 R2) by (apply (kept0_of R1 R2 KP1); exact KS21).
  assert (R2_8 : getr R2 (reg 8) = Z_to_bv 64 v) by (rewrite (KS2 8%nat) by inl; exact A8).
  assert (R2_9 : getr R2 (reg 9) = Z_to_bv 64 k) by (rewrite (KS2 9%nat) by inl; exact A9).
  assert (RU : forall i, In i [18; 19; 20; 21]%nat -> getr R2 (reg i) = Z_to_bv 64 (U i)).
  { intros i Hi. rewrite (KS2 i) by (clear - Hi; cbn in Hi; repeat (destruct Hi as [<-|Hi]; [inl|]); destruct Hi).
    cbn in Hi. destruct Hi as [<-|[<-|[<-|[<-|[]]]]]; assumption. }
  assert (SV2 : saves M2).
  { unfold PGVAPK.saves. split; [apply VUP2; [left; lia| exact J8]|]. split; [apply VUP2; [left; lia| exact J16]| apply VUP2; [left; lia| exact J24]]. }
  assert (GB2 : gbuf M2 B (B + PGV8.v8_size x) ((B + PGV8.v8_size x) + k) (B + A)).
  { unfold PGVAPK.gbuf. split; [apply VUP2; [left; lia| exact J64]|].
    split; [replace (B + PGV8.v8_size x) with (PGV8.v8_size x + B) by lia; apply VUP2; [left; lia| exact J56]|].
    split; [replace (B + PGV8.v8_size x + k) with (PGV8.v8_size x + (k + B)) by lia; apply VUP2; [left; lia| exact J48]|].
    apply VUP2; [left; lia| exact J40]. }
  exact (gtail_ok fx2 R2 M2 model2 LK Aw cr B A g' B1 B2 R2_8 R2_9 B10 B11 RU KP2 SO2 MO2 SV2 (VUP2 (S - 32) v ltac:(left; lia) J32)
           HH2 VS2 GB2 ltac:(lia) HnkA SHB2 PO).
Qed.

(* [comment removed for export] *)
Lemma gr_new (fx : FPState) R M model LK Aw A :
  getr R (reg 1) = Z_to_bv 64 744192 -> getr R (reg 2) = Z_to_bv 64 (S - 128) -> getr R (reg 8) = Z_to_bv 64 (S - 40) ->
  getr R (reg 9) = Z_to_bv 64 A -> getr R (reg 10) = Z_to_bv 64 A -> getr R (reg 18) = Z_to_bv 64 (S - 64) ->
  getr R (reg 19) = Z_to_bv 64 (PGV8.v8_size x) -> getr R (reg 20) = Z_to_bv 64 ((S - 40) / 8 + 2147450880) ->
  getr R (reg 21) = Z_to_bv 64 2147450880 -> kept0 R ->
  stok model LK Aw -> mem_ok M -> saves M -> gsv M -> L5.u64_at RSEGS M (S - 32) v -> L5.u64_at RSEGS M (S - 40) 0 ->
  L5.u64_at RSEGS M (S - 72) 743592 -> L5.u64_at RSEGS M (S - 80) v -> L5.u64_at RSEGS M (S - 88) k ->
  ri_inv HI (PGV8.v8_own x ++ LB) FF LK cr0 Aw M (vml_of model) -> v8_atA M v x ->
  A = Z.max (2 * PGV8.v8_cap x) (PGV8.v8_size x + k) -> PGV8.v8_cap x < PGV8.v8_size x + k ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x130338 M model) K.
Proof using All.
  intros E1 E2 E8 E9 E10 E18 E19 E20 E21 KP SO MO SV GV C32 C40 C72 C80 C88 HH VS EA GRW.
  pose proof xnum as (XD & XS & XC & K27 & XSK & XDC).
  assert (HA : 1 <= A <= 2 ^ 27).
  { unfold PGV8.v8_grow_ok in GROK. clear - GROK GRW EA XS Hk. lia. }
  assert (HnkA : PGV8.v8_size x + k <= A) by (clear - EA; lia).
  assert (H2c : 2 * PGV8.v8_cap x <= A) by (clear - EA; lia).
  destruct (nfacts _ LK cr0 Aw M model HH MO) as ((A16 & SLO & SHI & SPT & C0) & (O1 & O2 & O5 & ODEF) & BF). unfold PGVAPK.nsh in O5.
  pose proof SO as (AM & MRT & ILK & IAW).
  destruct (cstk _ LK cr0 Aw M model 128 4112 HH MO ltac:(lia) ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(reflexivity)) as (STKc & _).
  pose proof OPN as ON. unfold PMA.opnew_spec, PMSPA.opnew_spec in ON. cbn [pa_opnew PMA.AD ADDR_A] in ON.
  assert (E10' : getr R 10%bv = Z_to_bv 64 A) by (rewrite L5K.rl10; exact E10).
  assert (E1' : getr R 1%bv = Z_to_bv 64 744192) by (rewrite L5K.rl1; exact E1).
  assert (E2' : getr R 2%bv = Z_to_bv 64 (S - 128)) by (rewrite L5K.rl2; exact E2).
  assert (E4' : getr R 4%bv = Z_to_bv 64 (hl_tp L)) by (rewrite L5K.rl4; rewrite (KP 4%nat) by inl; exact Rtp0).
  unfold PMSP.cfg.
  apply (ON fx R M model K _ FF LK Aw cr0 A (S - 128) 744192 HH AM K0 E10' ltac:(lia)).
  { exact (proj1 (grow_credit A 0 0 H2c HA)). }
  { exact E1'. } { split; [lia| reflexivity]. } { exact E2'. } { exact E4'. } { exact STKc. }
  intros fx2 R2 M2 model2 Aw2 B RB RP2 FRESH HP2 MRT2 IA2 AM2 HH2.
  unfold PMSPA.OPNEW_SCR, PMSPA.MALLOC_SCR in HP2. change (16 + 4096) with 4112 in HP2. rewrite L5K.rl10 in RB.
  destruct FRESH as (QR & QAP & QFA & QDEF & QSH).
  assert (WIN : forall rg, In rg (@nil L5.range) -> exists q m, In (q, m) (PGV8.v8_own x) /\ q <= fst rg /\ fst rg + snd rg <= q + m) by (intros rg []).
  pose proof (mem_ok_callee _ (PGV8.v8_own x) LK cr0 Aw M model M2 (S - 128) 4112 _ HH MO HP2 ltac:(lia) ltac:(lia) ltac:(lia) WIN) as MO2.
  pose proof (saves_callee _ LK cr0 Aw M model M2 (PGV8.v8_own x) (S - 128) 4112 _ HH MO HP2 ltac:(lia) ltac:(lia) ltac:(lia) WIN SV) as SV2.
  assert (CK : forall a val, S - 128 <= a /\ a + 8 <= S -> L5.u64_at RSEGS M a val -> L5.u64_at RSEGS M2 a val).
  { intros a val Ha X. apply (cell_callee _ LK cr0 Aw M model M2 (PGV8.v8_own x) (S - 128) 4112 _ a val HH MO HP2 ltac:(lia) ltac:(lia) ltac:(lia) WIN); [left; lia| exact X]. }
  assert (GV2 : gsv M2).
  { destruct GV as (G96 & G104 & G112 & G120). split; [apply CK; [lia| exact G96]|]. split; [apply CK; [lia| exact G104]|].
    split; [apply CK; [lia| exact G112]| apply CK; [lia| exact G120]]. }
  assert (HH2' : ri_inv HI (((B, A) :: PGV8.v8_own x) ++ LB) FF LK (adebit L cr0 A) Aw2 M2 (vml_of model2)) by exact HH2.
  pose proof HP2 as (EK2 & _).
  destruct (nfacts _ LK (adebit L cr0 A) Aw2 M2 model2 HH2' MO2) as (_ & (_ & _ & _ & ODEF2) & BF2).
  assert (VS2 : v8_atA M2 v x).
  { apply (v8_at_agree M M2 x VS ODEF2); [| | lia| lia|].
    - apply (obj_ek _ FF (S - 128) 4112 _ M M2 v 24 v 24 EK2 AO V8); [lia| lia| lia| lia| intros i Hi rg []].
    - apply (objsh_ek _ FF (S - 128) 4112 _ M M2 v 24 EK2 ltac:(intros rg []) AO); lia.
    - intros b n c EX. destruct (BF2 b c ltac:(rewrite EX; right; left; reflexivity)) as (Q0 & Q1 & Q2 & Q4 & Q5 & Q6 & QD). unfold PGVAPK.nsh in Q5. split; [exact QD|].
      apply (blksh_ek _ FF (S - 128) 4112 _ M M2 b c EK2 ltac:(intros rg []) ltac:(rewrite EX; left; reflexivity)); lia. }
  assert (CS2 : forall i, In i L5SAR.cs_all -> getr R2 (reg i) = getr R (reg i)) by (intros i Hi; exact (L5SAR.cs_of_preserved R R2 i RP2 Hi)).
  destruct (grow_credit A B (PGV8.v8_size x + k) H2c HA) as (_ & CK' & OK').
  assert (PO : post_ok (PGV8.V8Blk B (PGV8.v8_size x + k) A) (g + 1) (adebit L cr0 A)).
  { unfold PGVAPK.post_ok. cbn [PGV8.v8_size PGV8.v8_cap PGV8.v8_own]. split; [reflexivity|]. split; [exact OK'|]. split; [clear - H2c XS; lia|].
    split; [intros X; exfalso; clear - X GRW; lia|]. split; [right; exact EA| exact CK']. }
  assert (R2_2 : getr R2 (reg 2) = Z_to_bv 64 (S - 128)) by (rewrite CS2 by inl; exact E2).
  assert (R2_8 : getr R2 (reg 8) = Z_to_bv 64 (S - 40)) by (rewrite CS2 by inl; exact E8).
  assert (R2_9 : getr R2 (reg 9) = Z_to_bv 64 A) by (rewrite CS2 by inl; exact E9).
  assert (R2_18 : getr R2 (reg 18) = Z_to_bv 64 (S - 64)) by (rewrite CS2 by inl; exact E18).
  assert (R2_19 : getr R2 (reg 19) = Z_to_bv 64 (PGV8.v8_size x)) by (rewrite CS2 by inl; exact E19).
  assert (R2_20 : getr R2 (reg 20) = Z_to_bv 64 ((S - 40) / 8 + 2147450880)) by (rewrite CS2 by inl; exact E20).
  assert (R2_21 : getr R2 (reg 21) = Z_to_bv 64 2147450880) by (rewrite CS2 by inl; exact E21).
  exact (gr_G fx2 R2 M2 model2 LK Aw2 (adebit L cr0 A) B A (g + 1) R2_2 R2_8 R2_9 RB R2_18 R2_19 R2_20 R2_21 (kept0_pres R R2 KP RP2)
           (stok_step model LK Aw model2 LK Aw2 SO AM2 MRT2 (incl_refl _) IA2) MO2 SV2 GV2 (CK (S - 32) _ ltac:(lia) C32) (CK (S - 40) _ ltac:(lia) C40)
           (CK (S - 72) _ ltac:(lia) C72) (CK (S - 80) _ ltac:(lia) C80) (CK (S - 88) _ ltac:(lia) C88) HH2' VS2 HA HnkA QSH PO).
Qed.

Lemma entry_ok (fx : FPState) : srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R0 0xb5800 M0 model0) K.
Proof using All.
  pose proof stok0 as SO. pose proof mem_ok0 as MO. pose proof HH0 as HH.
  destruct (nfacts _ LK0 cr0 Aw0 M0 model0 HH MO) as ((A16 & SLO & SHI & SPT & C0) & (O1 & O2 & O5 & ODEF) & BF). unfold PGVAPK.nsh in O5.
  destruct (vfacts _ LK0 cr0 Aw0 M0 model0 HH MO) as (X0 & X1 & X2 & XW & XZ & XWV & XSZ & XAV).
  pose proof xnum as (XD & XS & XC & K27 & XSK & XDC). pose proof xr as XR.
  pose proof (zs512 _ _ XSZ A16) as ZS.
  assert (KPR : forall R1 (KS : list nat), (forall i, In i KS -> getr R1 (reg i) = getr R0 (reg i)) ->
                (forall i, In i [3; 4; 22; 23; 24; 25; 26; 27]%nat -> In i KS) -> kept0 R1).
  { intros R1 KS KS1 SUB i Hi. exact (KS1 i (SUB i Hi)). }
  assert (SVP : forall (M1v M1 : word -> option byte),
      (forall a val, (S - 14336 <= a /\ a + 8 <= S) \/ (v <= a /\ a + 8 <= v + 24) -> L5.u64_at RSEGS M1v a val -> L5.u64_at RSEGS M1 a val) ->
      L5.u64_at RSEGS M1v (S - 24) (bv_unsigned (getr R0 (reg 9))) -> L5.u64_at RSEGS M1v (S - 16) (bv_unsigned (getr R0 (reg 8))) ->
      L5.u64_at RSEGS M1v (S - 8) (bv_unsigned (getr R0 (reg 1))) -> saves M1).
  { intros M1v M1 VUP C24 C16 C8. unfold PGVAPK.saves, PGVAPK.U. repeat split; (apply VUP; [left; lia| assumption]). }
  assert (GSP : forall (M1v M1 : word -> option byte),
      (forall a val, (S - 14336 <= a /\ a + 8 <= S) \/ (v <= a /\ a + 8 <= v + 24) -> L5.u64_at RSEGS M1v a val -> L5.u64_at RSEGS M1 a val) ->
      L5.u64_at RSEGS M1v (S - 120) (bv_unsigned (getr R0 (reg 21))) -> L5.u64_at RSEGS M1v (S - 112) (bv_unsigned (getr R0 (reg 20))) ->
      L5.u64_at RSEGS M1v (S - 104) (bv_unsigned (getr R0 (reg 19))) -> L5.u64_at RSEGS M1v (S - 96) (bv_unsigned (getr R0 (reg 18))) -> gsv M1).
  { intros M1v M1 VUP C120 C112 C104 C96. unfold gsv, PGVAPK.U. repeat split; (apply VUP; [left; lia| assumption]). }
  assert (VSP : forall (M1 : word -> option byte) model1,
      ri_inv HI (PGV8.v8_own x ++ LB) FF LK0 cr0 Aw0 M1 (vml_of model1) -> mem_ok M1 ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ (S - 128 <= a < S - 128 + 128) -> M1 (Z_to_bv 64 a) = M0 (Z_to_bv 64 a)) ->
      (forall a n, 0 <= a -> a + n <= 2 ^ 47 -> PMFA.agsh M0 M1 a n) -> v8_atA M1 v x).
  { intros M1 model1 HH1 MO1 FR1 AGS. destruct (nfacts _ LK0 cr0 Aw0 M1 model1 HH1 MO1) as (_ & (_ & _ & _ & ODEF1) & BF1).
    apply (v8_at_agree M0 M1 x VS0 ODEF1); [intros i Hi; apply FR1; lia| apply AGS; lia| lia| lia|].
    intros b n c EX. destruct (BF1 b c ltac:(rewrite EX; left; reflexivity)) as (Q0 & Q1 & Q2 & Q4 & Q5 & Q6 & QD). unfold PGVAPK.nsh in Q5. split; [exact QD| apply AGS; lia]. }
  assert (UKS : forall R1 (KS : list nat), (forall i, In i KS -> getr R1 (reg i) = getr R0 (reg i)) -> (forall i, In i [18; 19; 20; 21]%nat -> In i KS) ->
      forall i, In i [18; 19; 20; 21]%nat -> getr R1 (reg i) = Z_to_bv 64 (U i)).
  { intros R1 KS KS1 SUB i Hi. rewrite (KS1 i (SUB i Hi)). unfold PGVAPK.U. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  destruct (v8_case x) as [EX|(b & n & c & EX)].
  - (* [comment removed for export] *)
    pose proof VS0 as (_ & _ & VR). rewrite EX in VR, XS, XC. cbn [PGV8.v8_size PGV8.v8_cap] in XS, XC. destruct VR as (W0 & W8 & W16).
    LeanFeed.pfeed PP (PMAVGP.avaA0_conc fx R0 (mrestrict (ahid Aw0 model0) M0) (fun j => match j with 2%nat => S | 37%nat => v | 43%nat => k | _ => 0 end)) ltac:(pfeed XW XSZ XAV).
    destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & A1 & A2 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A18 & A19 & A20 & A21
                    & C32 & C40 & C120 & C112 & C104 & C96 & C88 & C80 & C72 & C24 & C16 & C8).
    apply (piece_step fx fx1 R0 0xb5800 R1 0x130338 _ M0 model0 cr0 LK0 Aw0 M1v (fun a => S - 128 <= a < S - 128 + 128) HH SO MO MS1 MG1 FRZ1); [intros a Pa; left; lia|].
    intros M1 model1 HH1 SO1 MO1 FR1 VUP AGS.
    assert (KP1 : kept0 R1) by (apply (KPR R1 _ KS1); intros i Hi; clear - Hi; cbn in Hi; repeat (destruct Hi as [<-|Hi]; [inl|]); destruct Hi).
    assert (E19 : getr R1 (reg 19) = Z_to_bv 64 (PGV8.v8_size x)) by (rewrite EX; exact A19).
    assert (EA : k = Z.max (2 * PGV8.v8_cap x) (PGV8.v8_size x + k)) by (rewrite EX; cbn [PGV8.v8_size PGV8.v8_cap]; lia).
    assert (GRW : PGV8.v8_cap x < PGV8.v8_size x + k) by (rewrite EX; cbn [PGV8.v8_size PGV8.v8_cap]; lia).
    exact (gr_new fx1 R1 M1 model1 LK0 Aw0 k A1 A2 A8 A9 A10 A18 E19 A20 A21 KP1 SO1 MO1 (SVP M1v M1 VUP C24 C16 C8) (GSP M1v M1 VUP C120 C112 C104 C96)
             (VUP (S - 32) v ltac:(left; lia) C32) (VUP (S - 40) 0 ltac:(left; lia) C40) (VUP (S - 72) _ ltac:(left; lia) C72)
             (VUP (S - 80) v ltac:(left; lia) C80) (VUP (S - 88) k ltac:(left; lia) C88) HH1 (VSP M1 model1 HH1 MO1 FR1 AGS) EA GRW).
  - (* [comment removed for export] *)
    pose proof VS0 as (_ & _ & VR). rewrite EX in VR, XS, XC, XR, XD, XSK. cbn [PGV8.v8_size PGV8.v8_cap PGV8.v8_data] in XS, XC, XD, XSK.
    destruct VR as (W0 & W8 & W16 & Hn & Hc & Hb & Hb16 & _).
    LeanFeed.pfeed PP (PMAVGP.avaA_conc fx R0 (mrestrict (ahid Aw0 model0) M0) (fun j => match j with 2%nat => S | 37%nat => v | 40%nat => b | 41%nat => n | 42%nat => c | 43%nat => k | _ => 0 end)) ltac:(pfeed XW XSZ XAV).
    rewrite (room_mod n c Hn ltac:(lia)) in PP.
    destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & [(MS1 & KS1 & A1 & A2 & A8 & A9 & A12 & A13 & C32 & C40 & C48 & C24 & C16 & C8 & CND)
       | [(MS1 & KS1 & A1 & A2 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A18 & A19 & A20 & A21 & C32 & C40 & C120 & C112 & C104 & C96 & C88 & C80 & C72 & CND2 & CND & C24 & C16 & C8)
         | (MS1 & KS1 & A1 & A2 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A18 & A19 & A20 & A21 & C32 & C40 & C120 & C112 & C104 & C96 & C88 & C80 & C72 & CND2 & CND & C24 & C16 & C8)]]).
    + (* [comment removed for export] *)
      apply (piece_step fx fx1 R0 0xb5800 R1 0xb609c _ M0 model0 cr0 LK0 Aw0 M1v (fun a => S - 128 <= a < S - 128 + 128) HH SO MO MS1 MG1 FRZ1); [intros a Pa; left; lia|].
      intros M1 model1 HH1 SO1 MO1 FR1 VUP AGS.
      assert (KP1 : kept0 R1) by (apply (KPR R1 _ KS1); intros i Hi; clear - Hi; cbn in Hi; repeat (destruct Hi as [<-|Hi]; [inl|]); destruct Hi).
      assert (E10 : getr R1 (reg 10) = Z_to_bv 64 v) by (rewrite (KS1 10%nat) by inl; exact Ra0).
      assert (E11 : getr R1 (reg 11) = Z_to_bv 64 k) by (rewrite (KS1 11%nat) by inl; exact Ra1).
      assert (EU : forall i, In i [18; 19; 20; 21]%nat -> getr R1 (reg i) = Z_to_bv 64 (U i))
        by (apply (UKS R1 _ KS1); intros i Hi; clear - Hi; cbn in Hi; repeat (destruct Hi as [<-|Hi]; [inl|]); destruct Hi).
      assert (HH1' : ri_inv HI ([(b, c)] ++ LB) FF LK0 cr0 Aw0 M1 (vml_of model1)) by (rewrite EX in HH1; exact HH1).
      exact (ip_inc_b fx1 R1 M1 model1 LK0 Aw0 b n c EX ltac:(lia) A1 A2 A8 A9 E10 E11 EU KP1 SO1 MO1 (SVP M1v M1 VUP C24 C16 C8) HH1'
               (VSP M1 model1 HH1 MO1 FR1 AGS) (VUP (S - 32) _ ltac:(left; lia) C32) (VUP (S - 40) _ ltac:(left; lia) C40) (VUP (S - 48) v ltac:(left; lia) C48)).
    + (* [comment removed for export] *)
      apply (piece_step fx fx1 R0 0xb5800 R1 0x130338 _ M0 model0 cr0 LK0 Aw0 M1v (fun a => S - 128 <= a < S - 128 + 128) HH SO MO MS1 MG1 FRZ1); [intros a Pa; left; lia|].
      intros M1 model1 HH1 SO1 MO1 FR1 VUP AGS.
      assert (KP1 : kept0 R1) by (apply (KPR R1 _ KS1); intros i Hi; clear - Hi; cbn in Hi; repeat (destruct Hi as [<-|Hi]; [inl|]); destruct Hi).
      assert (E19 : getr R1 (reg 19) = Z_to_bv 64 (PGV8.v8_size x)) by (rewrite EX; exact A19).
      assert (EA : 2 * c = Z.max (2 * PGV8.v8_cap x) (PGV8.v8_size x + k)) by (rewrite EX; cbn [PGV8.v8_size PGV8.v8_cap]; lia).
      assert (GRW : PGV8.v8_cap x < PGV8.v8_size x + k) by (rewrite EX; cbn [PGV8.v8_size PGV8.v8_cap]; lia).
      exact (gr_new fx1 R1 M1 model1 LK0 Aw0 (2 * c) A1 A2 A8 A9 A10 A18 E19 A20 A21 KP1 SO1 MO1 (SVP M1v M1 VUP C24 C16 C8) (GSP M1v M1 VUP C120 C112 C104 C96)
               (VUP (S - 32) v ltac:(left; lia) C32) (VUP (S - 40) 0 ltac:(left; lia) C40) (VUP (S - 72) _ ltac:(left; lia) C72)
               (VUP (S - 80) v ltac:(left; lia) C80) (VUP (S - 88) k ltac:(left; lia) C88) HH1 (VSP M1 model1 HH1 MO1 FR1 AGS) EA GRW).
    + (* [comment removed for export] *)
      apply (piece_step fx fx1 R0 0xb5800 R1 0x130338 _ M0 model0 cr0 LK0 Aw0 M1v (fun a => S - 128 <= a < S - 128 + 128) HH SO MO MS1 MG1 FRZ1); [intros a Pa; left; lia|].
      intros M1 model1 HH1 SO1 MO1 FR1 VUP AGS.
      assert (KP1 : kept0 R1) by (apply (KPR R1 _ KS1); intros i Hi; clear - Hi; cbn in Hi; repeat (destruct Hi as [<-|Hi]; [inl|]); destruct Hi).
      assert (E19 : getr R1 (reg 19) = Z_to_bv 64 (PGV8.v8_size x)) by (rewrite EX; exact A19).
      assert (EA : n + k = Z.max (2 * PGV8.v8_cap x) (PGV8.v8_size x + k)) by (rewrite EX; cbn [PGV8.v8_size PGV8.v8_cap]; lia).
      assert (GRW : PGV8.v8_cap x < PGV8.v8_size x + k) by (rewrite EX; cbn [PGV8.v8_size PGV8.v8_cap]; lia).
      exact (gr_new fx1 R1 M1 model1 LK0 Aw0 (n + k) A1 A2 A8 A9 A10 A18 E19 A20 A21 KP1 SO1 MO1 (SVP M1v M1 VUP C24 C16 C8) (GSP M1v M1 VUP C120 C112 C104 C96)
               (VUP (S - 32) v ltac:(left; lia) C32) (VUP (S - 40) 0 ltac:(left; lia) C40) (VUP (S - 72) _ ltac:(left; lia) C72)
               (VUP (S - 80) v ltac:(left; lia) C80) (VUP (S - 88) k ltac:(left; lia) C88) HH1 (VSP M1 model1 HH1 MO1 FR1 AGS) EA GRW).
Qed.

End Call.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem vu8_append_ok :
  PMA.opnew_spec L ar HI -> PMA.opdel_spec L ar HI ->
  PNSAX8.ann_increase_v8_spec RSEGS AD L ar HI 0xb609c -> PNSAX8.ann_new_v8_spec RSEGS AD L ar HI 0xb615c -> PNSAX.ann_delete_v8_spec RSEGS AD L ar HI 0xabb8c ->
  PGV8A.vu8_append_spec RSEGS AD L ar HI PNRA.FCB (PNL.pn_vu8_append PMA.AN).
Proof.
  intros OPN OPD ANNI ANNN ANND. unfold PGV8A.vu8_append_spec, PGV8A.vu8_grow_spec.
  intros fx R M model K LB FF LK Aw cr v a sp r g x HH AM K0 ENT FRM FRS A10 A11 AO V8 ACC VS OK Ha GOK CRL KONT.
  cbn [PNL.pn_vu8_append PMA.AN NADDR_A].
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10. rewrite L5SAR.r11 in A11.
  change (PMSPA.pm_scr 1) with 14336 in ASTK, STKSH. change (14336 / 8) with 1792 in STKSH.
  exact (entry_ok R M model K LB FF LK Aw cr v sp r g a x Rra RAok Rsp Rgp Rtp K0 FRS AO V8 OK (proj1 Ha) GOK CRL KONT OPN OPD ANNI ANNN ANND VS HH A10 A11 AM ASTK STKSH fx).
Qed.

End WithHeap.
End PGVAPA.

