(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceAEx L5Defs L5Core L5KnA L5LazyA L5DefsA L5CoreAS9.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PmModel PmStatics PmStaticsA PmSpecs PmSpecsA PmSpecsAX.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayout.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PeCSink PeCStatics PeCModel PeCSinkA PeCStaticsA PeCModelA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9.Spec Require Import UbjRefFactsS9.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PECEPA.
Section Specs.
Context {SCFG_P : ScfgP}.
Variable segs : list Segment.
Variable A : pm_addrs.
Variable E : pe_addrs.
Variable L : asan_layout.
Variable ar : asan_run.
Variable HI : asan_iface.
Abbreviation enc_at := (PECA.enc_atA segs E L ar).
Abbreviation cfg := (PMSPA.cfg segs).

Definition earg_ok (FF : list fframe) (sp ov p n : Z) : Prop :=
  (PMSPA.aobjA FF p n \/ (sp <= p /\ p + n <= ar_sptop ar)) /\ (p + n <= ov \/ ov + 56 <= p).

Definition ecells_k (FF : list fframe) (sp ov : Z) (M : word -> option byte) (R : bvmap 5 word) (it : eitem) : Prop :=
  exists pk kd, getr R 11%bv = Z_to_bv 64 pk /\ pk mod 4 = 0 /\ PMSPA.accA M pk 4 /\ earg_ok FF sp ov pk 4 /\ byte_at M (HeapIfaceA.S pk) 0
    /\ L5.u32_at segs M pk kd /\ 0 <= kd <= 3 /\ it = EI kd 0 0.

Definition ecells_kl (FF : list fframe) (sp ov : Z) (M : word -> option byte) (R : bvmap 5 word) (it : eitem) : Prop :=
  exists pk pl kd ln, getr R 11%bv = Z_to_bv 64 pk /\ getr R 12%bv = Z_to_bv 64 pl /\ pk mod 4 = 0 /\ pl mod 8 = 0
    /\ PMSPA.accA M pk 4 /\ PMSPA.accA M pl 8 /\ earg_ok FF sp ov pk 4 /\ earg_ok FF sp ov pl 8
    /\ byte_at M (HeapIfaceA.S pk) 0 /\ byte_at M (HeapIfaceA.S pl) 0
    /\ L5.u32_at segs M pk kd /\ L5.u64_at segs M pl ln /\ 0 <= kd <= 3 /\ 0 <= ln <= UbjRef.MAX_ITEMS /\ it = EI kd ln 0.

Definition epush_out (en en' : PEC.enc) (cr cr' : credit) : Prop :=
  (Z.of_nat (length (PEC.en_stk en)) < PEC.ecap (PEC.en_k en) /\ PEC.en_b en' = PEC.en_b en /\ PEC.en_k en' = PEC.en_k en /\ cr' = cr)
  \/ (Z.of_nat (length (PEC.en_stk en)) = PEC.ecap (PEC.en_k en) /\ PEC.en_k en' = PEC.en_k en + 1
      /\ cr' = adebit L cr (PEC.ESZ * PEC.ecap (PEC.en_k en + 1))).

Definition epush_spec_at (pc : Z) (cells : list fframe -> Z -> Z -> (word -> option byte) -> bvmap 5 word -> eitem -> Prop) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (ov fb : Z) (en : PEC.enc) (it : eitem) (sp r : Z),
    ri_inv HI (PEC.enc_own en ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA A L ar R M sp r 0 -> PMSPA.ffrsA FF sp ->
    getr R 10%bv = Z_to_bv 64 (ov + 24) -> PMSPA.aobjA FF ov 56 -> ov mod 8 = 0 ->
    enc_at M ov fb en -> Z.of_nat (length (PEC.en_stk en)) <= UbjRef.MAX_DEPTH -> PMSTA.base_okA segs A M ->
    cells FF sp ov M R it ->
    (Z.of_nat (length (PEC.en_stk en)) = PEC.ecap (PEC.en_k en) -> acredit_ok L cr (PEC.ESZ * PEC.ecap (PEC.en_k en + 1))) ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z))
            (en' : PEC.enc) (cr' : credit),
        regs_preserved R R' ->
        enc_at M' ov fb en' -> PEC.en_stk en' = PEC.en_stk en ++ [it] -> PEC.en_depth en' = PEC.en_depth en -> epush_out en en' cr cr' ->
        L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr 0) [(ov + 24, 24)] M M' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv HI (PEC.enc_own en' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes segs SCFG (cfg R' r M' model') K) ->
    srealizes segs SCFG (cfg R pc M model) K.

Definition econe_spec_at (pc : Z) (cells : list fframe -> Z -> Z -> (word -> option byte) -> bvmap 5 word -> eitem -> Prop) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (ov fb : Z) (en : PEC.enc) (it : eitem) (sp r : Z),
    ri_inv HI (PEC.enc_own en ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA A L ar R M sp r 0 -> PMSPA.ffrsA FF sp ->
    getr R 10%bv = Z_to_bv 64 (ov + 24) -> PMSPA.aobjA FF ov 56 -> ov mod 8 = 0 ->
    enc_at M ov fb en -> Z.of_nat (length (PEC.en_stk en)) < PEC.ecap (PEC.en_k en) -> PMSTA.base_okA segs A M ->
    cells FF sp ov M R it ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)),
        regs_preserved R R' ->
        enc_at M' ov fb (PEC.ENC (PEC.en_b en) (PEC.en_k en) (PEC.en_stk en ++ [it]) (PEC.en_depth en)) ->
        L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr 0) [(ov + 24, 24)] M M' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv HI (PEC.enc_own en ++ LBX) FF LK' cr Aw' M' (vml_of model') ->
        srealizes segs SCFG (cfg R' r M' model') K) ->
    srealizes segs SCFG (cfg R pc M model) K.

Definition eslow_spec_at (pc : Z) (cells : list fframe -> Z -> Z -> (word -> option byte) -> bvmap 5 word -> eitem -> Prop) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (ov fb : Z) (en : PEC.enc) (it : eitem) (sp r : Z),
    ri_inv HI (PEC.enc_own en ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA A L ar R M sp r 0 -> PMSPA.ffrsA FF sp ->
    getr R 10%bv = Z_to_bv 64 (ov + 24) -> PMSPA.aobjA FF ov 56 -> ov mod 8 = 0 ->
    enc_at M ov fb en -> Z.of_nat (length (PEC.en_stk en)) = PEC.ecap (PEC.en_k en) -> Z.of_nat (length (PEC.en_stk en)) <= UbjRef.MAX_DEPTH -> PMSTA.base_okA segs A M ->
    cells FF sp ov M R it ->
    acredit_ok L cr (PEC.ESZ * PEC.ecap (PEC.en_k en + 1)) ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (B : Z),
        regs_preserved R R' ->
        enc_at M' ov fb (PEC.ENC B (PEC.en_k en + 1) (PEC.en_stk en ++ [it]) (PEC.en_depth en)) ->
        getr R' 10%bv = Z_to_bv 64 (B + PEC.ESZ * Z.of_nat (length (PEC.en_stk en)) + PEC.ESZ) ->
        L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr 0) [(ov + 24, 24)] M M' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv HI (PEC.enc_own (PEC.ENC B (PEC.en_k en + 1) (PEC.en_stk en ++ [it]) (PEC.en_depth en)) ++ LBX) FF LK'
               (adebit L cr (PEC.ESZ * PEC.ecap (PEC.en_k en + 1))) Aw' M' (vml_of model') ->
        srealizes segs SCFG (cfg R' r M' model') K) ->
    srealizes segs SCFG (cfg R pc M model) K.
End Specs.
End PECEPA.

Module PECEPX.
Section Inst.
Context {SCFG_P : ScfgP}.
Variables (segs : list Segment) (A : pm_addrs) (E : pe_addrs) (L : asan_layout) (ar : asan_run) (HI : asan_iface).

Definition epush_k_spec : Prop := @PECEPA.epush_spec_at SCFG_P segs A E L ar HI 0xb0de0 (PECEPA.ecells_k segs ar).
Definition epush_kl_spec : Prop := @PECEPA.epush_spec_at SCFG_P segs A E L ar HI 0xae3ec (PECEPA.ecells_kl segs ar).

Definition econe_k_spec : Prop := @PECEPA.econe_spec_at SCFG_P segs A E L ar HI 0xb4078 (PECEPA.ecells_k segs ar).
Definition econe_kl_spec : Prop := @PECEPA.econe_spec_at SCFG_P segs A E L ar HI 0xb04f4 (PECEPA.ecells_kl segs ar).
Definition eslow_k_spec : Prop := @PECEPA.eslow_spec_at SCFG_P segs A E L ar HI 0xb417c (PECEPA.ecells_k segs ar).
Definition eslow_kl_spec : Prop := @PECEPA.eslow_spec_at SCFG_P segs A E L ar HI 0xb0648 (PECEPA.ecells_kl segs ar).
End Inst.
End PECEPX.
