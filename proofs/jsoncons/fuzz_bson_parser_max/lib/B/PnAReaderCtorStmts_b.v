(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA L5Defs L5Core
     L5KnA L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout PmLayoutA PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PnModel PmStatics PmStaticsA PnStatics PnStaticsA HeapIfaceABx
     PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PnSpecsAa_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b PgV8A_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnRun. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b PnRunAa_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNARCS.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition SCR : Z := 24576.                       (* [comment removed for export] *)
Definition iss_at := (PM.iss_at RSEGS PMA.AD PMSPA.accA).

Section Call.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (HI : asan_iface).
Variables (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet).
Variables (LB : list (Z * Z)) (FF LK0 : list fframe) (Aw0 : list (Z * Z)) (cr : credit) (sp r fb oo oa : Z) (str : PM.vstr) (sm : PM.strm).

Definition op : Z := fb + 464.
Definition cost : credit := PMSPA.scA L (PM.credit_add (PM.cost1 (PMSPA.HV L ar) PM.CHUNK) (PM.cost1 (PMSPA.HV L ar) 40)).

(* [comment removed for export] *)
Definition pre : Prop :=
  ri_inv HI LB FF LK0 cr Aw0 M0 (vml_of model0) /\ L5CA.amodel_ok Aw0 model0 /\ K [] /\ PMSPA.entryA PMA.AD L ar R0 M0 sp r 6
  /\ PGSA.ffroomB PNRA.FCB 6 FF LK0 /\ PMSPA.ffrsA FF sp /\ PNRA.frame_okB FF fb
  /\ getr R0 (reg 10) = Z_to_bv 64 op /\ getr R0 (reg 11) = Z_to_bv 64 (fb + 96) /\ getr R0 (reg 12) = Z_to_bv 64 oo /\ getr R0 (reg 13) = Z_to_bv 64 oa
  /\ PMSPA.aobjA FF oo 24 /\ (oo + 24 <= op \/ op + 416 + 8 <= oo) /\ oo mod 8 = 0
  /\ L5.defined M0 op 416 /\ PMSPA.accA M0 op 416 /\ PMSPA.accA M0 oo 24
  /\ L5.u64_at RSEGS M0 oo (pa_vp_opts PMA.AD) /\ L5.u32_at RSEGS M0 (oo + 16) 1024
  /\ iss_at M0 (fb + 96) str sm /\ PMSTA.base_okA RSEGS PMA.AD M0 /\ PMST.loc_ok RSEGS PMA.AD M0 true
  /\ PMSP.credit_le cost cr.

(* [comment removed for export] *)
Definition kont : Prop :=
  forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (qc b : Z) (cr' : credit),
    regs_preserved R0 R' -> PNM.bparser_at RSEGS PMA.AD PMSPA.accA PNRA.annA (pa_vp_parser PMA.AD) M' op (fb + 96) (PNRA.bparser_init qc b) ->
    L5CA.ahpres L ar LB FF sp (PMSPA.pm_scr 6) [(op, 416)] M0 M' ->
    PMSP.credit_keep cr cr' cost (PMSPA.scA L PMSP.cr0) ->
    model_rt model0 model' -> incl LK' LK0 -> incl Aw0 Aw' -> L5CA.amodel_ok Aw' model' ->
    ri_inv HI (PNM.bparser_own (PNRA.bparser_init qc b) ++ LB) FF LK' cr' Aw' M' (vml_of model') ->
    srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx') R' r M' model') K.

(* [comment removed for export] *)
Definition saves_rd (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M (sp - 8) (bv_unsigned (getr R0 (reg 1))) /\ L5.u64_at RSEGS M (sp - 16) (bv_unsigned (getr R0 (reg 8)))
  /\ L5.u64_at RSEGS M (sp - 24) (bv_unsigned (getr R0 (reg 9))) /\ L5.u64_at RSEGS M (sp - 32) (bv_unsigned (getr R0 (reg 18)))
  /\ L5.u64_at RSEGS M (sp - 40) (bv_unsigned (getr R0 (reg 19))) /\ L5.u64_at RSEGS M (sp - 48) (bv_unsigned (getr R0 (reg 20)))
  /\ L5.u64_at RSEGS M (sp - 56) (bv_unsigned (getr R0 (reg 21))) /\ L5.u64_at RSEGS M (sp - 64) (bv_unsigned (getr R0 (reg 22)))
  /\ L5.u64_at RSEGS M (sp - 72) (bv_unsigned (getr R0 (reg 23)))
  /\ L5.u64_at RSEGS M (sp - 80) (bv_unsigned (getr R0 (reg 24))) /\ L5.u64_at RSEGS M (sp - 88) (bv_unsigned (getr R0 (reg 25))).
(* [comment removed for export] *)
Definition saves_src (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M (sp - 120) 0xac860 /\ L5.u64_at RSEGS M (sp - 128) op /\ L5.u64_at RSEGS M (sp - 136) (op + 16)
  /\ L5.u64_at RSEGS M (sp - 144) oo /\ L5.u64_at RSEGS M (sp - 152) (bv_unsigned (getr R0 (reg 19))).
(* [comment removed for export] *)
Definition saves_nis (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M (sp - 168) 0xacb8c /\ L5.u64_at RSEGS M (sp - 176) (op + 24) /\ L5.u64_at RSEGS M (sp - 184) (op + 16)
  /\ L5.u64_at RSEGS M (sp - 192) (fb + 96) /\ L5.u64_at RSEGS M (sp - 200) 2147450880 /\ L5.u64_at RSEGS M (sp - 208) (bv_unsigned (getr R0 (reg 20)))
  /\ L5.u64_at RSEGS M (sp - 216) (bv_unsigned (getr R0 (reg 21))) /\ L5.u64_at RSEGS M (sp - 224) (bv_unsigned (getr R0 (reg 22)))
  /\ L5.u64_at RSEGS M (sp - 232) 2147450880.
(* [comment removed for export] *)
Definition hcells (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M op (pa_vp_parser PMA.AD) /\ L5.u8_at RSEGS M (op + 8) 1 /\ L5.u8_at RSEGS M (op + 9) 0 /\ L5.u8_at RSEGS M (op + 10) 0
  /\ L5.u32_at RSEGS M (op + 12) 0
  /\ L5.u64_at RSEGS M (op + 24) (pa_vp_nullis PMA.AD) /\ L5.u64_at RSEGS M (op + 48) (pa_classic_imp PMA.AD)
  /\ L5.u64_at RSEGS M (op + 104) (pa_vp_nullis_ios PMA.AD) /\ L5.u32_at RSEGS M (op + 136) 0 /\ L5.u32_at RSEGS M (op + 140) 0
  /\ L5.u64_at RSEGS M (op + 144) (op + 40) /\ L5.u64_at RSEGS M (op + 152) (pa_classic_imp PMA.AD) /\ PM.zeros_at M (op + 160) 80.

(* [comment removed for export] *)
Definition rmidc (M : word -> option byte) (model : Model) (LK : list fframe) (Aw : list (Z * Z)) : Prop :=
  saves_rd M /\ saves_src M /\ hcells M
  /\ L5.defined M op 416 /\ PMSPA.accA M op 416 /\ PMSPA.accA M oo 24
  /\ L5.u64_at RSEGS M oo (pa_vp_opts PMA.AD) /\ L5.u32_at RSEGS M (oo + 16) 1024
  /\ PMSPA.accA M (fb + 96) 272
  /\ L5CA.astk ar M sp SCR /\ shadow_zero M (sp - SCR) (SCR / 8)
  /\ PMSTA.base_okA RSEGS PMA.AD M /\ PMST.loc_ok RSEGS PMA.AD M true
  /\ ri_inv HI LB FF LK cr Aw M (vml_of model) /\ L5CA.amodel_ok Aw model /\ model_rt model0 model /\ incl LK LK0 /\ incl Aw0 Aw
  /\ L5SAR.ek L ar LB FF sp SCR [(op, 416)] M0 M /\ L5SAR.dk L ar LB FF sp SCR M0 M.

(* [comment removed for export] *)
Definition rmid1 (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LK : list fframe) (Aw : list (Z * Z)) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (sp - 240) /\ getr R (reg 8) = Z_to_bv 64 (op + 24) /\ getr R (reg 9) = Z_to_bv 64 (op + 104)
  /\ getr R (reg 18) = Z_to_bv 64 (op + 40) /\ getr R (reg 19) = Z_to_bv 64 ((op + 40) / 8 + 2147450880)
  /\ getr R (reg 20) = Z_to_bv 64 0x131ab8 /\ getr R (reg 21) = Z_to_bv 64 ((op + 24) / 8 + 2147450880)
  /\ getr R (reg 22) = Z_to_bv 64 0x131ad0 /\ getr R (reg 23) = Z_to_bv 64 ((op + 104) / 8 + 2147450880)
  /\ (forall k, In k [3; 4; 24; 25; 26; 27]%nat -> getr R (reg k) = getr R0 (reg k))
  /\ L5.u64_at RSEGS M (fb + 96) (pa_vp_iss PMA.AD) /\ L5.u64_at RSEGS M (fb + 256) (fb + 112)
  /\ saves_nis M /\ rmidc M model LK Aw.

(* [comment removed for export] *)
Definition rmid2 (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LK : list fframe) (Aw : list (Z * Z)) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (sp - 160) /\ getr R (reg 8) = Z_to_bv 64 (op + 24) /\ getr R (reg 9) = Z_to_bv 64 (op + 16)
  /\ getr R (reg 18) = Z_to_bv 64 (op + 296) /\ getr R (reg 19) = Z_to_bv 64 2147450880 /\ getr R (reg 23) = Z_to_bv 64 2147450880
  /\ (forall k, In k [3; 4; 20; 21; 22; 24; 25; 26; 27]%nat -> getr R (reg k) = getr R0 (reg k))
  /\ L5.u64_at RSEGS M (op + 40) (pa_vp_nullbuf PMA.AD) /\ L5.u64_at RSEGS M (op + 256) (fb + 96) /\ L5.u64_at RSEGS M (op + 264) (fb + 112)
  /\ PM.zeros_at M (op + 272) 16 /\ L5.u64_at RSEGS M (op + 288) PM.CHUNK /\ PM.zeros_at M (op + 296) 16
  /\ rmidc M model LK Aw.

End Call.
End PNARCS.
