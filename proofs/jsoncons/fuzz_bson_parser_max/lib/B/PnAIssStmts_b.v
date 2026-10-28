(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx L5Defs L5Core
     L5KnA L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmStatics PmStaticsA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PnSpecsAa_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMAIS.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition SCR : Z := 20480.                       (* [comment removed for export] *)
(* [comment removed for export] *)
Definition CSK : list nat := [3; 4]%nat.
Definition vstr_at := (PM.vstr_at RSEGS PMSPA.accA).
Definition iss_at := (PM.iss_at RSEGS PMA.AD PMSPA.accA).

Section Call.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (HI : asan_iface).
Variables (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet).
Variables (LB : list (Z * Z)) (FF LK0 : list fframe) (Aw0 : list (Z * Z)) (cr : credit) (ois os sp r : Z) (s : PM.vstr) (b : bool).

Definition WF : list L5.range := (ois, 272) :: (if b then [] else PMSPA.loc_W PMA.AD).
Definition cost : credit := PMSPA.scA L (PM.cost1 (PMSPA.HV L ar) (PM.vs_size s + 32)).

(* [comment removed for export] *)
Definition pre : Prop :=
  ri_inv HI LB FF LK0 cr Aw0 M0 (vml_of model0) /\ L5CA.amodel_ok Aw0 model0 /\ K [] /\ PMSPA.entryA PMA.AD L ar R0 M0 sp r 4
  /\ PMSPA.ffroomA 4 FF LK0 /\ PMSPA.ffrsA FF sp
  /\ getr R0 (reg 10) = Z_to_bv 64 ois /\ getr R0 (reg 11) = Z_to_bv 64 os /\ getr R0 (reg 12) = Z_to_bv 64 8
  /\ PMSPA.aobjA FF ois 272 /\ PMSPA.aobjA FF os 24 /\ ois = os + 64 /\ ois mod 8 = 0 /\ os mod 8 = 0 /\ L5.defined M0 ois 272 /\ PMSPA.accA M0 ois 272
  /\ vstr_at M0 os s /\ incl (PM.vs_own s) LB /\ PM.vs_size s < 2 ^ 26 /\ (forall c n p, s = PM.VLong c n p -> 23 <= n)
  /\ PMSTA.base_okA RSEGS PMA.AD M0 /\ PMST.loc_ok RSEGS PMA.AD M0 b
  /\ PMSPA.credit_le cost cr.

(* [comment removed for export] *)
Definition kont : Prop :=
  forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (s' : PM.vstr) (sm : PM.strm) (cr' : credit),
    regs_preserved R0 R' -> iss_at M' ois s' sm -> PM.vs_size s' = PM.vs_size s ->
    PM.sm_g sm = PM.vs_data (ois + 80) s' -> PM.sm_st sm = 0 ->
    PMST.loc_ok RSEGS PMA.AD M' true ->
    L5CA.ahpres L ar LB FF sp (PMSPA.pm_scr 4) WF M0 M' ->
    PMSPA.credit_keep cr cr' cost PMSPA.cr0 ->
    model_rt model0 model' -> incl LK' LK0 -> incl Aw0 Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (PM.vs_own s' ++ LB) FF LK' cr' Aw' M' (vml_of model') ->
    srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx') R' r M' model') K.

(* [comment removed for export] *)
Definition saves_iss (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M (sp - 8) (bv_unsigned (getr R0 (reg 1))) /\ L5.u64_at RSEGS M (sp - 16) (bv_unsigned (getr R0 (reg 8)))
  /\ L5.u64_at RSEGS M (sp - 24) (bv_unsigned (getr R0 (reg 9))) /\ L5.u64_at RSEGS M (sp - 32) (bv_unsigned (getr R0 (reg 18)))
  /\ L5.u64_at RSEGS M (sp - 40) (bv_unsigned (getr R0 (reg 19))) /\ L5.u64_at RSEGS M (sp - 48) (bv_unsigned (getr R0 (reg 20)))
  /\ L5.u64_at RSEGS M (sp - 56) (bv_unsigned (getr R0 (reg 21))) /\ L5.u64_at RSEGS M (sp - 64) (bv_unsigned (getr R0 (reg 22)))
  /\ L5.u64_at RSEGS M (sp - 72) (bv_unsigned (getr R0 (reg 23))) /\ L5.u64_at RSEGS M (sp - 80) (bv_unsigned (getr R0 (reg 24)))
  /\ L5.u64_at RSEGS M (sp - 88) (bv_unsigned (getr R0 (reg 25))) /\ L5.u64_at RSEGS M (sp - 96) (bv_unsigned (getr R0 (reg 26)))
  /\ L5.u64_at RSEGS M (sp - 104) (bv_unsigned (getr R0 (reg 27))).
Definition saves_sb (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M (sp - 120) 691528 /\ L5.u64_at RSEGS M (sp - 128) ois /\ L5.u64_at RSEGS M (sp - 136) (ois + 120)
  /\ L5.u64_at RSEGS M (sp - 144) 8 /\ L5.u64_at RSEGS M (sp - 152) os /\ L5.u64_at RSEGS M (sp - 160) 1266032
  /\ L5.u64_at RSEGS M (sp - 168) (ois + 16) /\ L5.u64_at RSEGS M (sp - 176) (ois + 120)
  /\ L5.u64_at RSEGS M (sp - 184) ((ois / 8) + 2147450880).
(* [comment removed for export] *)
Definition head_cells (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M ois (pa_vp_iss PMA.AD) /\ L5.u64_at RSEGS M (ois + 24) (pa_classic_imp PMA.AD)
  /\ L5.u64_at RSEGS M (ois + 120) (pa_vp_iss_ios PMA.AD) /\ L5.u32_at RSEGS M (ois + 152) 0 /\ L5.u32_at RSEGS M (ois + 156) 0
  /\ L5.u64_at RSEGS M (ois + 160) (ois + 16) /\ L5.u64_at RSEGS M (ois + 168) (pa_classic_imp PMA.AD) /\ PM.zeros_at M (ois + 176) 80.

(* [comment removed for export] *)
Definition midc (M : word -> option byte) (model : Model) (LK : list fframe) (Aw : list (Z * Z)) : Prop :=
  saves_iss M /\ saves_sb M /\ head_cells M
  /\ L5.defined M ois 272 /\ PMSPA.accA M ois 272 /\ vstr_at M os s /\ L5CA.astk ar M sp SCR /\ shadow_zero M (sp - SCR) (SCR / 8)
  /\ PMSTA.base_okA RSEGS PMA.AD M /\ PMST.loc_ok RSEGS PMA.AD M true
  /\ ri_inv HI LB FF LK cr Aw M (vml_of model) /\ L5CA.amodel_ok Aw model /\ model_rt model0 model /\ incl LK LK0 /\ incl Aw0 Aw
  /\ L5SAR.ek L ar LB FF sp SCR WF M0 M /\ L5SAR.dk L ar LB FF sp SCR M0 M.

(* [comment removed for export] *)
Definition mid (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LK : list fframe) (Aw : list (Z * Z)) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (sp - 192) /\ getr R (reg 8) = Z_to_bv 64 (ois + 16) /\ getr R (reg 9) = Z_to_bv 64 (ois + 24)
  /\ getr R (reg 18) = Z_to_bv 64 8 /\ getr R (reg 19) = Z_to_bv 64 8 /\ getr R (reg 20) = Z_to_bv 64 os /\ getr R (reg 21) = Z_to_bv 64 (((ois + 16) / 8) + 2147450880)
  /\ getr R (reg 22) = Z_to_bv 64 1265600 /\ getr R (reg 23) = Z_to_bv 64 2147450880 /\ getr R (reg 24) = Z_to_bv 64 2147450880
  /\ getr R (reg 25) = Z_to_bv 64 1265968 /\ getr R (reg 26) = Z_to_bv 64 (((ois + 120) / 8) + 2147450880) /\ getr R (reg 27) = Z_to_bv 64 1266008
  /\ (forall k, In k CSK -> getr R (reg k) = getr R0 (reg k))
  /\ midc M model LK Aw.

(* [comment removed for export] *)
Definition mid2 (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LK : list fframe) (Aw : list (Z * Z)) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (sp - 192) /\ getr R (reg 8) = Z_to_bv 64 (ois + 16) /\ getr R (reg 9) = Z_to_bv 64 (ois + 24)
  /\ getr R (reg 18) = Z_to_bv 64 (ois + 80) /\ getr R (reg 19) = Z_to_bv 64 8 /\ getr R (reg 20) = Z_to_bv 64 os /\ getr R (reg 21) = Z_to_bv 64 (((ois + 16) / 8) + 2147450880)
  /\ getr R (reg 22) = Z_to_bv 64 1265600 /\ getr R (reg 23) = Z_to_bv 64 2147450880 /\ getr R (reg 24) = Z_to_bv 64 2147450880
  /\ getr R (reg 25) = Z_to_bv 64 1265968 /\ getr R (reg 26) = Z_to_bv 64 (((ois + 120) / 8) + 2147450880) /\ getr R (reg 27) = Z_to_bv 64 1266008
  /\ (forall k, In k CSK -> getr R (reg k) = getr R0 (reg k))
  /\ L5.u64_at RSEGS M (ois + 16) (pa_vp_strbuf PMA.AD) /\ PM.zeros_at M (ois + 32) 48 /\ PM.zeros_at M (ois + 80) 24
  /\ midc M model LK Aw.

End Call.
End PMAIS.
