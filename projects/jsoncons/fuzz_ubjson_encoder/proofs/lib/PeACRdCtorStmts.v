(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA L5Defs L5Core
     L5KnA L5LazyA L5DefsA L5CoreA L5StepAR PmLayout PmLayoutA PmModel PmStatics PmStaticsA HeapIfaceAEx PmSpecsA PeSpecsAa PnStatics PeCLayoutA PeCModelA PeCSpecsA PeCSpecsAa.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMARS.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition SCR : Z := 24576.                       (* [comment removed for export] *)
Definition iss_at := (PM.iss_at RSEGS PeCLayoutA.CADDR_A PMSPA.accA).

Section Call.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (HI : asan_iface).
Variables (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet).
Variables (LB : list (Z * Z)) (FF LK0 : list fframe) (Aw0 : list (Z * Z)) (cr : credit) (sp r fb oa : Z) (str : PM.vstr) (sm : PM.strm).

Definition op : Z := fb + 592.
Definition cost : credit := PMSPA.scA L (PM.credit_add (PM.cost1 (PMSPA.HV L ar) PM.CHUNK) (PM.cost1 (PMSPA.HV L ar) 32)).

(* [comment removed for export] *)
Definition pre : Prop :=
  ri_inv HI LB FF LK0 cr Aw0 M0 (vml_of model0) /\ L5CA.amodel_ok Aw0 model0 /\ K [] /\ PMSPA.entryA PeCLayoutA.CADDR_A L ar R0 M0 sp r 6
  /\ PMSPA.ffroomA 6 FF LK0 /\ PMSPA.ffrsA FF sp /\ PECA.frame_ok5 FF fb
  /\ getr R0 (reg 10) = Z_to_bv 64 op /\ getr R0 (reg 11) = Z_to_bv 64 (fb + 96) /\ getr R0 (reg 12) = Z_to_bv 64 (op + 464) /\ getr R0 (reg 13) = Z_to_bv 64 oa
  /\ L5.defined M0 op 384 /\ PMSPA.accA M0 op 384 /\ PMSPA.accA M0 (op + 464) 32
  /\ L5.u64_at RSEGS M0 (op + 464) (pa_vp_opts PeCLayoutA.CADDR_A) /\ L5.u64_at RSEGS M0 (op + 472) PM.MAX_ITEMS /\ L5.u32_at RSEGS M0 (op + 488) PM.MAX_DEPTH
  /\ iss_at M0 (fb + 96) str sm /\ PMSTA.base_okA RSEGS PeCLayoutA.CADDR_A M0 /\ PMST.loc_ok RSEGS PeCLayoutA.CADDR_A M0 true
  /\ PMSPA.credit_le cost cr.

(* [comment removed for export] *)
Definition kont : Prop :=
  forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (qc b : Z) (cr' : credit),
    regs_preserved R0 R' -> PM.parser_at RSEGS PeCLayoutA.CADDR_A PMSPA.accA PMSPA.annA M' op (fb + 96) (PMSPA.parser_init qc b) ->
    L5CA.ahpres L ar LB FF sp (PMSPA.pm_scr 6) [(op, 384)] M0 M' ->
    PMSPA.credit_keep cr cr' cost PMSPA.cr0 ->
    model_rt model0 model' -> incl LK' LK0 -> incl Aw0 Aw' -> L5CA.amodel_ok Aw' model' ->
    ri_inv HI (PM.parser_own (PMSPA.parser_init qc b) ++ LB) FF LK' cr' Aw' M' (vml_of model') ->
    srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx') R' r M' model') K.

(* [comment removed for export] *)
Definition saves_rd (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M (sp - 8) (bv_unsigned (getr R0 (reg 1))) /\ L5.u64_at RSEGS M (sp - 16) (bv_unsigned (getr R0 (reg 8)))
  /\ L5.u64_at RSEGS M (sp - 24) (bv_unsigned (getr R0 (reg 9))) /\ L5.u64_at RSEGS M (sp - 32) (bv_unsigned (getr R0 (reg 18)))
  /\ L5.u64_at RSEGS M (sp - 40) (bv_unsigned (getr R0 (reg 19))) /\ L5.u64_at RSEGS M (sp - 48) (bv_unsigned (getr R0 (reg 20)))
  /\ L5.u64_at RSEGS M (sp - 56) (bv_unsigned (getr R0 (reg 21))).
(* [comment removed for export] *)
Definition saves_src (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M (sp - 88) 0xb1618 /\ L5.u64_at RSEGS M (sp - 96) op /\ L5.u64_at RSEGS M (sp - 104) (op + 464)
  /\ L5.u64_at RSEGS M (sp - 112) (op + 24) /\ L5.u64_at RSEGS M (sp - 120) (bv_unsigned (getr R0 (reg 19))).
(* [comment removed for export] *)
Definition saves_nis (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M (sp - 136) 0xb1840 /\ L5.u64_at RSEGS M (sp - 144) (op + 32) /\ L5.u64_at RSEGS M (sp - 152) (op + 24)
  /\ L5.u64_at RSEGS M (sp - 160) (fb + 96) /\ L5.u64_at RSEGS M (sp - 168) 2147450880 /\ L5.u64_at RSEGS M (sp - 176) (bv_unsigned (getr R0 (reg 20)))
  /\ L5.u64_at RSEGS M (sp - 184) 2147450880.
(* [comment removed for export] *)
Definition hcells (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M op (pa_vp_parser PeCLayoutA.CADDR_A) /\ L5.u8_at RSEGS M (op + 8) 1 /\ L5.u8_at RSEGS M (op + 9) 0 /\ L5.u32_at RSEGS M (op + 12) 0
  /\ L5.u8_at RSEGS M (op + 16) 0 /\ L5.u32_at RSEGS M (op + 20) 0
  /\ L5.u64_at RSEGS M (op + 32) (pa_vp_nullis PeCLayoutA.CADDR_A) /\ L5.u64_at RSEGS M (op + 56) (pa_classic_imp PeCLayoutA.CADDR_A)
  /\ L5.u64_at RSEGS M (op + 112) (pa_vp_nullis_ios PeCLayoutA.CADDR_A) /\ L5.u32_at RSEGS M (op + 144) 0 /\ L5.u32_at RSEGS M (op + 148) 0
  /\ L5.u64_at RSEGS M (op + 152) (op + 48) /\ L5.u64_at RSEGS M (op + 160) (pa_classic_imp PeCLayoutA.CADDR_A) /\ PM.zeros_at M (op + 168) 80.

(* [comment removed for export] *)
Definition rmidc (M : word -> option byte) (model : Model) (LK : list fframe) (Aw : list (Z * Z)) : Prop :=
  saves_rd M /\ saves_src M /\ hcells M
  /\ L5.defined M op 384 /\ PMSPA.accA M op 384 /\ PMSPA.accA M (op + 464) 32
  /\ L5.u64_at RSEGS M (op + 464) (pa_vp_opts PeCLayoutA.CADDR_A) /\ L5.u64_at RSEGS M (op + 472) PM.MAX_ITEMS /\ L5.u32_at RSEGS M (op + 488) PM.MAX_DEPTH
  /\ PMSPA.accA M (fb + 96) 272
  /\ L5CA.astk ar M sp SCR /\ shadow_zero M (sp - SCR) (SCR / 8)
  /\ PMSTA.base_okA RSEGS PeCLayoutA.CADDR_A M /\ PMST.loc_ok RSEGS PeCLayoutA.CADDR_A M true
  /\ ri_inv HI LB FF LK cr Aw M (vml_of model) /\ L5CA.amodel_ok Aw model /\ model_rt model0 model /\ incl LK LK0 /\ incl Aw0 Aw
  /\ L5SAR.ek L ar LB FF sp SCR [(op, 384)] M0 M /\ L5SAR.dk L ar LB FF sp SCR M0 M.

(* [comment removed for export] *)
Definition rmid1 (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LK : list fframe) (Aw : list (Z * Z)) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (sp - 192) /\ getr R (reg 8) = Z_to_bv 64 (op + 32) /\ getr R (reg 9) = Z_to_bv 64 (op + 48)
  /\ getr R (reg 18) = Z_to_bv 64 (op + 112) /\ getr R (reg 19) = Z_to_bv 64 ((op + 48) / 8 + 2147450880)
  /\ getr R (reg 20) = Z_to_bv 64 ((op + 32) / 8 + 2147450880) /\ getr R (reg 21) = Z_to_bv 64 ((op + 112) / 8 + 2147450880)
  /\ (forall k, In k [3; 4; 22; 23; 24; 25; 26; 27]%nat -> getr R (reg k) = getr R0 (reg k))
  /\ L5.u64_at RSEGS M (fb + 96) (pa_vp_iss PeCLayoutA.CADDR_A) /\ L5.u64_at RSEGS M (fb + 256) (fb + 112)
  /\ saves_nis M /\ rmidc M model LK Aw.

(* [comment removed for export] *)
Definition rmid2 (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LK : list fframe) (Aw : list (Z * Z)) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (sp - 128) /\ getr R (reg 8) = Z_to_bv 64 (op + 32) /\ getr R (reg 9) = Z_to_bv 64 (op + 24)
  /\ getr R (reg 18) = Z_to_bv 64 (op + 304) /\ getr R (reg 19) = Z_to_bv 64 2147450880 /\ getr R (reg 21) = Z_to_bv 64 2147450880
  /\ (forall k, In k [3; 4; 22; 23; 24; 25; 26; 27]%nat -> getr R (reg k) = getr R0 (reg k))
  /\ L5.u64_at RSEGS M (op + 48) (pa_vp_nullbuf PeCLayoutA.CADDR_A) /\ L5.u64_at RSEGS M (op + 264) (fb + 96) /\ L5.u64_at RSEGS M (op + 272) (fb + 112)
  /\ PM.zeros_at M (op + 280) 16 /\ L5.u64_at RSEGS M (op + 296) PM.CHUNK /\ PM.zeros_at M (op + 304) 16
  /\ rmidc M model LK Aw.

End Call.
End PMARS.
