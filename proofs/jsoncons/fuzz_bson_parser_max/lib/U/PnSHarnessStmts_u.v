(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface LibIface L5Defs L5Core
     PmLayout PmModel PmModelFacts PmStatics PmSpecs PmStep PgV8 PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnLayoutS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnModel PnStatics. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSpecsS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnRun. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnRunS_u PnTopS_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNH.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := PNRS.RSEGS.
Abbreviation AD := PNRS.AD.
Abbreviation AN := PNRS.AN.

Definition FRAME : Z := 784.
Definition SCR : Z := 65536.                      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition CSK : list nat := [3; 4; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Lemma CSK_in (KS : list nat) : forallb (fun k => existsb (Nat.eqb k) KS) CSK = true -> forall k, In k CSK -> In k KS.
Proof.
  intros H k Hk. rewrite forallb_forall in H. specialize (H k Hk). apply existsb_exists in H. destruct H as (x & Hx & E). apply Nat.eqb_eq in E. subst x. exact Hx.
Qed.
(* [comment removed for export] *)
Definition WF : list L5.range := map (fun iv => (fst iv, snd iv - fst iv)) (PNST.pn_foot AD AN).

Section Call.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Variable R0 : bvmap 5 word.
Variable M0 : word -> option byte.
Variable model0 : Model.
Variables (sp ptr ra n : Z).
Variable LB0 : list (Z * Z).
Variable cr0 : credit.
Variable g : PNST.st.

Definition fb : Z := sp - FRAME.
Definition P0 : credit := PNR.pot_callB L n.

(* [comment removed for export] *)
Definition hcore (R : bvmap 5 word) (M : word -> option byte) (model : Model) : Prop :=
  getr R (reg 2) = Z_to_bv 64 fb
  /\ (forall k, In k CSK -> getr R (reg k) = getr R0 (reg k))
  /\ L5.u64_at RSEGS M (fb + 776) ra /\ L5.u64_at RSEGS M (fb + 768) (bv_unsigned (getr R0 (reg 8)))
  /\ L5C.stk (hl_sptop L) M fb (SCR - FRAME) /\ L5.defined M fb FRAME /\ sp <= hl_sptop L
  /\ PMK.ek L LB0 sp SCR WF M0 M /\ (forall b, In b LB0 -> fst b + snd b <= hl_ceil L)
  /\ PMST.base_ok RSEGS AD M
  /\ model_but_vm model0 model /\ PMSP.model_ok model.

Definition T3 := PMSP.T3.
Definition T4 := PMSP.T4.
Abbreviation vstr_at := (PM.vstr_at RSEGS T3).
Abbreviation iss_at := (PM.iss_at RSEGS AD T3).
Abbreviation bparser_at := (PNM.bparser_at RSEGS AD T3 T4 (pa_vp_parser AD)).
Abbreviation v8_at := (PGV8.v8_at RSEGS T3 T4).

(* [comment removed for export] *)
Definition hstat (M : word -> option byte) (bl bs : bool) (ax : PNST.bax) : Prop :=
  PMST.loc_ok RSEGS AD M bl /\ PMST.sys_ok RSEGS AD M bs /\ PNST.berr_ok RSEGS AD AN M ax.

(* [comment removed for export] *)
Definition rest3 : credit :=
  PM.credit_add (PNR.pot_bstack L 0)
    (PM.credit_add (PM.pot_text L (PM.VShort 0) 0) (PM.credit_add (PM.pot_text L (PM.VShort 0) 0) (PGV8.pot_v8 L PGV8.V8Null 0))).
Definition rest2 : credit := PM.credit_add (PM.credit_add (PM.cost1 L PM.CHUNK) (PM.cost1 L PNM.BSZ)) rest3.
Definition rest1 : credit := PM.credit_add (PM.cost1 L (n + 32)) rest2.

(* [comment removed for export] *)
Definition H1 (R : bvmap 5 word) (M : word -> option byte) (model : Model) (cr : credit) (s : PM.vstr) : Prop :=
  hcore R M model /\ vstr_at M (fb + 744) s /\ PM.vs_size s = n
  /\ hstat M (PNST.st_loc g) (PNST.st_sys g) (PNST.st_ax g)
  /\ hi_heap HI (PM.vs_own s ++ LB0) cr M (m_vmmaps model) /\ PMSP.credit_keep cr0 cr P0 rest1
  /\ (forall c n' p, s = PM.VLong c n' p -> 23 <= n').       (* [comment removed for export] *)

(* [comment removed for export] *)
Definition H2 (R : bvmap 5 word) (M : word -> option byte) (model : Model) (cr : credit) (s s2 : PM.vstr) (sm : PM.strm) : Prop :=
  hcore R M model /\ vstr_at M (fb + 744) s /\ PM.vs_size s = n
  /\ iss_at M (fb + 472) s2 sm /\ PM.vs_size s2 = n /\ PM.sm_g sm = PM.vs_data (fb + 552) s2 /\ PM.sm_st sm = 0
  /\ hstat M true (PNST.st_sys g) (PNST.st_ax g)
  /\ hi_heap HI (PM.vs_own s2 ++ PM.vs_own s ++ LB0) cr M (m_vmmaps model) /\ PMSP.credit_keep cr0 cr P0 rest2.

(* [comment removed for export] *)
Definition H3 (R : bvmap 5 word) (M : word -> option byte) (model : Model) (cr : credit) (s s2 : PM.vstr) (sm : PM.strm) (qc b : Z) : Prop :=
  hcore R M model /\ vstr_at M (fb + 744) s /\ PM.vs_size s = n
  /\ iss_at M (fb + 472) s2 sm /\ PM.vs_size s2 = n /\ PM.sm_g sm = PM.vs_data (fb + 552) s2 /\ PM.sm_st sm = 0
  /\ bparser_at M (fb + 40) (fb + 472) (PNR.bparser_init qc b) /\ L5.u64_at RSEGS M (fb + 464) (pa_vp_visitor AD)
  /\ hstat M true (PNST.st_sys g) (PNST.st_ax g)
  /\ hi_heap HI (PNM.bparser_own (PNR.bparser_init qc b) ++ PM.vs_own s2 ++ PM.vs_own s ++ LB0) cr M (m_vmmaps model)
  /\ PMSP.credit_keep cr0 cr P0 rest3.

(* [comment removed for export] *)
Definition H4 (R : bvmap 5 word) (M : word -> option byte) (model : Model) (cr : credit) (s s2 : PM.vstr) (sm : PM.strm) (qc b : Z) : Prop :=
  hcore R M model /\ vstr_at M (fb + 744) s /\ PM.vs_size s = n
  /\ iss_at M (fb + 472) s2 sm /\ PM.vs_size s2 = n /\ PM.sm_g sm = PM.vs_data (fb + 552) s2 /\ PM.sm_st sm = 0
  /\ bparser_at M (fb + 40) (fb + 472) (PNR.bparser_init qc b) /\ L5.u64_at RSEGS M (fb + 464) (pa_vp_visitor AD)
  /\ hstat M true true (PNST.st_ax g)
  /\ hi_heap HI (PNM.bparser_own (PNR.bparser_init qc b) ++ PM.vs_own s2 ++ PM.vs_own s ++ LB0) cr M (m_vmmaps model)
  /\ PMSP.credit_keep cr0 cr P0 rest3
  /\ PMSP.ec_at RSEGS M (fb + 16) 0 (pa_syscat_obj AD) /\ L5.u64_at RSEGS M (fb + 456) (fb + 464).

(* [comment removed for export] *)
Definition H5 (R : bvmap 5 word) (M : word -> option byte) (model : Model) (cr : credit) (s s2 : PM.vstr) (p : PNM.bpst) (sm : PM.strm) (ax : PNST.bax) : Prop :=
  hcore R M model /\ vstr_at M (fb + 744) s /\ PM.vs_size s = n
  /\ iss_at M (fb + 472) s2 sm /\ bparser_at M (fb + 40) (fb + 472) p
  /\ hstat M true true ax /\ PNST.bax_le (PNST.st_ax g) ax
  /\ hi_heap HI (PNM.bparser_own p ++ PM.vs_own s2 ++ PM.vs_own s ++ LB0) cr M (m_vmmaps model)
  /\ PMSP.credit_keep cr0 cr P0 PMSP.cr0.

(* [comment removed for export] *)
Definition prest_at (M : word -> option byte) (src : PM.srcst) (bb : PGV8.v8) (nb tb : PM.vstr) : Prop :=
  PM.src_fields_at RSEGS T3 M (fb + 56) (fb + 472) (fb + 488) src /\ PM.nullis_at RSEGS AD T3 M (fb + 64)
  /\ v8_at M (fb + 360) bb /\ vstr_at M (fb + 384) nb /\ vstr_at M (fb + 408) tb.

(* [comment removed for export] *)
Definition H6 (R : bvmap 5 word) (M : word -> option byte) (model : Model) (cr : credit) (s s2 : PM.vstr) (src : PM.srcst) (bb : PGV8.v8)
           (nb tb : PM.vstr) (sm : PM.strm) (ax : PNST.bax) : Prop :=
  hcore R M model /\ vstr_at M (fb + 744) s /\ PM.vs_size s = n
  /\ iss_at M (fb + 472) s2 sm /\ prest_at M src bb nb tb
  /\ hstat M true true ax /\ PNST.bax_le (PNST.st_ax g) ax
  /\ hi_heap HI (PM.src_own src ++ PGV8.v8_own bb ++ PM.vs_own nb ++ PM.vs_own tb ++ PM.vs_own s2 ++ PM.vs_own s ++ LB0) cr M (m_vmmaps model)
  /\ PMSP.credit_keep cr0 cr P0 PMSP.cr0.

(* [comment removed for export] *)
Definition H7 (R : bvmap 5 word) (M : word -> option byte) (model : Model) (cr : credit) (s s2 : PM.vstr) (src : PM.srcst) (bb : PGV8.v8)
           (nb : PM.vstr) (sm : PM.strm) (ax : PNST.bax) : Prop :=
  hcore R M model /\ vstr_at M (fb + 744) s /\ PM.vs_size s = n
  /\ iss_at M (fb + 472) s2 sm
  /\ PM.src_fields_at RSEGS T3 M (fb + 56) (fb + 472) (fb + 488) src /\ PM.nullis_at RSEGS AD T3 M (fb + 64)
  /\ v8_at M (fb + 360) bb /\ vstr_at M (fb + 384) nb
  /\ hstat M true true ax /\ PNST.bax_le (PNST.st_ax g) ax
  /\ hi_heap HI (PM.src_own src ++ PGV8.v8_own bb ++ PM.vs_own nb ++ PM.vs_own s2 ++ PM.vs_own s ++ LB0) cr M (m_vmmaps model)
  /\ PMSP.credit_keep cr0 cr P0 PMSP.cr0.

(* [comment removed for export] *)
Definition H8 (R : bvmap 5 word) (M : word -> option byte) (model : Model) (cr : credit) (s s2 : PM.vstr) (src : PM.srcst) (bb : PGV8.v8)
           (sm : PM.strm) (ax : PNST.bax) : Prop :=
  hcore R M model /\ vstr_at M (fb + 744) s /\ PM.vs_size s = n
  /\ iss_at M (fb + 472) s2 sm
  /\ PM.src_fields_at RSEGS T3 M (fb + 56) (fb + 472) (fb + 488) src /\ PM.nullis_at RSEGS AD T3 M (fb + 64)
  /\ v8_at M (fb + 360) bb
  /\ hstat M true true ax /\ PNST.bax_le (PNST.st_ax g) ax
  /\ hi_heap HI (PM.src_own src ++ PGV8.v8_own bb ++ PM.vs_own s2 ++ PM.vs_own s ++ LB0) cr M (m_vmmaps model)
  /\ PMSP.credit_keep cr0 cr P0 PMSP.cr0.

(* [comment removed for export] *)
Definition H9 (R : bvmap 5 word) (M : word -> option byte) (model : Model) (cr : credit) (s s2 : PM.vstr) (sm : PM.strm) (ax : PNST.bax) : Prop :=
  hcore R M model /\ vstr_at M (fb + 744) s /\ PM.vs_size s = n
  /\ iss_at M (fb + 472) s2 sm
  /\ hstat M true true ax /\ PNST.bax_le (PNST.st_ax g) ax
  /\ hi_heap HI (PM.vs_own s2 ++ PM.vs_own s ++ LB0) cr M (m_vmmaps model)
  /\ PMSP.credit_keep cr0 cr P0 PMSP.cr0.

(* [comment removed for export] *)
Definition H10 (R : bvmap 5 word) (M : word -> option byte) (model : Model) (cr : credit) (s : PM.vstr) (ax : PNST.bax) : Prop :=
  hcore R M model /\ vstr_at M (fb + 744) s
  /\ hstat M true true ax /\ PNST.bax_le (PNST.st_ax g) ax
  /\ hi_heap HI (PM.vs_own s ++ LB0) cr M (m_vmmaps model)
  /\ PMSP.credit_keep cr0 cr P0 PMSP.cr0.

End Call.

(* [comment removed for export] *)
Record harness_deps {SCFG_P : ScfgP} {bmK : BMode} (L : heap_layout) (HI : heap_iface) : Prop := HDEPS {
  hd_str_ctor : PMS.str_ctor_spec L HI;
  hd_iss_ctor : PMS.iss_ctor_spec L HI;
  hd_reader_ctor : PNRS.reader_ctor_spec L HI;
  hd_syscat : PMS.syscat_spec L HI;
  hd_reset : PNRS.reset_spec L HI;
  hd_parse : PNRS.parse_spec L HI;
  hd_opdel : PMS.opdel_spec L HI;
  hd_src_dtor : PMS.src_dtor_spec L HI;
  hd_locale_dtor : PMS.locale_dtor_spec L;
  hd_ios_dtor : PMS.ios_dtor_spec L HI
}.
End PNH.
