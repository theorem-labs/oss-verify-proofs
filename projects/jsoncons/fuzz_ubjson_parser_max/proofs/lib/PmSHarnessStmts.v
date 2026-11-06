(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface LibIface L5Defs L5Core
PmLayout PmLayoutS PmModel PmModelFacts PmStatics PmSpecs PmSpecsS PmStep PmTopS.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PMH.
Import PMS.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Definition FRAME : Z := 752.
Definition SCR : Z := 65536.
Definition CSK : list nat := [3; 4; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Lemma CSK_in (KS : list nat) : forallb (fun k => existsb (Nat.eqb k) KS) CSK = true -> forall k, In k CSK -> In k KS.
Proof.
intros H k Hk. rewrite forallb_forall in H. specialize (H k Hk). apply existsb_exists in H. destruct H as (x & Hx & E). apply Nat.eqb_eq in E. subst x. exact Hx.
Qed.
Definition WF : list L5.range := map (fun iv => (fst iv, snd iv - fst iv)) (pm_foot AD).
Section Call.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Variable R0 : bvmap 5 word.
Variable M0 : word -> option byte.
Variable model0 : Model.
Variables (sp ptr ra n : Z).
Variable LB0 : list (Z * Z).
Variable cr0 : credit.
Variable g : PMST.st.
Definition fb : Z := sp - FRAME.
Definition P0 : credit := PM.pot_call L n.
Definition hcore (R : bvmap 5 word) (M : word -> option byte) (model : Model) : Prop :=
getr R (reg 2) = Z_to_bv 64 fb
/\ (forall k, In k CSK -> getr R (reg k) = getr R0 (reg k))
/\ L5.u64_at RSEGS M (fb + 744) ra /\ L5.u64_at RSEGS M (fb + 736) (bv_unsigned (getr R0 (reg 8)))
/\ L5C.stk (hl_sptop L) M fb (SCR - FRAME) /\ L5.defined M fb FRAME /\ sp <= hl_sptop L
/\ PMK.ek L LB0 sp SCR WF M0 M /\ (forall b, In b LB0 -> fst b + snd b <= hl_ceil L)
/\ PMST.base_ok RSEGS AD M
/\ model_but_vm model0 model /\ PMSP.model_ok model.
Definition T3 := PMSP.T3.
Definition T4 := PMSP.T4.
Abbreviation vstr_at := (PM.vstr_at RSEGS T3).
Abbreviation iss_at := (PM.iss_at RSEGS AD T3).
Abbreviation parser_at := (PM.parser_at RSEGS AD T3 T4).
Definition hstat (M : word -> option byte) (bl bs be : bool) : Prop :=
PMST.loc_ok RSEGS AD M bl /\ PMST.sys_ok RSEGS AD M bs /\ PMST.err_ok RSEGS AD M be.
Definition rest1 : credit := PM.credit_add (PM.cost1 L (n + 32))
(PM.credit_add (PM.credit_add (PM.cost1 L PM.CHUNK) (PM.cost1 L 32)) (PM.credit_add (PM.pot_stack L 0) (PM.pot_text L (PM.VShort 0) 0))).
Definition rest2 : credit :=
PM.credit_add (PM.credit_add (PM.cost1 L PM.CHUNK) (PM.cost1 L 32)) (PM.credit_add (PM.pot_stack L 0) (PM.pot_text L (PM.VShort 0) 0)).
Definition rest3 : credit := PM.credit_add (PM.pot_stack L 0) (PM.pot_text L (PM.VShort 0) 0).
Definition H1 (R : bvmap 5 word) (M : word -> option byte) (model : Model) (cr : credit) (s : PM.vstr) : Prop :=
hcore R M model /\ vstr_at M (fb + 712) s /\ PM.vs_size s = n
/\ hstat M (PMST.st_loc g) (PMST.st_sys g) (PMST.st_err g)
/\ hi_heap HI (PM.vs_own s ++ LB0) cr M (m_vmmaps model) /\ PMSP.credit_keep cr0 cr P0 rest1
/\ (forall c n' p, s = PM.VLong c n' p -> 23 <= n').
Definition H2 (R : bvmap 5 word) (M : word -> option byte) (model : Model) (cr : credit) (s s2 : PM.vstr) (sm : PM.strm) : Prop :=
hcore R M model /\ vstr_at M (fb + 712) s /\ PM.vs_size s = n
/\ iss_at M (fb + 440) s2 sm /\ PM.vs_size s2 = n /\ PM.sm_g sm = PM.vs_data (fb + 520) s2 /\ PM.sm_st sm = 0
/\ hstat M true (PMST.st_sys g) (PMST.st_err g)
/\ hi_heap HI (PM.vs_own s2 ++ PM.vs_own s ++ LB0) cr M (m_vmmaps model) /\ PMSP.credit_keep cr0 cr P0 rest2.
Definition H3 (R : bvmap 5 word) (M : word -> option byte) (model : Model) (cr : credit) (s s2 : PM.vstr) (sm : PM.strm) (qc b : Z) : Prop :=
hcore R M model /\ vstr_at M (fb + 712) s /\ PM.vs_size s = n
/\ iss_at M (fb + 440) s2 sm /\ PM.vs_size s2 = n /\ PM.sm_g sm = PM.vs_data (fb + 520) s2 /\ PM.sm_st sm = 0
/\ parser_at M (fb + 40) (fb + 440) (PMSP.parser_init qc b) /\ L5.u64_at RSEGS M (fb + 432) (pa_vp_visitor AD)
/\ hstat M true (PMST.st_sys g) (PMST.st_err g)
/\ hi_heap HI (PM.parser_own (PMSP.parser_init qc b) ++ PM.vs_own s2 ++ PM.vs_own s ++ LB0) cr M (m_vmmaps model)
/\ PMSP.credit_keep cr0 cr P0 rest3.
Definition H4 (R : bvmap 5 word) (M : word -> option byte) (model : Model) (cr : credit) (s s2 : PM.vstr) (sm : PM.strm) (qc b : Z) : Prop :=
hcore R M model /\ vstr_at M (fb + 712) s /\ PM.vs_size s = n
/\ iss_at M (fb + 440) s2 sm /\ PM.vs_size s2 = n /\ PM.sm_g sm = PM.vs_data (fb + 520) s2 /\ PM.sm_st sm = 0
/\ parser_at M (fb + 40) (fb + 440) (PMSP.parser_init qc b) /\ L5.u64_at RSEGS M (fb + 432) (pa_vp_visitor AD)
/\ hstat M true true (PMST.st_err g)
/\ hi_heap HI (PM.parser_own (PMSP.parser_init qc b) ++ PM.vs_own s2 ++ PM.vs_own s ++ LB0) cr M (m_vmmaps model)
/\ PMSP.credit_keep cr0 cr P0 rest3
/\ PMSP.ec_at RSEGS M (fb + 8) 0 (pa_syscat_obj AD) /\ L5.u64_at RSEGS M (fb + 424) (fb + 432).
Definition H5 (R : bvmap 5 word) (M : word -> option byte) (model : Model) (cr : credit) (s s2 : PM.vstr) (p : PM.pst) (sm : PM.strm) (be : bool) : Prop :=
hcore R M model /\ vstr_at M (fb + 712) s /\ PM.vs_size s = n
/\ iss_at M (fb + 440) s2 sm /\ parser_at M (fb + 40) (fb + 440) p
/\ hstat M true true be /\ (PMST.st_err g = true -> be = true)
/\ hi_heap HI (PM.parser_own p ++ PM.vs_own s2 ++ PM.vs_own s ++ LB0) cr M (m_vmmaps model)
/\ PMSP.credit_keep cr0 cr P0 PMSP.cr0.
Definition H6 (R : bvmap 5 word) (M : word -> option byte) (model : Model) (cr : credit) (s s2 tb : PM.vstr) (src : PM.srcst) (sm : PM.strm) (be : bool) : Prop :=
hcore R M model /\ vstr_at M (fb + 712) s /\ PM.vs_size s = n
/\ iss_at M (fb + 440) s2 sm /\ vstr_at M (fb + 376) tb
/\ PM.src_fields_at RSEGS T3 M (fb + 64) (fb + 440) (fb + 456) src /\ PM.nullis_at RSEGS AD T3 M (fb + 72)
/\ hstat M true true be /\ (PMST.st_err g = true -> be = true)
/\ hi_heap HI (PM.src_own src ++ PM.vs_own tb ++ PM.vs_own s2 ++ PM.vs_own s ++ LB0) cr M (m_vmmaps model)
/\ PMSP.credit_keep cr0 cr P0 PMSP.cr0.
Definition H7 (R : bvmap 5 word) (M : word -> option byte) (model : Model) (cr : credit) (s s2 : PM.vstr) (sm : PM.strm) (be : bool) : Prop :=
hcore R M model /\ vstr_at M (fb + 712) s /\ PM.vs_size s = n
/\ iss_at M (fb + 440) s2 sm
/\ hstat M true true be /\ (PMST.st_err g = true -> be = true)
/\ hi_heap HI (PM.vs_own s2 ++ PM.vs_own s ++ LB0) cr M (m_vmmaps model)
/\ PMSP.credit_keep cr0 cr P0 PMSP.cr0.
Definition hcore8 (R : bvmap 5 word) (M : word -> option byte) (model : Model) : Prop := hcore R M model.
Definition H8 (R : bvmap 5 word) (M : word -> option byte) (model : Model) (cr : credit) (s : PM.vstr) (be : bool) : Prop :=
hcore8 R M model /\ vstr_at M (fb + 712) s
/\ hstat M true true be /\ (PMST.st_err g = true -> be = true)
/\ hi_heap HI (PM.vs_own s ++ LB0) cr M (m_vmmaps model)
/\ PMSP.credit_keep cr0 cr P0 PMSP.cr0.
End Call.
End PMH.
