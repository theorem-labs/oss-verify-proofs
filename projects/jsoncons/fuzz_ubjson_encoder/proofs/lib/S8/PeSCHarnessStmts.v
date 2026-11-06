(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec StoreOk ShapeAlg SpinAlg HeapIface LibIface LibIfaceE L5Defs L5Core.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PmModel PmStatics PmSpecs PmStep PeSpecsS.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayout PeCLayoutS.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PeCSink PeCModel PeCSpecs PeCSpecsS PeCStatics PeCTopS.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.Spec Require Import UbjRefFactsS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PECH.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Plain.M.loaded_segments.
Abbreviation AD := PeCLayoutS.CADDR_S.
Abbreviation EE := PeCLayoutS.EADDR_S.

Definition FRAME : Z := 832.
Definition SCR : Z := 65536.

Definition SV : Z := 816.

Definition CSK : list nat := [3; 4; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Lemma CSK_in (KS : list nat) : forallb (fun k => existsb (Nat.eqb k) KS) CSK = true -> forall k, In k CSK -> In k KS.
Proof.
  intros H k Hk. rewrite forallb_forall in H. specialize (H k Hk). apply existsb_exists in H. destruct H as (x & Hx & E). apply Nat.eqb_eq in E. subst x. exact Hx.
Qed.

Definition WF : list L5.range := map (fun iv => (fst iv, snd iv - fst iv)) (pm_foot AD).

Section Call.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.
Variable L : heap_layout.
Variable HI : heap_iface.
Variable P : PESK.sink_policy.
Variable R0 : bvmap 5 word.
Variable M0 : word -> option byte.
Variable model0 : Model.
Variables (sp ptr ra : Z).
Variable payload : list byte.
Variable LB0 : list (Z * Z).
Variable cr0 : credit.
Variable g : PMST.st.

Definition n : Z := Z.of_nat (length payload).
Definition p : list Z := map bv_unsigned payload.
Definition fb : Z := sp - FRAME.

Definition P0 : credit := PEC.credit_add (PM.pot_call L n) (PEC.credit_add (PEC.pot_estack L 0) (PESK.sink_pot P 0)).

#[local] Notation T3 := PMSP.T3.
#[local] Notation T4 := PMSP.T4.
Abbreviation vstr_at := (PM.vstr_at RSEGS T3).
Abbreviation iss_at := (PM.iss_at RSEGS AD T3).
Abbreviation parser_at := (PM.parser_at RSEGS AD T3 T4).
Abbreviation enc_at := (PEC.enc_at RSEGS EE L T3 T4).
Abbreviation sink_at := (PESK.sink_at RSEGS L T3 T4 P).

Definition hcore (R : bvmap 5 word) (M : word -> option byte) (model : Model) : Prop :=
  getr R (reg 2) = Z_to_bv 64 fb
  /\ (forall k, In k CSK -> getr R (reg k) = getr R0 (reg k))
  /\ L5.u64_at RSEGS M (fb + 824) ra /\ L5.u64_at RSEGS M (fb + 816) (bv_unsigned (getr R0 (reg 8)))
  /\ L5C.stk (hl_sptop L) M fb (SCR - FRAME) /\ L5.defined M fb FRAME /\ sp <= hl_sptop L
  /\ PMK.ek L LB0 sp SCR WF M0 M /\ (forall b, In b LB0 -> fst b + snd b <= hl_ceil L)
  /\ PMST.base_ok RSEGS AD M
  /\ model_but_vm model0 model /\ PMSP.model_ok model.

Definition hstat (M : word -> option byte) (bl bs be : bool) : Prop :=
  PMST.loc_ok RSEGS AD M bl /\ PMST.sys_ok RSEGS AD M bs /\ PEST.err_ok RSEGS AD EE M be.

Definition rest1 : credit := PEC.credit_add (PM.cost1 L (n + 32)) (PEC.credit_add (PM.credit_add (PM.cost1 L PM.CHUNK) (PM.cost1 L 32))
                               (PEC.credit_add (PM.pot_parser L (PMSP.pst_reset (PMSP.parser_init 0 0))) (PEC.credit_add (PEC.pot_estack L 0) (PESK.sink_pot P 0)))).
Definition rest2 : credit := PEC.credit_add (PM.credit_add (PM.cost1 L PM.CHUNK) (PM.cost1 L 32))
                               (PEC.credit_add (PM.pot_parser L (PMSP.pst_reset (PMSP.parser_init 0 0))) (PEC.credit_add (PEC.pot_estack L 0) (PESK.sink_pot P 0))).
Definition rest3 : credit := PEC.credit_add (PM.pot_parser L (PMSP.pst_reset (PMSP.parser_init 0 0))) (PEC.credit_add (PEC.pot_estack L 0) (PESK.sink_pot P 0)).

Definition H1 (R : bvmap 5 word) (M : word -> option byte) (model : Model) (cr : credit) (s : PM.vstr) : Prop :=
  hcore R M model /\ vstr_at M (fb + 792) s /\ PM.vs_size s = n /\ L5.bytes_at RSEGS M (PM.vs_data (fb + 792) s) p
  /\ hstat M (PMST.st_loc g) (PMST.st_sys g) (PMST.st_err g)
  /\ hi_heap HI (PM.vs_own s ++ LB0) cr M (m_vmmaps model) /\ PMSP.credit_keep cr0 cr P0 rest1
  /\ (forall c n' q, s = PM.VLong c n' q -> 23 <= n').

Definition H2 (R : bvmap 5 word) (M : word -> option byte) (model : Model) (cr : credit) (s s2 : PM.vstr) (sm : PM.strm) : Prop :=
  hcore R M model /\ vstr_at M (fb + 792) s /\ PM.vs_size s = n
  /\ iss_at M (fb + 520) s2 sm /\ PM.vs_size s2 = n /\ PM.sm_g sm = PM.vs_data (fb + 600) s2 /\ PM.sm_st sm = 0
  /\ L5.bytes_at RSEGS M (PM.vs_data (fb + 600) s2) p
  /\ hstat M true (PMST.st_sys g) (PMST.st_err g)
  /\ hi_heap HI (PM.vs_own s2 ++ PM.vs_own s ++ LB0) cr M (m_vmmaps model) /\ PMSP.credit_keep cr0 cr P0 rest2.

Definition H3 (R : bvmap 5 word) (M : word -> option byte) (model : Model) (cr : credit) (s s2 : PM.vstr) (sm : PM.strm) (qc b : Z) : Prop :=
  hcore R M model /\ vstr_at M (fb + 792) s /\ PM.vs_size s = n
  /\ iss_at M (fb + 520) s2 sm /\ PM.vs_size s2 = n /\ PM.sm_g sm = PM.vs_data (fb + 600) s2 /\ PM.sm_st sm = 0
  /\ L5.bytes_at RSEGS M (PM.vs_data (fb + 600) s2) p
  /\ parser_at M (fb + 48) (fb + 520) (PMSP.parser_init qc b) /\ enc_at M (fb + 440) fb PEC.enc0 /\ sink_at M (fb + 496) PESK.sink0
  /\ hstat M true (PMST.st_sys g) (PMST.st_err g)
  /\ hi_heap HI (PM.parser_own (PMSP.parser_init qc b) ++ PM.vs_own s2 ++ PM.vs_own s ++ LB0) cr M (m_vmmaps model)
  /\ PMSP.credit_keep cr0 cr P0 rest3.

Definition H4 (R : bvmap 5 word) (M : word -> option byte) (model : Model) (cr : credit) (s s2 : PM.vstr) (sm : PM.strm) (qc b : Z) : Prop :=
  hcore R M model /\ vstr_at M (fb + 792) s /\ PM.vs_size s = n
  /\ PEC.crun_pre RSEGS AD EE L T3 T4 P M fb p UbjRef.init (PMSP.pst_reset (PMSP.parser_init qc b)) s2 sm PEC.enc0 PESK.sink0 (PMST.st_err g) (pa_syscat_obj AD)
  /\ PM.vs_size s2 = n
  /\ hstat M true true (PMST.st_err g)
  /\ hi_heap HI (PEC.owned (PMSP.pst_reset (PMSP.parser_init qc b)) PEC.enc0 PESK.sink0 ++ PM.vs_own s2 ++ PM.vs_own s ++ LB0) cr M (m_vmmaps model)
  /\ PMSP.credit_keep cr0 cr P0 rest3.

Definition H5 (R : bvmap 5 word) (M : word -> option byte) (model : Model) (cr : credit) (s s2 : PM.vstr) (sm : PM.strm)
           (s' : PM.pst) (en : PEC.enc) (k : PESK.sink) (be : bool) (nn : nat) : Prop :=
  hcore R M model /\ vstr_at M (fb + 792) s /\ PM.vs_size s = n
  /\ iss_at M (fb + 520) s2 sm /\ parser_at M (fb + 48) (fb + 520) s' /\ enc_at M (fb + 440) fb en /\ sink_at M (fb + 496) k /\ L5.defined M (fb + 16) 16
  /\ halted (run nn p UbjRef.init) = true /\ s_lo (run nn p UbjRef.init) <= PESK.sk_z k <= s_hi (run nn p UbjRef.init)
  /\ hstat M true true be /\ (PMST.st_err g = true -> be = true)
  /\ hi_heap HI (PEC.owned s' en k ++ PM.vs_own s2 ++ PM.vs_own s ++ LB0) cr M (m_vmmaps model)
  /\ PMSP.credit_keep cr0 cr P0 (PESK.sink_pot P (PESK.sk_c k)).

Definition H6 (R : bvmap 5 word) (M : word -> option byte) (model : Model) (cr : credit) (s s2 : PM.vstr) (sm : PM.strm) (be : bool) : Prop :=
  hcore R M model /\ vstr_at M (fb + 792) s /\ PM.vs_size s = n
  /\ iss_at M (fb + 520) s2 sm
  /\ hstat M true true be /\ (PMST.st_err g = true -> be = true)
  /\ hi_heap HI (PM.vs_own s2 ++ PM.vs_own s ++ LB0) cr M (m_vmmaps model)
  /\ PMSP.credit_keep cr0 cr P0 PMSP.cr0.

Definition H7 (R : bvmap 5 word) (M : word -> option byte) (model : Model) (cr : credit) (s : PM.vstr) (be : bool) : Prop :=
  hcore R M model /\ vstr_at M (fb + 792) s
  /\ hstat M true true be /\ (PMST.st_err g = true -> be = true)
  /\ hi_heap HI (PM.vs_own s ++ LB0) cr M (m_vmmaps model)
  /\ PMSP.credit_keep cr0 cr P0 PMSP.cr0.

End Call.
End PECH.
