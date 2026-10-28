(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core
     PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnLayoutS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmStatics PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSpecsS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMIS.
Import PMS.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Definition SCR : Z := 20480.                       (* [comment removed for export] *)
(* [comment removed for export] *)
Definition CSK : list nat := [3; 4; 24; 25; 26; 27]%nat.
Lemma CSK_in (KS : list nat) : forallb (fun k => existsb (Nat.eqb k) KS) CSK = true -> forall k, In k CSK -> In k KS.
Proof.
  intros H k Hk. rewrite forallb_forall in H. specialize (H k Hk). apply existsb_exists in H. destruct H as (x & Hx & E). apply Nat.eqb_eq in E. subst x. exact Hx.
Qed.
Definition vstr_at := (PM.vstr_at RSEGS PMSP.T3).
Definition iss_at := (PM.iss_at RSEGS AD PMSP.T3).

Section Call.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Variables (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet).
Variables (LB : list (Z * Z)) (cr : credit) (ois os sp r : Z) (s : PM.vstr) (b : bool).

Definition WF : list L5.range := (ois, 272) :: (if b then [] else PMSP.loc_W AD).
Definition cost : credit := PM.cost1 L (PM.vs_size s + 32).

(* [comment removed for export] *)
Definition pre : Prop :=
  hi_heap HI LB cr M0 (m_vmmaps model0) /\ PMSP.model_ok model0 /\ K [] /\ PMSP.entry AD L R0 M0 sp r 4
  /\ getr R0 (reg 10) = Z_to_bv 64 ois /\ getr R0 (reg 11) = Z_to_bv 64 os /\ getr R0 (reg 12) = Z_to_bv 64 8
  /\ sp <= ois /\ ois + 272 <= os /\ os + 24 <= hl_sptop L /\ ois mod 8 = 0 /\ os mod 8 = 0 /\ L5.defined M0 ois 272
  /\ vstr_at M0 os s /\ incl (PM.vs_own s) LB /\ PM.vs_size s < 2 ^ 26 /\ (forall c n p, s = PM.VLong c n p -> 23 <= n)
  /\ PMST.base_ok RSEGS AD M0 /\ PMST.loc_ok RSEGS AD M0 b
  /\ PMSP.credit_le cost cr.

(* [comment removed for export] *)
Definition kont : Prop :=
  forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (s' : PM.vstr) (sm : PM.strm) (cr' : credit),
    regs_preserved R0 R' -> iss_at M' ois s' sm -> PM.vs_size s' = PM.vs_size s ->
    PM.sm_g sm = PM.vs_data (ois + 80) s' -> PM.sm_st sm = 0 ->
    PMST.loc_ok RSEGS AD M' true ->
    L5C.hpres L LB sp (PMSP.pm_scr 4) WF M0 M' ->
    PMSP.credit_keep cr cr' cost PMSP.cr0 ->
    model_but_vm model0 model' -> hi_heap HI (PM.vs_own s' ++ LB) cr' M' (m_vmmaps model') ->
    srealizes RSEGS SCFG (PMSP.cfg RSEGS R' r M' model') K.

(* [comment removed for export] *)
Definition saves_iss (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M (sp - 8) (bv_unsigned (getr R0 (reg 1))) /\ L5.u64_at RSEGS M (sp - 16) (bv_unsigned (getr R0 (reg 8)))
  /\ L5.u64_at RSEGS M (sp - 24) (bv_unsigned (getr R0 (reg 9))) /\ L5.u64_at RSEGS M (sp - 32) (bv_unsigned (getr R0 (reg 18)))
  /\ L5.u64_at RSEGS M (sp - 40) (bv_unsigned (getr R0 (reg 19))) /\ L5.u64_at RSEGS M (sp - 48) (bv_unsigned (getr R0 (reg 20)))
  /\ L5.u64_at RSEGS M (sp - 56) (bv_unsigned (getr R0 (reg 21))) /\ L5.u64_at RSEGS M (sp - 64) (bv_unsigned (getr R0 (reg 22)))
  /\ L5.u64_at RSEGS M (sp - 72) (bv_unsigned (getr R0 (reg 23))).
Definition saves_sb (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M (sp - 88) 215696 /\ L5.u64_at RSEGS M (sp - 96) ois /\ L5.u64_at RSEGS M (sp - 104) os
  /\ L5.u64_at RSEGS M (sp - 112) 8 /\ L5.u64_at RSEGS M (sp - 120) (ois + 16) /\ L5.u64_at RSEGS M (sp - 128) (ois + 120)
  /\ L5.u64_at RSEGS M (sp - 136) 740848.
(* [comment removed for export] *)
Definition head_cells (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M ois (pa_vp_iss AD) /\ L5.u64_at RSEGS M (ois + 24) (pa_classic_imp AD)
  /\ L5.u64_at RSEGS M (ois + 120) (pa_vp_iss_ios AD) /\ L5.u32_at RSEGS M (ois + 152) 0 /\ L5.u32_at RSEGS M (ois + 156) 0
  /\ L5.u64_at RSEGS M (ois + 160) (ois + 16) /\ L5.u64_at RSEGS M (ois + 168) (pa_classic_imp AD) /\ PM.zeros_at M (ois + 176) 80.

(* [comment removed for export] *)
Definition mid (R : bvmap 5 word) (M : word -> option byte) (model : Model) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (sp - 144) /\ getr R (reg 8) = Z_to_bv 64 (ois + 16) /\ getr R (reg 9) = Z_to_bv 64 (ois + 24)
  /\ getr R (reg 19) = Z_to_bv 64 8 /\ getr R (reg 20) = Z_to_bv 64 os /\ getr R (reg 21) = Z_to_bv 64 740424
  /\ (forall k, In k CSK -> getr R (reg k) = getr R0 (reg k))
  /\ saves_iss M /\ saves_sb M /\ head_cells M
  /\ L5.defined M ois 272 /\ vstr_at M os s /\ L5C.stk (hl_sptop L) M sp SCR
  /\ PMST.base_ok RSEGS AD M /\ PMST.loc_ok RSEGS AD M true
  /\ hi_heap HI LB cr M (m_vmmaps model) /\ PMSP.model_ok model /\ model_but_vm model0 model
  /\ PMK.ek L LB sp SCR WF M0 M /\ PMK.dk L LB sp SCR M0 M.

End Call.
End PMIS.
