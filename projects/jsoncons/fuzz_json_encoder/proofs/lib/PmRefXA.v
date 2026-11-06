(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA LibIface FPSteps L5Defs L5Core.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA PmIcptIfaceA PmLibIfaceA PmLibDefs PmLibSpecs PmEncSpecs PmLibDefsA PmLibSpecsA PmLibSpecsXA PmLibSpecsW PmRef PmLibSpecsXAW.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMRXA.
Import PML PMR.
Section Inst.
Variable L : asan_layout.
(* [comment removed for export] *)
Definition rm_matchA (c : ctrl) (M : PMSA.mem) (P : Z) (ps : pstate) : Prop :=
  rm_core c ps /\
  (ps_st ps = ST_STRING ->
     c_sst c = ps_sst ps /\ c_dlen c = Z.of_nat (length (ps_buf ps)) /\ c_u8 c = u8_feeds u8_init (b256 (ps_buf ps)) /\
     (3 <= c_sst c <= 11 -> PMSA.u32 L M (P + 148) (c_cp c)) /\ (9 <= c_sst c <= 11 -> PMSA.u32 L M (P + 152) (c_cp2 c)) /\
     (exists t, PMSA.u8 L M (P + 220) t /\ 0 <= t <= 1)) /\      (* [comment removed for export] *)
  (ps_st ps = ST_NUMBER -> c_nst c = ps_nst ps /\ c_dlen c = Z.of_nat (length (ps_buf ps))).
Definition rm_staleA (c : ctrl) (M : PMSA.mem) (P : Z) (ps : pstate) : Prop := rm_core c ps.
Lemma rm_matchA_stale : forall c M P ps, rm_matchA c M P ps -> rm_staleA c M P ps.
Proof. intros c M P ps H. exact (proj1 H). Qed.
Lemma rm_staleA_eq : rm_staleA = PMR.rm_stale.
Proof. reflexivity. Qed.
Definition the_rmA : PMW.refmodel := PMW.RM ctrl rm_matchA rm_staleA rstep validate.
(* [comment removed for export] *)
Lemma rm_step_the_rmA : PMW.rm_step the_rmA = rstep.             Proof. reflexivity. Qed.
Lemma rm_validate_the_rmA : PMW.rm_validate the_rmA = validate.   Proof. reflexivity. Qed.
Lemma rm_match_the_rmA : PMW.rm_match the_rmA = rm_matchA.         Proof. reflexivity. Qed.
Lemma rm_stale_the_rmA : PMW.rm_stale the_rmA = rm_staleA.         Proof. reflexivity. Qed.
End Inst.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma kmax_begin : forall es a, PMXAW.kmax es (PMES.EvBegin a) = PMW.ind_k es (PMW.EkBegin a) + 0.
Proof. intros es a. rewrite PMXAW.kmax_kind, PMXAW.pay_hi_begin. reflexivity. Qed.
Lemma kmax_end : forall es, PMXAW.kmax es PMES.EvEnd = PMW.ind_k es PMW.EkEnd + 0.
Proof. intros es. rewrite PMXAW.kmax_kind, PMXAW.pay_hi_end. reflexivity. Qed.
Lemma kmax_null : forall es, PMXAW.kmax es PMES.EvNull <= PMW.ind_k es PMW.EkLit + AL_LIT.
Proof. intros es. rewrite PMXAW.kmax_kind. cbn [PMW.kind_of]. pose proof PMXAW.pay_hi_null. unfold AL_LIT. lia. Qed.
Lemma kmax_bool : forall es b, PMXAW.kmax es (PMES.EvBool b) <= PMW.ind_k es PMW.EkLit + AL_LIT.
Proof. intros es b. rewrite PMXAW.kmax_kind. cbn [PMW.kind_of]. pose proof (PMXAW.pay_hi_bool b). unfold AL_LIT. lia. Qed.
(* [comment removed for export] *)
Lemma kmax_u64 : forall es d, 0 <= d -> PMXAW.kmax es PMES.EvU64 <= PMW.ind_k es PMW.EkNum + al_num d.
Proof. intros es d Hd. rewrite PMXAW.kmax_kind, PMXAW.pay_hi_u64. cbn [PMW.kind_of]. unfold al_num. lia. Qed.
Lemma kmax_i64 : forall es d, 0 <= d -> PMXAW.kmax es PMES.EvI64 <= PMW.ind_k es PMW.EkNum + al_num d.
Proof. intros es d Hd. rewrite PMXAW.kmax_kind, PMXAW.pay_hi_i64. cbn [PMW.kind_of]. unfold al_num. lia. Qed.
Lemma kmax_dbl : forall es d, 0 <= d -> PMXAW.kmax es PMES.EvDbl <= PMW.ind_k es PMW.EkNum + al_num d.
Proof. intros es d Hd. rewrite PMXAW.kmax_kind, PMXAW.pay_hi_dbl. cbn [PMW.kind_of]. unfold al_num. lia. Qed.
Lemma kmax_raw : forall es tag bs d, tag = 2 \/ tag = 3 -> PMES.len bs <= d -> PMXAW.kmax es (PMES.EvStr tag bs) <= PMW.ind_k es PMW.EkNum + al_num d.
Proof. intros es tag bs d Ht Hd. unfold PMXAW.kmax. rewrite (proj1 (PMXAW.ind_raw_num es tag bs Ht)), (PMXAW.pay_hi_raw tag bs Ht). unfold al_num. lia. Qed.
(* [comment removed for export] *)
Lemma kmax_str : forall es tag bs d, PMES.len bs <= d -> PMXAW.kmax es (PMES.EvStr tag bs) <= PMW.ind_k es (PMW.kind_of (PMES.EvStr tag bs)) + al_str d.
Proof. intros es tag bs d Hd. rewrite PMXAW.kmax_kind. pose proof (PMXAW.pay_hi_str tag bs). unfold al_str. lia. Qed.
Lemma kmax_key : forall es bs d, PMES.len bs <= d -> PMXAW.kmax es (PMES.EvKey bs) <= PMW.ind_k es PMW.EkKey + al_str d.
Proof. intros es bs d Hd. rewrite PMXAW.kmax_kind. cbn [PMW.kind_of]. pose proof (PMXAW.pay_hi_key bs). unfold al_str. lia. Qed.
End PMRXA.
