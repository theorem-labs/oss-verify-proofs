(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec StoreOk HeapIface L5Defs L5Core PmLayout PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnLayoutS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSpecsS_u.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc PgV8 PnModel PnOwnerOk.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNOKS.
Import PMS.
Section WithHeap.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.

Definition owok_pre (fb : Z) : Prop :=
  hl_ceil L <= fb /\ fb + 784 <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47 /\ fb mod 16 = 0.

Local Ltac fin H T :=
  destruct H as (F1 & F2 & (T1 & T2) & F3); apply T;
  [exact (hio_wf L SCFG HI HIok)| rewrite (ly_img_lo L LY), (ly_img_hi L LY), (ly_errno L LY); lia| exact T2| unfold PNM.PSIZE; lia| unfold PNM.PSIZE; lia].

Theorem src_owner_ok_S fb s : owok_pre fb ->
  PGS.owner_ok RSEGS AD L HI (PNM.src_owner RSEGS AD PMSP.T3 PMSP.T4 (pa_vp_parser AD) (fb + 40) (fb + 472) fb (fb + 784) s).
Proof. intros H. fin H (PNOK.src_owner_ok RSEGS AD (pa_vp_parser AD) L HI (fb + 40) (fb + 472) fb (fb + 784) s). Qed.

Theorem txt_owner_ok_S fb s : owok_pre fb ->
  PGS.towner_ok RSEGS AD L HI (PNM.txt_owner RSEGS AD PMSP.T3 PMSP.T4 (pa_vp_parser AD) (fb + 40) (fb + 472) fb (fb + 784) s).
Proof. intros H. fin H (PNOK.txt_owner_ok RSEGS AD (pa_vp_parser AD) L HI (fb + 40) (fb + 472) fb (fb + 784) s). Qed.

Theorem vec_owner_ok_S fb s : owok_pre fb ->
  PGV8.vowner_ok RSEGS AD L HI (PNM.vec_owner RSEGS AD PMSP.T3 PMSP.T4 (pa_vp_parser AD) (fb + 40) (fb + 472) fb (fb + 784) s).
Proof. intros H. fin H (PNOK.vec_owner_ok RSEGS AD (pa_vp_parser AD) L HI (fb + 40) (fb + 472) fb (fb + 784) s). Qed.

End WithHeap.
End PNOKS.
