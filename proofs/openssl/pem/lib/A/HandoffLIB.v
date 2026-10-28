(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run Fs.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import PropExec ShapeAlg SpinAlg AsanAcct AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import HandoffKit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import HandoffImage HandoffCells RT_state RT_rep RT_init.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record cli_sigA : Type := mkCliA {
  ca_lib0 : mem -> Prop;                        (* [comment removed for export] *)
  ca_lib : list (Z * Z) -> mem -> Prop;         (* [comment removed for export] *)
  ca_sites : list (Z * Z);                      (* [comment removed for export] *)
  ca_calls : list (Z * Z);
  ca_test : acs -> bool                         (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Definition lib0_at_main (T : acs -> bool) (LIB0 : mem -> Prop) : Prop :=
  forall (A : atable) (LIMIT : Z) (SINV : env -> (word -> option byte) -> Prop) (argH : env -> word -> bool) (ISP : Z) (FS0 : Fs)
         (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model) (A' : list (Z * Z)),
    (forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment asegs (bv_unsigned a) 1 = None) ->
    APS.hull_ok A ->
    (forall E1 (a : word), argH E1 a = true -> CEIL <= bv_unsigned a /\ ISP <= bv_unsigned a) ->
    APS.cs_ok asegs A LIMIT SINV argH ISP FS0 E ch R FULL model ->
    (forall p, page_allowedb (APS.allowA A E ch) p = true -> page_allowedb A' p = true) ->
    img_hi A = SEGTOP_A -> img_lo A = SEGLO ->
    T ch = true -> LIB0 (mH FULL model A').

(* [comment removed for export] *)
Definition LIBpre (C : cli_sigA) (m : mem) : Prop := ca_lib0 C m /\ rw_cells asegs m TR_INIT [C1 (Z_to_bv 8 0)].

Lemma LIBpre_pre : forall C m, LIBpre C m -> ca_lib0 C m /\ rw_cells asegs m TR_INIT [C1 (Z_to_bv 8 0)].
Proof. intros C m H. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition hs_latch_ok (ch : acs) : bool := hs_rw_cells ch TR_INIT [C1 (Z_to_bv 8 0)].

Section Lib.
Variables (A : atable) (LIMIT : Z)
          (SINV : env -> (word -> option byte) -> Prop) (argH : env -> word -> bool) (ISP : Z) (FS0 : Fs).
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment asegs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a /\ ISP <= bv_unsigned a.
Hypothesis Hsegtop : img_hi A = SEGTOP_A.
Hypothesis Hseglo : img_lo A = SEGLO.
Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok asegs A LIMIT SINV argH ISP FS0 E ch R FULL model.
Variable C : cli_sigA.
Hypothesis HC0 : lib0_at_main (ca_test C) (ca_lib0 C).

(* [comment removed for export] *)
Theorem hs_latch_gen : forall A' : list (Z * Z),
  (forall p, page_allowedb (APS.allowA A E ch) p = true -> page_allowedb A' p = true) ->
  hs_latch_ok ch = true -> rw_cells asegs (mH FULL model A') TR_INIT [C1 (Z_to_bv 8 0)].
Proof.
  intros A' HA' HT. unfold hs_latch_ok in HT.
  exact (hi_rw_cells A LIMIT SINV argH ISP FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA' _ _ HT).
Qed.

Theorem hs_libpre_gen : forall A' : list (Z * Z),
  (forall p, page_allowedb (APS.allowA A E ch) p = true -> page_allowedb A' p = true) ->
  hs_latch_ok ch = true -> ca_test C ch = true -> LIBpre C (mH FULL model A').
Proof.
  intros A' HA' HT HTC. split.
  - exact (HC0 A LIMIT SINV argH ISP FS0 E ch R FULL model A' SEGS_in_hull HULL_ok argH_high HC HA' Hsegtop Hseglo HTC).
  - exact (hs_latch_gen A' HA' HT).
Qed.

(* [comment removed for export] *)
Theorem hs_libpre : hs_latch_ok ch = true -> ca_test C ch = true -> LIBpre C (mH FULL model (rtA_allow (sigma0 A E ch model))).
Proof. intros HT HTC. exact (hs_libpre_gen (rtA_allow (sigma0 A E ch model)) (ri_allow A E ch model) HT HTC). Qed.

End Lib.
