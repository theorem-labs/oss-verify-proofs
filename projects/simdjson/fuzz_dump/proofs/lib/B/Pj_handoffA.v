(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the library hand-off check is evaluated on the hand-off states the start-up certificate computes for each CONFIG_RSEQ value instead of the recorded ones. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run Fs.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Lib Require Import MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.AS Require Import PropExec ShapeAlg SpinAlg AsanAcct AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound
  BothStartupCert.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.A Require Import HandoffKit.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface D_defs HandoffImage HandoffCLX RT_state RT_rep Atp_activewA Atp_handoffA.
Import ListNotations.
Import AX2. Import AX2S. Import AP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Instance hl_fx : PropExec.FPState := PropExec.fx0.

#[local] Existing Instance OSSVerify.Proofs.simdjson.fuzz_dump.lib.A.Shadow.GWf.
Definition PJ_LOC_LO_AH : Z := 0x6a9ba8.
Definition loc0_cellsAH : list cell := [CB 3760 (repeat (Z_to_bv 8 0) 3760)].

Definition PJ_LOCKW_AH : Z := 0x6cb6d8.
Definition lockw_cellsAH : list cell := [C4 (Z_to_bv 64 0)].

Definition hs_libj_ok (ch : acs) : bool := (hs_lib_ok ch && hs_rw_cells ch PJ_LOC_LO_AH loc0_cellsAH && hs_rw_cells ch PJ_LOCKW_AH lockw_cellsAH)%bool.

Section Lib.
Variables (A : atable) (nx0 : nat) (LIMIT : Z)
          (SINV : env -> (word -> option byte) -> Prop) (argH : env -> word -> bool) (FS0 : Fs).
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment bsegs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok bsegs A nx0 LIMIT SINV argH FS0 E ch R FULL model.

Theorem hs_libj_gen : forall A' : list (Z * Z),
  (forall p, page_allowedb (APS.allowA A E ch) p = true -> page_allowedb A' p = true) ->
  hs_libj_ok ch = true -> sj_lib (mH FULL model A') /\ rw_cells bsegs (mH FULL model A') PJ_LOC_LO_AH loc0_cellsAH
                          /\ rw_cells bsegs (mH FULL model A') PJ_LOCKW_AH lockw_cellsAH.
Proof using SEGS_in_hull HULL_ok argH_high HC.
  intros A' HA' HT. unfold hs_libj_ok in HT. apply andb_prop in HT as [H12 H3]. apply andb_prop in H12 as [H1 H2]. split; [| split].
  - exact (hs_lib_gen A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA' H1).
  - exact (hi_rw_cells A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA' _ _ H2).
  - exact (hi_rw_cells A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA' _ _ H3).
Qed.

End Lib.

(* The hand-off states [AS/BothStartupCert.v] computes, one table per CONFIG_RSEQ value:
   [hs_libj_ok] is evaluated on each, per closed flag ([destruct b] leaves each branch
   closed for [vm_compute]; both branches are discharged). *)
Lemma HS_libj_ok : forall (b : bool) h ch, HS_both (rseq_z b) h = Some ch -> hs_libj_ok ch = true.
Proof. intros b. apply (HS_both_forall hs_libj_ok b). destruct b; vm_compute; reflexivity. Qed.
