(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run Fs.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import PropExec ShapeAlg SpinAlg AsanAcct AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound
  StartupHSAsan.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import HandoffKit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface D_defs. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import HandoffImage HandoffCLX RT_state RT_rep Atp_activewA Atp_handoffA.
Import ListNotations.
Import AX2. Import AX2S. Import AP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Instance hl_fx : PropExec.FPState := PropExec.fx0.

#[local] Existing Instance OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A.Shadow.GWf.
Definition PJ_LOC_LO_AH : Z := 0x6a66a8.
Definition loc0_cellsAH : list cell := [CB 3760 (repeat (Z_to_bv 8 0) 3760)].

Definition PJ_LOCKW_AH : Z := 0x6c81d8.
Definition lockw_cellsAH : list cell := [C4 (Z_to_bv 64 0)].

Definition hs_libj_ok (ch : acs) : bool := (hs_lib_ok ch && hs_rw_cells ch PJ_LOC_LO_AH loc0_cellsAH && hs_rw_cells ch PJ_LOCKW_AH lockw_cellsAH)%bool.

Section Lib.
Variables (A : atable) (nx0 : nat) (LIMIT : Z)
          (SINV : env -> (word -> option byte) -> Prop) (argH : env -> word -> bool) (FS0 : Fs).
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment asegs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok asegs A nx0 LIMIT SINV argH FS0 E ch R FULL model.

Theorem hs_libj_gen : forall A' : list (Z * Z),
  (forall p, page_allowedb (APS.allowA A E ch) p = true -> page_allowedb A' p = true) ->
  hs_libj_ok ch = true -> sj_lib (mH FULL model A') /\ rw_cells asegs (mH FULL model A') PJ_LOC_LO_AH loc0_cellsAH
                          /\ rw_cells asegs (mH FULL model A') PJ_LOCKW_AH lockw_cellsAH.
Proof using SEGS_in_hull HULL_ok argH_high HC.
  intros A' HA' HT. unfold hs_libj_ok in HT. apply andb_prop in HT as [H12 H3]. apply andb_prop in H12 as [H1 H2]. split; [| split].
  - exact (hs_lib_gen A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA' H1).
  - exact (hi_rw_cells A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA' _ _ H2).
  - exact (hi_rw_cells A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA' _ _ H3).
Qed.

End Lib.

Lemma hs_libj_0 : hs_libj_ok HS_asan_0 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma hs_libj_1000 : hs_libj_ok HS_asan_1000 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma hs_libj_2000 : hs_libj_ok HS_asan_2000 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma hs_libj_3000 : hs_libj_ok HS_asan_3000 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma HS_libj_ok : forall h ch, HS_asan h = Some ch -> hs_libj_ok ch = true.
Proof.
  intros h ch. unfold HS_asan.
  apply (hs_if_some_lib (fun c => hs_libj_ok c = true)); [exact hs_libj_3000|].
  apply (hs_if_some_lib (fun c => hs_libj_ok c = true)); [exact hs_libj_2000|].
  apply (hs_if_some_lib (fun c => hs_libj_ok c = true)); [exact hs_libj_1000|].
  apply (hs_if_some_lib (fun c => hs_libj_ok c = true)); [exact hs_libj_0| discriminate].
Qed.
