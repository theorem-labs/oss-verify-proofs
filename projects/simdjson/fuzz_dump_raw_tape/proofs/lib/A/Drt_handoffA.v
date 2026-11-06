(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run Fs.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import PropExec ShapeAlg SpinAlg AsanAcct AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound
  StartupHSAsan.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Layout Shadow RT_iface D_defs HandoffKit HandoffImage HandoffCLX RT_state RT_rep Atp_activewA Atp_handoffA Pj_handoffA.
Import ListNotations.
Import AX2. Import AX2S. Import AP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Instance hl_fx : PropExec.FPState := PropExec.fx0.

#[local] Existing Instance OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.A.Shadow.GWf.

Definition EL_EHG_AH : Z := 0x69e678.
Definition ehg_cellsAH : list cell := [C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)].
Definition EL_UNW_AH : Z := 0x69ff90.
Definition unw0_cellsAH : list cell := repeat (C1 (Z_to_bv 8 0)) 8.
Definition EL_TPLOC_AH : Z := 0x6a0038.
Definition tploc_cellsAH : list cell := [C8 (Z_to_bv 64 0x6c0330)].

Definition hs_libdrt_ok (ch : acs) : bool :=
  (hs_libj_ok ch && hs_rw_cells ch EL_EHG_AH ehg_cellsAH && hs_rw_cells ch EL_UNW_AH unw0_cellsAH && hs_rw_cells ch EL_TPLOC_AH tploc_cellsAH)%bool.

Section Lib.
Variables (A : atable) (nx0 : nat) (LIMIT : Z)
          (SINV : env -> (word -> option byte) -> Prop) (argH : env -> word -> bool) (FS0 : Fs).
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment asegs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok asegs A nx0 LIMIT SINV argH FS0 E ch R FULL model.

Theorem hs_libdrt_gen : forall A' : list (Z * Z),
  (forall p, page_allowedb (APS.allowA A E ch) p = true -> page_allowedb A' p = true) ->
  hs_libdrt_ok ch = true ->
  (sj_lib (mH FULL model A') /\ rw_cells asegs (mH FULL model A') PJ_LOC_LO_AH loc0_cellsAH /\ rw_cells asegs (mH FULL model A') PJ_LOCKW_AH lockw_cellsAH)
  /\ rw_cells asegs (mH FULL model A') EL_EHG_AH ehg_cellsAH
  /\ rw_cells asegs (mH FULL model A') EL_UNW_AH unw0_cellsAH
  /\ rw_cells asegs (mH FULL model A') EL_TPLOC_AH tploc_cellsAH.
Proof using SEGS_in_hull HULL_ok argH_high HC.
  intros A' HA' HT. unfold hs_libdrt_ok in HT.
  apply andb_prop in HT as [H123 H4]. apply andb_prop in H123 as [H12 H3]. apply andb_prop in H12 as [H1 H2].
  split; [exact (hs_libj_gen A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA' H1)|].
  split; [exact (hi_rw_cells A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA' _ _ H2)|].
  split; [exact (hi_rw_cells A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA' _ _ H3)|].
  exact (hi_rw_cells A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA' _ _ H4).
Qed.
End Lib.

Lemma hs_libdrt_0 : hs_libdrt_ok HS_asan_0 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma hs_libdrt_1000 : hs_libdrt_ok HS_asan_1000 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma hs_libdrt_2000 : hs_libdrt_ok HS_asan_2000 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma hs_libdrt_3000 : hs_libdrt_ok HS_asan_3000 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma HS_libdrt_ok : forall h ch, HS_asan h = Some ch -> hs_libdrt_ok ch = true.
Proof.
  intros h ch. unfold HS_asan.
  apply (hs_if_some_lib (fun c => hs_libdrt_ok c = true)); [exact hs_libdrt_3000|].
  apply (hs_if_some_lib (fun c => hs_libdrt_ok c = true)); [exact hs_libdrt_2000|].
  apply (hs_if_some_lib (fun c => hs_libdrt_ok c = true)); [exact hs_libdrt_1000|].
  apply (hs_if_some_lib (fun c => hs_libdrt_ok c = true)); [exact hs_libdrt_0| discriminate].
Qed.
