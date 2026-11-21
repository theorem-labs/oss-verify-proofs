(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the library hand-off check is evaluated on the hand-off states the start-up certificate computes for each CONFIG_RSEQ value instead of the recorded ones; taken in part from projects/simdjson/fuzz_ondemand/proofs/lib/B/Atp_handoffA.v, lines 10, 50-54. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run Fs.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.AS Require Import PropExec ShapeAlg SpinAlg AsanAcct AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound
  BothStartupCert.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.A Require Import HandoffKit.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.B Require Import Layout RT_iface D_defs HandoffImage HandoffCLX RT_state RT_rep Atp_activewA.
Import ListNotations.
Import AX2. Import AX2S. Import AP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Instance hl_fx : PropExec.FPState := PropExec.fx0.

#[local] Existing Instance OSSVerify.Proofs.simdjson.fuzz_element.lib.A.Shadow.GWf.
Definition hs_lib_ok (ch : acs) : bool :=
  (hs_rw_cells ch 0x6b5380 [C8 (Z_to_bv 64 0)] && hs_rw_cells ch 0x6b53a0 [C1 z8; C1 z8]
   && hs_rw_cells ch 0x6b5420 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]
   && hs_rw_cells ch 0x6b5480 [C1 z8; C1 z8])%bool.

Section Lib.
Variables (A : atable) (nx0 : nat) (LIMIT : Z)
          (SINV : env -> (word -> option byte) -> Prop) (argH : env -> word -> bool) (FS0 : Fs).
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment bsegs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok bsegs A nx0 LIMIT SINV argH FS0 E ch R FULL model.

Theorem hs_lib_gen : forall A' : list (Z * Z),
  (forall p, page_allowedb (APS.allowA A E ch) p = true -> page_allowedb A' p = true) ->
  hs_lib_ok ch = true -> sj_lib (mH FULL model A').
Proof using SEGS_in_hull HULL_ok argH_high HC.
  intros A' HA' HT. unfold hs_lib_ok in HT.
  apply andb_prop in HT as [HT H4]. apply andb_prop in HT as [HT H3]. apply andb_prop in HT as [H1 H2].
  left. unfold lib0.
  split; [exact (hi_rw_cells A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA' _ _ H1)|].
  split; [exact (hi_rw_cells A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA' _ _ H2)|].
  split; [exact (hi_rw_cells A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA' _ _ H3)|].
  exact (hi_rw_cells A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA' _ _ H4).
Qed.

End Lib.

(* The hand-off states [AS/BothStartupCert.v] computes, one table per CONFIG_RSEQ value:
   [hs_lib_ok] is evaluated on each, per closed flag ([destruct b] leaves each branch
   closed for [vm_compute]; both branches are discharged). *)
Lemma HS_lib_ok : forall (b : bool) h ch, HS_both (rseq_z b) h = Some ch -> hs_lib_ok ch = true.
Proof. intros b. apply (HS_both_forall hs_lib_ok b). destruct b; vm_compute; reflexivity. Qed.
