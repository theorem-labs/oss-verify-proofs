(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run Fs.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.Lib Require Import MState Mem Frame Cells Step Arr Exec.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.A08 Require Import ImageA.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.Lib Require Import RzCPS.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.A08 Require Import Layout.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.A08 Require Import RT_iface D_libiface.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.AS Require Import PropExec ShapeAlg SpinAlg AsanAcct AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.AG Require Import HandoffKit.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.A08 Require Import HandoffImage HandoffCLX RT_state RT_rep RT_init.
Import ListNotations.
Import AX2. Import AX2S. Import AP.
Open Scope Z_scope.

Local Instance hl_fx : PropExec.FPState := PropExec.fx0.

(* [comment removed for export] *)
Definition hs_lib_ok (ch : acs) : bool :=
  (hs_rw_cells ch 0xd0400 [C4 (Z_to_bv 64 3)] && hs_rw_cells ch 0xd0440 [C8 (Z_to_bv 64 e_malloc)]
   && hs_rw_cells ch 0xd0460 [C8 (Z_to_bv 64 e_free)] && hs_rw_cells ch 0xd0420 [C8 (hs_word ch 0xd0420 8)])%bool.

Section Lib.
Variables (A : atable) (nx0 : nat) (LIMIT : Z)
          (SINV : env -> (word -> option byte) -> Prop) (argH : env -> word -> bool) (FS0 : Fs).
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment asegs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok asegs A nx0 LIMIT SINV argH FS0 E ch R FULL model.

(* [comment removed for export] *)
Theorem hs_lib_gen : forall A' : list (Z * Z),
  (forall p, page_allowedb (APS.allowA A E ch) p = true -> page_allowedb A' p = true) ->
  hs_lib_ok ch = true -> LIB_A (mH FULL model A').
Proof.
  intros A' HA' HT. unfold hs_lib_ok in HT.
  apply andb_prop in HT as [HT H4]. apply andb_prop in HT as [HT H3]. apply andb_prop in HT as [H1 H2].
  unfold LIB_A. split; [split; [|split]|].
  - exact (hi_rw_cells A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA' _ _ H1).
  - exact (hi_rw_cells A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA' _ _ H2).
  - exact (hi_rw_cells A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA' _ _ H3).
  - exists (hs_word ch 0xd0420 8).
    exact (hi_rw_cells A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA' _ _ H4).
Qed.

(* [comment removed for export] *)
Theorem hs_lib : hs_lib_ok ch = true -> LIB_A (mH FULL model (rtA_allow (sigma0 A E ch model))).
Proof. intros HT. exact (hs_lib_gen (rtA_allow (sigma0 A E ch model)) (ri_allow A E ch model) HT). Qed.

End Lib.
