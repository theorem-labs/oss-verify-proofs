(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run Fs.
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Import MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OSSVerify.Proofs.openssl.punycode.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.punycode.lib.B Require Import Layout Fz_defs.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec ShapeAlg SpinAlg AsanAcct AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound.
From OSSVerify.Proofs.openssl.punycode.lib.A Require Import HandoffKit.
From OSSVerify.Proofs.openssl.punycode.lib.B Require Import HandoffImage HandoffCells RT_state RT_rep RT_init.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP.
Open Scope Z_scope.

Definition hs_lib_ok (ch : acs) : bool :=
  (hs_cells ch G_MALLOC_IMPL [C8 (Z_to_bv 64 e_cmalloc)] && hs_cells ch G_FREE_IMPL [C8 (Z_to_bv 64 e_cfree)]
   && hs_rw_cells ch G_LATCH [C1 (hs_byte ch G_LATCH)])%bool.

Section Lib.
Variables (A : atable) (LIMIT : Z)
          (SINV : env -> (word -> option byte) -> Prop) (argH : env -> word -> bool) (ISP : Z) (FS0 : Fs).
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment bsegs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a /\ ISP <= bv_unsigned a.
Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok bsegs A LIMIT SINV argH ISP FS0 E ch R FULL model.

(* [comment removed for export] *)
Theorem hs_lib_gen : forall A' : list (Z * Z),
  (forall p, page_allowedb (APS.allowA A E ch) p = true -> page_allowedb A' p = true) ->
  hs_lib_ok ch = true -> LIB_A (mH FULL model A').
Proof.
  intros A' HA' HT. unfold hs_lib_ok in HT.
  apply andb_prop in HT as [HT H3]. apply andb_prop in HT as [H1 H2].
  unfold LIB_A. split; [|split].
  - exact (hi_ro_cells A LIMIT SINV argH ISP FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA' _ _ H1).
  - exact (hi_ro_cells A LIMIT SINV argH ISP FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA' _ _ H2).
  - exists (hs_byte ch G_LATCH).
    exact (hi_rw_cells A LIMIT SINV argH ISP FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA' _ _ H3).
Qed.

(* [comment removed for export] *)
Theorem hs_lib : hs_lib_ok ch = true -> LIB_A (mH FULL model (rtA_allow (sigma0 A E ch model))).
Proof. intros HT. exact (hs_lib_gen (rtA_allow (sigma0 A E ch model)) (ri_allow A E ch model) HT). Qed.

End Lib.
